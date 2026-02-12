// Code for manipulating stack locations.
//
// Copyright (C) 2009-2015  Kevin O'Connor <kevin@koconnor.net>
//
// This file may be distributed under the terms of the GNU LGPLv3 license.

#include "biosvar.h" // GET_GLOBAL
#include "bregs.h" // CR0_PE
#include "x86.h" // cr0_read
#include "fw/paravirt.h" // PORT_SMI_CMD
#include "hw/rtc.h" // rtc_use
#include "list.h" // hlist_node
#include "malloc.h" // free
#include "output.h" // dprintf
#include "romfile.h" // romfile_loadint
#include "stacks.h" // struct mutex_s
#include "string.h" // memset
#include "util.h" // useRTC

#define MAIN_STACK_MAX (1024*1024)


/****************************************************************
 * BIOS Proxy for V86 mode support
 *
 * When DOS runs under EMM386, BIOS handlers execute in V86 mode and cannot
 * switch to protected mode (call32 fails). We use a helper CPU core that
 * stays in real mode to execute BIOS calls on behalf of the V86-mode core.
 *
 * The helper core uses MONITOR/MWAIT on the request_pending field for
 * efficient low-latency wake-up.
 ****************************************************************/

/* Unique signature for CSMWrap to locate this structure */
#define BIOS_PROXY_SIGNATURE 0x79787250504D5343ULL  /* "CSMPPrxy" */

struct bios_proxy_mailbox {
    u64 signature;              /* offset 0: BIOS_PROXY_SIGNATURE - must be first */
    volatile u32 request_pending; /* offset 8: Non-zero when request waiting */
    u32 func_ptr;               /* offset 12: 32-bit flat function pointer */
    u32 arg_eax;                /* offset 16: Argument passed in EAX */
    u32 arg_edx;                /* offset 20: Argument passed in EDX */
    u32 arg_ecx;                /* offset 24: Argument passed in ECX */
    u32 result;                 /* offset 28: Return value from function */
    u32 helper_core_id;         /* offset 32: APIC ID of helper core */
};

/*
 * Mailbox in F-segment (ROM area) so it stays at a fixed offset in the binary.
 * CSMWrap finds this by scanning for the signature and calculates the runtime
 * address. The F-segment is safe from OS writes (treated as ROM shadow).
 */
struct bios_proxy_mailbox bios_proxy VARFSEG __aligned(8) = {
    .signature = BIOS_PROXY_SIGNATURE,
};


/****************************************************************
 * 16bit / 32bit calling
 ****************************************************************/

struct {
    u8 method;
    u8 cmosindex;
    u8 a20;
    u16 ss, fs, gs;
    u32 cr0;
    struct descloc_s gdt;
} Call16Data VARLOW;

#define C16_BIG 1
#define C16_SMM 2

int HaveSmmCall32 VARFSEG;

/*
 * Get current CPU's APIC ID.
 * Checks IA32_APIC_BASE MSR to determine if x2APIC mode is enabled.
 * - x2APIC mode (bit 10 set): read from MSR 0x802, full 32-bit ID
 * - xAPIC mode: read from MMIO at LAPIC base + 0x20, ID in bits 24-31
 */
static inline u32 get_current_apic_id(void)
{
    u64 apic_base_msr = rdmsr(0x1B);

    if (apic_base_msr & (1 << 10)) {
        /* x2APIC mode: read from MSR 0x802 */
        return (u32)rdmsr(0x802);
    } else {
        /* xAPIC mode: read from MMIO */
        u32 lapic_base = (u32)(apic_base_msr & 0xFFFFF000);
        return readl((void*)(lapic_base + 0x20)) >> 24;
    }
}

// Backup state in preparation for call32
static int
call32_prep(u8 method)
{
    if (!CONFIG_CALL32_SMM || method != C16_SMM) {
        // Backup cr0
        u32 cr0 = cr0_read();
        if (cr0 & CR0_PE)
            // Called in 16bit protected mode?!
            return -1;
        SET_LOW(Call16Data.cr0, cr0);

        // Backup fs/gs and gdt
        SET_LOW(Call16Data.fs, GET_SEG(FS));
        SET_LOW(Call16Data.gs, GET_SEG(GS));
        struct descloc_s gdt;
        sgdt(&gdt);
        SET_LOW(Call16Data.gdt.length, gdt.length);
        SET_LOW(Call16Data.gdt.addr, gdt.addr);

        // Enable a20 and backup its previous state
        SET_LOW(Call16Data.a20, set_a20(1));
    }

    // Backup ss
    SET_LOW(Call16Data.ss, GET_SEG(SS));

    // Backup cmos index register and disable nmi
    u8 cmosindex = inb(PORT_CMOS_INDEX);
    if (!(cmosindex & NMI_DISABLE_BIT)) {
        outb(cmosindex | NMI_DISABLE_BIT, PORT_CMOS_INDEX);
        inb(PORT_CMOS_DATA);
    }
    SET_LOW(Call16Data.cmosindex, cmosindex);

    SET_LOW(Call16Data.method, method);
    return 0;
}

// Restore state backed up during call32
static u8
call32_post(void)
{
    u8 method = GET_LOW(Call16Data.method);
    SET_LOW(Call16Data.method, 0);
    SET_LOW(Call16Data.ss, 0);

    if (!CONFIG_CALL32_SMM || method != C16_SMM) {
        // Restore a20
        u8 a20 = GET_LOW(Call16Data.a20);
        if (!a20)
            set_a20(0);

        // Restore gdt and fs/gs
        struct descloc_s gdt;
        gdt.length = GET_LOW(Call16Data.gdt.length);
        gdt.addr = GET_LOW(Call16Data.gdt.addr);
        lgdt(&gdt);
        SET_SEG(FS, GET_LOW(Call16Data.fs));
        SET_SEG(GS, GET_LOW(Call16Data.gs));

        // Restore cr0
        u32 cr0_caching = GET_LOW(Call16Data.cr0) & (CR0_CD|CR0_NW);
        if (cr0_caching)
            cr0_mask(CR0_CD|CR0_NW, cr0_caching);
    }

    // Restore cmos index register
    u8 cmosindex = GET_LOW(Call16Data.cmosindex);
    if (!(cmosindex & NMI_DISABLE_BIT)) {
        outb(cmosindex, PORT_CMOS_INDEX);
        inb(PORT_CMOS_DATA);
    }
    return method;
}

// Force next call16() to restore to a pristine cpu environment state
static void
call16_override(int big)
{
    ASSERT32FLAT();
    if (getesp() > BUILD_STACK_ADDR)
        panic("call16_override with invalid stack\n");
    memset(&Call16Data, 0, sizeof(Call16Data));
    if (big) {
        Call16Data.method = C16_BIG;
        Call16Data.a20 = 1;
    } else {
        Call16Data.a20 = !CONFIG_DISABLE_A20;
    }
}

// 16bit handler code called from call16() / call16_smm()
u32 VISIBLE16
call16_helper(u32 eax, u32 edx, u32 (*func)(u32 eax, u32 edx))
{
    u8 method = call32_post();
    u32 ret = func(eax, edx);
    call32_prep(method);
    return ret;
}

#define ASM32_SWITCH16 "  .pushsection .text.32fseg." UNIQSEC "\n  .code16\n"
#define ASM32_BACK32   "  .popsection\n  .code32\n"
#define ASM16_SWITCH32 "  .code32\n"
#define ASM16_BACK16   "  .code16gcc\n"

// Call a SeaBIOS C function in 32bit mode using smm trampoline
static u32
call32_smm(void *func, u32 eax)
{
    ASSERT16();
    dprintf(9, "call32_smm %p %x\n", func, eax);
    call32_prep(C16_SMM);
    u32 bkup_esp;
    asm volatile(
        // Backup esp / set esp to flat stack location
        "  movl %%esp, %0\n"
        "  movl %%ss, %%eax\n"
        "  shll $4, %%eax\n"
        "  addl %%eax, %%esp\n"

        // Transition to 32bit mode, call func, return to 16bit
        "  movl $" __stringify(CALL32SMM_CMDID) ", %%eax\n"
        "  movl $" __stringify(CALL32SMM_ENTERID) ", %%ecx\n"
        "  movl $(" __stringify(BUILD_BIOS_ADDR) " + 1f), %%ebx\n"
        "  outb %%al, $" __stringify(PORT_SMI_CMD) "\n"
        "  rep; nop\n"
        "  hlt\n"

        ASM16_SWITCH32
        "1:movl %1, %%eax\n"
        "  calll *%2\n"
        "  movl %%eax, %1\n"

        "  movl $" __stringify(CALL32SMM_CMDID) ", %%eax\n"
        "  movl $" __stringify(CALL32SMM_RETURNID) ", %%ecx\n"
        "  movl $2f, %%ebx\n"
        "  outb %%al, $" __stringify(PORT_SMI_CMD) "\n"
        "  rep; nop\n"
        "  hlt\n"

        // Restore esp
        ASM16_BACK16
        "2:movl %0, %%esp\n"
        : "=&r" (bkup_esp), "+r" (eax)
        : "r" (func)
        : "eax", "ecx", "edx", "ebx", "cc", "memory");
    call32_post();

    dprintf(9, "call32_smm done %p %x\n", func, eax);
    return eax;
}

static u32
call16_smm(u32 eax, u32 edx, void *func)
{
    ASSERT32FLAT();
    if (!CONFIG_CALL32_SMM)
        return eax;
    func -= BUILD_BIOS_ADDR;
    dprintf(9, "call16_smm %p %x %x\n", func, eax, edx);
    u32 stackoffset = Call16Data.ss << 4;
    asm volatile(
        // Restore esp
        "  subl %0, %%esp\n"

        // Transition to 16bit mode, call func, return to 32bit
        "  movl $" __stringify(CALL32SMM_CMDID) ", %%eax\n"
        "  movl $" __stringify(CALL32SMM_RETURNID) ", %%ecx\n"
        "  movl $(1f - " __stringify(BUILD_BIOS_ADDR) "), %%ebx\n"
        "  outb %%al, $" __stringify(PORT_SMI_CMD) "\n"
        "  rep; nop\n"
        "  hlt\n"

        ASM32_SWITCH16
        "1:movl %1, %%eax\n"
        "  movl %3, %%ecx\n"
        "  calll _cfunc16_call16_helper\n"
        "  movl %%eax, %1\n"

        "  movl $" __stringify(CALL32SMM_CMDID) ", %%eax\n"
        "  movl $" __stringify(CALL32SMM_ENTERID) ", %%ecx\n"
        "  movl $2f, %%ebx\n"
        "  outb %%al, $" __stringify(PORT_SMI_CMD) "\n"
        "  rep; nop\n"
        "  hlt\n"

        // Set esp to flat stack location
        ASM32_BACK32
        "2:addl %0, %%esp\n"
        : "+r" (stackoffset), "+r" (eax), "+d" (edx)
        : "r" (func)
        : "eax", "ecx", "ebx", "cc", "memory");
    return eax;
}

/*
 * Find the bios_proxy mailbox by scanning for its signature in the F-segment.
 * Returns the linear address of the mailbox, or 0 if not found.
 */
static u32
find_bios_proxy(void)
{
    u32 offset;
    u32 expect_lo = (u32)BIOS_PROXY_SIGNATURE;
    u32 expect_hi = (u32)(BIOS_PROXY_SIGNATURE >> 32);

    for (offset = 0; offset < 0xFFF0; offset += 8) {
        u32 sig_lo = GET_FARVAR(SEG_BIOS, *(u32 *)offset);
        u32 sig_hi = GET_FARVAR(SEG_BIOS, *(u32 *)(offset + 4));

        if (sig_lo == expect_lo && sig_hi == expect_hi)
            return (SEG_BIOS << 4) + offset;
    }
    return 0;
}

void
init_bios_proxy_addr(void)
{
    ASSERT32FLAT();
    /* Force the linker to include bios_proxy in the binary */
    if (bios_proxy.signature != BIOS_PROXY_SIGNATURE)
        return;
}

/*
 * Access mailbox fields via computed segment:offset from a linear address.
 */
#define GET_PROXY_AT(mb, field) ({                                              \
    u32 __addr = (mb) + offsetof(struct bios_proxy_mailbox, field);             \
    GET_FARVAR(FLATPTR_TO_SEG(__addr),                                          \
               *(typeof(bios_proxy.field) *)FLATPTR_TO_OFFSET(__addr));         \
})

#define SET_PROXY_AT(mb, field, val) do {                                       \
    u32 __addr = (mb) + offsetof(struct bios_proxy_mailbox, field);             \
    SET_FARVAR(FLATPTR_TO_SEG(__addr),                                          \
               *(typeof(bios_proxy.field) *)FLATPTR_TO_OFFSET(__addr), (val));  \
} while (0)

static u32
call32_proxy(void *func, u32 eax, u32 edx, u32 ecx)
{
    /*
     * Send request to helper core and wait for response.
     * Helper is guaranteed to be ready - CSMWrap waits for it before booting SeaBIOS.
     */
    u32 mb = find_bios_proxy();
    if (!mb)
        return 0;

    /* Set up the request */
    SET_PROXY_AT(mb, func_ptr, (u32)func);
    SET_PROXY_AT(mb, arg_eax, eax);
    SET_PROXY_AT(mb, arg_edx, edx);
    SET_PROXY_AT(mb, arg_ecx, ecx);

    /* Compiler barrier before signaling request */
    asm volatile("" ::: "memory");

    /* Signal request */
    SET_PROXY_AT(mb, request_pending, 1);

    /* Wait for helper to complete (clears request_pending when done) */
    while (GET_PROXY_AT(mb, request_pending)) {
        asm volatile("pause" ::: "memory");
    }

    return GET_PROXY_AT(mb, result);
}

// Call a 32bit SeaBIOS function from a 16bit SeaBIOS function.
u32 VISIBLE16
__call32(void *func, u32 eax, u32 errret)
{
    ASSERT16();
    if (CONFIG_CALL32_SMM && GET_GLOBAL(HaveSmmCall32))
        return call32_smm(func, eax);

    return call32_proxy(func, eax, 0, 0);
}

// Call a 16bit SeaBIOS function, restoring the mode from last call32().
static u32
call16(u32 eax, u32 edx, void *func)
{
    ASSERT32FLAT();
    if (getesp() > MAIN_STACK_MAX)
        panic("call16 with invalid stack\n");
    if (CONFIG_CALL32_SMM && Call16Data.method == C16_SMM)
        return call16_smm(eax, edx, func);

    extern void transition16big(void);
    extern void transition16(void);
    void *thunk = transition16;
    if (Call16Data.method == C16_BIG || in_post())
        thunk = transition16big;
    func -= BUILD_BIOS_ADDR;
    u32 stackseg = Call16Data.ss;
    asm volatile(
        // Transition to 16bit mode
        "  movl $(1f - " __stringify(BUILD_BIOS_ADDR) "), %%edx\n"
        "  jmp *%%ecx\n"
        // Setup ss/esp and call func
        ASM32_SWITCH16
        "1:movl %2, %%ecx\n"
        "  shll $4, %2\n"
        "  movw %%cx, %%ss\n"
        "  subl %2, %%esp\n"
        "  movw %%cx, %%ds\n"
        "  movl %4, %%edx\n"
        "  movl %3, %%ecx\n"
        "  calll _cfunc16_call16_helper\n"
        // Return to 32bit and restore esp
        "  movl $2f, %%edx\n"
        "  jmp transition32_nmi_off\n"
        ASM32_BACK32
        "2:addl %2, %%esp\n"
        : "+a" (eax), "+c"(thunk), "+r"(stackseg)
        : "r" (func), "r" (edx)
        : "edx", "cc", "memory");
    return eax;
}


/****************************************************************
 * Extra 16bit stack
 ****************************************************************/

// Space for a stack for 16bit code.
u8 ExtraStack[BUILD_EXTRA_STACK_SIZE+1] VARLOW __aligned(8);
u8 *StackPos VARLOW;

// Test if currently on the extra stack
int
on_extra_stack(void)
{
    return MODE16 && GET_SEG(SS) == SEG_LOW && getesp() > (u32)ExtraStack;
}

// Switch to the extra stack and call a function.
u32
__stack_hop(u32 eax, u32 edx, void *func)
{
    if (on_extra_stack())
        return ((u32 (*)(u32, u32))func)(eax, edx);
    ASSERT16();
    u16 stack_seg = SEG_LOW;
    u32 bkup_ss, bkup_esp;
    asm volatile(
        // Backup current %ss/%esp values.
        "movw %%ss, %w3\n"
        "movl %%esp, %4\n"
        // Copy stack seg to %ds/%ss and set %esp
        "movw %w6, %%ds\n"
        "movw %w6, %%ss\n"
        "movl %5, %%esp\n"
        "pushl %3\n"
        "pushl %4\n"
        // Call func
        "calll *%2\n"
        "popl %4\n"
        "popl %3\n"
        // Restore segments and stack
        "movw %w3, %%ds\n"
        "movw %w3, %%ss\n"
        "movl %4, %%esp"
        : "+a" (eax), "+d" (edx), "+c" (func), "=&r" (bkup_ss), "=&r" (bkup_esp)
        : "m" (StackPos), "r" (stack_seg)
        : "cc", "memory");
    return eax;
}

// Switch back to original caller's stack and call a function.
u32
__stack_hop_back(u32 eax, u32 edx, void *func)
{
    if (!MODESEGMENT)
        return call16(eax, edx, func);
    if (!MODE16 || !on_extra_stack())
        return ((u32 (*)(u32, u32))func)(eax, edx);
    ASSERT16();
    u16 bkup_ss;
    u32 bkup_stack_pos, temp;
    asm volatile(
        // Backup stack_pos and current %ss/%esp
        "movl %6, %4\n"
        "movw %%ss, %w3\n"
        "movl %%esp, %6\n"
        // Restore original callers' %ss/%esp
        "movl -4(%4), %5\n"
        "movl %5, %%ss\n"
        "movw %%ds:-8(%4), %%sp\n"
        "movl %5, %%ds\n"
        // Call func
        "calll *%2\n"
        // Restore %ss/%esp and stack_pos
        "movw %w3, %%ds\n"
        "movw %w3, %%ss\n"
        "movl %6, %%esp\n"
        "movl %4, %6"
        : "+a" (eax), "+d" (edx), "+c" (func), "=&r" (bkup_ss)
          , "=&r" (bkup_stack_pos), "=&r" (temp), "+m" (StackPos)
        :
        : "cc", "memory");
    return eax;
}


/****************************************************************
 * External 16bit interface calling
 ****************************************************************/

// Far call 16bit code with a specified register state.
void VISIBLE16
_farcall16(struct bregs *callregs, u16 callregseg)
{
    if (need_hop_back()) {
        stack_hop_back(_farcall16, callregs, callregseg);
        return;
    }
    ASSERT16();
    asm volatile(
        "calll __farcall16\n"
        : "+a" (callregs), "+m" (*callregs), "+d" (callregseg)
        :
        : "ebx", "ecx", "esi", "edi", "cc", "memory");
}

// Invoke external 16bit code.
void
farcall16(struct bregs *callregs)
{
    call16_override(0);
    _farcall16(callregs, 0);
}

// Invoke external 16bit code in "big real" mode.
void
farcall16big(struct bregs *callregs)
{
    call16_override(1);
    _farcall16(callregs, 0);
}

// Invoke a 16bit software interrupt.
void
__call16_int(struct bregs *callregs, u16 offset)
{
    callregs->code.offset = offset;
    if (!MODESEGMENT) {
        callregs->code.seg = SEG_BIOS;
        _farcall16((void*)callregs - Call16Data.ss * 16, Call16Data.ss);
        return;
    }
    callregs->code.seg = GET_SEG(CS);
    _farcall16(callregs, GET_SEG(SS));
}

// Reset the machine
void
reset(void)
{
    extern void reset_vector(void) __noreturn;
    if (!MODE16)
        call16(0, 0, reset_vector);
    reset_vector();
}


/****************************************************************
 * Threads
 ****************************************************************/

// Thread info - stored at bottom of each thread stack - don't change
// without also updating the inline assembler below.
struct thread_info {
    void *stackpos;
    struct hlist_node node;
};
struct thread_info MainThread VARFSEG = {
    NULL, { &MainThread.node, &MainThread.node.next }
};
#define THREADSTACKSIZE 4096

// Check if any threads are running.
static int
have_threads(void)
{
    return (CONFIG_THREADS
            && GET_FLATPTR(MainThread.node.next) != &MainThread.node);
}

// Return the 'struct thread_info' for the currently running thread.
struct thread_info *
getCurThread(void)
{
    u32 esp = getesp();
    if (esp <= MAIN_STACK_MAX)
        return &MainThread;
    return (void*)ALIGN_DOWN(esp, THREADSTACKSIZE);
}

static u8 CanInterrupt, ThreadControl;

// Initialize the support for internal threads.
void
thread_setup(void)
{
    CanInterrupt = 1;
    call16_override(1);
    if (! CONFIG_THREADS)
        return;
    ThreadControl = romfile_loadint("etc/threads", 1);
}

// Should hardware initialization threads run during optionrom execution.
int
threads_during_optionroms(void)
{
    return CONFIG_THREADS && CONFIG_RTC_TIMER && ThreadControl == 2 && in_post();
}

// Switch to next thread stack.
static void
switch_next(struct thread_info *cur)
{
    struct thread_info *next = container_of(
        cur->node.next, struct thread_info, node);
    if (cur == next)
        // Nothing to do.
        return;
    asm volatile(
        "  pushl $1f\n"                 // store return pc
        "  pushl %%ebp\n"               // backup %ebp
        "  movl %%esp, (%%eax)\n"       // cur->stackpos = %esp
        "  movl (%%ecx), %%esp\n"       // %esp = next->stackpos
        "  popl %%ebp\n"                // restore %ebp
        "  retl\n"                      // restore pc
        "1:\n"
        : "+a"(cur), "+c"(next)
        :
        : "ebx", "edx", "esi", "edi", "cc", "memory");
}

// Last thing called from a thread (called on MainThread stack).
static void
__end_thread(struct thread_info *old)
{
    hlist_del(&old->node);
    dprintf(DEBUG_thread, "\\%08x/ End thread\n", (u32)old);
    free(old);
    if (!have_threads())
        dprintf(1, "All threads complete.\n");
}

void VISIBLE16 check_irqs(void);

// Create a new thread and start executing 'func' in it.
void
run_thread(void (*func)(void*), void *data)
{
    ASSERT32FLAT();
    if (! CONFIG_THREADS || ! ThreadControl)
        goto fail;
    struct thread_info *thread;
    thread = memalign_tmphigh(THREADSTACKSIZE, THREADSTACKSIZE);
    if (!thread)
        goto fail;

    dprintf(DEBUG_thread, "/%08x\\ Start thread\n", (u32)thread);
    thread->stackpos = (void*)thread + THREADSTACKSIZE;
    struct thread_info *cur = getCurThread();
    struct thread_info *edx = cur;
    hlist_add_after(&thread->node, &cur->node);
    asm volatile(
        // Start thread
        "  pushl $1f\n"                 // store return pc
        "  pushl %%ebp\n"               // backup %ebp
        "  movl %%esp, (%%edx)\n"       // cur->stackpos = %esp
        "  movl (%%ebx), %%esp\n"       // %esp = thread->stackpos
        "  calll *%%ecx\n"              // Call func

        // End thread
        "  movl %%ebx, %%eax\n"         // %eax = thread
        "  movl 4(%%ebx), %%ebx\n"      // %ebx = thread->node.next
        "  movl (%5), %%esp\n"          // %esp = MainThread.stackpos
        "  calll %4\n"                  // call __end_thread(thread)
        "  movl -4(%%ebx), %%esp\n"     // %esp = next->stackpos
        "  popl %%ebp\n"                // restore %ebp
        "  retl\n"                      // restore pc
        "1:\n"
        : "+a"(data), "+c"(func), "+b"(thread), "+d"(edx)
        : "m"(*(u8*)__end_thread), "m"(MainThread)
        : "esi", "edi", "cc", "memory");
    if (cur == &MainThread)
        // Permit irqs to fire
        check_irqs();
    return;

fail:
    func(data);
}


/****************************************************************
 * Thread helpers
 ****************************************************************/

// Low-level irq enable.
void VISIBLE16
check_irqs(void)
{
    if (!MODESEGMENT && !CanInterrupt) {
        // Can't enable interrupts (PIC and/or IVT not yet setup)
        cpu_relax();
        return;
    }
    if (need_hop_back()) {
        stack_hop_back(check_irqs, 0, 0);
        return;
    }
    if (MODE16)
        clock_poll_irq();
    asm volatile("sti ; nop ; rep ; nop ; cli ; cld" : : :"memory");
}

// Briefly permit irqs to occur.
void
yield(void)
{
    if (MODESEGMENT || !CONFIG_THREADS) {
        check_irqs();
        return;
    }
    // On helper core, don't try thread switching - the helper runs on a
    // separate stack that isn't a valid thread_info structure.
    // Check by comparing current APIC ID against the helper's stored ID.
    volatile u32 *helper_id_ptr = (volatile u32 *)((u32)&bios_proxy
                                   + offsetof(struct bios_proxy_mailbox, helper_core_id));
    u32 helper_id = *helper_id_ptr;
    u32 my_id = get_current_apic_id();
    if (helper_id != 0 && my_id == helper_id) {
        asm volatile("pause" : : : "memory");
        return;
    }
    struct thread_info *cur = getCurThread();
    // Switch to the next thread
    switch_next(cur);
    if (cur == &MainThread)
        // Permit irqs to fire
        check_irqs();
}

void VISIBLE16
wait_irq(void)
{
    if (need_hop_back()) {
        stack_hop_back(wait_irq, 0, 0);
        return;
    }
    asm volatile("sti ; hlt ; cli ; cld": : :"memory");
}

// Wait for next irq to occur.
void
yield_toirq(void)
{
    if (!CONFIG_HARDWARE_IRQ
        || (!MODESEGMENT && (have_threads() || !CanInterrupt))) {
        // Threads still active or irqs not available - do a yield instead.
        yield();
        return;
    }
    wait_irq();
}

// Wait for all threads (other than the main thread) to complete.
void
wait_threads(void)
{
    ASSERT32FLAT();
    while (have_threads())
        yield();
}

void
mutex_lock(struct mutex_s *mutex)
{
    ASSERT32FLAT();
    if (! CONFIG_THREADS)
        return;
    while (mutex->isLocked)
        yield();
    mutex->isLocked = 1;
}

void
mutex_unlock(struct mutex_s *mutex)
{
    ASSERT32FLAT();
    if (! CONFIG_THREADS)
        return;
    mutex->isLocked = 0;
}


/****************************************************************
 * Thread preemption
 ****************************************************************/

int CanPreempt VARFSEG;
static u32 PreemptCount;

// Turn on RTC irqs and arrange for them to check the 32bit threads.
void
start_preempt(void)
{
    if (! threads_during_optionroms())
        return;
    CanPreempt = 1;
    PreemptCount = 0;
    rtc_use();
}

// Turn off RTC irqs / stop checking for thread execution.
void
finish_preempt(void)
{
    if (! threads_during_optionroms()) {
        yield();
        return;
    }
    CanPreempt = 0;
    rtc_release();
    dprintf(9, "Done preempt - %d checks\n", PreemptCount);
    yield();
}

// Check if preemption is on, and wait for it to complete if so.
int
wait_preempt(void)
{
    if (MODESEGMENT || !CONFIG_THREADS || !CanPreempt
        || getesp() < MAIN_STACK_MAX)
        return 0;
    while (CanPreempt)
        yield();
    return 1;
}

// Try to execute 32bit threads.
void VISIBLE32INIT
yield_preempt(void)
{
    PreemptCount++;
    switch_next(&MainThread);
}

// 16bit code that checks if threads are pending and executes them if so.
void
check_preempt(void)
{
    if (CONFIG_THREADS && GET_GLOBAL(CanPreempt) && have_threads())
        call32(yield_preempt, 0, 0);
}


/****************************************************************
 * call32 helper
 ****************************************************************/

/*
 * Helper struct for SMM path (which can't use the proxy)
 */
struct call32_params_s {
    void *func;
    u32 eax, edx, ecx;
};

u32 VISIBLE32FLAT
call32_params_helper(struct call32_params_s *params)
{
    return ((u32 (*)(u32, u32, u32))params->func)(
        params->eax, params->edx, params->ecx);
}

u32
__call32_params(void *func, u32 eax, u32 edx, u32 ecx, u32 errret)
{
    ASSERT16();
    if (CONFIG_CALL32_SMM && GET_GLOBAL(HaveSmmCall32)) {
        /* SMM path: use the old helper struct approach */
        struct call32_params_s params = {func, eax, edx, ecx};
        return call32_smm(call32_params_helper,
                          (u32)MAKE_FLATPTR(GET_SEG(SS), &params));
    }

    /* Proxy path: pass args directly via mailbox */
    return call32_proxy(func, eax, edx, ecx);
}
