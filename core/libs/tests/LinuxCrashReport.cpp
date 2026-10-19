#include <algorithm>
#include <cerrno>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <dlfcn.h>
#include <link.h>
#include <poll.h>
#include <pthread.h>
#include <string>
#include <sys/mman.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

namespace {

[[noreturn]] void Fail(const char* message) {
    std::fprintf(stderr, "%s\n", message);
    std::fflush(stderr);
    std::_Exit(1);
}

void* OpenLibc(const char* path) {
    void* library = dlopen(path, RTLD_NOW | RTLD_GLOBAL);
    if (library == nullptr) Fail(dlerror());
    return library;
}

int ExecutableBias(dl_phdr_info* info, std::size_t, void* bias) {
    *static_cast<std::uintptr_t*>(bias) = info->dlpi_addr;
    return 1;
}

void PrintBias() {
    std::uintptr_t bias = 0;
    dl_iterate_phdr(ExecutableBias, &bias);
    std::fprintf(stderr, "bias 0x%llx\n", static_cast<unsigned long long>(bias));
    std::fflush(stderr);
}

[[noreturn]] void ReadNullPage() {
    static const char narrow[] = "allocation failed in the heap";
    static const char16_t wide[] = u"LowLevelFatalError [File:Unknown] [Line: 42] Out of memory";
    static const std::uint8_t binary[] = {0x08, 0xd4, 0x8e, 0x5b, 0xf6, 0x7f, 0x00, 0x00};
    static const void* const table[8] = {narrow, wide, binary, nullptr, nullptr, nullptr, nullptr, nullptr};
    auto* pages = static_cast<char*>(mmap(nullptr, 0x2000, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0));
    if (pages == MAP_FAILED || mprotect(pages + 0x1000, 0x1000, PROT_NONE) != 0) Fail("cannot prepare the page edge");
    char* const edge = pages + 0x1000 - 8;
    std::memcpy(edge, "PAGE END", 8);
    PrintBias();
    std::fprintf(stderr, "narrow 0x%016llx\n", static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(narrow)));
    std::fflush(stderr);
    const std::uintptr_t unmapped = 8;
    asm volatile(
        "movq %0, %%r12\n\t"
        "movq %1, %%r13\n\t"
        "movq %2, %%r14\n\t"
        "movq %3, %%rbx\n\t"
        "movq %4, %%r15\n\t"
        "movq (%5), %%rax"
        :
        : "r"(narrow), "r"(wide), "r"(edge), "r"(binary), "r"(table), "r"(unmapped)
        : "rax", "rbx", "r12", "r13", "r14", "r15", "memory");
    Fail("the read of address 8 did not fault");
}

[[noreturn]] void WriteReadOnlyPage() {
    auto* page = static_cast<volatile char*>(mmap(nullptr, 0x1000, PROT_READ, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0));
    if (page == MAP_FAILED) Fail("cannot map a read-only page");
    std::fprintf(stderr, "page 0x%016llx\n", static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(page)));
    std::fflush(stderr);
    page[0] = 1;
    Fail("the write to a read-only page did not fault");
}

int LoaderEnd(dl_phdr_info* info, std::size_t, void* end) {
    if (std::strstr(info->dlpi_name, "ld-linux") == nullptr) return 0;
    for (int index = 0; index < info->dlpi_phnum; ++index) {
        const auto& segment = info->dlpi_phdr[index];
        if (segment.p_type != PT_LOAD) continue;
        *static_cast<std::uintptr_t*>(end) = std::max(*static_cast<std::uintptr_t*>(end), info->dlpi_addr + segment.p_vaddr + segment.p_memsz);
    }
    return 1;
}

[[noreturn]] void JumpToData() {
    std::uintptr_t loaderEnd = 0;
    dl_iterate_phdr(LoaderEnd, &loaderEnd);
    void* page = MAP_FAILED;
    if (loaderEnd != 0) page = mmap(reinterpret_cast<void*>((loaderEnd + 0xfff) & ~std::uintptr_t{0xfff}), 0x1000, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (page == MAP_FAILED) page = mmap(nullptr, 0x1000, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (page == MAP_FAILED) Fail("cannot map a data page");
    std::fprintf(stderr, "page 0x%016llx\n", static_cast<unsigned long long>(reinterpret_cast<std::uintptr_t>(page)));
    std::fflush(stderr);
    reinterpret_cast<void (*)()>(page)();
    Fail("the call into a data page did not fault");
}

[[noreturn]] void ExecuteUd2() {
    asm volatile("ud2");
    Fail("ud2 did not fault");
}

[[noreturn]] void ExecuteGuestAbort() {
    asm volatile("int $0x45");
    Fail("int 0x45 did not fault");
}

[[noreturn]] void DivideByZero() {
    volatile int zero = 0;
    const int divisor = zero;
    asm volatile("xorl %%edx, %%edx\n\tmovl $1, %%eax\n\tidivl %0" : : "r"(divisor) : "eax", "edx");
    Fail("the division by zero did not fault");
}

int Recurse(int depth) {
    volatile char frame[512];
    frame[0] = static_cast<char>(depth);
    return Recurse(depth + 1) + frame[0];
}

void* Overflow(void* install) {
    reinterpret_cast<void (*)()>(install)();
    Recurse(0);
    return nullptr;
}

[[noreturn]] void OverflowThreadStack(void* library) {
    void* install = dlsym(library, "LibcInstallSignalStack_nid_no_patch");
    if (install == nullptr) Fail("libc does not export LibcInstallSignalStack_nid_no_patch");
    pthread_attr_t attributes;
    pthread_attr_init(&attributes);
    pthread_attr_setstacksize(&attributes, 256 * 1024);
    pthread_t thread;
    if (pthread_create(&thread, &attributes, Overflow, install) != 0) Fail("cannot start the overflowing thread");
    pthread_join(thread, nullptr);
    Fail("the recursion did not overflow");
}

volatile bool g_sleeperReady = false;

void* Sleep(void*) {
    pthread_setname_np(pthread_self(), "crash-sleeper");
    g_sleeperReady = true;
    for (;;) pause();
}

[[noreturn]] void CrashBesideSleeper() {
    pthread_t thread;
    if (pthread_create(&thread, nullptr, Sleep, nullptr) != 0) Fail("cannot start the sleeping thread");
    while (!g_sleeperReady) sched_yield();
    timespec settle{0, 20000000};
    nanosleep(&settle, nullptr);
    *reinterpret_cast<volatile int*>(std::uintptr_t{8}) = 1;
    Fail("the write to address 8 did not fault");
}

int Increment(int value) {
    return value + 1;
}

[[noreturn]] void CrashAfterTracedCall(void* library) {
    using Trace = void* (*)(void*, const char*, const char*);
    auto trace = reinterpret_cast<Trace>(dlsym(library, "TraceImport_nid_no_patch"));
    if (trace == nullptr) Fail("libc does not export TraceImport_nid_no_patch");
    auto* traced = reinterpret_cast<int (*)(int)>(trace(reinterpret_cast<void*>(Increment), "Increment", "libTraced.prx"));
    if (traced == reinterpret_cast<int (*)(int)>(Increment)) Fail("the import was not traced");
    if (traced(41) != 42) Fail("the traced call returned a wrong value");
    *reinterpret_cast<volatile int*>(std::uintptr_t{8}) = 1;
    Fail("the write to address 8 did not fault");
}

void PreviousHandler(int, siginfo_t*, void*) {
    static const char message[] = "previous handler ran\n";
    const auto written = write(STDERR_FILENO, message, sizeof(message) - 1);
    (void)written;
    _exit(7);
}

void InstallPreviousHandler() {
    struct sigaction action {};
    action.sa_sigaction = PreviousHandler;
    action.sa_flags = SA_SIGINFO;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGSEGV, &action, nullptr) != 0) Fail("cannot install the previous handler");
}

int RunScenario(const char* libc, const std::string& scenario) {
    if (scenario == "chained") InstallPreviousHandler();
    if (scenario == "traced") setenv("APS5_TRACE_CALLS", "libTraced", 1);
    void* library = OpenLibc(libc);
    if (scenario == "read" || scenario == "chained") ReadNullPage();
    if (scenario == "write") WriteReadOnlyPage();
    if (scenario == "jump") JumpToData();
    if (scenario == "illegal") ExecuteUd2();
    if (scenario == "abort") ExecuteGuestAbort();
    if (scenario == "divide") DivideByZero();
    if (scenario == "overflow") OverflowThreadStack(library);
    if (scenario == "threads") CrashBesideSleeper();
    if (scenario == "traced") CrashAfterTracedCall(library);
    if (scenario == "sent") {
        raise(SIGSEGV);
        Fail("raise(SIGSEGV) returned");
    }
    Fail("unknown scenario");
}

struct Outcome {
    std::string output;
    int status;
};

Outcome Run(const char* self, const char* libc, const char* scenario, bool options = false) {
    int pipe[2];
    if (::pipe(pipe) != 0) Fail("cannot create the output pipe");
    const pid_t child = fork();
    if (child < 0) Fail("cannot fork");
    if (child == 0) {
        dup2(pipe[1], STDERR_FILENO);
        close(pipe[0]);
        close(pipe[1]);
        if (options) {
            setenv("APS5_CRASH_STACK_BYTES", "0x40", 1);
            setenv("APS5_CRASH_INDIRECT_MEMORY", "1", 1);
        }
        execl(self, self, libc, scenario, static_cast<char*>(nullptr));
        _exit(127);
    }
    close(pipe[1]);
    Outcome outcome{{}, 0};
    timespec start{};
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (;;) {
        timespec now{};
        clock_gettime(CLOCK_MONOTONIC, &now);
        if (now.tv_sec - start.tv_sec > 15) {
            kill(child, SIGKILL);
            std::fprintf(stderr, "%s timed out:\n%s\n", scenario, outcome.output.c_str());
            Fail("scenario timed out");
        }
        pollfd descriptor{pipe[0], POLLIN, 0};
        if (poll(&descriptor, 1, 1000) <= 0) continue;
        char buffer[4096];
        const ssize_t got = read(pipe[0], buffer, sizeof(buffer));
        if (got < 0 && errno == EINTR) continue;
        if (got <= 0) break;
        outcome.output.append(buffer, static_cast<std::size_t>(got));
    }
    close(pipe[0]);
    if (waitpid(child, &outcome.status, 0) != child) Fail("cannot wait for the scenario");
    return outcome;
}

void Require(bool condition, const char* scenario, const char* what, const Outcome& outcome) {
    if (condition) return;
    std::fprintf(stderr, "%s: %s\n--- output ---\n%s--- status 0x%x ---\n", scenario, what, outcome.output.c_str(), outcome.status);
    Fail("linux crash report check failed");
}

void RequireText(const Outcome& outcome, const char* scenario, const std::string& text) {
    Require(outcome.output.find(text) != std::string::npos, scenario, ("missing: " + text).c_str(), outcome);
}

void RequireSignal(const Outcome& outcome, const char* scenario, int signal) {
    Require(WIFSIGNALED(outcome.status) && WTERMSIG(outcome.status) == signal, scenario, "the process did not end with the fault's signal", outcome);
}

std::uint64_t HexAfter(const std::string& text, const std::string& marker, std::size_t from = 0) {
    const auto at = text.find(marker, from);
    if (at == std::string::npos) return 0;
    return std::strtoull(text.c_str() + at + marker.size(), nullptr, 16);
}

void CheckRead(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "read");
    RequireText(outcome, "read", "FATAL: signal 11 (SIGSEGV, SEGV_MAPERR) on thread ");
    RequireText(outcome, "read", "  read of 0x0000000000000008\n");
    RequireText(outcome, "read", "  [r12] \"allocation failed in the heap\"\n");
    RequireText(outcome, "read", "  [r13] u\"LowLevelFatalError [File:Unknown] [Line: 42] Out of memory\"\n");
    RequireText(outcome, "read", "  [r14] \"PAGE END\"...\n");
    RequireText(outcome, "read", "  frame pointer chain:\n");
    RequireText(outcome, "read", "  stack return address candidates:\n");
    Require(outcome.output.find("[rbx] \"") == std::string::npos && outcome.output.find("[rbx] u\"") == std::string::npos, "read", "binary memory was printed as text", outcome);
    const char* name = std::strrchr(self, '/');
    const std::string base = std::string(" ") + (name != nullptr ? name + 1 : self) + "+0x";
    const auto rip = HexAfter(outcome.output, "  rip 0x");
    const auto line = outcome.output.find("  rip 0x");
    const auto offset = HexAfter(outcome.output, base, line);
    Require(rip != 0 && offset != 0 && outcome.output.find(base, line) < outcome.output.find('\n', line), "read", "rip is not described as an offset in the test executable", outcome);
    Require(rip - offset == HexAfter(outcome.output, "bias 0x"), "read", "the rip offset does not match the executable's load bias", outcome);
    RequireSignal(outcome, "read", SIGSEGV);
}

void CheckOptions(const char* self, const char* libc) {
    const auto plain = Run(self, libc, "read");
    Require(plain.output.find("stack words from rsp") == std::string::npos && plain.output.find("  [[") == std::string::npos, "read", "the optional dumps were printed without their variables", plain);
    const auto outcome = Run(self, libc, "read", true);
    RequireText(outcome, "read with options", " (APS5_CRASH_STACK_BYTES):\n    +0x0000: ");
    RequireText(outcome, "read with options", "  data at stack words that point outside the stack (8 words each):\n");
    char expected[64];
    std::snprintf(expected, sizeof(expected), "  [[r15+0x0]] @%016llx ", static_cast<unsigned long long>(HexAfter(outcome.output, "narrow 0x")));
    RequireText(outcome, "read with options", expected);
    RequireSignal(outcome, "read with options", SIGSEGV);
}

void CheckJump(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "jump");
    RequireText(outcome, "jump", "FATAL: signal 11 (SIGSEGV, SEGV_ACCERR)");
    const auto page = HexAfter(outcome.output, "page 0x");
    char expected[96];
    std::snprintf(expected, sizeof(expected), "  rip 0x%016llx\n  execute of 0x%016llx\n", static_cast<unsigned long long>(page), static_cast<unsigned long long>(page));
    RequireText(outcome, "jump", expected);
    RequireText(outcome, "jump", "    [rsp+0x0] 0x");
    RequireText(outcome, "jump", "  recently popped return address candidates:\n");
    RequireSignal(outcome, "jump", SIGSEGV);
}

void CheckWrite(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "write");
    RequireText(outcome, "write", "FATAL: signal 11 (SIGSEGV, SEGV_ACCERR)");
    const auto page = HexAfter(outcome.output, "page 0x");
    char expected[64];
    std::snprintf(expected, sizeof(expected), "  write of 0x%016llx\n", static_cast<unsigned long long>(page));
    RequireText(outcome, "write", expected);
    RequireSignal(outcome, "write", SIGSEGV);
}

void CheckIllegal(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "illegal");
    RequireText(outcome, "illegal", "FATAL: signal 4 (SIGILL, ILL_ILLOPN)");
    RequireText(outcome, "illegal", "  bytes 0f 0b");
    RequireSignal(outcome, "illegal", SIGILL);
}

void CheckGuestAbort(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "abort");
    RequireText(outcome, "abort", "FATAL: signal 11 (SIGSEGV, SI_KERNEL)");
    RequireText(outcome, "abort", "  general protection fault, no fault address\n  guest abort() (int 0x45)\n");
    RequireSignal(outcome, "abort", SIGSEGV);
}

void CheckDivide(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "divide");
    RequireText(outcome, "divide", "FATAL: signal 8 (SIGFPE, FPE_INTDIV)");
    RequireSignal(outcome, "divide", SIGFPE);
}

void CheckOverflow(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "overflow");
    RequireText(outcome, "overflow", "FATAL: signal 11 (SIGSEGV, ");
    RequireText(outcome, "overflow", "  the fault address is next to rsp, outside readable memory: likely a stack overflow\n");
    RequireSignal(outcome, "overflow", SIGSEGV);
}

void CheckThreads(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "threads");
    RequireText(outcome, "threads", "  write of 0x0000000000000008\n");
    RequireText(outcome, "threads", "  all threads:\n");
    RequireText(outcome, "threads", " 'crash-sleeper': rip 0x");
    Require(outcome.output.find("did not answer") == std::string::npos, "threads", "a thread did not answer", outcome);
    RequireSignal(outcome, "threads", SIGSEGV);
}

void CheckTraced(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "traced");
    RequireText(outcome, "traced", "  last traced system library calls (APS5_TRACE_CALLS):\n    #1 thread ");
    RequireText(outcome, "traced", " libTraced.prx Increment from 0x");
    RequireText(outcome, "traced", "  last traced calls of thread ");
    RequireText(outcome, "traced", "  most called traced imports (1 calls in total):\n               1 libTraced.prx Increment\n");
    RequireSignal(outcome, "traced", SIGSEGV);
}

void CheckChained(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "chained");
    const auto report = outcome.output.find("FATAL: signal 11 (SIGSEGV, SEGV_MAPERR)");
    const auto previous = outcome.output.find("previous handler ran\n");
    Require(report != std::string::npos && previous != std::string::npos && report < previous, "chained", "the previous handler did not run after the report", outcome);
    Require(WIFEXITED(outcome.status) && WEXITSTATUS(outcome.status) == 7, "chained", "the previous handler did not end the process", outcome);
}

void CheckSent(const char* self, const char* libc) {
    const auto outcome = Run(self, libc, "sent");
    RequireText(outcome, "sent", "FATAL: signal 11 (SIGSEGV, SI_TKILL)");
    RequireText(outcome, "sent", "  sent by process ");
    RequireSignal(outcome, "sent", SIGSEGV);
}

}

int main(int argc, char** argv) {
    if (argc == 3) return RunScenario(argv[1], argv[2]);
    if (argc != 2) {
        std::fprintf(stderr, "usage: %s <libc.prx>\n", argv[0]);
        return 2;
    }
    char self[4096];
    const ssize_t length = readlink("/proc/self/exe", self, sizeof(self) - 1);
    if (length <= 0) Fail("cannot find the test executable");
    self[length] = '\0';
    CheckRead(self, argv[1]);
    CheckOptions(self, argv[1]);
    CheckWrite(self, argv[1]);
    CheckJump(self, argv[1]);
    CheckIllegal(self, argv[1]);
    CheckGuestAbort(self, argv[1]);
    CheckDivide(self, argv[1]);
    CheckOverflow(self, argv[1]);
    CheckThreads(self, argv[1]);
    CheckTraced(self, argv[1]);
    CheckChained(self, argv[1]);
    CheckSent(self, argv[1]);
    std::puts("linux crash report: 13 runs passed");
    return 0;
}
