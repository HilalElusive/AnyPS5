#if defined(__linux__)
#include "prx/libc/include/CallTrace.hpp"
#include "prx/libc/include/CrashText.hpp"
#include "prx/libc/include/FailureReport.hpp"
#include "prx/libc/include/Shutdown.hpp"
#include "prx/libc/include/SignalStack.hpp"
#include <algorithm>
#include <atomic>
#include <cerrno>
#include <csignal>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <dlfcn.h>
#include <fcntl.h>
#include <link.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <time.h>
#include <ucontext.h>
#include <unistd.h>

#if defined(__GLIBC__) && (__GLIBC__ > 2 || (__GLIBC__ == 2 && __GLIBC_MINOR__ >= 35))
#define APS5_CRASH_FIND_OBJECT 1
#endif

namespace {

constexpr std::uint64_t PageSize = 0x1000;
constexpr std::size_t SignalStackBytes = 0x10000;
constexpr int FatalSignals[] = {SIGSEGV, SIGBUS, SIGILL, SIGFPE};
constexpr std::size_t FatalSignalCount = sizeof(FatalSignals) / sizeof(FatalSignals[0]);
constexpr std::uint64_t PageFaultTrap = 14;
constexpr std::uint64_t PageFaultWrite = 0x2;
constexpr std::uint64_t PageFaultFetch = 0x10;

class Line {
public:
    Line& Text(const char* text) {
        while (*text != '\0' && _length < sizeof(_buffer)) _buffer[_length++] = *text++;
        return *this;
    }

    Line& Character(char character) {
        if (_length < sizeof(_buffer)) _buffer[_length++] = character;
        return *this;
    }

    Line& Hex(std::uint64_t value, int digits) {
        char reversed[16];
        int count = 0;
        do {
            reversed[count++] = "0123456789abcdef"[value & 15];
            value >>= 4;
        } while (value != 0 && count < 16);
        while (count < digits && count < 16) reversed[count++] = '0';
        while (count > 0) Character(reversed[--count]);
        return *this;
    }

    Line& Address(std::uint64_t value) {
        return Text("0x").Hex(value, 16);
    }

    Line& Decimal(std::uint64_t value) {
        char reversed[20];
        int count = 0;
        do {
            reversed[count++] = static_cast<char>('0' + value % 10);
            value /= 10;
        } while (value != 0);
        while (count > 0) Character(reversed[--count]);
        return *this;
    }

    void Write() {
        const char* cursor = _buffer;
        std::size_t left = _length;
        while (left > 0) {
            const ssize_t written = ::write(STDERR_FILENO, cursor, left);
            if (written < 0 && errno == EINTR) continue;
            if (written <= 0) break;
            cursor += written;
            left -= static_cast<std::size_t>(written);
        }
        _length = 0;
    }

private:
    char _buffer[1536];
    std::size_t _length = 0;
};

struct Mapping {
    std::uint64_t start;
    std::uint64_t end;
    bool readable;
    bool executable;
    bool image;
};

constexpr std::size_t MappingCapacity = 65536;
Mapping g_mappings[MappingCapacity];
std::size_t g_mappingCount = 0;
std::atomic<bool> g_processRead{true};
char g_executableName[256] = "?";
std::uint64_t g_stackBytes = 0;
bool g_indirectMemory = false;
struct sigaction g_previous[FatalSignalCount];
std::atomic<int> g_reporter{0};

std::uint64_t ParseHex(const char*& cursor, const char* end) {
    std::uint64_t value = 0;
    while (cursor < end) {
        const char character = *cursor;
        int digit = -1;
        if (character >= '0' && character <= '9') digit = character - '0';
        else if (character >= 'a' && character <= 'f') digit = character - 'a' + 10;
        if (digit < 0) break;
        value = value << 4 | static_cast<std::uint64_t>(digit);
        ++cursor;
    }
    return value;
}

void AddMapping(const char* line, const char* end) {
    if (g_mappingCount == MappingCapacity) return;
    const char* cursor = line;
    const auto start = ParseHex(cursor, end);
    if (cursor == end || *cursor != '-') return;
    ++cursor;
    const auto stop = ParseHex(cursor, end);
    if (end - cursor < 5 || *cursor != ' ') return;
    ++cursor;
    const bool readable = cursor[0] == 'r';
    const bool executable = cursor[2] == 'x';
    cursor += 4;
    for (int field = 0; field < 2; ++field) {
        while (cursor < end && *cursor == ' ') ++cursor;
        while (cursor < end && *cursor != ' ') ++cursor;
    }
    while (cursor < end && *cursor == ' ') ++cursor;
    bool inode = false;
    for (; cursor < end && *cursor >= '0' && *cursor <= '9'; ++cursor) {
        if (*cursor != '0') inode = true;
    }
    while (cursor < end && *cursor == ' ') ++cursor;
    const bool vdso = end - cursor >= 6 && std::memcmp(cursor, "[vdso]", 6) == 0;
    g_mappings[g_mappingCount++] = {start, stop, readable, executable, inode || vdso};
}

void SnapshotMappings() {
    g_mappingCount = 0;
    const int descriptor = ::open("/proc/self/maps", O_RDONLY | O_CLOEXEC);
    if (descriptor < 0) return;
    static char buffer[16384];
    std::size_t kept = 0;
    for (;;) {
        const ssize_t got = ::read(descriptor, buffer + kept, sizeof(buffer) - kept);
        if (got < 0 && errno == EINTR) continue;
        if (got <= 0) break;
        const std::size_t length = kept + static_cast<std::size_t>(got);
        std::size_t lineStart = 0;
        for (std::size_t index = 0; index < length; ++index) {
            if (buffer[index] != '\n') continue;
            AddMapping(buffer + lineStart, buffer + index);
            lineStart = index + 1;
        }
        kept = length - lineStart;
        if (kept == sizeof(buffer)) kept = 0;
        std::memmove(buffer, buffer + lineStart, kept);
    }
    ::close(descriptor);
}

const Mapping* FindMapping(std::uint64_t address) {
    std::size_t low = 0;
    std::size_t high = g_mappingCount;
    while (low < high) {
        const std::size_t middle = low + (high - low) / 2;
        if (g_mappings[middle].end <= address) low = middle + 1;
        else high = middle;
    }
    if (low == g_mappingCount || g_mappings[low].start > address) return nullptr;
    return &g_mappings[low];
}

bool IsExecutable(std::uint64_t address) {
    const Mapping* mapping = FindMapping(address);
    return mapping != nullptr && mapping->executable;
}

bool IsReadable(std::uint64_t address) {
    const Mapping* mapping = FindMapping(address);
    return mapping != nullptr && mapping->readable;
}

bool ReadWithinPage(std::uint64_t address, void* out, std::size_t size) {
    if (g_processRead.load(std::memory_order_relaxed)) {
        iovec local{out, size};
        iovec remote{reinterpret_cast<void*>(address), size};
        const ssize_t got = ::process_vm_readv(::getpid(), &local, 1, &remote, 1, 0);
        if (got == static_cast<ssize_t>(size)) return true;
        if (got >= 0 || errno == EFAULT) return false;
        g_processRead.store(false, std::memory_order_relaxed);
    }
    const Mapping* mapping = FindMapping(address);
    if (mapping == nullptr || !mapping->readable || address + size > mapping->end) return false;
    std::memcpy(out, reinterpret_cast<const void*>(address), size);
    return true;
}

std::size_t ReadUpTo(std::uint64_t address, void* out, std::size_t size) {
    auto* bytes = static_cast<std::uint8_t*>(out);
    std::size_t done = 0;
    while (done < size) {
        const std::uint64_t at = address + done;
        if (at < address) break;
        const std::size_t chunk = static_cast<std::size_t>(std::min<std::uint64_t>(size - done, PageSize - (at & (PageSize - 1))));
        if (!ReadWithinPage(at, bytes + done, chunk)) break;
        done += chunk;
    }
    return done;
}

bool ReadWords(std::uint64_t address, std::uint64_t* words, std::size_t count) {
    return ReadUpTo(address, words, count * sizeof(*words)) == count * sizeof(*words);
}

const char* BaseName(const char* path) {
    const char* name = path;
    for (const char* cursor = path; *cursor != '\0'; ++cursor) {
        if (*cursor == '/') name = cursor + 1;
    }
    return name;
}

const link_map* FindImage(std::uint64_t address) {
#ifdef APS5_CRASH_FIND_OBJECT
    dl_find_object object{};
    if (_dl_find_object(reinterpret_cast<void*>(address), &object) != 0) return nullptr;
    return object.dlfo_link_map;
#else
    Dl_info info{};
    link_map* image = nullptr;
    if (::dladdr1(reinterpret_cast<void*>(address), &info, reinterpret_cast<void**>(&image), RTLD_DL_LINKMAP) == 0) return nullptr;
    return image;
#endif
}

Line& Describe(Line& line, std::uint64_t address) {
    line.Address(address);
    if (address == 0) return line;
    const Mapping* mapping = FindMapping(address);
    if (mapping == nullptr || !mapping->image) return line;
    const link_map* image = FindImage(address);
    if (image == nullptr) return line;
    const char* name = image->l_name != nullptr && image->l_name[0] != '\0' ? BaseName(image->l_name) : g_executableName;
    return line.Character(' ').Text(name).Text("+0x").Hex(address - image->l_addr, 0);
}

const char* SignalName(int signal) {
    switch (signal) {
    case SIGSEGV: return "SIGSEGV";
    case SIGBUS: return "SIGBUS";
    case SIGILL: return "SIGILL";
    case SIGFPE: return "SIGFPE";
    default: return "?";
    }
}

const char* CodeName(int signal, int code) {
    switch (code) {
    case SI_USER: return "SI_USER";
    case SI_KERNEL: return "SI_KERNEL";
    case SI_QUEUE: return "SI_QUEUE";
    case SI_TKILL: return "SI_TKILL";
    default: break;
    }
    if (signal == SIGSEGV) {
        switch (code) {
        case SEGV_MAPERR: return "SEGV_MAPERR";
        case SEGV_ACCERR: return "SEGV_ACCERR";
        case SEGV_BNDERR: return "SEGV_BNDERR";
        case SEGV_PKUERR: return "SEGV_PKUERR";
        default: return nullptr;
        }
    }
    if (signal == SIGBUS) {
        switch (code) {
        case BUS_ADRALN: return "BUS_ADRALN";
        case BUS_ADRERR: return "BUS_ADRERR";
        case BUS_OBJERR: return "BUS_OBJERR";
        case BUS_MCEERR_AR: return "BUS_MCEERR_AR";
        case BUS_MCEERR_AO: return "BUS_MCEERR_AO";
        default: return nullptr;
        }
    }
    if (signal == SIGILL) {
        switch (code) {
        case ILL_ILLOPC: return "ILL_ILLOPC";
        case ILL_ILLOPN: return "ILL_ILLOPN";
        case ILL_ILLADR: return "ILL_ILLADR";
        case ILL_ILLTRP: return "ILL_ILLTRP";
        case ILL_PRVOPC: return "ILL_PRVOPC";
        case ILL_PRVREG: return "ILL_PRVREG";
        case ILL_COPROC: return "ILL_COPROC";
        case ILL_BADSTK: return "ILL_BADSTK";
        default: return nullptr;
        }
    }
    if (signal == SIGFPE) {
        switch (code) {
        case FPE_INTDIV: return "FPE_INTDIV";
        case FPE_INTOVF: return "FPE_INTOVF";
        case FPE_FLTDIV: return "FPE_FLTDIV";
        case FPE_FLTOVF: return "FPE_FLTOVF";
        case FPE_FLTUND: return "FPE_FLTUND";
        case FPE_FLTRES: return "FPE_FLTRES";
        case FPE_FLTINV: return "FPE_FLTINV";
        case FPE_FLTSUB: return "FPE_FLTSUB";
        default: return nullptr;
        }
    }
    return nullptr;
}

std::size_t FatalIndex(int signal) {
    for (std::size_t index = 0; index < FatalSignalCount; ++index) {
        if (FatalSignals[index] == signal) return index;
    }
    return FatalSignalCount;
}

std::size_t CaptureFrames(std::uint64_t frame, std::uint64_t* frames, std::size_t capacity) {
    std::size_t count = 0;
    while (count < capacity && frame != 0 && (frame & 7) == 0) {
        std::uint64_t pair[2];
        if (!ReadWords(frame, pair, 2) || !IsExecutable(pair[1])) break;
        frames[count++] = pair[1];
        if (pair[0] <= frame) break;
        frame = pair[0];
    }
    return count;
}

struct CapturedThread {
    std::atomic<int> state;
    int tid;
    std::uint64_t rip;
    std::uint64_t rsp;
    std::uint64_t rbp;
    std::uint64_t frames[12];
    std::size_t frameCount;
};

constexpr int ThreadRequested = 1;
constexpr int ThreadAnswered = 2;
constexpr int ThreadGone = 3;
constexpr std::size_t ThreadCapacity = 128;
CapturedThread g_threads[ThreadCapacity];
std::atomic<std::size_t> g_threadCount{0};

void AnswerCapture(int, siginfo_t*, void* context) {
    const int saved = errno;
    const int tid = static_cast<int>(::gettid());
    const std::size_t count = g_threadCount.load(std::memory_order_acquire);
    for (std::size_t index = 0; index < count; ++index) {
        auto& thread = g_threads[index];
        if (thread.tid != tid || thread.state.load(std::memory_order_acquire) != ThreadRequested) continue;
        const auto& registers = static_cast<const ucontext_t*>(context)->uc_mcontext.gregs;
        thread.rip = static_cast<std::uint64_t>(registers[REG_RIP]);
        thread.rsp = static_cast<std::uint64_t>(registers[REG_RSP]);
        thread.rbp = static_cast<std::uint64_t>(registers[REG_RBP]);
        thread.frameCount = CaptureFrames(thread.rbp, thread.frames, sizeof(thread.frames) / sizeof(thread.frames[0]));
        thread.state.store(ThreadAnswered, std::memory_order_release);
        break;
    }
    errno = saved;
}

int ParseDecimal(const char* text) {
    int value = 0;
    for (; *text != '\0'; ++text) {
        if (*text < '0' || *text > '9' || value > 100000000) return 0;
        value = value * 10 + (*text - '0');
    }
    return value;
}

void ReadThreadName(int tid, char* name, std::size_t capacity) {
    name[0] = '\0';
    char text[64];
    std::size_t length = 0;
    const char prefix[] = "/proc/self/task/";
    for (const char* cursor = prefix; *cursor != '\0'; ++cursor) text[length++] = *cursor;
    char digits[12];
    int count = 0;
    for (unsigned value = static_cast<unsigned>(tid); count == 0 || value != 0; value /= 10) digits[count++] = static_cast<char>('0' + value % 10);
    while (count > 0) text[length++] = digits[--count];
    const char suffix[] = "/comm";
    for (const char* cursor = suffix; *cursor != '\0'; ++cursor) text[length++] = *cursor;
    text[length] = '\0';
    const int descriptor = ::open(text, O_RDONLY | O_CLOEXEC);
    if (descriptor < 0) return;
    ssize_t got = 0;
    do {
        got = ::read(descriptor, name, capacity - 1);
    } while (got < 0 && errno == EINTR);
    ::close(descriptor);
    if (got <= 0) return;
    name[got] = '\0';
    if (name[got - 1] == '\n') name[got - 1] = '\0';
}

std::uint64_t MonotonicMilliseconds() {
    timespec now{};
    ::clock_gettime(CLOCK_MONOTONIC, &now);
    return static_cast<std::uint64_t>(now.tv_sec) * 1000 + static_cast<std::uint64_t>(now.tv_nsec) / 1000000;
}

void ReportAllThreads(int self) {
    const int signal = SIGRTMAX;
    struct sigaction current {};
    if (::sigaction(signal, nullptr, &current) != 0) return;
    const bool answering = (current.sa_flags & SA_SIGINFO) != 0 && current.sa_sigaction == AnswerCapture;
    if (!answering && current.sa_handler != SIG_DFL) {
        Line().Text("  all threads: not captured, signal ").Decimal(static_cast<std::uint64_t>(signal)).Text(" is in use\n").Write();
        return;
    }
    struct sigaction answer {};
    answer.sa_sigaction = AnswerCapture;
    answer.sa_flags = SA_SIGINFO | SA_RESTART | SA_ONSTACK;
    sigemptyset(&answer.sa_mask);
    if (::sigaction(signal, &answer, nullptr) != 0) return;
    const int directory = ::open("/proc/self/task", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (directory < 0) return;
    std::size_t count = 0;
    std::uint64_t skipped = 0;
    alignas(8) static char entries[8192];
    for (;;) {
        const long got = ::syscall(SYS_getdents64, directory, entries, sizeof(entries));
        if (got <= 0) break;
        for (long offset = 0; offset < got;) {
            const auto length = *reinterpret_cast<const unsigned short*>(entries + offset + 16);
            const int tid = ParseDecimal(entries + offset + 19);
            offset += length;
            if (tid == 0 || tid == self) continue;
            if (count == ThreadCapacity) {
                ++skipped;
                continue;
            }
            g_threads[count].tid = tid;
            g_threads[count].frameCount = 0;
            g_threads[count].state.store(ThreadRequested, std::memory_order_relaxed);
            ++count;
        }
    }
    ::close(directory);
    g_threadCount.store(count, std::memory_order_release);
    const pid_t process = ::getpid();
    for (std::size_t index = 0; index < count; ++index) {
        if (::syscall(SYS_tgkill, process, g_threads[index].tid, signal) != 0) g_threads[index].state.store(ThreadGone, std::memory_order_release);
    }
    const std::uint64_t deadline = MonotonicMilliseconds() + 1000;
    for (;;) {
        bool waiting = false;
        for (std::size_t index = 0; index < count; ++index) {
            if (g_threads[index].state.load(std::memory_order_acquire) == ThreadRequested) waiting = true;
        }
        if (!waiting || MonotonicMilliseconds() >= deadline) break;
        timespec pause{0, 1000000};
        ::nanosleep(&pause, nullptr);
    }
    Line().Text("  all threads:\n").Write();
    for (std::size_t index = 0; index < count; ++index) {
        const auto& thread = g_threads[index];
        const int state = thread.state.load(std::memory_order_acquire);
        if (state == ThreadGone) continue;
        char name[32];
        ReadThreadName(thread.tid, name, sizeof(name));
        Line line;
        line.Text("  thread ").Decimal(static_cast<std::uint64_t>(thread.tid)).Text(" '").Text(name).Text("': ");
        if (state != ThreadAnswered) {
            line.Text("did not answer\n").Write();
            continue;
        }
        line.Text("rip ");
        Describe(line, thread.rip).Text(" rsp ").Address(thread.rsp).Text(" rbp ").Address(thread.rbp).Character('\n').Write();
        for (std::size_t depth = 0; depth < thread.frameCount; ++depth) {
            Line frame;
            frame.Text("    #").Decimal(depth).Character(' ');
            Describe(frame, thread.frames[depth]).Character('\n').Write();
        }
    }
    if (skipped != 0) Line().Text("  ").Decimal(skipped).Text(" further thread(s) left out\n").Write();
}

void ReportStackCandidates(std::uint64_t rsp, int limit, std::uint64_t span) {
    Line().Text("  stack return address candidates:\n").Write();
    static std::uint64_t words[0x4000 / 8];
    const std::size_t count = ReadUpTo(rsp, words, static_cast<std::size_t>(std::min<std::uint64_t>(span, sizeof(words)))) / sizeof(words[0]);
    int printed = 0;
    for (std::size_t index = 0; index < count && printed < limit; ++index) {
        if (!IsExecutable(words[index])) continue;
        Line line;
        line.Text("    [rsp+0x").Hex(index * 8, 0).Text("] ");
        Describe(line, words[index]).Character('\n').Write();
        ++printed;
    }
}

void ReportStackWords(std::uint64_t rsp) {
    if (g_stackBytes == 0) return;
    const Mapping* stack = FindMapping(rsp);
    const std::uint64_t stackLow = stack != nullptr ? stack->start : rsp;
    const std::uint64_t stackHigh = stack != nullptr ? stack->end : rsp;
    const std::uint64_t first = rsp & ~std::uint64_t{7};
    Line().Text("  stack words from rsp ").Address(rsp).Text(" (APS5_CRASH_STACK_BYTES):\n").Write();
    const std::uint64_t limit = std::min(first + g_stackBytes, stackHigh);
    std::uint64_t end = first;
    for (std::uint64_t at = first; at < limit; at += 32) {
        std::uint64_t words[4] = {};
        const std::size_t count = std::min<std::size_t>(ReadUpTo(at, words, static_cast<std::size_t>(std::min<std::uint64_t>(32, limit - at))) / 8, 4);
        if (count == 0) break;
        Line line;
        line.Text("    +0x").Hex(at - first, 4).Character(':');
        for (std::size_t index = 0; index < count; ++index) line.Character(' ').Hex(words[index], 16);
        line.Character('\n').Write();
        end = at + count * 8;
        if (count < 4) break;
    }
    static std::uint64_t seen[256];
    std::size_t seenCount = 0;
    Line().Text("  data at stack words that point outside the stack (8 words each):\n").Write();
    for (std::uint64_t slot = first; slot + 8 <= end && seenCount < sizeof(seen) / sizeof(seen[0]); slot += 8) {
        std::uint64_t value = 0;
        if (!ReadWords(slot, &value, 1)) break;
        if (value < 0x10000 || (value & 7) != 0 || value > 0x7fffffffffffull || (value >= stackLow && value < stackHigh)) continue;
        if (std::find(seen, seen + seenCount, value) != seen + seenCount) continue;
        std::uint64_t words[8];
        if (IsExecutable(value) || !ReadWords(value, words, 8)) continue;
        seen[seenCount++] = value;
        Line line;
        line.Text("    [+0x").Hex(slot - first, 4).Text("] ").Address(value).Character(':');
        for (const std::uint64_t word : words) line.Character(' ').Hex(word, 16);
        line.Character('\n').Write();
    }
}

void ReportFault(int signal, const siginfo_t* info, const mcontext_t& context) {
    const auto& registers = context.gregs;
    const auto value = [&](int index) { return static_cast<std::uint64_t>(registers[index]); };
    const std::uint64_t rip = value(REG_RIP);
    const std::uint64_t rsp = value(REG_RSP);
    const auto fault = reinterpret_cast<std::uint64_t>(info->si_addr);
    char threadName[17] = {};
    ::prctl(PR_GET_NAME, threadName, 0, 0, 0);
    {
        Line line;
        line.Text("\nFATAL: signal ").Decimal(static_cast<std::uint64_t>(signal)).Text(" (").Text(SignalName(signal)).Text(", ");
        if (const char* code = CodeName(signal, info->si_code)) line.Text(code);
        else line.Text("code ").Decimal(static_cast<std::uint64_t>(static_cast<std::uint32_t>(info->si_code)));
        line.Text(") on thread ").Decimal(static_cast<std::uint64_t>(::gettid())).Text(" '").Text(threadName).Text("'\n").Write();
    }
    {
        Line line;
        line.Text("  rip ");
        Describe(line, rip).Character('\n').Write();
    }
    if (info->si_code <= 0) {
        Line().Text("  sent by process ").Decimal(static_cast<std::uint64_t>(info->si_pid)).Character('\n').Write();
    } else if (signal == SIGILL) {
        std::uint8_t bytes[8];
        const std::size_t available = ReadUpTo(rip, bytes, sizeof(bytes));
        Line line;
        line.Text("  bytes");
        for (std::size_t index = 0; index < available; ++index) line.Character(' ').Hex(bytes[index], 2);
        line.Character('\n').Write();
    } else if (signal == SIGSEGV && info->si_code == SI_KERNEL) {
        Line().Text("  general protection fault, no fault address\n").Write();
        std::uint8_t trap[2];
        if (ReadUpTo(rip, trap, sizeof(trap)) == sizeof(trap) && trap[0] == 0xcd && trap[1] == 0x45) Line().Text("  guest abort() (int 0x45)\n").Write();
    } else if (signal == SIGSEGV) {
        const std::uint64_t error = value(REG_ERR);
        const char* kind = value(REG_TRAPNO) != PageFaultTrap ? "access" : (error & PageFaultFetch) != 0 ? "execute" : (error & PageFaultWrite) != 0 ? "write" : "read";
        Line().Text("  ").Text(kind).Text(" of ").Address(fault).Character('\n').Write();
        if (fault < rsp + PageSize && fault + 0x10000 > rsp && !IsReadable(fault)) Line().Text("  the fault address is next to rsp, outside readable memory: likely a stack overflow\n").Write();
    } else if (signal == SIGBUS) {
        Line().Text("  bus error at ").Address(fault).Character('\n').Write();
    }
    Line().Text("  rax ").Hex(value(REG_RAX), 16).Text(" rbx ").Hex(value(REG_RBX), 16).Text(" rcx ").Hex(value(REG_RCX), 16).Text(" rdx ").Hex(value(REG_RDX), 16).Character('\n').Write();
    Line().Text("  rsi ").Hex(value(REG_RSI), 16).Text(" rdi ").Hex(value(REG_RDI), 16).Text(" rbp ").Hex(value(REG_RBP), 16).Text(" rsp ").Hex(rsp, 16).Character('\n').Write();
    Line().Text("  r8  ").Hex(value(REG_R8), 16).Text(" r9  ").Hex(value(REG_R9), 16).Text(" r10 ").Hex(value(REG_R10), 16).Text(" r11 ").Hex(value(REG_R11), 16).Character('\n').Write();
    Line().Text("  r12 ").Hex(value(REG_R12), 16).Text(" r13 ").Hex(value(REG_R13), 16).Text(" r14 ").Hex(value(REG_R14), 16).Text(" r15 ").Hex(value(REG_R15), 16).Character('\n').Write();
    struct Named {
        const char* name;
        int index;
    };
    constexpr Named pointers[] = {{"rax", REG_RAX}, {"rbx", REG_RBX}, {"rcx", REG_RCX}, {"rdx", REG_RDX}, {"rsi", REG_RSI}, {"rdi", REG_RDI}, {"r12", REG_R12}, {"r13", REG_R13}, {"r14", REG_R14}, {"r15", REG_R15}};
    for (const auto& pointer : pointers) {
        const std::uint64_t address = value(pointer.index);
        std::uint64_t words[8];
        if (address < 0x10000 || (address & 7) != 0 || !ReadWords(address, words, 8)) continue;
        Line line;
        line.Text("  [").Text(pointer.name).Character(']');
        for (const std::uint64_t word : words) line.Character(' ').Hex(word, 16);
        line.Character('\n').Write();
        if (!g_indirectMemory) continue;
        for (std::size_t index = 0; index < 8; ++index) {
            const std::uint64_t target = words[index];
            std::uint64_t content[8];
            if (target < 0x10000 || IsExecutable(target) || !ReadWords(target, content, 8)) continue;
            Line indirect;
            indirect.Text("  [[").Text(pointer.name).Text("+0x").Hex(index * 8, 0).Text("]] @").Hex(target, 16);
            for (const std::uint64_t word : content) indirect.Character(' ').Hex(word, 16);
            indirect.Character('\n').Write();
        }
    }
    constexpr Named texts[] = {{"rax", REG_RAX}, {"rbx", REG_RBX}, {"rcx", REG_RCX}, {"rdx", REG_RDX}, {"rsi", REG_RSI}, {"rdi", REG_RDI}, {"rbp", REG_RBP}, {"r8", REG_R8}, {"r9", REG_R9}, {"r10", REG_R10}, {"r11", REG_R11}, {"r12", REG_R12}, {"r13", REG_R13}, {"r14", REG_R14}, {"r15", REG_R15}};
    static std::uint8_t bytes[crash_text::MaximumBytes];
    static char text[960];
    for (const auto& named : texts) {
        const std::uint64_t address = value(named.index);
        if (address < 0x10000) continue;
        if (crash_text::Format(bytes, ReadUpTo(address, bytes, sizeof(bytes)), text, sizeof(text))) Line().Text("  [").Text(named.name).Text("] ").Text(text).Character('\n').Write();
    }
    Line().Text("  frame pointer chain:\n").Write();
    std::uint64_t frames[32];
    const std::size_t frameCount = CaptureFrames(value(REG_RBP), frames, sizeof(frames) / sizeof(frames[0]));
    for (std::size_t depth = 0; depth < frameCount; ++depth) {
        Line line;
        line.Text("    #").Decimal(depth).Character(' ');
        Describe(line, frames[depth]).Character('\n').Write();
    }
    ReportStackCandidates(rsp, 16, 0x2000);
    ReportStackWords(rsp);
    if (rip == 0 || !IsExecutable(rip)) {
        Line().Text("  recently popped return address candidates:\n").Write();
        for (std::uint64_t slot = rsp - 8; slot >= rsp - 0x800; slot -= 8) {
            std::uint64_t candidate = 0;
            if (!ReadWords(slot, &candidate, 1)) break;
            if (!IsExecutable(candidate)) continue;
            Line line;
            line.Text("    [rsp-0x").Hex(rsp - slot, 0).Text("] ");
            Describe(line, candidate).Character('\n').Write();
        }
        constexpr Named bases[] = {{"rdi", REG_RDI}, {"rsi", REG_RSI}, {"rbx", REG_RBX}, {"r12", REG_R12}, {"r13", REG_R13}, {"r14", REG_R14}, {"r15", REG_R15}};
        for (const auto& base : bases) {
            const std::uint64_t address = value(base.index);
            std::uint64_t first = 0;
            if (address < 0x10000 || (address & 7) != 0 || !ReadWords(address, &first, 1)) continue;
            Line().Text("  code addresses above ").Text(base.name).Text(" (0x").Hex(address, 0).Text("):\n").Write();
            int found = 0;
            for (std::uint64_t slot = address; found < 24 && slot < address + 0x1000; slot += 8) {
                std::uint64_t candidate = 0;
                if (!ReadWords(slot, &candidate, 1)) break;
                if (!IsExecutable(candidate)) continue;
                Line line;
                line.Text("    [+0x").Hex(slot - address, 0).Text("] ");
                Describe(line, candidate).Character('\n').Write();
                ++found;
            }
        }
    }
}

void ReportCallTrace(int self) {
    static CallTraceEntry entries[64];
    const std::size_t count = CopyCallTrace_nid_no_patch(entries, sizeof(entries) / sizeof(entries[0]));
    if (count == 0) return;
    Line().Text("  last traced system library calls (APS5_TRACE_CALLS):\n").Write();
    for (std::size_t index = 0; index < count; ++index) {
        Line line;
        line.Text("    #").Decimal(entries[index].sequence).Text(" thread ").Decimal(entries[index].thread).Character(' ').Text(entries[index].library).Character(' ').Text(entries[index].name).Text(" from ");
        Describe(line, entries[index].returnAddress).Character('\n').Write();
    }
    static CallTraceEntry own[32];
    const auto thread = static_cast<std::uint64_t>(self);
    const std::size_t owned = CopyThreadCallTrace_nid_no_patch(thread, own, sizeof(own) / sizeof(own[0]));
    if (owned != 0) {
        Line().Text("  last traced calls of thread ").Decimal(thread).Text(":\n").Write();
        for (std::size_t index = 0; index < owned; ++index) {
            Line line;
            line.Text("    #").Decimal(own[index].sequence).Character(' ').Text(own[index].library).Character(' ').Text(own[index].name).Text(" from ");
            Describe(line, own[index].returnAddress).Character('\n').Write();
        }
    }
    static CallTraceCount counts[32];
    std::uint64_t total = 0;
    const std::size_t counted = CopyCallCounts_nid_no_patch(counts, sizeof(counts) / sizeof(counts[0]), &total);
    if (counted == 0) return;
    Line().Text("  most called traced imports (").Decimal(total).Text(" calls in total):\n").Write();
    for (std::size_t index = 0; index < counted; ++index) {
        Line line;
        line.Text("    ");
        std::uint64_t width = 1;
        for (std::uint64_t value = counts[index].calls; value >= 10; value /= 10) ++width;
        for (; width < 12; ++width) line.Character(' ');
        line.Decimal(counts[index].calls).Character(' ').Text(counts[index].library).Character(' ').Text(counts[index].name).Character('\n').Write();
    }
}

void PassOn(int signal, siginfo_t* info, void* context) {
    const std::size_t index = FatalIndex(signal);
    if (index < FatalSignalCount) {
        const auto& previous = g_previous[index];
        if ((previous.sa_flags & SA_SIGINFO) != 0 && previous.sa_sigaction != nullptr) {
            previous.sa_sigaction(signal, info, context);
            return;
        }
        if ((previous.sa_flags & SA_SIGINFO) == 0 && previous.sa_handler != SIG_DFL && previous.sa_handler != SIG_IGN && previous.sa_handler != nullptr) {
            previous.sa_handler(signal);
            return;
        }
    }
    struct sigaction fallback {};
    fallback.sa_handler = SIG_DFL;
    sigemptyset(&fallback.sa_mask);
    ::sigaction(signal, &fallback, nullptr);
    if (info->si_code <= 0) ::syscall(SYS_tgkill, ::getpid(), ::gettid(), signal);
}

void ReportFatal(int signal, siginfo_t* info, void* context) {
    const int saved = errno;
    const int self = static_cast<int>(::gettid());
    int reporter = 0;
    if (!g_reporter.compare_exchange_strong(reporter, self, std::memory_order_acq_rel)) {
        if (reporter != self) {
            for (;;) ::pause();
        }
        PassOn(signal, info, context);
        errno = saved;
        return;
    }
    LibcRunEndFlush_nid_no_patch();
    SnapshotMappings();
    ReportFault(signal, info, static_cast<const ucontext_t*>(context)->uc_mcontext);
    ReportCallTrace(self);
    ReportAllThreads(self);
    LibcRunFailureReports_nid_no_patch();
    PassOn(signal, info, context);
    errno = saved;
}

class SignalStack {
public:
    SignalStack() {
        stack_t current{};
        if (::sigaltstack(nullptr, &current) != 0 || (current.ss_flags & SS_DISABLE) == 0) return;
        void* memory = ::mmap(nullptr, SignalStackBytes + PageSize, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (memory == MAP_FAILED) return;
        stack_t stack{};
        stack.ss_sp = static_cast<char*>(memory) + PageSize;
        stack.ss_size = SignalStackBytes;
        if (::mprotect(memory, PageSize, PROT_NONE) != 0 || ::sigaltstack(&stack, nullptr) != 0) {
            ::munmap(memory, SignalStackBytes + PageSize);
            return;
        }
        _memory = memory;
    }

    ~SignalStack() {
        if (_memory == nullptr) return;
        stack_t disabled{};
        disabled.ss_flags = SS_DISABLE;
        if (::sigaltstack(&disabled, nullptr) != 0) return;
        ::munmap(_memory, SignalStackBytes + PageSize);
    }

    SignalStack(const SignalStack&) = delete;
    SignalStack& operator=(const SignalStack&) = delete;

private:
    void* _memory = nullptr;
};

void InstallFatalHandlers() {
    char path[sizeof(g_executableName)];
    const ssize_t length = ::readlink("/proc/self/exe", path, sizeof(path) - 1);
    if (length > 0) {
        path[length] = '\0';
        const char* name = BaseName(path);
        std::memcpy(g_executableName, name, std::strlen(name) + 1);
    }
    if (const char* bytes = std::getenv("APS5_CRASH_STACK_BYTES")) g_stackBytes = std::min<std::uint64_t>(std::strtoull(bytes, nullptr, 0), std::uint64_t{1} << 20);
    const char* indirect = std::getenv("APS5_CRASH_INDIRECT_MEMORY");
    g_indirectMemory = indirect != nullptr && indirect[0] != '\0';
    LibcInstallSignalStack_nid_no_patch();
    struct sigaction action {};
    action.sa_sigaction = ReportFatal;
    action.sa_flags = SA_SIGINFO | SA_ONSTACK;
    sigemptyset(&action.sa_mask);
    for (std::size_t index = 0; index < FatalSignalCount; ++index) ::sigaction(FatalSignals[index], &action, &g_previous[index]);
}

const bool g_crashReportInstalled = (InstallFatalHandlers(), true);

}

extern "C" void LibcInstallSignalStack_nid_no_patch() {
    thread_local SignalStack stack;
    (void)stack;
}
#endif
