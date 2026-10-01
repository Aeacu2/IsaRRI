/* anewdsc_wallclock.c -- make RS-ANewDsc's own timing points report WALL-CLOCK time (2026-09-19).
 *
 * WHY. test_descartes_osx (precompiled, no source) times isolation itself: with -v 1 it prints a
 * getrusage() snapshot "Infos : Before Isolation" and another "After Isolation", and
 * anewdsc_bench.py reports After.t - Before.t, where t = ru_utime + ru_stime (CPU time). Every
 * other arm in the thesis campaigns is timed on a wall/steady clock. External wall-clock around
 * the process cannot be used: it includes process start-up, dynamic loading and input parsing,
 * and subtracting an estimated overhead inverted a verdict at small sizes (2026-07-09).
 *
 * HOW. Interpose getrusage (the binary's only timing import: `nm -u` shows _getrusage and no
 * clock_gettime/gettimeofday). For RUSAGE_SELF we return the real struct with ru_utime replaced
 * by CLOCK_MONOTONIC_RAW (wall time since boot) and ru_stime = 0, so the binary's own
 * "(t)" column -- and hence After.t - Before.t, taken at exactly the same two points as before --
 * becomes elapsed wall-clock time. Memory fields are untouched.
 *
 * Build (the binary is x86_64 and runs under Rosetta 2, so the dylib must be x86_64 too):
 *   clang -arch x86_64 -O2 -dynamiclib anewdsc_wallclock.c -o build/anewdsc_wallclock.dylib
 * Use:  DYLD_INSERT_LIBRARIES=build/anewdsc_wallclock.dylib test_descartes_osx -S 1 -v 1 in.txt
 */
#include <sys/resource.h>
#include <time.h>

static int wall_getrusage(int who, struct rusage *ru) {
  int rc = getrusage(who, ru);
  if (rc == 0 && who == RUSAGE_SELF) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    ru->ru_utime.tv_sec = ts.tv_sec;
    ru->ru_utime.tv_usec = (int)(ts.tv_nsec / 1000);
    ru->ru_stime.tv_sec = 0;
    ru->ru_stime.tv_usec = 0;
  }
  return rc;
}

__attribute__((used)) static struct { const void *replacement, *replacee; } interposers[]
    __attribute__((section("__DATA,__interpose"))) = {{(const void *)wall_getrusage,
                                                       (const void *)getrusage}};
