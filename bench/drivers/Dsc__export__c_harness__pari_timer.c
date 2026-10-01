/* pari_timer.c -- PARI's real-root isolation, timed in-process around the call (2026-09-18).
 *
 * WHY. The 2026-09-12 campaign ran PARI as `gp` running polrootsreal, timed by gp's gettime()
 * (whole milliseconds; on SMT-BENCH, wall time minus 12.3 ms of start-up). polrootsreal also
 * (1) computes a squarefree factorisation (ZX_squff) that the other arms are excused, and
 * (2) refines every root to working precision, which is more than isolation.
 * This timer links libpari and times realroots_nosqf_count() (pari_realroots_nosqf.c: PARI's own
 * realroots with only those two things removed) with a steady clock, like every library arm.
 *
 * Interface = all_roots_vs_competitors_bench's:
 *   --solve-stdin <name> <solver> [reps]    one polynomial "c0,c1,..." (ascending) on stdin
 *   --solve-stdin-multi <name> <solver>     SMT-BENCH dump lines, summed per instance
 * Build:
 *   cc -O2 -I/opt/homebrew/include pari_timer.c pari_realroots_nosqf.c -L/opt/homebrew/lib \
 *      -lpari-gmp-tls -o build/pari_timer
 */
#include <pari/pari.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

long realroots_nosqf_count(GEN P);

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
  return ts.tv_sec * 1e3 + ts.tv_nsec / 1e6;
}

/* Build the ZX sum c_i x^i from "c0,c1,...,cn" (modifies s). */
static GEN parse_poly(char *s) {
  long n = 1;
  for (char *p = s; *p; p++) if (*p == ',') n++;
  GEN P = cgetg(n + 2, t_POL);
  P[1] = evalsigne(1) | evalvarn(0);
  long i = 0;
  char *tok = strtok(s, ",\r\n");
  while (tok && i < n) {
    while (*tok == ' ') tok++;
    gel(P, i + 2) = (*tok == '-') ? negi(strtoi(tok + 1)) : strtoi(*tok == '+' ? tok + 1 : tok);
    i++;
    tok = strtok(NULL, ",\r\n");
  }
  setlg(P, i + 2);
  return normalizepol(P);
}

static char *read_line(FILE *f) {
  size_t cap = 1 << 16, len = 0;
  char *buf = malloc(cap);
  int c;
  while ((c = fgetc(f)) != EOF && c != '\n') {
    if (len + 1 >= cap) { cap *= 2; buf = realloc(buf, cap); }
    buf[len++] = (char)c;
  }
  if (len == 0 && c == EOF) { free(buf); return NULL; }
  buf[len] = 0;
  return buf;
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: %s --solve-stdin|--solve-stdin-multi <name> <solver> [reps]\n", argv[0]); return 2; }
  const char *mode = argv[1], *name = argv[2], *solver = argv[3];
  /* SINGLE-THREADED (2026-09-19). Homebrew's libpari is the pthread build: pari_mt_init() sets
   * pari_mt_nbthreads to the core count (10 on the M4), and ZX_gcd_all -- reached through
   * ZX_Uspensky's rational-root step (nfrootsQ -> ZX_radical) -- runs a parallel CRT worker.
   * Every other arm is single-threaded, so pin PARI to one thread. It must be set AFTER
   * pari_init (setting it before is overwritten: the guard below caught that); the parallel
   * code reads it at call time (mt_queue_start: lim = pari_mt_nbthreads). */
  pari_init(1UL << 28, 0);
  pari_mt_nbthreads = 1;
  if (pari_mt_nbthreads != 1) { fprintf(stderr, "pari_timer: nbthreads=%lu, expected 1\n", pari_mt_nbthreads); return 3; }
  paristack_setsize(1UL << 28, 1UL << 34);  /* up to 16 GB virtual, as the gp arm's parisizemax */
  if (!strcmp(mode, "--solve-stdin")) {
    int reps = argc > 4 ? atoi(argv[4]) : 1; if (reps < 1) reps = 1;
    char *line = read_line(stdin);
    if (!line) { fprintf(stderr, "no input\n"); return 2; }
    pari_sp av = avma;
    GEN P = parse_poly(line);
    if (degpol(P) < 1) { fprintf(stderr, "need degree >= 1\n"); return 2; }
    double best = 1e300; long roots = -1;
    for (int r = 0; r < reps; r++) {
      pari_sp av2 = avma;
      double t0 = now_ms();
      long n = realroots_nosqf_count(P);
      double t1 = now_ms();
      set_avma(av2);
      if (t1 - t0 < best) best = t1 - t0;
      roots = n;
    }
    set_avma(av);
    printf("%s,%s_roots=%ld,%s_ms=%g\n", name, solver, roots, solver, best);
    return 0;
  }
  if (!strcmp(mode, "--solve-stdin-multi")) {
    char *line; double total = 0; long total_roots = 0; unsigned np = 0;
    while ((line = read_line(stdin))) {
      char *coeff = line;
      if (line[0] == 'A' && line[1] == '\t') {
        char *t2 = strchr(line + 2, '\t');
        if (!t2) { free(line); continue; }
        coeff = t2 + 1;
      } else if (strchr(line, '\t') || !*line) { free(line); continue; }
      pari_sp av = avma;
      GEN P = parse_poly(coeff);
      if (degpol(P) < 1) { set_avma(av); free(line); continue; }
      double t0 = now_ms();
      long n = realroots_nosqf_count(P);
      double t1 = now_ms();
      printf("P\t%u\t%ld\t%ld\t%f\n", np + 1, degpol(P), n, t1 - t0);
      set_avma(av);
      total += t1 - t0; total_roots += n; np++;
      free(line);
    }
    if (!np) { fprintf(stderr, "no polynomials parsed\n"); return 2; }
    printf("%s,%s_roots=%ld,%s_ms=%f,polys=%u\n", name, solver, total_roots, solver, total, np);
    return 0;
  }
  fprintf(stderr, "unknown mode %s\n", mode);
  return 2;
}
