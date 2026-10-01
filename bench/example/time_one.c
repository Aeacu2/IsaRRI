/* time_one.c -- time the exported isarri entry on one benchmark input, as the campaign did.
 *
 *   ./time_one <coefficient file> [runs] [--windows]
 *
 * The file holds one line of comma-separated integer coefficients in ascending degree (the format
 * of the benchmark inputs). The input must meet the caller obligations of
 * export/isarri_contract.h; every benchmark input is certified squarefree.
 *
 * Timed region, as in the campaign harness (drivers/Dsc__export__c_harness__suite_v2_bench.cpp,
 * run_once): for every run a fresh set of output arrays is allocated and initialised BEFORE the
 * clock starts, with capacity equal to the number of coefficients (more than the roots of either
 * half, so every window is stored); only the call to isarri is timed; the result is read and freed
 * after the clock stops. The recorded time of a case is the minimum over its runs.
 *
 * Prints the total root count (positive + negative + zero) and the minimum time in milliseconds;
 * with --windows also every window of the last run, as `sign lo hi k` meaning (lo/2^k, hi/2^k) on
 * the positive half, or (-hi/2^k, -lo/2^k) for sign `-` (the negative half is reflected).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <gmp.h>

#include "isarri_contract.h"

#define AS_ISARRI(z) ((gmp_mpz_struct *)(z))

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e3 + ts.tv_nsec / 1e6;
}

static char *read_all(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) { perror(path); exit(2); }
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  rewind(f);
  char *s = malloc((size_t)n + 1);
  if (fread(s, 1, (size_t)n, f) != (size_t)n) { perror(path); exit(2); }
  s[n] = 0;
  fclose(f);
  return s;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s <coefficient file> [runs] [--windows]\n", argv[0]); return 2; }
  int runs = (argc > 2 && argv[2][0] != '-') ? atoi(argv[2]) : 1;
  int show = (argc > 2 && strcmp(argv[argc - 1], "--windows") == 0);
  if (runs < 1) runs = 1;

  char *text = read_all(argv[1]);
  int64_t len = 1;
  for (char *p = text; *p; ++p) len += (*p == ',');
  mpz_t *c = malloc(sizeof(mpz_t) * (size_t)len);
  gmp_mpz_struct **cp = malloc(sizeof(*cp) * (size_t)len);
  char *tok = strtok(text, ",\n\r ");
  for (int64_t i = 0; i < len; ++i, tok = strtok(NULL, ",\n\r ")) {
    if (!tok || mpz_init_set_str(c[i], tok, 10) != 0) { fprintf(stderr, "bad coefficient %lld\n", (long long)i); return 2; }
    cp[i] = AS_ISARRI(c[i]);
  }

  const int64_t cap = len;
  double best = -1;
  int64_t pos = -1, neg = -1, xs0 = -1, ok = -1;
  mpz_t *pl = NULL, *pr = NULL, *nl = NULL, *nr = NULL;
  int64_t *pk = NULL, *nk = NULL;
  for (int r = 0; r < runs; ++r) {
    if (pl) {
      for (int64_t i = 0; i < cap; ++i) mpz_clears(pl[i], pr[i], nl[i], nr[i], NULL);
      free(pl); free(pr); free(nl); free(nr); free(pk); free(nk);
    }
    pl = malloc(sizeof(mpz_t) * cap); pr = malloc(sizeof(mpz_t) * cap);
    nl = malloc(sizeof(mpz_t) * cap); nr = malloc(sizeof(mpz_t) * cap);
    pk = malloc(sizeof(int64_t) * cap); nk = malloc(sizeof(int64_t) * cap);
    gmp_mpz_struct **plp = malloc(sizeof(void *) * cap), **prp = malloc(sizeof(void *) * cap),
                   **nlp = malloc(sizeof(void *) * cap), **nrp = malloc(sizeof(void *) * cap);
    for (int64_t i = 0; i < cap; ++i) {
      mpz_inits(pl[i], pr[i], nl[i], nr[i], NULL);
      plp[i] = AS_ISARRI(pl[i]); prp[i] = AS_ISARRI(pr[i]);
      nlp[i] = AS_ISARRI(nl[i]); nrp[i] = AS_ISARRI(nr[i]);
      pk[i] = nk[i] = -1;
    }
    double t0 = now_ms();
    isarri(&pos, plp, prp, pk, &neg, nlp, nrp, nk, &xs0, &ok,
           cap, /* nfloor */ 22, /* hcap */ 32, /* dlt */ 8, len, cp);
    double t1 = now_ms();
    free(plp); free(prp); free(nlp); free(nrp);
    if (pos < 0 || pos > cap || neg < 0 || neg > cap) { fprintf(stderr, "count out of range\n"); return 1; }
    if (best < 0 || t1 - t0 < best) best = t1 - t0;
  }
  printf("roots=%lld ms=%.4f runs=%d\n", (long long)(pos + neg + (xs0 == 1)), best, runs);
  if (show) {
    for (int64_t i = 0; i < pos; ++i) gmp_printf("+ %Zd %Zd %lld\n", pl[i], pr[i], (long long)pk[i]);
    for (int64_t i = 0; i < neg; ++i) gmp_printf("- %Zd %Zd %lld\n", nl[i], nr[i], (long long)nk[i]);
    if (xs0 == 1) printf("0\n");
  }
  return 0;
}
