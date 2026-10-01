/* window_dump.c -- B2 (2026-09-26): run the PUBLIC IsaRRI export (IsaRRI/export/isarri.ll) on
 * benchmark inputs and print every returned window, outside any timing, for an independent check.
 *
 *   window_dump <file>          file = one line of ascending comma-separated coefficients, or an
 *                               SMT-Bench .apolys file (lines "A\t<deg>\t<coeffs>"; others skipped)
 *
 * Output per polynomial:  "P <idx> <pos_count> <neg_count> <xs0>"  then one line per stored window,
 * "+ <l> <r> <k>" (positive half: (l/2^k, r/2^k)) or "- <l> <r> <k>" (reflected: P(-x) window, i.e.
 * (-r/2^k, -l/2^k) for P). out_cap = number of coefficients, so every window is stored; parameters
 * as in the campaign (nfloor 22, hcap 32, dlt 8). A count above out_cap prints "E capacity".
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include "isarri_contract.h"
#define AS_ISARRI(z) ((gmp_mpz_struct *)(z))

static void solve(long idx, char *coeffs) {
  int64_t len = 1;
  for (char *p = coeffs; *p; ++p) len += (*p == ',');
  mpz_t *c = malloc(sizeof(mpz_t) * len);
  gmp_mpz_struct **cp = malloc(sizeof(void *) * len);
  char *save = NULL, *tok = strtok_r(coeffs, ",\n\r ", &save);
  for (int64_t i = 0; i < len; ++i, tok = strtok_r(NULL, ",\n\r ", &save)) {
    if (!tok || mpz_init_set_str(c[i], tok, 10) != 0) { fprintf(stderr, "bad coefficient in poly %ld\n", idx); exit(2); }
    cp[i] = AS_ISARRI(c[i]);
  }
  int64_t cap = len;
  mpz_t *pl = malloc(sizeof(mpz_t) * cap), *pr = malloc(sizeof(mpz_t) * cap),
        *nl = malloc(sizeof(mpz_t) * cap), *nr = malloc(sizeof(mpz_t) * cap);
  gmp_mpz_struct **plp = malloc(sizeof(void *) * cap), **prp = malloc(sizeof(void *) * cap),
                 **nlp = malloc(sizeof(void *) * cap), **nrp = malloc(sizeof(void *) * cap);
  int64_t *pk = malloc(sizeof(int64_t) * cap), *nk = malloc(sizeof(int64_t) * cap);
  for (int64_t i = 0; i < cap; ++i) {
    mpz_inits(pl[i], pr[i], nl[i], nr[i], NULL);
    plp[i] = AS_ISARRI(pl[i]); prp[i] = AS_ISARRI(pr[i]); nlp[i] = AS_ISARRI(nl[i]); nrp[i] = AS_ISARRI(nr[i]);
    pk[i] = nk[i] = -1;
  }
  int64_t pos = -1, neg = -1, xs0 = -1, ok = -1;
  isarri(&pos, plp, prp, pk, &neg, nlp, nrp, nk, &xs0, &ok, cap, 22, 32, 8, len, cp);
  printf("P %ld %lld %lld %lld\n", idx, (long long)pos, (long long)neg, (long long)xs0);
  if (pos < 0 || neg < 0 || pos > cap || neg > cap) { printf("E capacity\n"); }
  else {
    for (int64_t i = 0; i < pos; ++i) gmp_printf("+ %Zd %Zd %lld\n", pl[i], pr[i], (long long)pk[i]);
    for (int64_t i = 0; i < neg; ++i) gmp_printf("- %Zd %Zd %lld\n", nl[i], nr[i], (long long)nk[i]);
  }
  for (int64_t i = 0; i < cap; ++i) mpz_clears(pl[i], pr[i], nl[i], nr[i], NULL);
  for (int64_t i = 0; i < len; ++i) mpz_clear(c[i]);
  free(c); free(cp); free(pl); free(pr); free(nl); free(nr); free(plp); free(prp); free(nlp); free(nrp); free(pk); free(nk);
  fflush(stdout);
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: %s <file>\n", argv[0]); return 2; }
  FILE *f = fopen(argv[1], "r");
  if (!f) { perror(argv[1]); return 2; }
  char *line = NULL; size_t n = 0; ssize_t got; long idx = 0;
  while ((got = getline(&line, &n, f)) > 0) {
    if (line[0] == 'A' && line[1] == '\t') {           /* .apolys: A <deg> <coeffs> */
      char *t = strchr(line + 2, '\t');
      if (!t) continue;
      solve(++idx, t + 1);
    } else if ((line[0] >= '0' && line[0] <= '9') || line[0] == '-') {
      solve(++idx, line);
    }
  }
  free(line); fclose(f);
  return 0;
}
