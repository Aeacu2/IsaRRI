/* isarri_example.c -- isolate the real roots of x^3 - 2x^2 - 5x + 6 = (x - 1)(x - 3)(x + 2).
 *
 * The polynomial is squarefree with a nonzero leading coefficient and 4 coefficients, so it meets
 * the input obligations in export/isarri_contract.h.
 */
#include <stdint.h>
#include <stdio.h>
#include <gmp.h>

#include "isarri_contract.h"

/* isarri.h's gmp_mpz_struct has the layout of GMP's __mpz_struct (alloc, size, limb pointer). */
#define AS_ISARRI(z) ((gmp_mpz_struct *)(z))

/* An open window (lo, hi) / 2^k, or a point window {lo} / 2^k when the endpoints are equal. */
static void print_window(const char *sign, mpz_t lo, mpz_t hi, int64_t k) {
  if (mpz_cmp(lo, hi) == 0)
    gmp_printf("  %s{%Zd} / 2^%lld\n", sign, lo, (long long)k);
  else
    gmp_printf("  %s(%Zd, %Zd) / 2^%lld\n", sign, lo, hi, (long long)k);
}

int main(void) {
  enum { LEN = 4, CAP = 4 };
  const long coeffs[LEN] = {6, -5, -2, 1}; /* ascending degree */

  mpz_t c[LEN];
  gmp_mpz_struct *coeff_ptrs[LEN];
  for (int i = 0; i < LEN; ++i) {
    mpz_init_set_si(c[i], coeffs[i]);
    coeff_ptrs[i] = AS_ISARRI(c[i]);
  }

  /* Output arrays: CAP initialised, distinct mpz_t per endpoint column (obligation 9). */
  mpz_t pos_l[CAP], pos_r[CAP], neg_l[CAP], neg_r[CAP];
  gmp_mpz_struct *pos_lp[CAP], *pos_rp[CAP], *neg_lp[CAP], *neg_rp[CAP];
  int64_t pos_k[CAP], neg_k[CAP];
  for (int i = 0; i < CAP; ++i) {
    mpz_inits(pos_l[i], pos_r[i], neg_l[i], neg_r[i], NULL);
    pos_lp[i] = AS_ISARRI(pos_l[i]);
    pos_rp[i] = AS_ISARRI(pos_r[i]);
    neg_lp[i] = AS_ISARRI(neg_l[i]);
    neg_rp[i] = AS_ISARRI(neg_r[i]);
  }

  int64_t pos_count, neg_count, xs0, substituted;
  isarri(&pos_count, pos_lp, pos_rp, pos_k,
         &neg_count, neg_lp, neg_rp, neg_k,
         &xs0, &substituted,
         CAP, /* nfloor */ 22, /* hcap */ 32, /* dlt */ 8,
         LEN, coeff_ptrs);

  if (pos_count > CAP || neg_count > CAP) {
    fprintf(stderr, "output capacity exceeded: %lld positive, %lld negative roots\n",
            (long long)pos_count, (long long)neg_count);
    return 1;
  }

  printf("positive roots: %lld\n", (long long)pos_count);
  for (int64_t i = 0; i < pos_count; ++i)
    print_window("", pos_l[i], pos_r[i], pos_k[i]);

  /* The negative half is in reflected coordinates: negate both endpoints and swap them. */
  printf("negative roots: %lld\n", (long long)neg_count);
  for (int64_t i = 0; i < neg_count; ++i) {
    mpz_t lo, hi;
    mpz_init(lo);
    mpz_init(hi);
    mpz_neg(lo, neg_r[i]);
    mpz_neg(hi, neg_l[i]);
    print_window("", lo, hi, neg_k[i]);
    mpz_clears(lo, hi, NULL);
  }
  printf("zero is a root: %s\n", xs0 ? "yes" : "no");

  for (int i = 0; i < CAP; ++i) mpz_clears(pos_l[i], pos_r[i], neg_l[i], neg_r[i], NULL);
  for (int i = 0; i < LEN; ++i) mpz_clear(c[i]);
  return 0;
}
