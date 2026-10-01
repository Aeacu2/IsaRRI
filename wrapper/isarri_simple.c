/*
 * isarri_simple.c -- a convenience layer over isarri(). NOT VERIFIED; see isarri_simple.h.
 */
#include "isarri_simple.h"

#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>

#include "isarri_contract.h"

/* The runtime allocator the exported code calls keeps unlocked free lists, so isarri() must not
   run concurrently; every call through this layer takes this lock. */
static pthread_mutex_t isarri_lock = PTHREAD_MUTEX_INITIALIZER;

#define AS_ISARRI(z) ((gmp_mpz_struct *)(z))

/* Sign of lo_a / 2^ka - lo_b / 2^kb, then of the right endpoints: a total order for sorting. */
static int cmp_scaled(const mpz_t a, unsigned long ka, const mpz_t b, unsigned long kb) {
  mpz_t x, y;
  mpz_init(x);
  mpz_init(y);
  if (ka >= kb) {
    mpz_set(x, a);
    mpz_mul_2exp(y, b, ka - kb);
  } else {
    mpz_mul_2exp(x, a, kb - ka);
    mpz_set(y, b);
  }
  int c = mpz_cmp(x, y);
  mpz_clear(x);
  mpz_clear(y);
  return c;
}

/* Lowest terms: divide both numerators by 2 while both are even and the exponent is positive. */
static void reduce(isarri_window *w) {
  while (w->k > 0 && mpz_even_p(w->lo) && mpz_even_p(w->hi)) {
    mpz_tdiv_q_2exp(w->lo, w->lo, 1);
    mpz_tdiv_q_2exp(w->hi, w->hi, 1);
    --w->k;
  }
}

static int cmp_window(const void *pa, const void *pb) {
  const isarri_window *a = pa, *b = pb;
  int c = cmp_scaled(a->lo, a->k, b->lo, b->k);
  return c ? c : cmp_scaled(a->hi, a->k, b->hi, b->k);
}

int isarri_isolate(const mpz_t *coeffs, size_t len, isarri_roots *out) {
  out->n = 0;
  out->w = NULL;
  if (len < 2) return ISARRI_TOO_SHORT;
  if (mpz_sgn(coeffs[len - 1]) == 0) return ISARRI_ZERO_LEADING;

  /* Capacity len: each half has at most deg = len - 1 roots, so no window is dropped. */
  const size_t cap = len;
  gmp_mpz_struct **in = malloc(len * sizeof *in);
  mpz_t *z = malloc(4 * cap * sizeof *z);           /* pos_l, pos_r, neg_l, neg_r */
  gmp_mpz_struct **zp = malloc(4 * cap * sizeof *zp);
  int64_t *kk = malloc(2 * cap * sizeof *kk);        /* pos_k, neg_k */
  if (!in || !z || !zp || !kk) {
    free(in); free(z); free(zp); free(kk);
    return ISARRI_NO_MEMORY;
  }
  /* The solver borrows the input and preserves it (the theorem's postcondition). */
  for (size_t i = 0; i < len; ++i) in[i] = AS_ISARRI(coeffs[i]);
  /* Obligation 9: every output slot is its own initialised mpz_t. */
  for (size_t i = 0; i < 4 * cap; ++i) {
    mpz_init(z[i]);
    zp[i] = AS_ISARRI(z[i]);
  }

  int64_t pos_count = 0, neg_count = 0, xs0 = 0, substituted = 0;
  pthread_mutex_lock(&isarri_lock);
  isarri(&pos_count, zp, zp + cap, kk,
         &neg_count, zp + 2 * cap, zp + 3 * cap, kk + cap,
         &xs0, &substituted,
         (int64_t)cap, ISARRI_SIMPLE_NFLOOR, ISARRI_SIMPLE_HCAP, ISARRI_SIMPLE_DLT,
         (int64_t)len, in);
  pthread_mutex_unlock(&isarri_lock);

  int rc = ISARRI_OK;
  const size_t n = (size_t)pos_count + (size_t)neg_count + (xs0 ? 1 : 0);
  isarri_window *w = n ? malloc(n * sizeof *w) : NULL;
  if (n && !w) {
    rc = ISARRI_NO_MEMORY;
  } else {
    size_t j = 0;
    for (int64_t i = 0; i < pos_count; ++i, ++j) {
      mpz_init_set(w[j].lo, z[i]);
      mpz_init_set(w[j].hi, z[cap + i]);
      w[j].k = (unsigned long)kk[i];
    }
    /* The negative half is in reflected coordinates: (a, b) there stands for (-b, -a). */
    for (int64_t i = 0; i < neg_count; ++i, ++j) {
      mpz_init(w[j].lo);
      mpz_init(w[j].hi);
      mpz_neg(w[j].lo, z[3 * cap + i]);
      mpz_neg(w[j].hi, z[2 * cap + i]);
      w[j].k = (unsigned long)kk[cap + i];
    }
    if (xs0) {
      mpz_init(w[j].lo);
      mpz_init(w[j].hi);
      w[j].k = 0;
      ++j;
    }
    for (size_t i = 0; i < n; ++i) reduce(&w[i]);
    qsort(w, n, sizeof *w, cmp_window);
    out->n = n;
    out->w = w;
  }

  for (size_t i = 0; i < 4 * cap; ++i) mpz_clear(z[i]);
  free(in); free(z); free(zp); free(kk);
  return rc;
}

void isarri_roots_clear(isarri_roots *roots) {
  for (size_t i = 0; i < roots->n; ++i) {
    mpz_clear(roots->w[i].lo);
    mpz_clear(roots->w[i].hi);
  }
  free(roots->w);
  roots->n = 0;
  roots->w = NULL;
}
