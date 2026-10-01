/*
 * test_isarri_simple.c -- tests of the unverified convenience layer (isarri_simple.c).
 * Known roots are checked against the returned windows (each root in exactly one window, each
 * window holding exactly one root, windows sorted); then eight threads call the layer at once.
 */
#include <math.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

#include "isarri_simple.h"

static int failures = 0;
#define CHECK(c, ...) do { if (!(c)) { ++failures; fprintf(stderr, "FAIL: " __VA_ARGS__); fprintf(stderr, "\n"); } } while (0)

static double endpoint(const mpz_t num, unsigned long k) { return ldexp(mpz_get_d(num), -(int)k); }

static int in_window(double r, const isarri_window *w) {
  double lo = endpoint(w->lo, w->k), hi = endpoint(w->hi, w->k);
  return mpz_cmp(w->lo, w->hi) == 0 ? r == lo : (lo < r && r < hi);
}

static void set_poly(mpz_t *c, const long *v, size_t len) {
  for (size_t i = 0; i < len; ++i) mpz_init_set_si(c[i], v[i]);
}

static void check_roots(const char *name, const mpz_t *c, size_t len, const double *roots, size_t nroots) {
  isarri_roots r;
  int rc = isarri_isolate(c, len, &r);
  CHECK(rc == ISARRI_OK, "%s: rc %d", name, rc);
  CHECK(r.n == nroots, "%s: %zu windows, expected %zu", name, r.n, nroots);
  for (size_t i = 0; i < nroots; ++i) {
    size_t hits = 0;
    for (size_t j = 0; j < r.n; ++j) hits += in_window(roots[i], &r.w[j]);
    CHECK(hits == 1, "%s: root %.17g lies in %zu windows", name, roots[i], hits);
  }
  for (size_t j = 0; j < r.n; ++j) {
    size_t hits = 0;
    for (size_t i = 0; i < nroots; ++i) hits += in_window(roots[i], &r.w[j]);
    CHECK(hits == 1, "%s: window %zu holds %zu known roots", name, j, hits);
    if (j) CHECK(endpoint(r.w[j - 1].lo, r.w[j - 1].k) <= endpoint(r.w[j].lo, r.w[j].k), "%s: not sorted", name);
  }
  printf("%-28s %zu roots:", name, r.n);
  for (size_t j = 0; j < r.n; ++j) {
    if (mpz_cmp(r.w[j].lo, r.w[j].hi) == 0) gmp_printf(" {%Zd}/2^%lu", r.w[j].lo, r.w[j].k);
    else gmp_printf(" (%Zd, %Zd)/2^%lu", r.w[j].lo, r.w[j].hi, r.w[j].k);
  }
  printf("\n");
  isarri_roots_clear(&r);
}

/* prod_{j=1}^{n} (x - j), ascending coefficients */
static void wilkinson(mpz_t *c, size_t n) {
  for (size_t i = 0; i <= n; ++i) mpz_init_set_ui(c[i], i == 0 ? 1 : 0);
  for (size_t j = 1; j <= n; ++j)
    for (size_t i = j; i-- > 0;) {        /* multiply by (x - j) in place */
      mpz_add(c[i + 1], c[i + 1], c[i]);
      mpz_mul_si(c[i], c[i], -(long)j);
    }
}

enum { WLEN = 11 };
static mpz_t W[WLEN];
static isarri_roots W_ref;

static void *worker(void *arg) {
  (void)arg;
  for (int it = 0; it < 100; ++it) {
    isarri_roots r;
    if (isarri_isolate((const mpz_t *)W, WLEN, &r) != ISARRI_OK || r.n != W_ref.n) {
      __atomic_add_fetch(&failures, 1, __ATOMIC_SEQ_CST);
      return NULL;
    }
    for (size_t j = 0; j < r.n; ++j)
      if (mpz_cmp(r.w[j].lo, W_ref.w[j].lo) || mpz_cmp(r.w[j].hi, W_ref.w[j].hi) || r.w[j].k != W_ref.w[j].k)
        __atomic_add_fetch(&failures, 1, __ATOMIC_SEQ_CST);
    isarri_roots_clear(&r);
  }
  return NULL;
}

int main(void) {
  { long v[] = {6, -5, -2, 1}; mpz_t c[4]; set_poly(c, v, 4);
    double roots[] = {-2, 1, 3};
    check_roots("(x-1)(x-3)(x+2)", (const mpz_t *)c, 4, roots, 3);
    for (int i = 0; i < 4; ++i) mpz_clear(c[i]); }
  { long v[] = {0, -2, 0, 1}; mpz_t c[4]; set_poly(c, v, 4);
    double roots[] = {-sqrt(2.0), 0, sqrt(2.0)};
    check_roots("x^3 - 2x", (const mpz_t *)c, 4, roots, 3);
    for (int i = 0; i < 4; ++i) mpz_clear(c[i]); }
  { long v[25] = {0}; v[0] = 4; v[12] = -5; v[24] = 1; mpz_t c[25]; set_poly(c, v, 25);
    double r = pow(4.0, 1.0 / 12.0), roots[] = {-r, -1, 1, r};
    check_roots("x^24 - 5x^12 + 4", (const mpz_t *)c, 25, roots, 4);
    for (int i = 0; i < 25; ++i) mpz_clear(c[i]); }
  { long v[] = {1, 0, 1}; mpz_t c[3]; set_poly(c, v, 3);
    check_roots("x^2 + 1", (const mpz_t *)c, 3, NULL, 0);
    for (int i = 0; i < 3; ++i) mpz_clear(c[i]); }

  wilkinson(W, WLEN - 1);
  { double roots[10]; for (int j = 0; j < 10; ++j) roots[j] = j + 1;
    check_roots("Wilkinson W_10", (const mpz_t *)W, WLEN, roots, 10); }

  { mpz_t c[2]; mpz_init_set_si(c[0], 5); mpz_init_set_si(c[1], 0); isarri_roots r;
    CHECK(isarri_isolate((const mpz_t *)c, 2, &r) == ISARRI_ZERO_LEADING, "zero leading coefficient not rejected");
    CHECK(isarri_isolate((const mpz_t *)c, 1, &r) == ISARRI_TOO_SHORT, "length 1 not rejected");
    mpz_clear(c[0]); mpz_clear(c[1]); }

  CHECK(isarri_isolate((const mpz_t *)W, WLEN, &W_ref) == ISARRI_OK, "reference call");
  pthread_t t[8];
  for (int i = 0; i < 8; ++i) pthread_create(&t[i], NULL, worker, NULL);
  for (int i = 0; i < 8; ++i) pthread_join(t[i], NULL);
  printf("8 threads x 100 concurrent calls on W_10: %s\n", failures ? "MISMATCH" : "all equal to the reference");
  isarri_roots_clear(&W_ref);
  for (int i = 0; i < WLEN; ++i) mpz_clear(W[i]);

  printf(failures ? "FAILED (%d)\n" : "all tests passed\n", failures);
  return failures != 0;
}
