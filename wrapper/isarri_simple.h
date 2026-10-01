/*
 * isarri_simple.h -- a convenience layer over isarri(). NOT VERIFIED.
 *
 * isarri() (export/isarri.h, contract in export/isarri_contract.h) is the verified function. This
 * layer is ordinary C around it: it sets up the memory layout the theorem assumes (obligation 9),
 * checks the two obligations that are cheap to check (len >= 2, nonzero leading coefficient),
 * maps the negative half back from reflected coordinates, adds the root at zero, sorts the
 * windows, and serialises calls with a mutex so that several threads may call it (a program that
 * also calls isarri() directly must keep those calls from overlapping with these). Its own
 * correctness is not proved; it is short so that it can be read.
 *
 * The caller must still establish the obligations the code does not check: a SQUAREFREE input
 * (pass P / gcd(P, P')) and the word bounds of obligations 4, 5 and 8 in isarri_contract.h. For an
 * input violating them the result is not covered by the theorem, and the call need not terminate.
 */
#ifndef ISARRI_SIMPLE_H
#define ISARRI_SIMPLE_H

#include <stddef.h>
#include <gmp.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The tuning parameters of the thesis's measurements. The theorem holds for any values meeting
   obligations 6, 8 and 9; with HCAP = 32, obligation 8 applies to inputs P(x) = Q(x^d) with even d. */
#define ISARRI_SIMPLE_NFLOOR 22
#define ISARRI_SIMPLE_HCAP 32
#define ISARRI_SIMPLE_DLT 8

/* One real root, in ORIGINAL coordinates and lowest terms: if lo == hi, the root is lo / 2^k
   exactly; otherwise it is the only root in the open interval (lo / 2^k, hi / 2^k). */
typedef struct {
  mpz_t lo, hi;
  unsigned long k;
} isarri_window;

/* All distinct real roots, sorted by the window's left endpoint. Two open windows may overlap
   in an interval that contains no root (power-substitution path); no root lies in two windows. */
typedef struct {
  size_t n;
  isarri_window *w;
} isarri_roots;

enum {
  ISARRI_OK = 0,
  ISARRI_TOO_SHORT = -1,     /* len < 2 (a constant has no isolated roots) */
  ISARRI_ZERO_LEADING = -2,  /* coeffs[len - 1] == 0 */
  ISARRI_NO_MEMORY = -3
};

/* Isolates the real roots of sum_{i < len} coeffs[i] x^i. coeffs is read, not modified.
   On ISARRI_OK, *out holds the roots and must be released with isarri_roots_clear. */
int isarri_isolate(const mpz_t *coeffs, size_t len, isarri_roots *out);

void isarri_roots_clear(isarri_roots *roots);

#ifdef __cplusplus
}
#endif

#endif
