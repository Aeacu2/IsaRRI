/* pari_realroots_nosqf.c -- PARI 2.17.4's realroots() (src/basemath/rootpol.c:2582) with two changes,
 * for timing PARI on the same task as the other arms (thesis re-benchmark, 2026-09-18):
 *   1. no ZX_squff(): the input is treated as its own single squarefree factor. Valid because every
 *      suite input is certified squarefree (sqfree_gate_2026-09-18.csv; SMT polys by construction).
 *   2. ZX_Uspensky(.., flag = 0): return isolating intervals (and exact rational roots) instead of
 *      roots refined to working precision -- isolation, the task every other arm performs.
 * Everything else is PARI's: primitive part, removal of x^v, ZX_deflate_max (power substitution),
 * and ZX_Uspensky's own rational-root step. Returns the number of distinct real roots.
 * Build: cc -O2 -shared -fPIC -I/opt/homebrew/include pari_realroots_nosqf.c
 *        -L/opt/homebrew/lib -lpari-gmp-tls -o build/pari_realroots_nosqf.dylib
 * gp:    install("realroots_nosqf_count", "lG", , "build/pari_realroots_nosqf.dylib") */
#include <pari/pari.h>

GEN ZX_Uspensky(GEN P, GEN ab, long flag, long bitprec);

long
realroots_nosqf_count(GEN P)
{
  pari_sp av = avma;
  long v, h, n;
  GEN soli;
  if (typ(P) != t_POL || degpol(P) <= 0) pari_err_TYPE("realroots_nosqf_count", P);
  v = ZX_valrem(Q_primpart(P), &P);
  if (degpol(P) == 0) { set_avma(av); return v ? 1 : 0; }
  P = ZX_deflate_max(P, &h);
  soli = ZX_Uspensky(P, odd(h) ? NULL : gen_0, 0, 64);
  n = lg(soli) - 1;
  if (!odd(h)) n *= 2;          /* each positive root r of Q gives +-r^(1/h) */
  set_avma(av);
  return n + (v ? 1 : 0);
}
