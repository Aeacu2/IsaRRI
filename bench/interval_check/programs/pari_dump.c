/* pari_dump.c -- the isolating intervals PARI's arm returns, for the interval check
 * (docs/LOGCF_PLAN_2026-10-08.md section 8). NOT a timing tool: the campaign's pari_timer is untouched.
 * Same steps as pari_realroots_nosqf.c (primitive part, removal of x^v, ZX_deflate_max, ZX_Uspensky with
 * flag 0), but the list ZX_Uspensky returns is printed instead of counted. PARI isolates the roots of the
 * DEFLATED polynomial Q (P = x^v Q(x^h)); for even h only the positive ones. Lines on stdout:
 *   I <name> <idx> <h> <v> <left> <right>     one per returned item (a rational root has left = right)
 * Usage: pari_dump stdin <name> | stdin-multi <name>   (idx = ordinal of the "A" line, 1-based)
 * Build: cc -O2 -I/opt/homebrew/include pari_dump.c -L/opt/homebrew/lib -lpari-gmp-tls -o ../build/pari_dump */
#include <pari/pari.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
GEN ZX_Uspensky(GEN P, GEN ab, long flag, long bitprec);
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
static void one(const char *name, long idx, GEN P) {
  pari_sp av = avma;
  long v, h;
  v = ZX_valrem(Q_primpart(P), &P);
  if (degpol(P) > 0) {
    P = ZX_deflate_max(P, &h);
    GEN soli = ZX_Uspensky(P, odd(h) ? NULL : gen_0, 0, 64);
    for (long i = 1; i < lg(soli); i++) {
      GEN e = gel(soli, i);
      if (typ(e) == t_VEC) pari_printf("I\t%s\t%ld\t%ld\t%ld\t%Ps\t%Ps\n", name, idx, h, v, gel(e, 1), gel(e, 2));
      else pari_printf("I\t%s\t%ld\t%ld\t%ld\t%Ps\t%Ps\n", name, idx, h, v, e, e);
    }
  }
  pari_printf("E\t%s\t%ld\n", name, idx);
  set_avma(av);
}
int main(int argc, char **argv) {
  if (argc != 3) return 2;
  pari_init(1UL << 28, 0);
  pari_mt_nbthreads = 1;
  paristack_setsize(1UL << 28, 1UL << 34);
  char *line; long idx = 0;
  int multi = !strcmp(argv[1], "stdin-multi");
  while ((line = read_line(stdin))) {
    char *coeff = line;
    if (multi) {
      if (!(line[0] == 'A' && line[1] == '\t')) { free(line); continue; }
      idx++;
      char *t2 = strchr(line + 2, '\t');
      if (!t2) { free(line); continue; }
      coeff = t2 + 1;
    } else idx = 1;
    GEN P = parse_poly(coeff);
    if (degpol(P) >= 1) one(argv[2], idx, P);
    free(line);
    if (!multi) break;
  }
  return 0;
}
