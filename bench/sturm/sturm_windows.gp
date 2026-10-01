\\ sturm_windows.gp -- B2 (2026-09-26): independent check of IsaRRI's returned windows with a
\\ genuine Sturm sequence (the remainder sequence of P and P'), NOT PARI's polsturm (which PARI
\\ 2.17.4 implements with Uspensky's Descartes method, rootpol.c ZX_sturmpart -> ZX_Uspensky).
\\ For squarefree P and its Sturm sequence S, V(x) (sign changes of S at x, zeros deleted) is constant
\\ between roots of P, V(c) = V(c+) at a root c, and V drops by one across each root. Hence
\\   #roots in (a,b) = V(a) - V(b) - [P(b) = 0]      (a < b rational)
\\   #roots in (0,+oo) = V(0) - V(+oo),   #roots in (-oo,0) = V(-oo) - V(0) - [P(0) = 0].
\\ Integer version (2026-09-26): pseudorem(A,B) = lc(B)^(dd+1) rem(A,B), so
\\ -sign(lc(B))^(dd+1) pseudorem(A,B) = |lc(B)|^(dd+1) (-rem(A,B)), a POSITIVE multiple of the Sturm
\\ member; dividing by the (positive) content keeps it so. Same signs at every point as the rational
\\ sequence, 5-8x faster (checked equal sign/degree structure on chrma342 and umand511).
install("RgX_pseudorem", "GG", "pseudorem");
sturmseq(P) = {
  my(S = List([P, P']), A, B, r, dd);
  while (poldegree(S[#S]) > 0,
    A = S[#S-1]; B = S[#S]; dd = poldegree(A) - poldegree(B);
    r = -sign(pollead(B))^(dd + 1) * pseudorem(A, B);
    if (r == 0, error("not squarefree"));
    r = r / abs(content(r));
    listput(S, r));
  Vec(S);
}
sc(v) = {my(c = 0, last = 0); for (i = 1, #v, if (v[i], if (last && v[i] != last, c++); last = v[i])); c}
Vat(S, t) = sc(vector(#S, i, sign(subst(S[i], 'x, t))));
Vinf(S, s) = sc(vector(#S, i, sign(pollead(S[i])) * if (s < 0, (-1)^poldegree(S[i]), 1)));
openc(S, P, a, b) = if (a >= b, 0, Vat(S, a) - Vat(S, b) - (subst(P, 'x, b) == 0));

\\ Exact reduction (2026-09-26): squarefree P = x^k R(x), k <= 1, R(0) != 0, R(x) = Q(x^d) with d the
\\ gcd of the exponents of R's terms. Q is squarefree (a repeated root y0 != 0 of Q would repeat
\\ at the d-th roots of y0 in R; y0 = 0 contradicts R(0) != 0). x -> x^d is a bijection of
\\ [0,oo) onto itself, and of (-oo,0] onto (-oo,0] (d odd) or [0,oo) (d even), so the Sturm
\\ sequence of Q decides every count about P.
red(P) = {
  my(k = valuation(P, 'x), R = P / 'x^k, d = 0, Q, v);
  if (k > 1, error("not squarefree"));
  v = Vecrev(R); for (i = 2, #v, if (v[i], d = gcd(d, i - 1)));
  if (d == 0, d = 1);
  Q = Polrev(vector(poldegree(R) \ d + 1, j, v[(j - 1) * d + 1]), 'x);
  [k, d, Q, sturmseq(Q)];
}
\\ roots of R (hence of P away from 0) in the open interval (a, b)
rootsR(D, a, b) = {
  my(d = D[2], Q = D[3], S = D[4]);
  if (a >= b, return(0));
  if (a < 0 && b > 0, return(rootsR(D, a, 0) + rootsR(D, 0, b)));
  if (a >= 0, return(openc(S, Q, a^d, b^d)));
  if (d % 2, openc(S, Q, a^d, b^d), openc(S, Q, b^d, a^d));
}
rootsP(D, a, b) = rootsR(D, a, b) + (D[1] == 1 && a < 0 && b > 0);

\\ W: vector of [sgn, l, r, k] as dumped ("+"=1, "-"=-1). Prints one line:
\\   <idx> OK|FAIL <totpos> <totneg> <zero> [reasons]
check(idx, P, pos, neg, xs0, W) = {
  my(D = red(P), S = D[4], Q = D[3], d = D[2], err = List(), tp, tn, z, np = 0, nn = 0, iv = vector(#W), a, b, s, pnt, qp, qn);
  z = (D[1] == 1);
  qp = Vat(S, 0) - Vinf(S, 1);                 \\ positive roots of Q
  qn = Vinf(S, -1) - Vat(S, 0);                \\ negative roots of Q (Q(0) != 0)
  tp = qp; tn = if (d % 2, qn, qp);
  if (xs0 != z, listput(err, "zeroflag"));
  for (i = 1, #W,
    s = W[i][1];
    if (s > 0, np++; a = W[i][2] / 2^W[i][4]; b = W[i][3] / 2^W[i][4],
               nn++; a = -W[i][3] / 2^W[i][4]; b = -W[i][2] / 2^W[i][4]);
    iv[i] = [a, b];
    if (a == b,
      if (subst(P, 'x, a) != 0, listput(err, Str("point-not-root:", i)));
      if (s * a <= 0, listput(err, Str("point-wrong-half:", i))),
      if (a > b, listput(err, Str("reversed:", i)));
      if (s > 0 && a < 0, listput(err, Str("window-wrong-half:", i)));
      if (s < 0 && b > 0, listput(err, Str("window-wrong-half:", i)));
      if (a < b && rootsP(D, a, b) != 1, listput(err, Str("not-one-root:", i)))));
  if (np != pos || nn != neg, listput(err, "dump-count"));
  if (pos != tp, listput(err, Str("pos-count:", pos, "/", tp)));
  if (neg != tn, listput(err, Str("neg-count:", neg, "/", tn)));
  for (i = 1, #W, for (j = i + 1, #W,
    my(A = iv[i], B = iv[j], lo, hi);
    if (A[1] == A[2] && B[1] == B[2],
      if (A[1] == B[1], listput(err, Str("shared-point:", i, ",", j))),
    if (A[1] == A[2] || B[1] == B[2],
      pnt = if (A[1] == A[2], A[1], B[1]);
      my(O = if (A[1] == A[2], B, A));
      if (O[1] < pnt && pnt < O[2], listput(err, Str("point-in-window:", i, ",", j))),
      lo = max(A[1], B[1]); hi = min(A[2], B[2]);
      if (lo < hi && rootsP(D, lo, hi) > 0, listput(err, Str("shared-root:", i, ",", j)))))));
  print(idx, "\t", if (#err, "FAIL", "OK"), "\t", tp, "\t", tn, "\t", z, "\t", strjoin(Vec(err), ","), "\t", D[1], "\t", D[2]);
}
\\ total distinct real roots of a squarefree P by the same reduction (reference counts)
sturmtotal(P) = {my(D = red(P), S = D[4], qp, qn); qp = Vat(S, 0) - Vinf(S, 1); qn = Vinf(S, -1) - Vat(S, 0);
  qp + if (D[2] % 2, qn, qp) + (D[1] == 1)}
