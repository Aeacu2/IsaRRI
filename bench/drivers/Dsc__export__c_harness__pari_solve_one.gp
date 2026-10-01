\\ Generic single-case companion to pari_all_roots_bench.gp: expects the globals `coeffs`
\\ (ascending-degree integer vector, c0..cn) and `casename` (string) to already be set by the
\\ invoker (e.g. `echo 'coeffs=[...]; casename="x"; read("pari_solve_one.gp")' | gp -q`), so an
\\ external driver can feed any suite_v2_bench.cpp case (via its --dump-coeffs mode) without
\\ hand-porting every generator into this file, same idea as the --solve-stdin addition to
\\ all_roots_vs_competitors_bench.cpp / cgal_descartes_bench.cpp's `stdin` mode.
poly = Pol(Vecrev(coeffs));
gettime();
roots = polrootsreal(poly);
ms = gettime();
printf("%s,deg=%d,roots=%d,ms=%d\n", casename, poldegree(poly), #roots, ms);
quit;
