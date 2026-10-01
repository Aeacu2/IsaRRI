\\ SMT-BENCH Phase 2 multi-poly companion to pari_solve_one.gp: reads one dump-format poly
\\ per line ("A\t<deg>\t<c0>,<c1>,...") from the file named by the global `polysfile`, loops
\\ polrootsreal over ALL of them IN-PROCESS (one gp session per instance, not per poly),
\\ sums isolation ms and root counts. The runner's subprocess cap is the sole supervisor.
\\ Invoked: echo 'polysfile="..."; casename="x"; read("pari_solve_multi.gp")' | gp -q
lines = readstr(polysfile);
total_ms = 0; total_roots = 0; npolys = 0;
for(i = 1, #lines, ln = lines[i]; if(#ln == 0, next); parts = strsplit(ln, "\t"); if(#parts < 3 || parts[1] != "A", next); coeffs = eval(concat("[", concat(parts[3], "]"))); if(#coeffs == 0, next); poly = Pol(coeffs); gettime(); roots = polrootsreal(poly); ms = gettime(); printf("P\t%d\t%d\t%d\t%d\n", npolys + 1, poldegree(poly), #roots, ms); total_ms += ms; total_roots += #roots; npolys += 1);
if(npolys == 0, error("pari_solve_multi: no polynomials parsed"));
printf("%s,roots=%d,ms=%d,polys=%d\n", casename, total_roots, total_ms, npolys);
quit;
