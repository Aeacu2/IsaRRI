# Reproducing the measurements

This is a **partial reproduction package**. It lets a reader check three things independently, and
documents, without fully automating, a fourth.

| level | what you can do | status |
|---|---|---|
| 1. Rescore | recompute the campaign's rows of Tables 7.4–7.6 from the recorded runs | complete: `python3 bench/score.py` |
| 2. Check | check every window IsaRRI returns on an input with a genuine Sturm sequence | complete: `bench/sturm/check_one.py <input>` |
| 3. Rerun IsaRRI | time the public export on any benchmark input with the campaign's timed region | complete: `bench/example/` |
| 3b. One comparison | IsaRRI against PARI on one input: digest check, interleaved runs, minimum, Sturm check, scoring | complete: `bench/example/compare.sh` |
| 4. Rerun the campaign | rerun every arm on every input | **documented, not automated**: the drivers in `drivers/` are verbatim copies that assume the development repository's layout |

## 3. Rerunning IsaRRI on one case

```bash
bench/example/run.sh            # builds, checks the input digest, times chebyshev320, prints the recorded row
bench/example/time_one <file> 3 # any input from the archive: total root count and the minimum of 3 runs
bench/example/time_one <file> 1 --windows   # also print every window (outside the timed region)
```

`time_one.c` reproduces the campaign harness's timed region
(`drivers/Dsc__export__c_harness__suite_v2_bench.cpp`, `run_once`): a fresh set of output arrays for
every run, allocated and initialised before the clock starts, with capacity equal to the number of
coefficients; only the call to `isarri` is timed; the recorded time of a case is the minimum over
its runs. Parameters `nfloor = 22`, `hcap = 32`, `dlt = 8`. On the measuring machine it reports
320 roots for `chebyshev320` in about 37 ms; the campaign recorded 41.2 ms with the development
harness binary. Absolute times depend on the machine.

`bench/example/compare.sh [input]` runs one complete comparison from this repository alone: it
builds IsaRRI's timer and PARI's (from the copies in `drivers/`), checks the input's digest, runs
three repetitions with both arms in alternating order, takes each arm's minimum, checks both counts
and IsaRRI's windows against a Sturm sequence, and scores the case as MPSolve-Bench does. It needs
clang, GMP and PARI 2.17 with its library.

## 4. Rerunning the other arms

**Modified or wrapped competitor components, all in `drivers/`:** PARI's `realroots` without the
squarefree step (`Dsc__export__c_harness__pari_realroots_nosqf.c`) and its timer (`pari_timer.c`);
the libpoly patch (`libpoly_nosqf.patch`) and its timer (`libpoly_timer.cpp`); the ANewDsc
wall-clock interposition library (`anewdsc_wallclock.c`) and driver (`anewdsc_bench.py`); the msolve
and CGAL harnesses (`all_roots_vs_competitors_bench.cpp`, `cgal_descartes_bench.cpp`); the Z3 timers
(`z3_allroots_timer.cpp`, `z3_isolate_timer.cpp`); the Sage scripts (`sage_solve_*_sqf.sage`). The
ANewDsc binary itself is not redistributed.


**Tools and versions** (the campaign's `PROVENANCE.txt` in `drivers/` records the SHA-256 prefix of
every binary and script that ran):

| arm | tool | version / identity | how it was built or called |
|---|---|---|---|
| IsaRRI | `export/isarri.ll` | this repository | `clang -O2`, linked with `runtime/lib_isabelle_llvm.c` and GMP 6.3.0 |
| msolve | msolve | commit `1c67c70` | library call `real_roots(coeffs, deg, &pos, &neg, -1, 1, 0)` (refinement off, one thread), in `drivers/Dsc__export__c_harness__all_roots_vs_competitors_bench.cpp` |
| ANewDsc | RS-ANewDsc `test_descartes_osx` | SVN 549, x86-64 binary run under Rosetta 2 | `-S 1` (and `-S 1 -i 0` for the reference row); `drivers/Dsc__export__c_harness__anewdsc_wallclock.c` is preloaded so its two measurement points read a wall clock; driver `anewdsc_bench.py` |
| Sage | SageMath | 10.9 | `real_roots(f, skip_squarefree=True)`; `sage_solve_one_sqf.sage`, `sage_solve_multi_sqf.sage` |
| PARI | libpari | 2.17.4 | `pari_realroots_nosqf.c` is PARI's `realroots` with the squarefree factorisation removed; timer `pari_timer.c`; one thread |
| Z3 | Z3 | 4.17.0 | `sqf_isolate_roots`; `z3_allroots_timer.cpp`, `z3_isolate_timer.cpp` (SMT-Bench) |
| CGAL | CGAL | 6.2 | `CGAL::internal::Descartes`; `cgal_descartes_bench.cpp` |
| libpoly | libpoly | 0.2.1, commit `c342ff1` | `drivers/Dsc__export__c_harness__libpoly_nosqf.patch` removes the squarefree factorisation from `root_finding.c`; timer `libpoly_timer.cpp` built against the patched tree |

**Build flags.** `drivers/scripts__build-allcomp-bench.sh` builds the IsaRRI harness
(`clang -O2`, `clang++ -std=c++17 -O2`). The PARI, Z3, libpoly and ANewDsc-shim sources record
their build commands in their headers, all at `-O2`. The build commands of the msolve harness
(`all_roots_vs_competitors_bench.cpp`) and of the CGAL timer were not recorded; the binaries'
digests are in `PROVENANCE.txt`.

**Orchestration.** `drivers/scripts__thesis-campaign2-run.sh` runs the three legs;
`drivers/scripts__final-suite-run.py` (MPSolve-Bench, AND-Bench) and
`drivers/benchmark_results__smt_bench__smt_bench_phase2.py` (SMT-Bench) run the cases;
`drivers/scripts__bench-guard.sh` is the quiet-machine check; `drivers/scripts__thesis-campaign-audit.sh`
audits the recorded rows. These scripts use development paths (`Dsc/export/c_harness/build/...`,
`benchmark_results/...`); rerunning them needs the binaries above built at those paths and the
inputs archive unpacked there.

**Output handling in the timed region.** Every arm times one call of its isolation entry,
including any memory the entry allocates for its own result; converting the input before and
freeing the result after lie outside. IsaRRI's interface instead writes into caller-supplied
arrays, which the harness allocates before the timer (above). `alloc_ab/` measures what that is
worth on SMT-Bench (27 September 2026, one binary, four interleaved arms): PAR2 0.816 ms for the
call alone, 0.859 ms with a minimal per-call allocation timed, 1.114 ms with the harness's own
set-up timed, against msolve's 1.117 ms in the same session (`alloc_ab/README.md`).

## Settled counts and window checks

Root counts are settled by genuine Sturm sequences (`sturm/sturm_windows.gp`), not by PARI's
`polsturm`, which PARI computes with Uspensky's Descartes method. Results:
`results/sturm_smt.tsv.gz`, `results/sturm_mpsolve.tsv` and `results/sturm_and.tsv` (one row per
polynomial: input digest, export digest, checker commit, reported counts, Sturm counts, the
reduction x^k Q(x^d) used, and an explicit status: OK, FAIL, UNCHECKED when the Sturm sequence did
not finish within the checker's budget, or DUMP_TIMEOUT when collecting the windows did not finish;
the checks ran as parallel shards, merged by `drivers/scripts__b2__merge_shards.py`, and
`sturm_and.tsv`'s `credited` column is 0 for the one IsaRRI answer returned above the 150 s cap),
`results/and_disputes.tsv` (the AND-Bench inputs on which the arms disagree, and how each was
settled) and `results/and_reference_status.tsv` (every AND-Bench input's reference status: settled,
two tools agree, one tool only, or no count).

## Per-polynomial counts on SMT-Bench

`results/smt_per_poly_check.tsv` summarises, per arm, the comparison of every recorded
per-polynomial count (every polynomial of every instance, every repetition) with the Sturm count of
that polynomial; `results/smt_per_poly_mismatches.tsv` lists the disagreements (all ANewDsc, all
inside the instances already scored as wrong). The per-polynomial run records themselves (about
1 GB) are not included.
