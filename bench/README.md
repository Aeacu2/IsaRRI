# Benchmarks

This directory holds the measurements behind Chapter 7 and Appendix D of the thesis: IsaRRI and
seven other real-root isolators, timed on three benchmark suites on one machine (Apple M4, 16 GB,
macOS 26.5.2) from 18 to 19 September 2026 (UTC). A second configuration of one of them (ANewDsc
with `-i 0`) is recorded for reference. The protocol was written down and fixed before the first
measurement.

| path | contents |
|---|---|
| `results/smt.tsv` | SMT-Bench: one row per run (instance, arm, repetition) |
| `results/mpsolve.csv` | MPSolve-Bench: one row per (case, arm), the best of its runs |
| `results/and.csv` | AND-Bench: one row per (case, arm), the best of its runs |
| `results/campaign.log` | the log of the MPSolve-Bench and AND-Bench runs, one line per completed or timed-out run |
| `results/sturm_smt.tsv.gz`, `results/sturm_mpsolve.tsv`, `results/sturm_and.tsv` | per polynomial: the Sturm count and the check of every window IsaRRI returned, with input and export digests and the checker commit |
| `results/and_disputes.tsv`, `results/and_reference_status.tsv` | AND-Bench: how each disputed count was settled, and every input's reference status |
| `results/smt_per_poly_check.tsv` | SMT-Bench: per arm, every recorded per-polynomial count against that polynomial's Sturm count |
| `results/smt_per_poly_mismatches.tsv` | the disagreements found by that check (all ANewDsc, all in instances already scored wrong) |
| `score.py` | recomputes the campaign's rows of the thesis's three per-suite tables from `results/` |
| `sturm/` | the Sturm-sequence checker (`sturm_windows.gp`, `window_dump.c`) and `check_one.py`, which checks IsaRRI's windows on any input |
| `inputs/` | the case tables of the three suites and the digests of every input file |
| `drivers/` | verbatim copies of the programs that produced the data |
| `example/` | one benchmark case end to end against the public export (`example/run.sh`) |
| `REPRODUCE.md` | what can be reproduced from this directory, tool versions, build flags and how each arm was called |

## Reproducing the tables

```bash
python3 bench/score.py                 # the campaign's rows of the three per-suite tables (Chapter 7)
python3 bench/score.py and --cap 90    # AND-Bench scored at a lower cap
python3 bench/score.py spread          # the run-to-run spread quoted in the protocol
python3 bench/sturm/check_one.py <in> # IsaRRI's windows on one input, checked with a Sturm sequence
bench/example/compare.sh               # one complete comparison, IsaRRI against PARI
```

`score.py` needs only Python 3; its docstring restates the scoring rules below. `check_one.py`
also needs clang, GMP and PARI/GP (for exact integer arithmetic only) and an input file (below).

## The three suites

| suite | inputs |
|---|---|
| **SMT-Bench** | 326 instances of the SMT-LIB 2025 library (non-incremental). 812 instances of five logics with nonlinear arithmetic (QF_NIA, QF_NRA, NRA, AUFNIRA, QF_FP) were sampled by family (a family of at most 50 instances in full; from a family of N > 50 instances, √N of them, at least 10 and at most 100), and Z3 4.17.0, instrumented, was run on each with a 30 s limit. The suite consists of the 326 instances, from the first four logics, on which Z3's nonlinear engine called its root isolator. For each, the input is the set of distinct univariate polynomials that the engine passed to that isolator (`sqf_isolate_roots`): 341 282 polynomials in all, 325 663 distinct across the suite, 99.91% of degree at most 8. |
| **MPSolve-Bench** | the 131 of the 166 test polynomials distributed with MPSolve 3.2.1 whose coefficients are real: integer (101), rational (22) or exact decimal (8). Rational and decimal coefficients are converted exactly to integers by clearing denominators. The 35 polynomials with complex coefficients are excluded. The 10 inputs with repeated roots are replaced by their squarefree parts. |
| **AND-Bench** | 295 polynomials regenerated from the benchmark tables of ANewDsc (Kobel, Rouillier and Sagraloff, ISSAC 2016, and the tables on its web page): 19 tables of 16 families, each table a ladder of rungs of increasing degree or coefficient size. The tables give parameters and timings but not the polynomials, so each polynomial is generated from its row's construction, with the exact degree and a coefficient size within two bits of the stated one. The random families are therefore new draws, not the authors' instances. |

Every input is squarefree: for each one a prime `p` not dividing the leading coefficient was found
with `gcd(P mod p, P' mod p) = 1`, which implies that `P` is squarefree over the rationals.

**Reference root counts.** Counts are settled by genuine Sturm sequences, computed by
`sturm/sturm_windows.gp` in exact integer arithmetic (pseudo-remainders) (not by PARI's `polsturm`, which PARI
computes with Uspensky's Descartes method). On SMT-Bench and MPSolve-Bench every polynomial is
Sturm-counted: on SMT-Bench, where the scored reference is Z3's count summed over an instance, the
Sturm counts give the same total on all 326 instances, and every arm's count for every polynomial,
in every repetition, was compared with its Sturm count (`results/smt_per_poly_check.tsv`), so no
two errors can cancel inside an instance total; on MPSolve-Bench the Sturm count equals the scored
count on all 131 polynomials. AND-Bench reaches degrees where a Sturm sequence is often out of
reach. Every count on which the arms disagree is settled (13 inputs; `results/and_disputes.tsv`): by
a Sturm sequence, by the theorem that the Chebyshev, Hermite and Legendre polynomials of degree n
have n distinct real roots, or, for the two largest gauss rungs, by an exact Gerschgorin certificate
(`results/and_gauss_gerschgorin.tsv`). Separately, the window check confirmed 161 of IsaRRI's 209
AND-Bench answers (208 within the cap and one above it); the other 48 exceeded the checker's 900 s
budget and are recorded as UNCHECKED (`results/sturm_and.tsv`). On 223 inputs at least two tools agree, on 40
only ANewDsc returns a count (credited unchecked), and on 19 no arm does
(`results/and_reference_status.tsv`). These are the classes of the campaign's arms. With RisolateR's counts added, as in the thesis's
Table 7.3, 245 inputs are agreed, 22 have one tool and 15 have none. The case tables' `oracle` column is the count used for
scoring: on a settled input it equals the settled count; elsewhere it equals the count every tool
that answered returned, or is `-1` (26 inputs), where any count is credited.

## The task and the arms

Every arm does the same work inside its timed region: isolate the real roots of a squarefree
integer polynomial, with no squarefree preprocessing and no refinement of the intervals. Reading
the input, starting a process and printing the output are outside the timed region.

| arm | tool and entry point |
|---|---|
| `IsaRRI` | `export/isarri.ll` of this repository, entry `isarri` (see below for the renaming) |
| `msolve` | msolve, commit `1c67c70`, `real_roots` with interval refinement off, one thread |
| `anewdsc` | the precompiled RS-ANewDsc binary `test_descartes_osx` (SVN 549; x86-64, run under Rosetta 2), `-S 1` (input is squarefree), otherwise its default configuration |
| `anewdsc_i0` | the same binary with `-S 1 -i 0`: the tool marks its default `-i 1` as experimental, so this configuration is recorded for reference; it is not ranked, and `score.py` prints it below the ranked arms |
| `sage` | SageMath 10.9, `real_roots` with `skip_squarefree=True` |
| `pari` | PARI 2.17.4, a copy of its internal `realroots` with the squarefree factorisation removed and returning isolating intervals, one thread |
| `z3` | Z3 4.17.0, `sqf_isolate_roots`, the entry Z3's own engine calls |
| `cgal` | CGAL 6.2, the Descartes isolator of its algebraic kernel |
| `libpoly` | libpoly 0.2.1 (commit `c342ff1`), its isolation entry with the squarefree factorisation removed |

ANewDsc measures its own isolation phase; a preloaded library makes the two measurement points
read a wall clock instead of processor time (`drivers/Dsc__export__c_harness__anewdsc_wallclock.c`).
Every other arm is timed on a monotonic wall clock around its isolation call.

## Protocol

**Runs.** A *run* is one timed isolation of one input by one arm. Each case is run 5 times on
SMT-Bench, 3 times on MPSolve-Bench and at most twice on AND-Bench. Runs are made one at a time.
Within each repetition every arm runs once, in an order rotated by case and repetition, so that
no arm always runs first or last and no arm's runs follow one another directly.

**Caps.** A run counts as a timeout when the solve time it reports exceeds the cap of its suite:
1 s on SMT-Bench, 60 s on MPSolve-Bench, and 180 s on AND-Bench, which is then scored at 150 s
(below). A process is killed only at the cap plus 15 s of wall time (plus 4 s of interpreter
start-up for Sage on SMT-Bench), so that start-up and parsing never count against the cap.

**The recorded time** of a case and arm is the minimum over its completed runs: interference from
the machine only adds time. A case counts as a timeout for an arm only if none of its runs
completed.

**AND-Bench: run at 180 s, scored at 150 s, one timeout ends a case.** AND-Bench runs are long, so
a case is not run a second time once a run has timed out at 180 s. Scoring at 150 s makes this
safe: the second run could change the score only by finishing within 150 s after the first
exceeded 180 s, i.e. by being at least a sixth faster. On this campaign's own repeated runs of a
second or more (887 case–arm pairs), the fastest and slowest run differ by 0.15% at the median,
3.24% at the 95th percentile and 11.9% at most (`score.py spread`). Every run that completes
within a lower cap is recorded, so the suite can be re-scored exactly at any cap up to 180 s.

**AND-Bench: ladders.** Once an arm times out or stops with an error on a rung of a table, the
larger rungs of that table are recorded as `SKIPPED` for that arm without being run. A wrong
count does not trigger this. On the random families, where a larger rung is not obviously harder,
the rule was checked on 48 pairs of arm and table from earlier runs in which every rung was run: in
none did an arm complete a rung after failing a smaller one. When AND-Bench is scored at a cap
below 180 s, the rule is applied again, so a rung that completes only above the new cap is a
timeout and the larger rungs of its table become `SKIPPED`.

**MPSolve-Bench** has no early stop: every case gets all 3 runs.

**Quiet machine.** Before the first case of each family, a check waited until no other process
was using the processor. Before every other case the same check ran without waiting and logged
any other busy process; it logged one case, which was measured again on a quiet machine before
scoring. After the launch, the check was changed to ignore activity that stops within five
seconds, after a transient system process had stalled it; no cap, repetition count, arm or
scoring rule changed. The machine was kept from sleeping throughout.

## Scoring

Each (case, arm) pair is one cell, and every cell is one of:

| outcome | meaning | charged |
|---|---|---|
| done | completed within the cap with the reference count (or any count where none is determined) | its recorded time |
| wrong | completed with a count other than the reference count | twice the cap |
| timeout | no run completed within the cap | twice the cap |
| skipped | not run because of the ladder rule (AND-Bench only) | twice the cap |
| error | the tool stopped with an error | twice the cap |
| slow | SMT-Bench only: completed, correct, but above the cap | twice the cap |

**PAR2** is the mean charge over all cases of the suite. It is a mean of times and so is dominated
by the hardest cases. The **geometric mean** of an arm's recorded times over the cases it
completes is published beside it; it weighs every case equally, but each arm's is taken over its
own completed cases. The thesis also reports, for pairs of arms, the geometric mean of the
per-case time ratio over the cases both complete. PAR2 and the geometric mean can rank arms
differently.

On SMT-Bench a cell's time is the sum over the instance's polynomials, and "slow" is a separate
outcome because a run above the 1 s cap is not stopped: only its 16 s kill ends it. Sage has 24
slow instances; ANewDsc's 29 timeouts per configuration are that kill, reached because the binary
is started once per polynomial and the starts accumulate, so they measure how it must be called
rather than its isolation.

## File formats

**`results/smt.tsv`** — one row per run; the first line is the header.

| column | meaning |
|---|---|
| `instance` | SMT-LIB instance, `<logic>_<family>__<file>` |
| `arm` | arm name as above |
| `rep` | repetition, 1–5 |
| `status` | `OK` or `TIMEOUT` (killed at 16 s wall) |
| `roots` | total number of real roots over the instance's polynomials (`NA` on timeout) |
| `ms` | total solve time over the instance's polynomials, in milliseconds (`NA` on timeout) |
| `polys` | number of polynomials solved |
| `wall_ms` | wall time of the whole process, including start-up; not used for scoring |
| `rc`, `err` | exit code and error text of the process |

**`results/mpsolve.csv`, `results/and.csv`** — one row per (case, arm).

| column | meaning |
|---|---|
| `case` | input name (file name without extension) |
| `id` | row number in the suite's case table (`inputs/`) |
| `band` | position of the rung in its table's ladder, counted from 1 (always 1 on MPSolve-Bench, which has no ladders) |
| `family` | MPSolve-Bench: MPSolve's file type (`d`/`s`/`u` dense, sparse or user-defined; `r` real; `i`/`q`/`f` integer, rational or decimal coefficients; `v3` a file in MPSolve's newer format). AND-Bench: the family |
| `degree` | degree |
| `params` | MPSolve-Bench: `tau=` maximum coefficient bit length. AND-Bench: table (`t01`–`t19`), degree `d` and coefficient bit length `b` of the rung, plus the construction's own parameter where it has one |
| `oracle` | reference count of distinct real roots; `-1` where undetermined |
| `solver` | arm name |
| `roots` | count returned (`-1` if none) |
| `ms` | recorded time in milliseconds; for a timeout, the run cap (60 000 or 180 000); `-1` for skipped and error |
| `status` | `OK`, `TIMEOUT`, `SKIPPED(>=B<n>)` (skipped because the arm failed rung `n` of the table), or `ERROR` / `ERROR(<reason>)` |

The error rows are Sage's `RecursionError` on `mig1_500_1` (MPSolve-Bench) and on four AND-Bench
cases, and one CGAL error on `and10_mignotte_rat_d129_b180`: the process was killed by the system
without a message (a rerun ended the same way after 106 s, at 1.3 GB resident). Four of Sage's
reproduce with its stock entry point; on `and17_random_monic_lt1_d724_b1024` the error occurs
only with `skip_squarefree=True`, although the input is squarefree, and the stock entry solves it
in 0.24 s. At the 150 s scoring cap the CGAL row is a skipped rung, because CGAL's previous rung
took 159 s.

**`results/campaign.log`** — the log written while MPSolve-Bench and AND-Bench ran, with local
directory paths removed. A line `<case>/<arm> rep1 OK roots=<n> <t>ms` records one completed
run: the number printed after `rep` is always 1 in these lines, and an arm's repetitions of a case
follow one another in log order. A line `<case>/<arm> rep<r> over cap on solve time (<t> ms) ->
TIMEOUT` records a run whose reported time exceeded the cap (the wrapper's `OK` line for the same
run comes just before it; see "Names, and the drivers"), and `<case>/<arm> rep1 TIMEOUT` one that
was killed. Runs that end in an error are not logged individually. Lines starting with `[`
report progress, `guard:` lines the check for other processes, and `WARNING root-count mismatch`
lines a disagreement with the reference count. The SMT-Bench leg writes only its start and end
here (its runs are in `smt.tsv`), and the log ends with the output of the post-campaign audit. The
log uses the development repository's arm names (below).

**`inputs/`**: `MANIFEST.tsv` gives, for every input file, the suite, its path, its size and its
SHA-256 digest. `mpsolve_cases_record.json` and `and_cases_record.json` are the case tables
(fields as in the result files; `desc` is `params`, `table` the AND-Bench table number).
`smt_manifest.tsv` lists the SMT-Bench instances: `corpus` (logic and family), `nA` (number of
isolation calls Z3 made), `ndistinct` (distinct polynomials), `max_deg`, `tot_deg`, `max_digits`
(the widest coefficient, in decimal digits) and `top_multiplicity` (how often the most frequent
polynomial was isolated).

The input files themselves (755 files, 198 MB, 95 MB compressed) are distributed as the release
archive `isarri-bench-inputs.tar.gz` (SHA-256 `b78edf63a92018b7ab52fc57a9948fd2c5cc970eb3b448875fc53722ba5ee1ad`),
which unpacks to the paths in `MANIFEST.tsv`. Each MPSolve-Bench and AND-Bench file holds the
integer coefficients, comma-separated, constant term first; each SMT-Bench file
(`<instance>.apolys`) holds one polynomial per line as `A<TAB><degree><TAB><c0>,<c1>,…`.

## Names, and the drivers

The measurements were taken with the development repository's build of the solver (the LLVM
file with SHA-256 `0561bdc3…`). This repository's `export/isarri.ll` is that file with its
identifiers renamed: after renaming, the 181 functions the file defines have identical
bodies, and on all 326 SMT-Bench instances, all 131 MPSolve-Bench cases and 32 AND-Bench cases
covering every family the two emit windows with identical hashes
(`drivers/scripts__gates__isarri-hash-compare.py`).

`drivers/` holds verbatim copies of the programs that produced the data, each named after its
path in the development repository with `/` replaced by `__`. They use that repository's names
and paths:

| here | in the drivers and in `campaign.log` |
|---|---|
| `IsaRRI` | `powsub_l4` (and the C entry `all_dsc_powsub_main`) |
| `sage` | `sage` on MPSolve-Bench and AND-Bench, `sagesqf` on SMT-Bench |
| `z3` | `z3sqf` on MPSolve-Bench and AND-Bench, plain `z3` on SMT-Bench |
| `pari`, `libpoly` | `parisqf`, `libpolysqf` |
| SMT-Bench | `smt`, and the suite directory `SMT-BENCH` |

The two spellings of the Sage and Z3 arms are the driver's: it labels them `sage`/`z3sqf` in the
MPSolve-Bench and AND-Bench run lines and `sagesqf`/`z3` in the SMT-Bench run lines. A run whose
reported time exceeds the cap is logged twice: first as `OK` by the tool's wrapper, then as
`over cap on solve time (… ms) -> TIMEOUT` by the protocol, which decides. All 12 such runs in the
log are AND-Bench runs above 180 s; on one of them the two lines carry Sage's two labels
(`and16_random_monic_d724_b1024`, 184 980 ms). The scored rows are those of `results/`, where every
arm has the name used in this README.

The main programs are the campaign runner (`scripts__thesis-campaign2-run.sh`), the MPSolve-Bench
and AND-Bench driver (`scripts__final-suite-run.py`), the SMT-Bench driver
(`benchmark_results__smt_bench__smt_bench_phase2.py`), the per-tool harnesses under
`Dsc__export__c_harness__*`, the generators of AND-Bench (`benchmark_results__and_bench__and_gen*`)
and of SMT-Bench (`benchmark_results__smt_bench__smt_bench_extract.py`), and the audit run after the
campaign (`scripts__thesis-campaign-audit.sh`). `…PROVENANCE.txt` records the digests of every
binary and script at the launch. The development repository is not public, so the drivers
document how the data were produced rather than forming a runnable harness on their own.
