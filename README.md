# IsaRRI — verified real root isolation in Isabelle-LLVM

IsaRRI (Isabelle Real Root Isolation) isolates the real roots of a squarefree integer polynomial.
The solver is written and proved correct in Isabelle/HOL, refined to imperative code with Sepref,
and exported to LLVM IR through Isabelle-LLVM; coefficients are arbitrary-precision GMP integers.

This repository is the supplement to the MScR thesis *Efficient Verified Real Root Isolation in
Isabelle-LLVM* (Aeacus Sheng, University of Edinburgh, 2026). The thesis explains the algorithms, the proofs and the measurements; this repository
lets a reader check them.

| | where |
|---|---|
| the exported C function `isarri` | `export/isarri.ll` (LLVM IR), `export/isarri.h` (generated header) |
| the caller contract: every obligation, and whether the code checks it | `export/isarri_contract.h` |
| the theorem about the exported function, `isarri_correct` | `thys/proofs/Isarri/Isarri_Correct.thy` |
| `dsc` and `newdsc` proven to be root isolations (`dsc_complete_strong`, `newdsc_isolation`) | `thys/proofs/Lowdeg_Strong/Lowdeg_Isolation_Strong.thy`, `thys/proofs/NewDsc_Strong/NewDsc_Isolation_Strong.thy` |
| the trust audit (fails the build on an oracle in any fact of the development, or on an unexpected axiom) | `thys/proofs/Isarri/Isarri_Audit.thy` |
| an unverified convenience layer: memory set-up, original coordinates, sorted output, thread-safe | `wrapper/isarri_simple.h` |
| the benchmark results, scoring script and correctness checks | `bench/` (`bench/README.md`, `bench/REPRODUCE.md`) |
| build instructions | `BUILD.md` |

## Contents

1. [Quick start](#quick-start)
2. [The guarantee](#the-guarantee)
3. [What is trusted](#what-is-trusted)
4. [Measurements](#measurements)
5. [Repository layout](#repository-layout)
6. [Provenance](#provenance)
7. [Credits](#credits)
8. [Licence](#licence)
9. [Citing](#citing)

## Quick start

**Run the solver** (needs clang and GMP). The example calls the verified function directly:

```bash
make -C example GMP=$(brew --prefix gmp)
./example/isarri_example
```

The example isolates the roots of `x³ − 2x² − 5x + 6 = (x − 1)(x − 3)(x + 2)` and prints

```
positive roots: 2
  (8, 16) / 2^2
  (0, 8) / 2^2
negative roots: 1
  (-8, 0) / 2^0
zero is a root: no
```

that is, the windows (2, 4), (0, 2) and (−8, 0). The windows are not refined: IsaRRI isolates,
and each window together with the polynomial determines its root.

**Or use the convenience layer**, which sets up the memory layout the theorem assumes, maps the
negative half back, adds the root at zero, returns the windows sorted and in lowest terms, and
serialises calls so that several threads may use it. It is ordinary C and **not verified**:

```bash
make -C wrapper test GMP=$(brew --prefix gmp)
```

**Check the proofs** (Isabelle2025-2 and the AFP release for it dated 2026-09-11; see `BUILD.md`):

```bash
isabelle build -d <afp>/thys -d . -j 2 -o threads=5 -v IsaRRI
```

This builds the session chain `IsaRRI_Spec → IsaRRI_LLVM → IsaRRI_Refine → IsaRRI` with
`quick_and_dirty = false`, writes `export/isarri.ll` and runs the oracle audit.

**Check the numbers** (see `bench/REPRODUCE.md`):

```bash
python3 bench/score.py                     # recompute the result tables from the recorded runs
python3 bench/sturm/check_one.py <input>   # check every window IsaRRI returns with a Sturm sequence
bench/example/run.sh                       # time IsaRRI on one benchmark input
```

Rescoring and `run.sh` (which ships its one input) need only this repository. Checking or timing
any other input needs the benchmark inputs, listed with their SHA-256 digests in
`bench/inputs/MANIFEST.tsv` and distributed as the release archive `isarri-bench-inputs.tar.gz`.

## The guarantee

### What the theorem says

`isarri_correct` is a total-correctness Hoare triple on the exported LLVM function itself, proven
in Isabelle/HOL with no `sorry` and no axioms beyond Isabelle/HOL's own: every GMP operation is
introduced by a `specification` command or a locale interpretation, each with a proven witness.
It covers all three paths the function dispatches to:

- degree ≤ 8: closed forms for some quadratics and cubics, and Descartes bisection otherwise;
- power substitution, when `P(x) = Q(x^d)` for an even `d = gcd(h, hcap) ≥ 2`, where `h` is the gcd
  of the exponents with nonzero coefficient;
- otherwise, a Descartes solve with Newton steps that divides out the roots it finds exactly
  (deflation).

When the hypotheses below hold, the call terminates. The positive and negative roots are reported
separately, the negative ones in reflected coordinates (a window `(a, b)` of the negative half
stands for `(−b, −a)`). After the call, for each half:

- **soundness**: every emitted window isolates exactly one real root (`dsc_pair_ok`);
- **strict completeness**: every root of that sign lies in the open interior of some window or is
  some point window;
- **root uniqueness**: no root lies in two windows;
- hence **the count cells equal the number of distinct positive and negative real roots**, and the
  first `min(count, out_cap)` slots of the output arrays hold those windows;
- `out_xs0` is 1 exactly when the constant coefficient is 0.

### Hypotheses

**None of these is checked at run time.** They are hypotheses of the theorem and compile to no
code; for an input that violates them the theorem says nothing, including about termination. The
code only bounds its stores by the capacity value: it never stores more than `out_cap` windows,
whatever the number of roots, but it cannot check that the arrays have that size.
`export/isarri_contract.h` lists every obligation.

1. **`dsc_isolate_all_split_defl_pre` of the input.** It contains squarefreeness (the standard
   precondition of subdivision isolators; pass the squarefree part `P/gcd(P, P')`), a nonzero
   leading coefficient, at least two coefficients, coefficients of at most `2^63 − len − 2` bits,
   and word bounds that are linear in the depth of the search: `k·len < 2^63` and
   `k + μ + 3 < 2^63` for the root-bound exponent `k` of each half, and `(258μ' + 1)·len < 2^40`
   for the depth measure μ' of the normalised search box (the predicate's other length and depth
   clauses follow from this one). Since μ' grows with the logarithm of the inverse root
   separation, the last bound excludes only separations below about `2^(−2^40/(258·len))`.
2. **`hcap < 2^63`.**
3. **`dsc_isolate_all_split_defl_pre` of the reduced polynomial** `Q = pow_sub_extract d xs` (the
   coefficients `c_0, c_d, c_2d, …` of the input), only when the substitution is attempted: `len ≥ 10`,
   `len ≥ nfloor`, and `d = gcd(h, hcap)` even and at least 2. With `hcap = 1` it never applies.
4. **A memory model for the caller's buffers** (`thys/proofs/Isarri/Isarri_Memory.thy`): the
   coefficient buffer has Isabelle-LLVM's array-list layout, `len` pointers each to its own
   initialised GMP integer; each output `mpz_t` array holds `out_cap` initialised objects with
   pairwise disjoint storage (the values they hold may coincide); every output cell is disjoint from
   every other and from the input.

Memory exhaustion, which the theorem's model does not have, aborts the process rather than
producing an answer, as does an integer exceeding GMP's own size limit. The output capacity bounds
only what is stored, not the memory the solver uses. `out_substituted` (called `out_ok` in the
theory and the IR) only records which path produced the output; the theorem says nothing about it.

**Not thread-safe.** The runtime allocator keeps unlocked free lists, so no two calls may run at
once, even on disjoint buffers; `wrapper/isarri_simple.c` serialises its calls with a mutex.

**Any tuning-parameter value is safe.** Before mapping windows back through the substitution, a
run-time guard requires `h < 1024`, `dlt < 1024`, a reduced length below 2^20 and every reduced
window's exponent below 2^20, and otherwise hands the input to the deflating solver.

### Scope

For each half, the theorem is the definition of a root isolation (every window isolates one root,
every root lies in a window, no root lies in two), with strict completeness and exact counts, and
it is stated about the exported function itself. Four remarks delimit it.

1. **The output is specified by its properties, not by a reference algorithm.** Deflation, power
   substitution and the closed forms return other windows than a plain Descartes solve, so the
   isolation property is proven directly, not through a multiset equality with `dsc_int`.
2. **Two windows may share a root-free gap** on the substituting path; no root lies in two windows.
3. **The memory model is a hypothesis**, and the theorem does not specify the informational output
   `out_substituted`.
4. **Hypothesis 3 does not follow from hypothesis 1 in general.** Squarefreeness, the leading
   coefficient and the length carry over from the input to `Q`, but the depth bounds need `Q`'s own
   root separation, which can be smaller because `x ↦ x^d` compresses roots near zero
   (`P(x) = (2^80 x² − 1)(2^80 x² − 4) = Q(x²)`). With bounds linear in the depth this matters only
   at very small separations, and the hypothesis holds on the reduced polynomial of every benchmark
   input where it was decided.

### Non-vacuity, and which inputs satisfy the hypotheses

A precondition nothing satisfies makes a theorem vacuously true. The precondition bundles,
including the one `isarri_correct` takes, are shown satisfiable by certified witnesses in
`thys/proofs/Vacuity_Probe/Split_Pre_Witness.thy` (`dsc_isolate_all_split_pre_satisfiable`,
`dsc_isolate_all_split_hybrid_pre_satisfiable`, `dsc_isolate_all_split_defl_pre_satisfiable`) and,
for the substituting path, `pow_sub_entry_correct_not_vacuous` (`P = 1 + x²` with `Q = 1 + x` at
`hcap = 32`). The witnesses have degree 1 or 2: they show the bundles are consistent, not that a
large polynomial satisfies them, nor that the exported dispatch takes the substituting path.

Which benchmark inputs satisfy the hypotheses is established outside the proof, in exact
arithmetic by unverified scripts (thesis, Chapter 7, "Which polynomial hypotheses were
established"): all 326 SMT-Bench and 131 MPSolve-Bench inputs, and 248 of the 295 AND-Bench inputs,
including every input on which IsaRRI returned an answer; the other 47 are undecided.

## What is trusted

**Checked proofs.** Every session is built with `quick_and_dirty = false`, under which Isabelle
rejects `sorry`. `thys/proofs/Isarri/Isarri_Audit.thy` imports every theory of the four sessions and
fails the build unless two checks pass:

- **no oracle**: none of the 11 538 facts proved in the supplement's theories depends on any oracle,
  whether `skip_proof` (from `sorry`), the code generator's evaluation oracle (from `eval`) or another,
  with one exception that is not a proof of this development: for the record type that models a GMP
  integer, Isabelle's Quickcheck (as for every datatype and record) states its test-data generator
  equations with `skip_proof`, as code equations for testing; the audit names that fact and checks
  that no other fact depends on it. The check is first shown to detect a planted `skip_proof` theorem;
- **no unexpected axiom**: every axiom of the theory, including those of Isabelle/HOL, the AFP and the
  vendored Isabelle-LLVM, is a registered definition (10 135 of the 10 462), a type-class arity or
  `typedef` fact, or one of 22 named axioms of Pure and HOL themselves.

Separately, neither `thys/` nor `vendor/` contains an `axiomatization` command
(`grep -rn '^\s*axiomatization' thys vendor` prints nothing).

**Upstream proof gaps.** The vendored Isabelle-LLVM tree contains two upstream theories with
`sorry` (`Similar.thy`, `IEEE_Fp_Add.thy`); no session built here loads them, and the audit
establishes that the headline theorems do not depend on them. Six upstream theories that are loaded
(`Frame_Infer`, `LLVM_Integer`, `LLVM_Shallow_RS`, `Monadify`, `NEMonad` and `Proto_IICF_EOArray`,
the last of which `Dsc_Impl_Setup` imports directly) contain `oops`, an abandoned proof attempt that
registers no theorem.

**Trusted components.** Beyond the Isabelle kernel, the correctness of the running code rests on:

- Isabelle-LLVM's embedding of LLVM and its printer of `.ll` text;
- GMP meeting the specification of each of the 20 functions the code calls;
- the allocator in `runtime/`, which is not verified and not thread-safe (its global free lists
  have no locks, so concurrent calls are unsupported);
- `clang`, the C library and the operating system;
- the caller meeting the obligations above.

## Measurements

The thesis compares IsaRRI with eight unverified isolators (msolve, ANewDsc, Sage, PARI, Z3, CGAL,
libpoly and RisolateR) on three suites derived from third-party sources, every arm on the same task:
isolating an already squarefree polynomial without refining the windows. PAR2 at each suite's
scoring cap, all cases counted; the full tables and the per-case ratios are in Chapter 7.
`bench/score.py` recomputes the campaign's rows for IsaRRI and the seven competitors timed in it,
including ANewDsc's unranked reference configuration; RisolateR was timed in separate sessions, and its records are not in this repository. The thesis
also reports a held-out sample of SMT-LIB instances and the Ccluster suite, whose records are not
in this repository either.

| suite | cases | cap | IsaRRI | best competitor | IsaRRI's rank of 9 |
|---|---|---|---|---|---|
| SMT-Bench | 326 instances | 1 s | 0.824 ms | msolve 1.122 ms | 1 |
| MPSolve-Bench | 131 polynomials | 60 s | 0.268 s | msolve 0.745 s | 1 |
| AND-Bench | 295 polynomials | 150 s | 95.9 s | RisolateR 51.5 s, then ANewDsc 54.6 s | 3 |

IsaRRI has the lowest PAR2 among the exact-arithmetic isolators on all three suites. On
MPSolve-Bench, msolve is faster on 98 of the 131 polynomials, and on AND-Bench the paired geometric
mean of IsaRRI's time over ANewDsc's is 1.84. The SMT-Bench times assume, as the interface does,
that the caller supplies the output arrays (`bench/alloc_ab/`).

**Correctness of the answers.** Every count IsaRRI returned agrees with every available reference.
Root counts are settled by genuine Sturm sequences in exact integer arithmetic
(`bench/sturm/`), never by agreement among tools. Every window IsaRRI returned was checked with a
Sturm sequence on all SMT-Bench and MPSolve-Bench inputs and on 161 of its 209 AND-Bench answers;
none failed, and the other 48 are recorded as unchecked because the Sturm sequence exceeded its
900 s budget. The records are in `bench/results/`.

## Repository layout

| path | contents |
|---|---|
| `thys/spec` | abstract algorithms (Descartes and NewDsc recursions, deflation, closed forms, power substitution) and their correctness |
| `thys/framework` | GMP bindings and Sepref additions, adapted from the Eberl–Lammich artefact (see Credits) |
| `thys/impl` | the monadic programs and their Sepref implementations |
| `thys/refine` | refinement from implementation to specification, per solver |
| `thys/proofs` | loop refinements, the isolation theorems, the theorem about the exported function, the witnesses and the audit |
| `thys/export/Public_Export.thy` | the `export_llvm` command that writes `export/isarri.ll` |
| `vendor/isabelle_llvm` | Isabelle-LLVM, with its licence, as distributed with the Eberl–Lammich artefact |
| `export` | `isarri.ll` and `isarri.h` (generated by the build), `isarri_contract.h` (the caller contract) |
| `runtime` | the C support library the exported IR calls for allocation |
| `example` | a minimal C caller of the verified function |
| `wrapper` | an unverified convenience layer over it, with its tests |
| `bench/results` | the recorded runs of every arm, the Sturm counts and window checks, the settled AND-Bench disputes |
| `bench/inputs` | the input manifest (SHA-256 of every input) and the case tables |
| `bench/sturm` | the Sturm-sequence checker |
| `bench/example` | timing IsaRRI on one input, and one complete comparison against PARI |
| `bench/alloc_ab` | the SMT-Bench output-allocation measurement |
| `bench/drivers` | verbatim copies of the drivers, harnesses and competitor patches that produced the data |
| `NAMES.tsv` | identifier map from the development repository to this one |

The theories hold about 126 200 lines in 113 files: 14 100 in `spec`, 6 100 in `framework`,
41 500 in `impl`, 15 600 in `refine`, 48 700 in `proofs` and 200 in `export`.

## Provenance

This repository is generated from the development repository by a scripted transform: renaming,
layout and a comment cleanup, with no change to any statement or proof. The exported IR is compared
against the IR that was benchmarked: after renaming, the 181 functions the file defines (the 179 reachable from
`isarri` and the two GMP helpers) have identical bodies, and on 489 benchmark inputs (all 326 of SMT-Bench, all 131 of MPSolve-Bench,
and 32 AND-Bench cases covering every family) the emitted windows hash identically. `NAMES.tsv`
gives the old name of every renamed identifier. The solver the thesis calls the *hybrid* solver is
the development's *adaptive* solver; the transform renames `adaptive` to `hybrid` inside every
identifier, file name and comment. The drivers in `bench/drivers/` keep the development names and
paths, and `bench/README.md` maps them.

## Credits

The Isabelle-LLVM setup, the GMP bindings and the runtime library were copied from the artefact of
Manuel Eberl and Peter Lammich's verified implementation of Harvey's algorithm for Bernoulli
numbers, and extended here:

- M. Eberl and P. Lammich. *Verifying an Efficient Algorithm for Computing Bernoulli Numbers.*
  ITP 2025, LIPIcs 352, 35:1–35:19. doi:10.4230/LIPIcs.ITP.2025.35
- M. Eberl and P. Lammich. *Artifact accompanying ITP 2025 paper: Verifying an Efficient Algorithm
  for Computing Bernoulli Numbers.* Zenodo, 2025, v1. doi:10.5281/zenodo.15749805
  (Creative Commons Attribution 4.0 International)
- D. Harvey. *A multimodular algorithm for computing Bernoulli numbers.* Mathematics of Computation
  79(272):2361–2370, 2010. doi:10.1090/S0025-5718-2010-02367-1

`thys/framework/Sepref_Add/` is a modified copy of the artefact's `thys/Sepref_Add/`: we added GMP
operations and lemmas, gave the bit-length query (`mpz_sizeinbase`, which the artefact binds with
the contract `1 ≤ r`) a base-2 contract with its own witness, and renamed identifiers
(`NAMES.tsv`). `vendor/isabelle_llvm/` and `runtime/lib_isabelle_llvm.c` come from the
same artefact; the runtime's allocator is modified.

## Licence

The files of this repository are released under the MIT licence (`LICENSE`), with these
exceptions:

- `vendor/isabelle_llvm/` and `runtime/lib_isabelle_llvm.c` (Isabelle-LLVM and its support library,
  with a modified allocator) remain under Isabelle-LLVM's BSD-style licence
  (`vendor/isabelle_llvm/LICENSE`);
- the material in `thys/framework/` adapted from the Eberl–Lammich artefact remains under the
  Creative Commons Attribution 4.0 International licence.

## Citing

Aeacus Sheng. *Efficient Verified Real Root Isolation in Isabelle-LLVM.* MScR thesis, University
of Edinburgh, 2026.

The verification of the abstract Descartes algorithms is described in: Aeacus Sheng, Wenda Li and
Paul B. Jackson. *Faster Verified Real Root Isolation with Descartes' Rule of Signs (Short Paper).*
ITP 2026, LIPIcs 382, article 32.
