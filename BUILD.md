# Building IsaRRI

## Requirements

| component | version used | notes |
|---|---|---|
| Isabelle | Isabelle2025-2 | |
| AFP | release for Isabelle2025-2 dated 2026-09-11 (`afp-current.tar.gz`, sha256 `2b18fad0516067983b9155d95d831b3a2af088cb58a17ac8eb8bb22dd4e89f7f`) | a fresh AFP checkout, not a development clone |
| GMP | 6.3.0 | headers and library, for the C side only |
| C compiler | Apple clang 21.0.0 | any clang that accepts LLVM IR on its command line |

The proofs were last checked on 2 October 2026, on an Apple M4 with 16 GB of memory, macOS
26.5.2.

## Checking the proofs

```bash
isabelle build -d <afp>/thys -d . -j 2 -o threads=5 -v IsaRRI
```

The session chain is `IsaRRI_Spec → IsaRRI_LLVM → IsaRRI_Refine → IsaRRI`, all with
`quick_and_dirty = false`. On the machine above, in the three most recent builds, the four
sessions took 1–3, 12–23, 8–14 and 2–3 minutes (elapsed, 5 threads), not counting the HOL and
AFP sessions they build on. Building the `IsaRRI` session writes `export/isarri.ll` and
`export/isarri.h` and runs the trust audit
(`thys/proofs/Isarri/Isarri_Audit.thy`); the build fails if any fact proved in the supplement
depends on an oracle (apart from one Quickcheck generator equation that no other fact uses; see the
README), or if the theory has an axiom that is neither a definition, a type-class or `typedef` fact,
nor one of Pure's and HOL's own.

To keep Isabelle's heaps for this repository apart from other work, point `USER_HOME` at a
separate directory for the build.

## Building and running the example

```bash
make -C example GMP=$(brew --prefix gmp)
```

```bash
./example/isarri_example
```

The example links `export/isarri.ll` with `runtime/lib_isabelle_llvm.c` and GMP, isolates the
roots of `x³ − 2x² − 5x + 6 = (x − 1)(x − 3)(x + 2)`, and prints the windows with the negative
half mapped back from reflected coordinates.

## Building and testing the convenience layer

```bash
make -C wrapper test GMP=$(brew --prefix gmp)
```

`wrapper/isarri_simple.{h,c}` is an unverified layer over the verified function (see its header).
The test checks known roots of five polynomials covering the three paths, the input checks, and
800 concurrent calls from eight threads against a single-threaded reference.
