# SMT-Bench: what IsaRRI's caller-allocated outputs are worth (2026-09-27)

Thesis: Ch. 7, "Output handling"; App. D, "Output allocation on SMT-Bench".

Question: the competitors allocate their result objects inside their timed calls; IsaRRI writes
into caller-supplied arrays that the campaign harness allocates and initialises before the clock
starts. How much of IsaRRI's SMT-Bench lead is that?

Design: one binary (`suite_alloc.cpp`, the campaign harness
`../drivers/Dsc__export__c_harness__suite_v2_bench.cpp` plus two environment switches, so there is
no cross-binary layout difference), the exported IR measured in the campaign (digest prefix in
`PROVENANCE.txt`), all 326 SMT-Bench instances, 5 repetitions, four arms interleaved per instance
with rotating order, the per-instance minimum, PAR2 at the 1 s cap (no instance is near it).
Freeing stays outside every timer, as for the competitors. The machine was checked quiet before
launch and kept awake throughout. Driver: `alloc_ab.py`; rows: `alloc_ab.tsv`; log: `alloc_ab.log`.

| arm | what is timed | PAR2 ms/instance | vs same-session msolve |
|---|---|---|---|
| A | the call only (the campaign's timed region) | 0.816 | faster on 175/326, paired geomean 0.954 |
| C | minimal per-call allocation (3 mallocs, one `mpz_init` per slot) + call | 0.859 (+5.3%) | faster on 167/326, geomean 0.994 |
| B | the harness's own set-up (4 `vector<mpz_class>`, 4 pointer vectors grown by `push_back`, 2 exponent vectors) + call | 1.114 (+36.5%) | faster on 97/326, geomean 1.189 |
| M | msolve, campaign harness | 1.117 | — |

The campaign recorded IsaRRI 0.824 and msolve 1.122 ms (`../results/smt.tsv`), reproduced here to
within 1%. An earlier 3-arm session (A, B, M) gave 0.823 / 1.129 / 1.121 (`alloc_ab_3arm.*`).

Reading: IsaRRI's first place on SMT-Bench holds for a caller that reuses its output arrays or
allocates them economically per call (+5%); timing the harness's uneconomical set-up brings it
level with msolve.

## Why arm C is the like-for-like comparison with msolve

Inside its timed call, msolve's `real_roots` (commit `1c67c70`, `src/usolve/usolve.c`, through
`bisection_Uspensky`) allocates a flags struct; copies the input coefficients (`malloc` plus
`mpz_init_set` per coefficient); allocates two scratch arrays of `deg` intervals without
initialising them; initialises one GMP integer per root, when the root is stored (`merge_root`);
and returns a final array of exactly as many intervals as roots, into which the stored intervals
are moved (limb pointers transferred), freeing the scratch arrays. Each msolve interval is one GMP
integer and an exponent. Arm C instead initialises 4(d+1) GMP integers whatever the number of
roots, because IsaRRI's contract needs the capacity before the call; so arm C's output allocation
is slightly unfavourable to IsaRRI. With GMP 6.3.0, `mpz_init` allocates no limbs; in both arms the
limbs are allocated when a value is first written, inside the call.
