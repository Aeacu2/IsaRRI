theory Newton_Solver
  imports Bisection_Solver Newton_Spec Window_Mono Newton Bisection
begin

text \<open>The carried Newton solver: the monadic layer.

  Main definition: \<open>newton_main_list\<close> and its Sepref implementation, a sibling of the bisection solver
  (\<open>Bisection\<close>) that refines @{const newdsc_pol_int}\<open> pol_final\<close> as an exact multiset: carried
  representation, Ruffini/ET-Horner counting, dyadic endpoints, in-place kernels and the truncated
  count, plus block and Newton window acceleration on cluster signals.

  Three facts the design rests on: windows are dyadic (\<open>newton_window_child\<close>); the Newton probe is \<open>O(deg)\<close>
  coefficient reads on the node polynomial (\<open>Q(0) = q\<^sub>0\<close>, \<open>Q'(0) = q\<^sub>1\<close>, \<open>Q(1) = \<Sigma>q\<^sub>i\<close>, \<open>Q'(1) = \<Sigma>i\<cdot>q\<^sub>i\<close>); and the
  window-child transform is the in-place op \<open>carried_init_inplace_monadic\<close> (\<open>Carried_Kernel\<close>), which takes the
  grid denominator as the word exponent \<open>j = 2^e + 2\<close>, borrows the node polynomial (so the probe does not
  modify it), and whose \<open>_correct\<close> targets \<open>carried_init_same_den\<close>. The exact verification count is
  @{const poly_reverse_monadic} followed by @{const descartes_finish_monadic}.

  The after-pop dispatch consumes only the classification trichotomy; the node dispatch uses the truncated
  \<open>carried_descartes_count_trunc_monadic\<close> (\<open>Count\<close>), whose classification statement is that of the exact op, so
  the solver uses truncation at every node where no window is attempted.

  The scheduling policy \<open>pol_final\<close> is sound, complete and terminating (\<open>newdsc_pol_pol_final_sound\<close>/\<open>_complete\<close>/
  \<open>_dom\<close>, instances of the theorems quantified over every policy).\<close>

section \<open>The concrete scheduling policy (every tuning knob lives HERE — D-a)\<close>

text \<open>Tuning changes ONLY these definitions (+ the trivial real-twin relation);
  no proof re-opens (the abstract theorems quantify over \<open>pol\<close>). \<open>e_cap\<close> and the \<open>dk\<close>
  headroom are word-safety bounds.\<close>

text \<open>\<^bold>\<open>The proper-split delay\<close> (Kobel, Rouillier and Sagraloff, \<section>3.1). A bisection is a proper split
  when both children keep a nonzero sign-variation count; by Obreshkoff's one-circle theorem that refutes
  the single-cluster hypothesis at the parent, so Newton machinery should not be attempted nearby. A cluster
  shows the opposite: a long chain of nodes whose variations all follow one child. \<open>s\<close> (threaded on the
  worklist) counts consecutive bisections since the last proper split.

  \<^bold>\<open>Why not a depth threshold.\<close> Depth cannot separate ``deep because there is a cluster'' from ``deep because
  the search box is large relative to the root separation''; the proper-split signal separates them.
  \<open>newton_pol_emin\<close> keeps Newton active during an already converging quadratic phase (accepts push \<open>e + 1\<close>).

  The six derived word-bound lemmas below depend only on \<open>e \<le> ecap\<close>, \<open>dk \<le> kcap\<close> and the degree bounds, never
  on \<open>emin\<close>, \<open>s\<close> or the delay, so the gate signal affects only when the gate opens.\<close>
text \<open>\<^bold>\<open>The \<open>\<sigma>\<close> gate.\<close> The gate opens on \<open>\<sigma> \<ge> newton_pol_sig_thresh\<close>, where \<open>\<sigma>\<close> (the \<open>ss\<close> column) is the
  run length of count stagnation: consecutive bisections in which all sign-variation mass followed the
  current path, with forgetting on contrary evidence (\<open>newton_split_run_len\<close>: \<open>+1\<close> on stagnation,
  \<open>\<sigma> - \<sigma> div 11\<close> on a proper split or midpoint root; a proper split requires both children nonzero, and in the
  hybrid solver also decisive, \<open>cl, cr \<in> {1,2,3}\<close>, since only there can a classification return the ambiguous
  sentinel \<open>4\<close>: \<open>hybrid_split_run_len\<close>). \<open>\<sigma> \<ge> s\<close> means at least two roots confined in a box shrunk by \<open>2\<^sup>-\<^sup>\<sigma>\<close>,
  i.e. a cluster of depth \<open>\<ge> s\<close>. The signal is scale-free: a spread proper-splits at every level, so
  \<open>\<sigma> \<rightarrow> \<beta>\<^sup>n\<sigma> \<rightarrow> 0\<close> for any \<open>\<beta> < 1\<close>. A fixed depth threshold, by contrast, admits any non-cluster deeper than the
  threshold, where the window's fixed cost is pure loss. \<open>dk\<close> remains only as the \<open>kcap\<close> word bound. The
  threshold \<open>newton_pol_sig_thresh\<close> is a performance parameter; the theorems quantified over every policy hold
  for any value.\<close>



text \<open>Degree / dyadic-exponent caps. The gate must be EVALUATED at run time (it is what
  supplies \<open>newton_try_window_monadic\<close>'s word-headroom preconditions), and a machine word
  cannot hold \<open>max_snat LENGTH(gmp_poly_len)\<close> = \<open>2\<^sup>6\<^sup>3\<close>, so the two headroom conjuncts are
  stated as comparisons against these numerals and the \<open>max_snat\<close> facts DERIVED below
  (\<open>newton_pol_gate_wcap\<close> / \<open>_kjump\<close> / \<open>_mul\<close>). \<open>2\<^sup>4\<^sup>0\<close> is far beyond any reachable degree or
  bisection depth, and capping is free: \<open>newdsc_pol\<close> is sound/complete/terminating for
  EVERY policy, so a gate that closes merely forfeits a window and bisects instead.\<close>

text \<open>The v-FREE pre-gate (the impl computes only the 0/1/\<ge>2 classify
  when this is \<open>False\<close>; the exact \<open>v\<close> is computed only after it fires). \<open>deg\<close> is
  the solve-constant polynomial degree; the last two conjuncts are the word
  headroom for the window k-jump AND for \<open>carried_init_inplace_monadic\<close>'s
  \<open>j * (len - 1) < max_snat\<close> precondition.\<close>

text \<open>The window width \<open>2\<^sup>e + 2\<close> is bounded by \<open>258\<close> once the gate's \<open>e \<le> newton_pol_ecap\<close>
  conjunct holds — the single fact every word bound below is derived from.\<close>
lemma newton_pol_ecap_width:
  assumes "e \<le> newton_pol_ecap"
  shows "(2::nat) ^ e + 2 \<le> 258"
proof -
  have "(2::nat) ^ e \<le> 2 ^ 8"
    using assms unfolding newton_pol_ecap_def by (rule power_increasing) simp
  thus ?thesis by simp
qed

text \<open>The four word-headroom facts the gate IMPLIES --- consequences of the gate predicate
  rather than separate hypotheses: the exponent fits a shift amount, the window width and the
  window k-jump fit an \<open>snat\<close>, and so does the in-place carried-init product
  \<open>(2\<^sup>e + 2) \<cdot> deg\<close>.\<close>
lemma newton_pol_gate_eL: "newton_pol_gate deg e dk s \<Longrightarrow> e < LENGTH(gmp_poly_len)"
  by (simp add: newton_pol_gate_def newton_pol_ecap_def)

lemma newton_pol_gate_wcap:
  "newton_pol_gate deg e dk s \<Longrightarrow> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
  using newton_pol_ecap_width[of e]
  by (simp add: newton_pol_gate_def max_snat_def)

lemma newton_pol_gate_kjump:
  "newton_pol_gate deg e dk s \<Longrightarrow> dk + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
  using newton_pol_ecap_width[of e]
  by (simp add: newton_pol_gate_def newton_pol_kcap_def max_snat_def)

text \<open>The degree conjuncts, in the shape the Newton probe ops want their polynomial LENGTH
  (\<open>deg = length Q - 1\<close>): at least two coefficients (\<open>newton_lambda_loc0_monadic\<close>) and enough
  headroom for \<open>newton_lambda_loc1_monadic\<close>'s \<open>length + 2\<close>.\<close>
lemma newton_pol_gate_len1: "newton_pol_gate deg e dk s \<Longrightarrow> 1 \<le> deg"
  by (simp add: newton_pol_gate_def)

lemma newton_pol_gate_len2:
  "newton_pol_gate deg e dk s \<Longrightarrow> deg + 3 < max_snat LENGTH(gmp_poly_len)"
  by (simp add: newton_pol_gate_def newton_pol_dcap_def max_snat_def)

text \<open>NUMERAL-form companions of the two facts above. A refinement proof's \<open>clarsimp\<close> evaluates
  \<open>max_snat LENGTH(64)\<close> to its numeral and distributes \<open>(2\<^sup>e + 2) \<cdot> deg\<close>, after which the symbolic
  lemmas no longer match; these two feed \<open>linarith\<close> the only non-linear steps it cannot take.\<close>
lemma newton_pol_ecap_pow: "e \<le> newton_pol_ecap \<Longrightarrow> (2::nat) ^ e \<le> 256"
  using newton_pol_ecap_width[of e] by simp

lemma newton_pol_dcap_mul:
  assumes "e \<le> newton_pol_ecap" and "deg \<le> newton_pol_dcap"
  shows "(2::nat) ^ e * deg \<le> 281474976710656"
proof -
  have "(2::nat) ^ e * deg \<le> 256 * newton_pol_dcap"
    by (rule mult_le_mono[OF newton_pol_ecap_pow[OF assms(1)] assms(2)])
  thus ?thesis by (simp add: newton_pol_dcap_def)
qed

lemma newton_pol_gate_mul:
  "newton_pol_gate deg e dk s \<Longrightarrow> (2 ^ e + 2) * deg < max_snat LENGTH(gmp_poly_len)"
proof -
  assume g: "newton_pol_gate deg e dk s"
  have "(2 ^ e + 2) * deg \<le> 258 * newton_pol_dcap"
  proof (rule mult_le_mono)
    show "(2::nat) ^ e + 2 \<le> 258"
      using g by (intro newton_pol_ecap_width) (simp add: newton_pol_gate_def)
    show "deg \<le> newton_pol_dcap" using g by (simp add: newton_pol_gate_def)
  qed
  thus ?thesis by (simp add: newton_pol_dcap_def max_snat_def)
qed

text \<open>The policy pair is \<open>(blocks gate, Newton gate)\<close>: \<open>newdsc_pol\<close> passes \<open>fst\<close> to \<open>try_blocks_g\<close> and \<open>snd\<close> to
  \<open>try_newton_g\<close>. Both components are the \<open>\<sigma>\<close> gate.

  \<^bold>\<open>One policy serves both routes.\<close> The plain Newton route reads both components (probes and blocks). The
  bail and hybrid route reads only \<open>snd\<close>, because \<open>try_window_bail\<close> has no blocks parameter, so no second
  policy constant or type is needed, and \<open>newton_pol_real\<close> is shared, so the hybrid capstone's \<open>\<exists>pol\<close> witness
  has the same type.\<close>
definition pol_final :: newton_pol where
  "pol_final deg a b e dk sv =
     (newton_pol_gate deg e dk (fst sv),
      newton_pol_gate deg e dk (fst sv))"

definition pol_final_real :: newton_pol_real where
  "pol_final_real deg a b e dk sv =
     (newton_pol_gate deg e dk (fst sv),
      newton_pol_gate deg e dk (fst sv))"

text \<open>The pointwise relation for the \<open>polrel\<close> hypothesis of @{thm [source] newdsc_pol_int_eq_newdsc_pol}: the
  policy consumes the node view \<open>(s, v)\<close> (\<open>s\<close> the proper-split run length, \<open>v\<close> the count). By definitional
  simp (\<open>of_nat_le_iff\<close>).\<close>
lemma pol_final_real_rel:
  "pol_final_real deg (of_rat a) (of_rat b) e dk (s, int v) = pol_final deg a b e dk (s, v)"
  unfolding pol_final_real_def pol_final_def by simp

section \<open>Exact (uncapped) Descartes count — the window-verification kernel\<close>

text \<open>The accept tests need \<open>count = v\<close> EXACTLY (v can exceed 2), so the capped
  ET kernel does not apply; the baseline kernel does — its contract is
  already exact equality. Sibling of \<open>carried_descartes_count_monadic\<close>
  (\<open>Carried_Kernel.thy\<close>) with @{const descartes_finish_monadic}
  (\<open>Fast_Descartes.thy\<close>, frees the reversed copy) in place of the ET kernel.\<close>


section \<open>The local Newton probe (O(deg), no rational hom-eval)\<close>

text \<open>Abstract twins first (plain functions on the int-list level; the
  correspondence in \<open>Bail_Loop_Refine.thy\<close> ties them to @{const newton_at}
  and @{const snap_window_rat} through the node's affine map).\<close>


text \<open>\<open>(ok, num, den)\<close> with \<open>\<lambda>_loc = num/den\<close>; \<open>ok = False\<close> iff the derivative
  vanishes at the probe point. Left probe: \<open>\<lambda>_loc = -v\<cdot>Q(0)/Q'(0)\<close>; right probe:
  \<open>\<lambda>_loc = 1 - v\<cdot>Q(1)/Q'(1) = (Q'(1) - v\<cdot>Q(1))/Q'(1)\<close>.\<close>



text \<open>The snap grid position (clipped): \<open>kn = nat (max 2 (min (s - 2) \<lfloor>s\<cdot>num/den\<rfloor>))\<close>
  with \<open>s = 2^(2^e + 2)\<close>. HOL \<open>div\<close> IS floor division for both operand signs =
  GMP \<open>mpz_fdiv_q\<close> — no rounding fixups anywhere.\<close>


text \<open>Monadic forms. The coefficient reads are BORROWED slot reads
  (as \<open>poly_shift_coeff_impl\<close>, \<open>Dyadic_Interval.thy\<close>); the plain
  int arithmetic synthesizes to mpz scalar calls; the eval1 accumulators are
  fresh owned mpz's, freed by the callers of the probe results.\<close>

text \<open>\<open>mpz_of_snat_monadic\<close> (an snat as an owned mpz) is defined in \<open>Bisection\<close> and inherited here.\<close>

text \<open>\<open>poly_eval1_pair\<close>: a probe with no clone of the polynomial. The two accumulators are standalone owned
  scalars (\<open>s\<close>, \<open>ds\<close>), and \<open>xs\<close> is read by borrow via @{const poly_hom_eval_addmul_monadic}
  (\<open>acc := acc + xs!idx*dpow\<close>, borrowed polynomial, borrowed \<open>dpow\<close>). The index \<open>i\<close> is shadowed by an owned mpz
  \<open>ic\<close> incremented in place with @{const mpz_add_monadic} (\<open>mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k\<close>, reusing \<open>ic\<close>'s storage), so
  the probe performs \<open>O(1)\<close> allocations. Correctness is \<open>poly_eval1_pair_monadic_correct\<close> below; it is used by
  \<open>newton_lambda_loc1_monadic\<close>.\<close>


text \<open>The borrowed two-coefficient probe: the sign test on \<open>xs!1\<close> uses @{const poly_coeff_sgn_monadic} with no
  copy, so the \<open>sg=0\<close> branch (which does not need \<open>xs!1\<close>'s value) allocates nothing for it; \<open>xs!1\<close> is copied
  only in the \<open>else\<close> branch, where it is returned as \<open>ds\<close>. The accept branch computes \<open>v\<cdot>xs!0\<close> with the
  borrowing @{const poly_hom_eval_addmul_monadic} (seeded at \<open>0\<close>: \<open>0 + xs!0*vi = xs!0*vi\<close>) rather than copying
  \<open>xs!0\<close>.\<close>

text \<open>Same ownership idiom as @{const newton_lambda_loc0_monadic}, mirrored: @{const mpz_sgn_mop}
  borrows \<open>ds\<close> for the test; the accept branch computes \<open>ds - v\<cdot>s\<close> via @{const mpz_mul.amop_r1}
  (consumes a fresh \<open>vi\<close>, borrows \<open>s\<close>) + @{const mpz_sub.amop_r1} (consumes \<open>ds\<close>, borrows the
  product).\<close>

text \<open>Owned-mpz compare / min / max. \<open>newton_window_cmp\<close> is non-destructive (both inputs
  BORROWED/KEPT); max/min consume the loser. The compare delegates to
  @{const mpz_cmp_sgn_monadic} (native \<open>__gmpz_cmp\<close>, \<open>Scalar.thy\<close>), so it needs no scratch
  value.\<close>






section \<open>Window child + guarded window try (reusing the in-place init op)\<close>

text \<open>The window child for grid cells \<open>m..m+4\<close> of \<open>s = 4 * N_of e = 2^j\<close>,
  \<open>j = 2^e + 2\<close>, IS \<open>carried_init_inplace_monadic (m) j (m + 4)\<close> applied
  to the NODE poly — one existing proven op (\<open>Carried_Kernel.thy\<close>, in-place: 1 allocation,
  exponent-arg so \<open>s\<close> is never materialized as an mpz, BORROWS \<open>xs\<close>), covering
  blocks (\<open>m = 0\<close>, \<open>m = s - 4\<close>) and Newton snaps (\<open>m = kn - 2\<close>) uniformly.
  The candidate is verified with the EXACT kernel and freed on reject, so
  the parent \<open>Q\<close> and the node interval are untouched until an
  accept commits. The \<open>j * (len - 1)\<close> word-headroom ASSERT is discharged by the
  caller's \<open>newton_pol_gate\<close> (which carries exactly this conjunct).\<close>

text \<open>The capped count kernel, used by \<open>newton_try_window_monadic\<close> below; it uses only \<open>Poly_Ops\<close>. The window
  try uses cap \<open>max 2 (v+1)\<close> and match \<open>r = v\<close>, which is correct from the cap contract alone.\<close>

section \<open>Cap-parameterized cond mop\<close>


section \<open>Cap-parameterized body mop\<close>


section \<open>The cap-parameterized outer kernel\<close>




(*FASTLOOP_FREEZE_ABOVE*)

section \<open>The extended loop state (\<open>es\<close> alongside \<open>qtodo\<close>)\<close>

text \<open>\<open>es\<close> is a PLAIN \<open>nat list\<close> (no GMP ownership,
  unlike \<open>qtodo\<close>) tracking the NewDsc scheduling exponent \<open>e\<close> per node — pushed/
  popped in lockstep with \<open>qtodo\<close>, reusing the SAME primitives already used for
  \<open>todo\<close>'s own \<open>ks\<close> (dyadic exponent) column: @{const dyadic_exp_push2_monadic}
  (push the SAME value twice — exactly the bisection case, both children get
  \<open>e' = max 1 (e-1)\<close>) and @{const dyadic_exp_pop_last_monadic}.\<close>

type_synonym newton_loop_state =
  "(gmp_dyadic_interval_vec \<times> gmp_poly list \<times> nat list \<times> nat list \<times> nat list) \<times>
    gmp_dyadic_interval_vec"

text \<open>The worklist columns: dyadic boxes, carried node polys, NewDsc scheduling exponents \<open>es\<close>,
  \<open>ss\<close> — the proper-split run lengths (Kobel, Rouillier and Sagraloff, \<section>3.1) — and \<open>cs\<close> — each
  node's CLASSIFY (the truncated count's 0/1/\<ge>2 bucket), computed ONCE at the parent's push and
  cached so the pop never re-counts: total count work is exactly the bisection solver's, and the
  parent gets both children's classes for free to decide the proper-split flag. \<open>ss\<close>/\<open>cs\<close>
  mirror \<open>es\<close> exactly: same \<open>nat list\<close> assertion, same push/pop primitives.\<close>
abbreviation newton_triple_assn where
"newton_triple_assn \<equiv>
  gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_poly_vec_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn
    \<times>\<^sub>a gmp_dyadic_exp_list_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn"

abbreviation newton_loop_state_assn where
"newton_loop_state_assn \<equiv>
  newton_triple_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn"

definition newton_loop_state_invar ::
  "newton_loop_state \<Rightarrow> bool" where
"newton_loop_state_invar st \<equiv>
  (let ((todo, qtodo, es, ss, cs), acc) = st in
    dyadic_interval_vec_invar todo \<and>
    dyadic_interval_vec_invar acc \<and>
    (case todo of (lns, _, _) \<Rightarrow> length qtodo = length lns \<and> length es = length lns
                                \<and> length ss = length lns \<and> length cs = length lns))"

definition newton_loop_cond ::
  "newton_loop_state \<Rightarrow> bool" where
"newton_loop_cond st \<equiv>
  (let ((todo, _, _, _, _), _) = st in
    let (lns, _, _) = todo in lns \<noteq> [])"

sepref_register "PR_CONST newton_loop_cond"
  :: "newton_loop_state \<Rightarrow> bool"

text \<open>Clone of the bisection loop's condition mop (\<open>Bisection.thy\<close>): the abstract test is a pure
  \<open>lns \<noteq> []\<close>, but \<open>gmp_dyadic_interval_vec_assn\<close> is heap-owning, so it must be read through the
  registered length op.\<close>
definition newton_loop_cond_mop_monadic ::
  "newton_loop_state \<Rightarrow> bool nres" where
"newton_loop_cond_mop_monadic st \<equiv>
  (case st of ((todo, qtodo, es, ss, cs), acc) \<Rightarrow>
    (PR_CONST gmp_dyadic_interval_vec_nonempty) todo)"

lemma newton_loop_cond_mop_monadic_eq:
  "newton_loop_cond_mop_monadic = RETURN o newton_loop_cond"
  unfolding newton_loop_cond_mop_monadic_def
    gmp_dyadic_interval_vec_nonempty_def newton_loop_cond_def
    dyadic_interval_vec_length_monadic_def poly_length_monadic_def PR_CONST_def
  by (auto intro!: ext split: prod.splits)

sepref_definition newton_loop_cond_impl [llvm_inline] is
  "newton_loop_cond_mop_monadic" ::
  "newton_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding newton_loop_cond_mop_monadic_def
  by sepref

lemma newton_loop_cond_impl_hnr[sepref_fr_rules]:
  "(newton_loop_cond_impl, RETURN o (PR_CONST newton_loop_cond)) \<in>
    newton_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using newton_loop_cond_impl.refine
  by (simp add: newton_loop_cond_mop_monadic_eq PR_CONST_def)

section \<open>es-threaded clones of the bisection/zero/one branches\<close>

text \<open>\<open>newton_split_pair_state_monadic\<close> clones
  @{const bisection_split_pair_state_monadic} (\<open>Bisection.thy\<close>) with the
  SAME two pushes (children interval + children polys) plus ONE more:
  \<open>es\<close> gets \<open>e' = max 1 (e-1)\<close> pushed TWICE (one per child), matching
  \<open>dyadic_exp_push2_monadic\<close>'s "same value both times" contract —
  NewDsc's \<open>e\<close> update on bisection.\<close>

text \<open>The bisection child's scheduling exponent as its own pure op: an inline \<open>max 1 (e - 1)\<close> inside the
  heap-owning split body would leave \<open>RETURN ((-) e 1)\<close> / \<open>RETURN (max ..)\<close> untranslated (machine-word
  arithmetic mixed into a heap body). It is stated with an \<open>if\<close> rather than \<open>max\<close>, so it translates to an
  \<open>snat\<close> comparison and subtraction.\<close>

text \<open>\<^bold>\<open>The proper-split successor, implementation side\<close>, following the abstract \<open>split_run_len_int\<close>. A
  bisection is a proper split iff both children keep a nonzero sign-variation count (Obreshkoff), which counts
  against the single-cluster hypothesis; otherwise the chain continues. The two child counts come from the
  truncated classification, whose 0/1/\<open>\<ge>2\<close> trichotomy decides ``nonzero'' exactly.

  A midpoint-root emission is also variation mass leaving the path (the root leaves via the point interval,
  invisible to both children's counts), so it counts as contrary evidence; otherwise an input whose roots lie
  exactly on the dyadic grid (every step a midpoint hit, both siblings of class 0) would look like one deep
  cluster. \<open>mid\<close> is the \<open>carried_mid_zero\<close> result already computed in the split branch.

  \<^bold>\<open>Decay rather than reset.\<close> Contrary evidence reduces the run to \<open>\<lfloor>10\<sigma>/11\<rfloor>\<close> (\<open>s - s div 11\<close>, without
  multiplication) rather than to 0, so a nested sub-cluster inherits most of its parent's confirmation instead
  of starting from zero at each level. The separation from non-clusters does not depend on the rate: a spread
  proper-splits at every level, so \<open>\<sigma> \<rightarrow> \<beta>\<^sup>n\<sigma> \<rightarrow> 0\<close> for any \<open>\<beta> < 1\<close>.\<close>
text \<open>\<^bold>\<open>Where the class-\<open>4\<close> exclusion belongs.\<close> Treating the ambiguous sentinel \<open>4\<close> as not a proper split is
  specific to the hybrid solver, whose \<open>hybrid_classify_prebuilt_monadic\<close> can return it. Here the children are
  classified by @{const carried_descartes_count_trunc_monadic}, bounded by \<open>3\<close>
  (@{thm [source] carried_descartes_count_trunc_monadic_le3}), so a \<open>cl < 4\<close> conjunct would not change behaviour,
  but it would break the loop refinement, whose model uses the exact @{const carried_descartes_count}
  (unbounded: a child may have \<open>\<ge> 4\<close> sign variations) against the abstract \<open>split_run_len_int\<close>'s nonzero test.
  So the exclusion is in \<open>hybrid_split_run_len\<close>, at the hybrid solver's call sites, and this constant keeps
  the nonzero test.\<close>
definition newton_split_run_len :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "newton_split_run_len mid cl cr s = (if mid \<or> (cl \<noteq> 0 \<and> cr \<noteq> 0) then s - s div 11 else s + 1)"

sepref_register "PR_CONST newton_split_run_len" :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

sepref_definition newton_split_run_len_impl [llvm_inline] is
  "uncurry3 (RETURN oooo newton_split_run_len)" ::
  "[\<lambda>(((mid, cl), cr), s). s + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding newton_split_run_len_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma newton_split_run_len_impl_hnr[sepref_fr_rules]:
  "(uncurry3 newton_split_run_len_impl, uncurry3 (RETURN oooo PR_CONST newton_split_run_len)) \<in>
    [\<lambda>(((mid, cl), cr), s). s + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using newton_split_run_len_impl.refine by (simp add: PR_CONST_def)

text \<open>Push both bisection children AND report their classifies, so the parent can decide the
  proper-split flag. Replaces \<open>bisection_push_children_monadic\<close> in the Newton split branch:
  the children's polynomials are built exactly once (by @{const carried_left_right_monadic},
  which consumes \<open>Q\<close> in place) and classified before they are pushed.\<close>
text \<open>Tuple packaging as its OWN registered op: monadify decomposes an inline
  \<open>RETURN (qtodo, cl, cr)\<close> into nested pair-\<open>RETURN\<close>s that the translate phase cannot synthesize.\<close>
definition newton_pcc_result_monadic ::
  "gmp_poly list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (gmp_poly list \<times> nat \<times> nat) nres" where
"newton_pcc_result_monadic qtodo cl cr \<equiv> RETURN (qtodo, cl, cr)"

sepref_register "PR_CONST newton_pcc_result_monadic"
  :: "gmp_poly list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (gmp_poly list \<times> nat \<times> nat) nres"

sepref_definition newton_pcc_result_impl [llvm_inline] is
  "uncurry2 newton_pcc_result_monadic" ::
  "gmp_poly_vec_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    gmp_poly_vec_assn \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  unfolding newton_pcc_result_monadic_def
  by sepref

lemma newton_pcc_result_impl_hnr[sepref_fr_rules]:
  "(uncurry2 newton_pcc_result_impl,
    uncurry2 (PR_CONST newton_pcc_result_monadic)) \<in>
    gmp_poly_vec_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
      gmp_poly_vec_assn \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  using newton_pcc_result_impl.refine by (simp add: PR_CONST_def)

definition newton_push_children_classify_monadic ::
  "gmp_poly list \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly list \<times> nat \<times> nat) nres" where
"newton_push_children_classify_monadic qtodo Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>IN-PLACE split: \<open>carried_left_right_monadic\<close> consumes \<open>Q\<close> in place, as
     \<open>bisection_push_children_monadic\<close> (\<open>Bisection.thy\<close>) does, instead of the ALLOCATING
     \<open>carried_left\<close>/\<open>carried_right\<close> followed by \<open>poly_free\<close>.\<close>
  (ql, qr) \<leftarrow> (PR_CONST carried_left_right_monadic) Q;
  ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length qr + 1 < max_snat LENGTH(gmp_poly_len));
  cl \<leftarrow> (PR_CONST carried_descartes_count_trunc_monadic) ql;
  cr \<leftarrow> (PR_CONST carried_descartes_count_trunc_monadic) qr;
  qtodo \<leftarrow> (PR_CONST poly_vec_push2_monadic) qtodo ql qr;
  (PR_CONST newton_pcc_result_monadic) qtodo cl cr
}"

sepref_register "PR_CONST newton_push_children_classify_monadic"
  :: "gmp_poly list \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly list \<times> nat \<times> nat) nres"

sepref_definition newton_push_children_classify_impl [llvm_code] is
  "uncurry newton_push_children_classify_monadic" ::
  "[\<lambda>(qtodo, Q). 0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_vec_assn \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  unfolding newton_push_children_classify_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_push_children_classify_impl_hnr[sepref_fr_rules]:
  "(uncurry newton_push_children_classify_impl,
    uncurry (PR_CONST newton_push_children_classify_monadic)) \<in>
    [\<lambda>(qtodo, Q). 0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
        gmp_poly_vec_assn \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  using newton_push_children_classify_impl.refine by (simp add: PR_CONST_def)

definition newton_split_pair_state_monadic ::
  "(gmp_dyadic_interval_vec \<times> gmp_poly list \<times> nat list \<times> nat list \<times> nat list) \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow>
    (gmp_dyadic_interval_vec \<times> gmp_poly list \<times> nat list \<times> nat list \<times> nat list) nres" where
"newton_split_pair_state_monadic st l_num r_num k e s mid Q \<equiv> doN {
  let (todo, qtodo, es, ss, cs) = st;
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length es + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length ss + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length cs + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable2 todo);
  todo \<leftarrow> (PR_CONST dyadic_interval_vec_push_children_monadic) todo l_num r_num k;
  (qtodo, cl, cr) \<leftarrow>
    (PR_CONST newton_push_children_classify_monadic) qtodo Q;
  let e' = (PR_CONST newton_child_exp) e;
  es \<leftarrow> (PR_CONST dyadic_exp_push2_monadic) es e';
  ASSERT (s + 1 < max_snat LENGTH(gmp_poly_len));
  let s' = (PR_CONST newton_split_run_len) mid cl cr s;
  ss \<leftarrow> (PR_CONST dyadic_exp_push2_monadic) ss s';
  ASSERT (length cs + 1 < max_snat LENGTH(gmp_poly_len));
  cs \<leftarrow> mop_list_append cs cl;
  ASSERT (length cs + 1 < max_snat LENGTH(gmp_poly_len));
  cs \<leftarrow> mop_list_append cs cr;
  RETURN (todo, qtodo, es, ss, cs)
}"

text \<open>There is deliberately no standalone \<open>_correct\<close> lemma for
  @{const newton_split_pair_state_monadic}, exactly as for
  @{const bisection_split_pair_state_monadic}: the op's correctness is established INLINE
  inside the loop refinement, where
  @{thm [source] dyadic_interval_vec_push_children_monadic_spec} and
  @{const carried_left_right_monadic} are unfolded at the point of use (a standalone
  wrapper would drop the library spec's \<open>dyadic_interval_vec_to_list\<close> conjunct that the
  \<open>refine_vcg\<close> context keeps).\<close>

definition newton_branch_split_nonroot_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> newton_loop_state nres" where
"newton_branch_split_nonroot_monadic todo qtodo es ss cs acc l_num r_num k e s Q \<equiv> doN {
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  triple \<leftarrow> (PR_CONST newton_split_pair_state_monadic)
    (todo, qtodo, es, ss, cs) l_num r_num k e s False Q;
  RETURN (triple, acc)
}"

definition newton_branch_split_root_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> newton_loop_state nres" where
"newton_branch_split_root_monadic todo qtodo es ss cs acc l_num r_num k e s Q \<equiv> doN {
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable acc);
  acc \<leftarrow> (PR_CONST carried_push_mid_monadic) acc l_num r_num k;
  triple \<leftarrow> (PR_CONST newton_split_pair_state_monadic)
    (todo, qtodo, es, ss, cs) l_num r_num k e s True Q;
  RETURN (triple, acc)
}"

text \<open>Clone of @{const bisection_branch_split_monadic} (\<open>Bisection.thy\<close>) — the
  bisection FALLBACK (used both when the window gate is off and when all four
  window tries reject). \<open>e\<close> is threaded only to compute \<open>e'\<close> inside the pair-
  state op above; the root/midpoint test is UNCHANGED (\<open>bisection_mid_zero_monadic\<close>
  depends only on \<open>Q\<close>, not on \<open>e\<close>).\<close>

definition newton_branch_split_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> newton_loop_state nres" where
"newton_branch_split_monadic todo qtodo es ss cs acc l_num r_num k e s Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  is_root \<leftarrow> (PR_CONST bisection_mid_zero_monadic) Q;
  if is_root then
    (PR_CONST newton_branch_split_root_monadic) todo qtodo es ss cs acc l_num r_num k e s Q
  else
    (PR_CONST newton_branch_split_nonroot_monadic) todo qtodo es ss cs acc l_num r_num k e s Q
}"

text \<open>\<open>cnt = 0\<close>/\<open>cnt = 1\<close> clones: BEHAVIORALLY unchanged from
  @{const bisection_branch_zero_monadic}/@{const bisection_branch_one_monadic} — the
  popped \<open>e\<close> value is simply discarded (a dropped or finalized node's schedule
  state is irrelevant), \<open>es\<close> (already shrunk by the caller's pop) threads
  through untouched.\<close>

definition newton_branch_zero_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> newton_loop_state nres" where
"newton_branch_zero_monadic todo qtodo es ss cs acc l_num r_num k Q \<equiv> doN {
  (PR_CONST mpzb_discard_monadic) l_num;
  (PR_CONST mpzb_discard_monadic) r_num;
  (PR_CONST poly_free_monadic) Q;
  RETURN ((todo, qtodo, es, ss, cs), acc)
}"

definition newton_branch_one_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> newton_loop_state nres" where
"newton_branch_one_monadic todo qtodo es ss cs acc l_num r_num k Q \<equiv> doN {
  let (lns, rns, ks) = acc;
  ASSERT (dyadic_interval_vec_pushable acc);
  lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) lns l_num;
  rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) rns r_num;
  ASSERT (length ks + 1 < max_snat LENGTH(gmp_poly_len));
  ks \<leftarrow> mop_list_append ks k;
  (PR_CONST poly_free_monadic) Q;
  RETURN ((todo, qtodo, es, ss, cs), (lns, rns, ks))
}"

section \<open>The window-accept push (a single child, not a pair)\<close>

text \<open>On a successful @{const newton_try_window_monadic} at grid position \<open>m\<close>:
  free the SUPERSEDED node poly \<open>Q\<close>, push exactly ONE child — the interval
  @{const newton_window_child}\<open> l_num r_num k e m\<close> (\<open>Newton_Spec.thy\<close>), the candidate poly
  \<open>cand\<close>, and \<open>e + 1\<close> onto \<open>es\<close> (the accept-side exponent bump, matching \<open>newdsc_pol\<close>'s
  \<open>e + 1\<close> on block/Newton acceptance). \<open>m\<close>/\<open>r_num - l_num\<close> are UNRESTRICTED int/nat
  values here (arbitrary-precision mpz scalars in the implementation — only the WORD-sized
  exponent \<open>j = 2^e+2\<close> is headroom-guarded, per \<open>newton_pol_gate\<close>).\<close>

definition newton_window_push_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
    (gmp_dyadic_interval_vec \<times> gmp_poly list \<times> nat list \<times> nat list \<times> nat list) nres" where
"newton_window_push_monadic todo qtodo es ss cs l_num r_num k e s m Q cand \<equiv> doN {
  (PR_CONST poly_free_monadic) Q;
  ASSERT (e < LENGTH(gmp_poly_len));
  ASSERT (((1::nat) << e) + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + (((1::nat) << e) + 2) < max_snat LENGTH(gmp_poly_len));
  ASSERT (e + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>\<open>base = l_num \<cdot> 2^(2^e+2)\<close> via the immediate shift on a copy of \<open>l_num\<close>
     (@{const mpz_shift_left_snat_monadic}): no materialised \<open>2^(2^e+2)\<close> and no general multiply.\<close>
  base \<leftarrow> RETURN (COPY l_num);
  base \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) base (((1::nat) << e) + 2);
  w \<leftarrow> (PR_CONST mpz_sub.amop_r1) r_num l_num;
  (PR_CONST mpzb_discard_monadic) l_num;
  z1 \<leftarrow> RETURN (mpz_from_int 0);
  mw \<leftarrow> (PR_CONST mpz_mul.amop) z1 m w;
  \<comment> \<open>\<open>m+4\<close> via the immediate @{const mpz_add_ui_snat_monadic} (\<open>m\<close> consumed destructively): no
     materialised \<open>4\<close>.\<close>
  m4 \<leftarrow> (PR_CONST mpz_add_ui_snat_monadic) m 4;
  m4w \<leftarrow> (PR_CONST mpz_mul.amop_r1) m4 w;
  (PR_CONST mpzb_discard_monadic) w;
  bcopy \<leftarrow> RETURN (COPY base);
  l' \<leftarrow> (PR_CONST mpz_add.amop_r1) bcopy mw;
  (PR_CONST mpzb_discard_monadic) mw;
  r' \<leftarrow> (PR_CONST mpz_add.amop_r1) base m4w;
  (PR_CONST mpzb_discard_monadic) m4w;
  let k' = k + (((1::nat) << e) + 2);
  let (lns, rns, ks) = todo;
  ASSERT (dyadic_interval_vec_pushable todo);
  lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) lns l';
  rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) rns r';
  ASSERT (length ks + 1 < max_snat LENGTH(gmp_poly_len));
  ks \<leftarrow> mop_list_append ks k';
  ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
  qtodo \<leftarrow> (PR_CONST poly_vec_push_monadic) qtodo cand;
  ASSERT (length es + 1 < max_snat LENGTH(gmp_poly_len));
  es \<leftarrow> mop_list_append es (e + 1);
  ASSERT (length ss + 1 < max_snat LENGTH(gmp_poly_len));
  ss \<leftarrow> mop_list_append ss s;
  \<comment> \<open>The caller appends the \<open>cs\<close> entry \<open>v+2\<close>, the accepted child's exact count (\<open>v \<ge> 2 \<Rightarrow> \<ge> 4\<close>, disjoint
     from the classification range \<open>{0,1,2,3}\<close>), before this call, so the child's pop reuses it instead of
     recounting. \<open>cs\<close> passes through here.\<close>
  RETURN ((lns, rns, ks), qtodo, es, ss, cs)
}"

text \<open>The op's abstract contract is UNCHANGED (the keystone consumes it black-box): the pushed
  child is exactly @{const newton_window_child}. Only the plumbing is GMP now — \<open>2\<^bsup>2\<^sup>e\<^sup>+\<^sup>2\<^esup>\<close> via
  @{const mpz_pow2_monadic} over the machine shift \<open>1 << e\<close> (Sepref has no \<open>snat\<close> exponentiation),
  and the two endpoints share the \<open>base = l \<cdot> 2\<^bsup>j\<^esup>\<close> and \<open>w = r - l\<close> temporaries. The extra word
  hypotheses are all supplied by @{const newton_pol_gate} at the call site.\<close>
lemma newton_window_push_monadic_correct:
  assumes "dyadic_interval_vec_pushable todo"
      and "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)"
      and "length es + 1 < max_snat LENGTH(gmp_poly_len)"
      and "length ss + 1 < max_snat LENGTH(gmp_poly_len)"
      and "length cs + 1 < max_snat LENGTH(gmp_poly_len)"
      and "e < LENGTH(gmp_poly_len)"
      and "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
      and "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
      and "e + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "newton_window_push_monadic todo qtodo es ss cs l_num r_num k e s m Q cand
           \<le> SPEC (\<lambda>(todo', qtodo', es', ss', cs').
                let (lns, rns, ks) = todo; (l', r', k') = newton_window_child l_num r_num k e m in
                todo' = (lns @ [l'], rns @ [r'], ks @ [k']) \<and>
                qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1] \<and>
                ss' = ss @ [s] \<and> cs' = cs)"
proof -
  have sh: "((1::nat) << e) = 2 ^ e" by (simp add: shiftl_def push_bit_eq_mult)
  have b4: "(4::nat) < max_snat LENGTH(gmp_long_len)" by (simp add: max_snat_def)
  show ?thesis
    using assms sh b4
    unfolding newton_window_push_monadic_def PR_CONST_def sh
      dyadic_interval_vec_pushable_def Let_def newton_window_child_def
      mpz_mul.amop_r1_def mpz_mul.aop_r1_def mpz_mul.amop_def mpz_mul.aop_def
      mpz_add.amop_r1_def mpz_add.aop_r1_def
      mpz_sub.amop_r1_def mpz_sub.aop_r1_def
      mpzb_discard_monadic_def COPY_def
      poly_push_coeff_monadic_def poly_vec_push_monadic_def
    apply (refine_vcg mpz_shift_left_snat_monadic_spec_plain[THEN order_trans]
        mpz_add_ui_snat_monadic_spec[THEN order_trans])
    by (auto simp: pw_le_iff refine_pw_simps mpz_from_int_def algebra_simps
        slong_bounds_def max_sint_def min_sint_def split: prod.splits)
qed

section \<open>The after-pop dispatch\<close>

text \<open>Clone of @{const bisection_after_pop_monadic} (\<open>Bisection.thy-830\<close>).
  The FOUR window tries run in the EXACT order the abstract
  \<open>newdsc_pol_main_int pol_final\<close> tries its guarded \<open>try_blocks_int_g\<close>/
  \<open>try_newton_int_g\<close> (block \<open>m=0\<close>; block \<open>m=s-4\<close>; Newton at the left endpoint;
  Newton at the right endpoint) — the loop-bridge proof (not yet attempted,
  see the keystone note below) must align its case-split to THIS order, never
  reshape the abstract side to match an impl convenience.\<close>

text \<open>The window choice, factored out of @{text newton_after_pop_monadic}: the four guarded window tries,
  returning the first accepted \<open>(m, cand)\<close> or @{term None}. As one op, it lets the after-pop refinement split
  only on \<open>Some\<close>/\<open>None\<close> rather than on the combinations of tries; its correctness (\<open>= newton_window_pick\<close>) is a
  separate lemma.\<close>
text \<open>\<^bold>\<open>The two Newton sides, each an op.\<close> Factoring them out (rather than inlining)
  buys two things: the refinement lemmas \<open>nlr_loc0_branch_refine\<close> /
  \<open>nlr_loc1_branch_refine\<close> each mirror ONE monadic call, and the
  probe's owned mpz's get freed on the \<open>\<not>ok\<close> path: \<open>newton_lambda_loc0\<close>
  ALWAYS allocates \<open>num\<close>/\<open>den\<close> (the reject branch returns owned \<open>0\<close>/\<open>1\<close>), so an
  \<open>else RETURN None\<close> would leak them. On the accept path \<open>newton_snap_kn\<close> consumes both.\<close>

definition newton_side0_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres" where
"newton_side0_monadic v e Q \<equiv> doN {
  (ok0, num0, den0) \<leftarrow> (PR_CONST newton_lambda_loc0_monadic) v Q;
  if ok0 then doN {
    kn0 \<leftarrow> (PR_CONST newton_snap_kn_monadic) e num0 den0;
    ASSERT (2 \<le> kn0);
    ASSERT (slong_bounds (int 2));
    two \<leftarrow> (PR_CONST mpz_of_snat_monadic) 2;
    m \<leftarrow> (PR_CONST mpz_sub.amop_r1) kn0 two;
    (PR_CONST mpzb_discard_monadic) two;
    (PR_CONST newton_try_window_monadic) v e m Q
  } else doN {
    (PR_CONST mpzb_discard_monadic) num0;
    (PR_CONST mpzb_discard_monadic) den0;
    RETURN gmp_mpoly_opt.None
  }
}"

definition newton_side1_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres" where
"newton_side1_monadic v e Q \<equiv> doN {
  (ok1, num1, den1) \<leftarrow> (PR_CONST newton_lambda_loc1_monadic) v Q;
  if ok1 then doN {
    kn1 \<leftarrow> (PR_CONST newton_snap_kn_monadic) e num1 den1;
    ASSERT (2 \<le> kn1);
    ASSERT (slong_bounds (int 2));
    two \<leftarrow> (PR_CONST mpz_of_snat_monadic) 2;
    m \<leftarrow> (PR_CONST mpz_sub.amop_r1) kn1 two;
    (PR_CONST mpzb_discard_monadic) two;
    (PR_CONST newton_try_window_monadic) v e m Q
  } else doN {
    (PR_CONST mpzb_discard_monadic) num1;
    (PR_CONST mpzb_discard_monadic) den1;
    RETURN gmp_mpoly_opt.None
  }
}"

text \<open>The four tries in the implementation's order, probes first, all unconditional at a gate-open node:
  Newton at the left endpoint; Newton at the right; block \<open>m=0\<close>; block \<open>m=s-4\<close>. The blocks are guarded on
  \<open>is_None res0 \<and> is_None res1\<close>, i.e. they run whenever neither probe accepts. Each \<open>m\<close> is an owned mpz handed to
  \<open>newton_try_window_monadic\<close>, which returns it inside an accept or frees it on a reject, so no branch leaks.
  \<open>s = 2^(2^e+2)\<close> comes from \<open>mpz_pow2\<close> over the \<open>1<<e\<close> shift (Sepref has no snat exponentiation). The guards use
  the option's registered \<open>is_None\<close> rather than \<open>case_option\<close>, which the \<open>dflt_option_private\<close> setup does not
  identify.\<close>
definition newton_window_choice_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres" where
"newton_window_choice_monadic v e Q \<equiv> doN {
  \<comment> \<open>Newton probes first; the two blocks run as a fallback when neither probe accepts
     (\<open>is_None res0 \<and> is_None res1\<close>).\<close>
  res0 \<leftarrow> (PR_CONST newton_side0_monadic) v e Q;
  res1 \<leftarrow> (if gmp_mpoly_opt.is_None res0
           then (PR_CONST newton_side1_monadic) v e Q
           else RETURN gmp_mpoly_opt.None);
  r0 \<leftarrow> (if gmp_mpoly_opt.is_None res0 \<and> gmp_mpoly_opt.is_None res1 then doN {
           ASSERT (slong_bounds (int 0));
           m0 \<leftarrow> (PR_CONST mpz_of_snat_monadic) 0;
           (PR_CONST newton_try_window_monadic) v e m0 Q
         } else RETURN gmp_mpoly_opt.None);
  r1 \<leftarrow> (if gmp_mpoly_opt.is_None res0 \<and> gmp_mpoly_opt.is_None res1
              \<and> gmp_mpoly_opt.is_None r0 then doN {
           ASSERT (((1::nat) << e) + 2 < max_snat LENGTH(gmp_poly_len));
           s \<leftarrow> (PR_CONST mpz_pow2_monadic) (((1::nat) << e) + 2);
           ASSERT (slong_bounds (int 4));
           four \<leftarrow> (PR_CONST mpz_of_snat_monadic) 4;
           s4 \<leftarrow> (PR_CONST mpz_sub.amop_r1) s four;
           (PR_CONST mpzb_discard_monadic) four;
           (PR_CONST newton_try_window_monadic) v e s4 Q
         } else RETURN gmp_mpoly_opt.None);
  RETURN (if \<not> gmp_mpoly_opt.is_None res0 then res0
          else if \<not> gmp_mpoly_opt.is_None res1 then res1
          else if \<not> gmp_mpoly_opt.is_None r0 then r0
          else r1)
}"

sepref_register "PR_CONST newton_side0_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres"

sepref_definition newton_side0_impl [llvm_code] is
  "uncurry2 newton_side0_monadic" ::
  "[\<lambda>((v, e), Q). 0 < length Q \<and> 1 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  unfolding newton_side0_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free gmp_poly_assn_free
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_side0_impl_hnr[sepref_fr_rules]:
  "(uncurry2 newton_side0_impl, uncurry2 (PR_CONST newton_side0_monadic)) \<in>
    [\<lambda>((v, e), Q). 0 < length Q \<and> 1 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  using newton_side0_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_side1_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres"

sepref_definition newton_side1_impl [llvm_code] is
  "uncurry2 newton_side1_monadic" ::
  "[\<lambda>((v, e), Q). 0 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> length Q + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  unfolding newton_side1_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free gmp_poly_assn_free
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_side1_impl_hnr[sepref_fr_rules]:
  "(uncurry2 newton_side1_impl, uncurry2 (PR_CONST newton_side1_monadic)) \<in>
    [\<lambda>((v, e), Q). 0 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> length Q + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  using newton_side1_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_window_choice_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres"

sepref_definition newton_window_choice_impl [llvm_code] is
  "uncurry2 newton_window_choice_monadic" ::
  "[\<lambda>((v, e), Q). 0 < length Q \<and> 1 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> length Q + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  unfolding newton_window_choice_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free gmp_poly_assn_free
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_window_choice_impl_hnr[sepref_fr_rules]:
  "(uncurry2 newton_window_choice_impl,
      uncurry2 (PR_CONST newton_window_choice_monadic)) \<in>
    [\<lambda>((v, e), Q). 0 < length Q \<and> 1 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> length Q + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  using newton_window_choice_impl.refine by (simp add: PR_CONST_def)

section \<open>Sepref synthesis of the branch cascade\<close>

text \<open>Direct clones of the bisection branch impls (\<open>Bisection.thy\<close>) with the \<open>es\<close> column
  threaded through as one more owned argument (\<open>gmp_dyadic_exp_list_assn\<close>, the same
  assertion the \<open>todo\<close>'s own \<open>ks\<close> column uses). The window push and the after-pop dispatch
  are the two genuinely new ones.\<close>



sepref_register "PR_CONST newton_split_pair_state_monadic"
  :: "(gmp_dyadic_interval_vec \<times> gmp_poly list \<times> nat list \<times> nat list \<times> nat list) \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow>
      (gmp_dyadic_interval_vec \<times> gmp_poly list \<times> nat list \<times> nat list \<times> nat list) nres"

sepref_definition newton_split_pair_state_impl [llvm_code] is
  "uncurry7 newton_split_pair_state_monadic" ::
  "[\<lambda>(((((((st, _), _), k), _), _), _), Q).
      let (todo, qtodo, es, ss, cs) = st in
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    newton_triple_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      newton_triple_assn"
  unfolding newton_split_pair_state_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_split_pair_state_impl_hnr[sepref_fr_rules]:
  "(uncurry7 newton_split_pair_state_impl,
    uncurry7 (PR_CONST newton_split_pair_state_monadic)) \<in>
    [\<lambda>(((((((st, _), _), k), _), _), _), Q).
      let (todo, qtodo, es, ss, cs) = st in
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      newton_triple_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        bool1_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        newton_triple_assn"
  using newton_split_pair_state_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_branch_split_nonroot_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> newton_loop_state nres"

sepref_definition newton_branch_split_nonroot_impl [llvm_code] is
  "uncurry11 newton_branch_split_nonroot_monadic" ::
  "[\<lambda>(((((((((((todo, qtodo), es), ss), cs), _), _), _), k), _), _), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding newton_branch_split_nonroot_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_branch_split_nonroot_impl_hnr[sepref_fr_rules]:
  "(uncurry11 newton_branch_split_nonroot_impl,
    uncurry11 (PR_CONST newton_branch_split_nonroot_monadic)) \<in>
    [\<lambda>(((((((((((todo, qtodo), es), ss), cs), _), _), _), k), _), _), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using newton_branch_split_nonroot_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_branch_split_root_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> newton_loop_state nres"

sepref_definition newton_branch_split_root_impl [llvm_code] is
  "uncurry11 newton_branch_split_root_monadic" ::
  "[\<lambda>(((((((((((todo, qtodo), es), ss), cs), acc), _), _), k), _), _), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding newton_branch_split_root_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_branch_split_root_impl_hnr[sepref_fr_rules]:
  "(uncurry11 newton_branch_split_root_impl,
    uncurry11 (PR_CONST newton_branch_split_root_monadic)) \<in>
    [\<lambda>(((((((((((todo, qtodo), es), ss), cs), acc), _), _), k), _), _), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using newton_branch_split_root_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_branch_split_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> newton_loop_state nres"

sepref_definition newton_branch_split_impl [llvm_code] is
  "uncurry11 newton_branch_split_monadic" ::
  "[\<lambda>(((((((((((todo, qtodo), es), ss), cs), acc), _), _), k), _), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding newton_branch_split_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_branch_split_impl_hnr[sepref_fr_rules]:
  "(uncurry11 newton_branch_split_impl,
    uncurry11 (PR_CONST newton_branch_split_monadic)) \<in>
    [\<lambda>(((((((((((todo, qtodo), es), ss), cs), acc), _), _), k), _), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using newton_branch_split_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_branch_zero_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> newton_loop_state nres"

sepref_definition newton_branch_zero_impl [llvm_inline] is
  "uncurry9 newton_branch_zero_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
    newton_loop_state_assn"
  unfolding newton_branch_zero_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_branch_zero_impl_hnr[sepref_fr_rules]:
  "(uncurry9 newton_branch_zero_impl,
    uncurry9 (PR_CONST newton_branch_zero_monadic)) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
      newton_loop_state_assn"
  using newton_branch_zero_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_branch_one_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> newton_loop_state nres"

sepref_definition newton_branch_one_impl [llvm_inline] is
  "uncurry9 newton_branch_one_monadic" ::
  "[\<lambda>(((((((((_, _), _), _), _), acc), _), _), _), _).
      dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding newton_branch_one_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_branch_one_impl_hnr[sepref_fr_rules]:
  "(uncurry9 newton_branch_one_impl,
    uncurry9 (PR_CONST newton_branch_one_monadic)) \<in>
    [\<lambda>(((((((((_, _), _), _), _), acc), _), _), _), _).
      dyadic_interval_vec_pushable acc]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using newton_branch_one_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_window_push_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
      (gmp_dyadic_interval_vec \<times> gmp_poly list \<times> nat list \<times> nat list \<times> nat list) nres"

sepref_definition newton_window_push_impl [llvm_code] is
  "uncurry12 newton_window_push_monadic" ::
  "[\<lambda>((((((((((((todo, qtodo), es), ss), cs), _), _), k), e), _), _), _), _).
      dyadic_interval_vec_pushable todo \<and>
      length qtodo + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      e < LENGTH(gmp_poly_len) \<and>
      e + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      2 ^ e + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow>
    newton_triple_assn"
  unfolding newton_window_push_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_window_push_impl_hnr[sepref_fr_rules]:
  "(uncurry12 newton_window_push_impl,
    uncurry12 (PR_CONST newton_window_push_monadic)) \<in>
    [\<lambda>((((((((((((todo, qtodo), es), ss), cs), _), _), k), e), _), _), _), _).
      dyadic_interval_vec_pushable todo \<and>
      length qtodo + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      e < LENGTH(gmp_poly_len) \<and>
      e + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      2 ^ e + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      newton_triple_assn"
  using newton_window_push_impl.refine by (simp add: PR_CONST_def)

definition newton_after_pop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> newton_loop_state nres" where
"newton_after_pop_monadic todo qtodo es ss cs acc l_num r_num k e s c Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  if c = 0 then
    (PR_CONST newton_branch_zero_monadic) todo qtodo es ss cs acc l_num r_num k Q
  else if c = 1 then
    (PR_CONST newton_branch_one_monadic) todo qtodo es ss cs acc l_num r_num k Q
  else doN {
    gate \<leftarrow> (PR_CONST newton_pol_gate_mop) Q e k s;
    if \<not> gate then
      (PR_CONST newton_branch_split_monadic) todo qtodo es ss cs acc l_num r_num k e s Q
    else doN {
      ASSERT (1 < length Q);
      ASSERT (length Q + 2 < max_snat LENGTH(gmp_poly_len));
      ASSERT (e < LENGTH(gmp_poly_len));
      ASSERT (e + 1 < max_snat LENGTH(gmp_poly_len));
      ASSERT (2 ^ e + 2 < max_snat LENGTH(gmp_poly_len));
      ASSERT (k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len));
      ASSERT ((2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len));
      \<comment> \<open>A window child caches its exact count as \<open>c = v+2 (\<ge> 4)\<close> at push, so its pop reuses \<open>v = c-2\<close> instead
         of recounting. \<open>c \<le> 3\<close> is a bisection or initial classification (range \<open>{0,1,2,3}\<close>: the loop cap of 2
         plus the \<open>extra_f\<close> boundary bit), with the exact count unknown, so it is recounted. The window
         encoding \<open>v+2 \<ge> 4\<close> (\<open>v \<ge> 2\<close> at gate-open) is disjoint from \<open>{0,1,2,3}\<close>; \<open>v+1\<close> would collide at \<open>v = 2\<close>
         with class 3.\<close>
      v \<leftarrow> (if 4 \<le> c then RETURN (c - 2)
             else (PR_CONST carried_descartes_count_exact_monadic) Q);
      ASSERT (int v < max_sint LENGTH(gmp_long_len));
      wc \<leftarrow> (PR_CONST newton_window_choice_monadic) v e Q;
      if gmp_mpoly_opt.is_None wc then
        (PR_CONST newton_branch_split_monadic) todo qtodo es ss cs acc l_num r_num k e s Q
      else doN {
        ASSERT (dyadic_interval_vec_pushable todo);
        ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
        ASSERT (length es + 1 < max_snat LENGTH(gmp_poly_len));
        ASSERT (length ss + 1 < max_snat LENGTH(gmp_poly_len));
        ASSERT (length cs + 1 < max_snat LENGTH(gmp_poly_len));
        ASSERT (v + 2 < max_snat LENGTH(gmp_poly_len));
        let (m, cand) = gmp_mpoly_opt.the wc;
        \<comment> \<open>W1: cache the exact count as \<open>v+2\<close> (\<ge> 4, disjoint from the \<open>{0,1,2,3}\<close> classify range)
           as this window child's \<open>cs\<close> entry (moved out of \<open>newton_window_push\<close>, where
           \<open>v\<close> is not in scope).\<close>
        cs \<leftarrow> mop_list_append cs (v + 2);
        triple \<leftarrow> (PR_CONST newton_window_push_monadic)
                    todo qtodo es ss cs l_num r_num k e s m Q cand;
        RETURN (triple, acc)
      }
    }
  }
}"

text \<open>The after-pop dispatch. The window branch's callee preconditions (\<open>1 < length Q\<close>, the window-width
  products, the \<open>k\<close>-jump headroom) all follow from the gate, and Sepref cannot see through the gate's opaque
  \<open>bool\<close>, so they are \<open>ASSERT\<close>s at the call site, discharged in the loop refinement from
  \<open>newton_pol_gate_len1\<close> / \<open>_len2\<close> / \<open>_eL\<close> / \<open>_wcap\<close> / \<open>_kjump\<close> / \<open>_mul\<close>.\<close>
sepref_register "PR_CONST newton_after_pop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> newton_loop_state nres"

sepref_definition newton_after_pop_impl [llvm_code] is
  "uncurry12 newton_after_pop_monadic" ::
  "[\<lambda>((((((((((((todo, qtodo), es), ss), cs), acc), _), _), k), _), _), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding newton_after_pop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free gmp_poly_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_after_pop_impl_hnr[sepref_fr_rules]:
  "(uncurry12 newton_after_pop_impl,
    uncurry12 (PR_CONST newton_after_pop_monadic)) \<in>
    [\<lambda>((((((((((((todo, qtodo), es), ss), cs), acc), _), _), k), _), _), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using newton_after_pop_impl.refine by (simp add: PR_CONST_def)

section \<open>The loop (WHILEIT over the extended state) + main-list wiring\<close>

text \<open>Mirrors @{const bisection_loop_step_monadic}/@{const bisection_loop_monadic}/
  @{const bisection_main_list} (\<open>Bisection.thy/1258/1306\<close>) with the
  extra \<open>es\<close> column popped in lockstep (via the SAME @{const dyadic_exp_pop_last_monadic}
  the todo's own \<open>ks\<close> uses) and the Newton after-pop dispatch in place of the
  plain 0/1/split one. Every op is total (the ASSERTs are discharged by the
  loop invariant, exactly as in the ET loop).\<close>

definition newton_loop_step_monadic ::
  "newton_loop_state \<Rightarrow> newton_loop_state nres" where
"newton_loop_step_monadic st \<equiv>
  (case st of ((todo, qtodo, es, ss, cs), acc) \<Rightarrow> doN {
    ((l_num, r_num, k), todo) \<leftarrow> (PR_CONST dyadic_interval_vec_pop_last_monadic) todo;
    ASSERT (qtodo \<noteq> []);
    (Q, qtodo) \<leftarrow> (PR_CONST poly_vec_pop_last_monadic) qtodo;
    ASSERT (es \<noteq> []);
    (e, es) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) es;
    ASSERT (ss \<noteq> []);
    (s, ss) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) ss;
    ASSERT (cs \<noteq> []);
    (c, cs) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) cs;
    ASSERT (0 < length Q);
    ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (dyadic_interval_vec_pushable2 todo);
    ASSERT (dyadic_interval_vec_pushable acc);
    ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length es + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length ss + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length cs + 2 < max_snat LENGTH(gmp_poly_len));
    (PR_CONST newton_after_pop_monadic) todo qtodo es ss cs acc l_num r_num k e s c Q
  })"

definition newton_loop_safe_invar ::
  "newton_loop_state \<Rightarrow> bool" where
"newton_loop_safe_invar st \<equiv>
  newton_loop_state_invar st \<and>
  (newton_loop_cond st \<longrightarrow>
    (case st of (((lns, rns, ks), qtodo, es, ss, cs), acc) \<Rightarrow>
      dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks) \<and>
      dyadic_interval_vec_pushable acc \<and>
      qtodo \<noteq> [] \<and> es \<noteq> [] \<and> ss \<noteq> [] \<and> cs \<noteq> [] \<and>
      0 < length (last qtodo) \<and>
      length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      last ks + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len)))"

definition newton_loop_body_checked_monadic ::
  "newton_loop_state \<Rightarrow> newton_loop_state nres" where
"newton_loop_body_checked_monadic st \<equiv>
  (if (PR_CONST newton_loop_cond) st then
    (PR_CONST newton_loop_step_monadic) st
   else RETURN st)"

definition newton_loop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> newton_loop_state nres" where
"newton_loop_monadic todo qtodo es ss cs acc \<equiv>
  WHILEIT newton_loop_safe_invar
    (\<lambda>st. (PR_CONST newton_loop_cond) st)
    (\<lambda>st. (PR_CONST newton_loop_body_checked_monadic) st)
    ((todo, qtodo, es, ss, cs), acc)"

text \<open>The seed pushes the input dyadic box \<open>(l_num, r_num, k)\<close>, the input poly, and
  the initial NewDsc scheduling exponent \<open>e0\<close>; runs the loop; frees the drained
  worklist columns and returns the accepted-interval vector. \<open>es0 = [e0]\<close> is a
  plain nat-list literal (no GMP alloc).\<close>

text \<open>The step precondition, in the shape Sepref wants it (one predicate on the whole state):
  the safe invariant plus the loop condition. Mirrors \<open>bisection_loop_step_pre\<close>.\<close>
definition newton_loop_step_pre ::
  "newton_loop_state \<Rightarrow> bool" where
"newton_loop_step_pre st \<equiv>
  newton_loop_safe_invar st \<and> newton_loop_cond st"

sepref_register "PR_CONST newton_loop_step_monadic"
  :: "newton_loop_state \<Rightarrow> newton_loop_state nres"

sepref_definition newton_loop_step_impl [llvm_code] is
  "newton_loop_step_monadic" ::
  "[newton_loop_step_pre]\<^sub>a
    newton_loop_state_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding newton_loop_step_monadic_def
  unfolding newton_loop_step_pre_def
  unfolding newton_loop_safe_invar_def
  unfolding newton_loop_state_invar_def
  unfolding newton_loop_cond_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] =
    dyadic_interval_vec_pop_last_impl_hnr
    poly_vec_pop_last_impl_hnr
    dyadic_exp_pop_last_impl_hnr
    newton_after_pop_impl_hnr
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_loop_step_impl_hnr[sepref_fr_rules]:
  "(newton_loop_step_impl, PR_CONST newton_loop_step_monadic) \<in>
    [newton_loop_step_pre]\<^sub>a
      newton_loop_state_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using newton_loop_step_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_loop_body_checked_monadic"
  :: "newton_loop_state \<Rightarrow> newton_loop_state nres"

sepref_definition newton_loop_body_checked_impl [llvm_code] is
  "newton_loop_body_checked_monadic" ::
  "[newton_loop_safe_invar]\<^sub>a
    newton_loop_state_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding newton_loop_body_checked_monadic_def
  supply [simp] = newton_loop_step_pre_def
  supply [sepref_fr_rules] =
    newton_loop_cond_impl_hnr
    newton_loop_step_impl_hnr
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_loop_body_checked_impl_hnr[sepref_fr_rules]:
  "(newton_loop_body_checked_impl,
    PR_CONST newton_loop_body_checked_monadic) \<in>
    [newton_loop_safe_invar]\<^sub>a
      newton_loop_state_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using newton_loop_body_checked_impl.refine by (simp add: PR_CONST_def)

text \<open>The \<open>ASSN_ANNOT\<close>-seeded stateful form the \<open>WHILEIT\<close> rule needs (the loop state is a nested
  tuple of heap-owning assertions, so Sepref cannot infer its assertion from the seed alone).
  Definitionally equal to @{const newton_loop_monadic}, which stays the keystone's target.\<close>
definition newton_loop_stateful_monadic ::
  "newton_loop_state \<Rightarrow> newton_loop_state nres" where
"newton_loop_stateful_monadic st0 \<equiv> doN {
  st0 \<leftarrow> RETURN ((PR_CONST (ASSN_ANNOT newton_loop_state_assn)) st0);
  WHILEIT newton_loop_safe_invar
    (\<lambda>st. (PR_CONST newton_loop_cond) st)
    (\<lambda>st. (PR_CONST newton_loop_body_checked_monadic) st)
    st0
}"

lemma newton_loop_monadic_eq_stateful:
  "newton_loop_monadic todo qtodo es ss cs acc
     = (PR_CONST newton_loop_stateful_monadic) ((todo, qtodo, es, ss, cs), acc)"
  unfolding newton_loop_monadic_def newton_loop_stateful_monadic_def
    ASSN_ANNOT_def PR_CONST_def by simp

sepref_register "PR_CONST newton_loop_stateful_monadic"
  :: "newton_loop_state \<Rightarrow> newton_loop_state nres"

sepref_definition newton_loop_stateful_impl [llvm_code] is
  "newton_loop_stateful_monadic" ::
  "[newton_loop_safe_invar]\<^sub>a
    newton_loop_state_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding newton_loop_stateful_monadic_def
  supply [sepref_fr_rules] =
    newton_loop_cond_impl_hnr
    newton_loop_body_checked_impl_hnr
  by sepref_dbg_keep

lemma newton_loop_stateful_impl_hnr[sepref_fr_rules]:
  "(newton_loop_stateful_impl, PR_CONST newton_loop_stateful_monadic) \<in>
    [newton_loop_safe_invar]\<^sub>a
      newton_loop_state_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using newton_loop_stateful_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_loop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> newton_loop_state nres"

sepref_definition newton_loop_impl [llvm_code] is
  "uncurry5 newton_loop_monadic" ::
  "[\<lambda>(((((todo, qtodo), es), ss), cs), acc).
      newton_loop_safe_invar ((todo, qtodo, es, ss, cs), acc)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding newton_loop_monadic_eq_stateful
  supply [sepref_fr_rules] = newton_loop_stateful_impl_hnr
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry5 newton_loop_impl, uncurry5 (PR_CONST newton_loop_monadic)) \<in>
    [\<lambda>(((((todo, qtodo), es), ss), cs), acc).
      newton_loop_safe_invar ((todo, qtodo, es, ss, cs), acc)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using newton_loop_impl.refine by (simp add: PR_CONST_def)

definition newton_main_list_monadic ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"newton_main_list_monadic e0 l_num r_num k P \<equiv> doN {
  todo0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 1;
  c_l \<leftarrow> RETURN (COPY l_num);
  c_r \<leftarrow> RETURN (COPY r_num);
  let (todo_lns, todo_rns, todo_ks) = todo0;
  ASSERT (dyadic_interval_vec_pushable todo0);
  todo_lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) todo_lns c_l;
  todo_rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) todo_rns c_r;
  ASSERT (length todo_ks + 1 < max_snat LENGTH(gmp_poly_len));
  todo_ks \<leftarrow> mop_list_append todo_ks k;
  todo1 \<leftarrow> RETURN (todo_lns, todo_rns, todo_ks);
  c0 \<leftarrow> (PR_CONST carried_descartes_count_trunc_monadic) P;
  qtodo0 \<leftarrow> (PR_CONST poly_vec_empty_sz_monadic) 1;
  ASSERT (length qtodo0 + 1 < max_snat LENGTH(gmp_poly_len));
  qtodo1 \<leftarrow> (PR_CONST poly_vec_push_monadic) qtodo0 P;
  let es0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length es0 + 1 < max_snat LENGTH(gmp_poly_len));
  es1 \<leftarrow> mop_list_append es0 e0;
  let ss0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length ss0 + 1 < max_snat LENGTH(gmp_poly_len));
  ss1 \<leftarrow> mop_list_append ss0 0;
  let cs0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length cs0 + 1 < max_snat LENGTH(gmp_poly_len));
  cs1 \<leftarrow> mop_list_append cs0 c0;
  acc0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 1;
  ASSERT (newton_loop_safe_invar ((todo1, qtodo1, es1, ss1, cs1), acc0));
  st \<leftarrow> (PR_CONST newton_loop_monadic) todo1 qtodo1 es1 ss1 cs1 acc0;
  let ((todo, qtodo, es, ss, cs), acc) = st;
  ASSERT (qtodo = []);
  (PR_CONST poly_vec_free_empty_monadic) qtodo;
  (PR_CONST dyadic_interval_vec_free_monadic) todo;
  RETURN acc
}"

text \<open>The exported solver entry (working C name \<open>newbisection_main\<close>). Clone of
  @{const bisection_main_list}'s synthesis plus the \<open>es\<close> seed \<open>[e0]\<close>; the drained \<open>es\<close> column
  is freed by frame inference (\<open>al_assn\<close> carries its own \<open>MK_FREE\<close>), like the ET loop's \<open>ks\<close>.\<close>
sepref_register "PR_CONST newton_main_list_monadic"
  :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition newton_main_list_impl [llvm_code] is
  "uncurry4 newton_main_list_monadic" ::
  "[\<lambda>((((_, _), _), k), P).
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding newton_main_list_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  supply [sepref_frame_free_rules] = mk_free_is_pure
  \<comment> \<open>\<open>newton_loop_safe_invar\<close> stays FOLDED: the seed \<open>ASSERT\<close> discharges the loop's
     precondition by assumption, whereas unfolding it leaves a conjunction over the loop
     state's still-opaque tuple variables that the side solver cannot close.\<close>
  supply [simp] =
    dyadic_interval_vec_invar_def
    dyadic_interval_vec_pushable_def
    dyadic_interval_vec_pushable2_def
  supply [sepref_fr_rules] =
    newton_loop_impl_hnr
    poly_vec_free_empty_impl_hnr
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma newton_main_list_impl_hnr[sepref_fr_rules]:
  "(uncurry4 newton_main_list_impl,
    uncurry4 (PR_CONST newton_main_list_monadic)) \<in>
    [\<lambda>((((_, _), _), k), P).
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        gmp_dyadic_interval_vec_assn"
  using newton_main_list_impl.refine by (simp add: PR_CONST_def)

section \<open>\<open>pol_final\<close> is sound / complete / terminating\<close>

text \<open>\<^bold>\<open>The concrete scheduling policy \<open>pol_final\<close> yields a SOUND and COMPLETE
  isolator\<close> — the payoff of the pol-parameterization (soundness, completeness and termination
  are proved for ALL policies; here they are instantiated at the runtime policy).
  \<open>pol_final_real\<close> is a \<open>newton_pol_real\<close>, so
  @{const newdsc_pol} feeds it the degree as its first argument;
  @{thm [source] newdsc_pol_terminates_squarefree} gives the domain and
  @{thm [source] newdsc_pol_sound}/@{thm [source] newdsc_pol_complete} the two
  directions. The bridge @{thm [source] newdsc_pol_int_eq_newdsc_pol} maps
  @{const newdsc_pol_int}\<open> pol_final\<close> to exactly this
  @{const newdsc_pol}\<open> pol_final_real\<close> interval set.\<close>

lemma newdsc_pol_pol_final_dom:
  fixes P :: "int poly"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "newdsc_pol_dom (pol_final_real, degree P, a, b, e, dk, s, map_poly of_int P)"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  show ?thesis by (rule newdsc_pol_terminates_squarefree[OF dne dle p0 sf ab])
qed

theorem newdsc_pol_pol_final_sound:
  fixes P :: "int poly"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "\<forall>I \<in> set (newdsc_pol pol_final_real (degree P) a b e dk s (map_poly of_int P)).
           dsc_pair_ok (map_poly of_int P) I"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  show ?thesis
    by (rule newdsc_pol_sound[OF newdsc_pol_pol_final_dom[OF P0 p0 sf ab] dle dne ab])
qed

theorem newdsc_pol_pol_final_complete:
  fixes P :: "int poly" and x :: real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
    and root: "poly (map_poly of_int P :: real poly) x = 0" and ax: "a < x" and xb: "x < b"
  shows "\<exists>I \<in> set (newdsc_pol pol_final_real (degree P) a b e dk s (map_poly of_int P)).
           fst I \<le> x \<and> x \<le> snd I"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  show ?thesis
    by (rule newdsc_pol_complete[OF newdsc_pol_pol_final_dom[OF P0 p0 sf ab] dle dne root ax xb])
qed

section \<open>Sepref synthesis order\<close>

text \<open>Synthesis, bottom-up, with both a registration and an HNR per op:
  \<^enum> probe reads: the borrowed slot-read route (as \<open>poly_shift_coeff_impl\<close> in \<open>Dyadic_Interval\<close>, or
    \<open>poly_coeff_bitlen2_impl\<close> in \<open>Count\<close>; HNR by \<open>sepref_to_hoare\<close> and \<open>vcg\<close>); the \<open>eval1\<close> loop is a WHILET with a
    borrowed polynomial and an owned mpz-pair state;
  \<^enum> \<open>newton_snap_kn\<close>: a scalar op, \<open>raw_mpz_mul_2exp\<close> for \<open>num * s\<close> and \<open>raw_mpz_fdiv_q\<close>, then a clip into a word
    after a magnitude ASSERT (with \<open>op_unat_snat_conv\<close> for size-typed intermediates);
  \<^enum> window try: composes \<open>carried_init_inplace_impl_hnr\<close> and the \<open>descartes_finish\<close> HNRs;
  \<^enum> after-pop: condition/body/result op decomposition where the WHILET meets the destructive state; \<open>es\<close> is a pure
    word-list state;
  \<^enum> the outer loop and the \<open>[llvm_code]\<close> main implementation.
  When a composed op's HNR has to be transferred onto an op whose classification is proved, the \<open>impl_form\<close> and
  program-equality pattern is used, peeling one bind at a time with \<open>bind_cong\<close>
  (\<open>carried_descartes_count_trunc_impl_form_eq\<close> is an example).\<close>

end
