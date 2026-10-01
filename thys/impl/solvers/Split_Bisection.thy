theory Split_Bisection
imports Split Kiou_Bound Bisection_Solver "IsaRRI_LLVM.Dyadic_Interval"
begin

text \<open>The bisection all-roots split pipeline: the two half-solve stages (positive and negative),
  the top-level assembly \<open>bisection_isolate_all_split_main\<close>, and their Sepref-synthesised
  \<open>[llvm_code]\<close> implementations (entry @{term dsc_isolate_all_split_main_impl}). The primitives they
  build on are in \<open>Split\<close>. Abstract soundness is in \<open>Kiou_Bound_Reflect\<close>.\<close>

text \<open>The Kioustelidis kernel @{const kiou_bound_k_monadic} bounds the positive roots of any \<open>xs\<close>
  with \<open>last xs \<noteq> 0\<close>, of either sign. Both of this pipeline's bound calls need that: the caller's
  \<open>xs\<close> may have \<open>last xs < 0\<close>, and the reflection \<open>refl_list xs\<close> has
  \<open>last = last xs * (-1)^deg\<close>, which is negative at odd degree. So the negative half needs no
  sign-normalising pre-pass.\<close>

section \<open>The split pipeline (NRES layer)\<close>

text \<open>Assembles the pieces above into one NRES computation. Returns a TRIPLE
  \<open>(accP, accQ, xs0)\<close> -- the positive-half solve result, the negative-half solve result (still in
  the REFLECTED polynomial's coordinate frame; the negate-and-swap remap is left to the caller,
  since no \<open>dyadic_interval_vec\<close> merge/map op is needed in Isabelle), and \<open>xs0\<close> (whether \<open>x=0\<close>
  is a root, i.e. \<open>xs!0=0\<close>) for the caller to push the degenerate triple. Both halves seed
  \<open>l_num=0, k=0\<close> (the \<open>l=0\<close> box \<open>(0,2^k)\<close>) and are solved via the SAME
  @{const bisection_main_list} entry the non-split pipeline uses.\<close>
text \<open>The pipeline is three named stage ops rather than one inlined \<open>doN\<close> block, for two reasons:
  (1) each stage gets its own small \<open>sepref_definition\<close> instead of one long owned-mpz chain;
  (2) the correctness capstone composes the three stage \<open>\<le> SPEC\<close> facts by the standard
  \<open>refine_vcg\<close> and \<open>order_trans\<close> pattern, whereas with an inlined pipeline the fragments'
  trailing-\<open>RETURN\<close> form does not match the goal's continuation form. The \<open>ASSERT\<close>s inside each
  stage are the call-site preconditions Sepref needs for the constituent ops' HNRs; each is proved
  from the producer specifications in the stage's correctness lemma.\<close>
definition dsc_split_pos_solve_monadic :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"dsc_split_pos_solve_monadic xs \<equiv> doN {
  ASSERT (1 \<le> length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
  kpos \<leftarrow> (PR_CONST kiou_bound_k_monadic) xs;
  ASSERT (kpos * length xs < max_snat LENGTH(gmp_poly_len) \<and>
          kpos < max_snat LENGTH(gmp_poly_len));
  Pinit \<leftarrow> (PR_CONST split_init_pow2_l0_monadic) kpos xs;
  ASSERT (0 < length Pinit \<and> length Pinit + 1 < max_snat LENGTH(gmp_poly_len));
  zl \<leftarrow> RETURN (mpz_from_int 0);
  rpos \<leftarrow> (PR_CONST mpz_pow2_monadic) kpos;
  \<comment> \<open>@{const bisection_main_list} borrows both endpoint scalars (\<open>mpzb_assn\<^sup>k\<close>; it copies them
    into its own worklist), so \<open>zl\<close>/\<open>rpos\<close> are passed directly and both are freed here after the
    call.\<close>
  accP \<leftarrow> (PR_CONST bisection_main_list) zl rpos 0 Pinit;
  (PR_CONST mpzb_discard_monadic) rpos;
  (PR_CONST mpzb_discard_monadic) zl;
  RETURN accP
}"

definition dsc_split_neg_solve_monadic :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"dsc_split_neg_solve_monadic xs \<equiv> doN {
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  Qb \<leftarrow> (PR_CONST poly_clone_monadic) xs;
  ASSERT (length Qb + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>@{const poly_reflect_in_place_monadic} negates only the odd-index coefficients in place
    (\<open>mpz_neg.aop_r_impl\<close>, no multiplication, no allocation) and proves the target
    \<open>poly_reflect_in_place_correct: \<le> RETURN (refl_list xs)\<close> directly.\<close>
  Qb \<leftarrow> (PR_CONST poly_reflect_in_place_monadic) Qb;
  \<comment> \<open>\<open>Qb = refl_list xs\<close>. Its leading coefficient is \<open>last xs * (-1)^deg\<close>, of either sign --
    the sign-robust kernel handles that directly, so no \<open>map uminus\<close> normalization pass here.\<close>
  ASSERT (1 \<le> length Qb \<and> length Qb + 1 < max_snat LENGTH(gmp_poly_len));
  kneg \<leftarrow> (PR_CONST kiou_bound_k_monadic) Qb;
  ASSERT (kneg * length Qb < max_snat LENGTH(gmp_poly_len) \<and>
          kneg < max_snat LENGTH(gmp_poly_len));
  Qinit \<leftarrow> (PR_CONST split_init_pow2_l0_monadic) kneg Qb;
  (PR_CONST poly_free_monadic) Qb;
  ASSERT (0 < length Qinit \<and> length Qinit + 1 < max_snat LENGTH(gmp_poly_len));
  zln \<leftarrow> RETURN (mpz_from_int 0);
  rneg \<leftarrow> (PR_CONST mpz_pow2_monadic) kneg;
  accQ \<leftarrow> (PR_CONST bisection_main_list) zln rneg 0 Qinit;
  \<comment> \<open>Both endpoints are borrowed (see the positive half); free both.\<close>
  (PR_CONST mpzb_discard_monadic) rneg;
  (PR_CONST mpzb_discard_monadic) zln;
  RETURN accQ
}"

definition bisection_isolate_all_split_main ::
  "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres" where
"bisection_isolate_all_split_main xs \<equiv> doN {
  ASSERT (2 \<le> length xs);
  \<comment> \<open>Positive-root bound and solve.\<close>
  accP \<leftarrow> (PR_CONST dsc_split_pos_solve_monadic) xs;
  \<comment> \<open>Negative-root bound (on the reflection; the bound kernel is sign-robust)
      and solve -- the result stays in the REFLECTED frame; remap is the export layer's job.\<close>
  accQ \<leftarrow> (PR_CONST dsc_split_neg_solve_monadic) xs;
  \<comment> \<open>Exact-zero root: \<open>ripoly (Poly xs) 0 = xs!0\<close>, no search needed.\<close>
  xs0 \<leftarrow> (PR_CONST dsc_split_zero_check_monadic) xs;
  RETURN (accP, accQ, xs0)
}"

section \<open>Sepref synthesis of the split pipeline\<close>

text \<open>Each stage op synthesises unconditionally (\<open>gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a \<dots>\<close>): every constituent
  op's HNR precondition is discharged from the call-site \<open>ASSERT\<close>s in the stage definitions, and
  the stage correctness lemmas in \<open>Kiou_Bound_Reflect\<close> (where the abstract precondition
  \<open>dsc_isolate_all_split_pre\<close> lives) prove those assertions hold. The input polynomial is borrowed
  (\<open>\<^sup>k\<close>) throughout; the negative half works on its own clone. @{const bisection_main_list} consumes
  the polynomial (\<open>\<^sup>d\<close>) but borrows its two endpoint scalars (\<open>\<^sup>k\<close>), so every owned \<open>mpz\<close> scalar
  this layer allocates (the \<open>l=0\<close> and \<open>2^k\<close> endpoints, the \<open>-1\<close> reflection scale) is freed by
  \<open>mpzb_discard_monadic\<close> after its last use. (Sepref's frame closing, \<open>sepref_frame_free_rules\<close>,
  would insert those frees anyway; the explicit discards make the ownership contract visible.)\<close>

sepref_register "PR_CONST dsc_split_pos_solve_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition dsc_split_pos_solve_impl [llvm_code] is
  "dsc_split_pos_solve_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding dsc_split_pos_solve_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma dsc_split_pos_solve_impl_hnr[sepref_fr_rules]:
  "(dsc_split_pos_solve_impl, PR_CONST dsc_split_pos_solve_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using dsc_split_pos_solve_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST dsc_split_neg_solve_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition dsc_split_neg_solve_impl [llvm_code] is
  "dsc_split_neg_solve_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding dsc_split_neg_solve_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma dsc_split_neg_solve_impl_hnr[sepref_fr_rules]:
  "(dsc_split_neg_solve_impl, PR_CONST dsc_split_neg_solve_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using dsc_split_neg_solve_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST bisection_isolate_all_split_main"
  :: "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres"

sepref_definition dsc_isolate_all_split_main_impl [llvm_code] is
  "bisection_isolate_all_split_main" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
    gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  unfolding bisection_isolate_all_split_main_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma bisection_isolate_all_split_main_impl_hnr[sepref_fr_rules]:
  "(dsc_isolate_all_split_main_impl, PR_CONST bisection_isolate_all_split_main) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  using dsc_isolate_all_split_main_impl.refine by (simp add: PR_CONST_def)


end
