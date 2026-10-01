theory Split_Newton
  imports Split Newton_Solver Kiou_Bound
begin

text \<open>Newton-core variant of the all-roots split pipeline.
  Layer: SEPREF.
  Main exports: \<open>dsc_split_pos_solve_newton_monadic\<close> / \<open>_neg_\<close> and the pipeline entry
  \<open>dsc_isolate_all_split_newton_main\<close>. The Newton entry gate is owned by \<open>Newton.thy\<close>
  (\<open>newton_pol_gate\<close>).\<close>

text \<open>The Newton variant of the split pipeline: the three-stage structure of
  \<open>bisection_isolate_all_split_main\<close> with both half solves running
  @{const newton_main_list_monadic} (the carried Newton solver) in place of \<open>bisection_main_list\<close>.
  The zero-root stage @{const dsc_split_zero_check_monadic} is shared.

  Ownership: @{const newton_main_list_monadic} borrows its endpoint scalars (\<open>mpzb_assn\<^sup>k\<close>) and
  copies them into its own worklist, so both scalars and the \<open>-1\<close> reflection scale are discarded
  here after their last use.\<close>

definition dsc_split_pos_solve_newton_monadic ::
  "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"dsc_split_pos_solve_newton_monadic xs \<equiv> doN {
  ASSERT (1 \<le> length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
  kpos \<leftarrow> (PR_CONST kiou_bound_k_monadic) xs;
  ASSERT (kpos * length xs < max_snat LENGTH(gmp_poly_len) \<and>
          kpos < max_snat LENGTH(gmp_poly_len));
  Pinit \<leftarrow> (PR_CONST split_init_pow2_l0_monadic) kpos xs;
  ASSERT (0 < length Pinit \<and> length Pinit + 1 < max_snat LENGTH(gmp_poly_len));
  zl \<leftarrow> RETURN (mpz_from_int 0);
  rpos \<leftarrow> (PR_CONST mpz_pow2_monadic) kpos;
  accP \<leftarrow> (PR_CONST newton_main_list_monadic) split_pipeline_e0 zl rpos 0 Pinit;
  (PR_CONST mpzb_discard_monadic) rpos;
  (PR_CONST mpzb_discard_monadic) zl;
  RETURN accP
}"

definition dsc_split_neg_solve_newton_monadic ::
  "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"dsc_split_neg_solve_newton_monadic xs \<equiv> doN {
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  Qb \<leftarrow> (PR_CONST poly_clone_monadic) xs;
  ASSERT (length Qb + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>The reflection uses @{const poly_reflect_in_place_monadic} (negate the odd-index
      coefficients in place) rather than a general scale by \<open>-1\<close>.\<close>
  Qb \<leftarrow> (PR_CONST poly_reflect_in_place_monadic) Qb;
  \<comment> \<open>\<open>Qb = refl_list xs\<close>, exactly as in \<open>dsc_split_neg_solve_monadic\<close> — the sign-robust
      Kioustelidis kernel takes the reflected leading coefficient of either sign directly.\<close>
  ASSERT (1 \<le> length Qb \<and> length Qb + 1 < max_snat LENGTH(gmp_poly_len));
  kneg \<leftarrow> (PR_CONST kiou_bound_k_monadic) Qb;
  ASSERT (kneg * length Qb < max_snat LENGTH(gmp_poly_len) \<and>
          kneg < max_snat LENGTH(gmp_poly_len));
  Qinit \<leftarrow> (PR_CONST split_init_pow2_l0_monadic) kneg Qb;
  (PR_CONST poly_free_monadic) Qb;
  ASSERT (0 < length Qinit \<and> length Qinit + 1 < max_snat LENGTH(gmp_poly_len));
  zln \<leftarrow> RETURN (mpz_from_int 0);
  rneg \<leftarrow> (PR_CONST mpz_pow2_monadic) kneg;
  accQ \<leftarrow> (PR_CONST newton_main_list_monadic) split_pipeline_e0 zln rneg 0 Qinit;
  (PR_CONST mpzb_discard_monadic) rneg;
  (PR_CONST mpzb_discard_monadic) zln;
  RETURN accQ
}"

definition dsc_isolate_all_split_newton_main ::
  "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres" where
"dsc_isolate_all_split_newton_main xs \<equiv> doN {
  ASSERT (2 \<le> length xs);
  accP \<leftarrow> (PR_CONST dsc_split_pos_solve_newton_monadic) xs;
  accQ \<leftarrow> (PR_CONST dsc_split_neg_solve_newton_monadic) xs;
  xs0 \<leftarrow> (PR_CONST dsc_split_zero_check_monadic) xs;
  RETURN (accP, accQ, xs0)
}"

section \<open>Sepref synthesis (as in \<open>Split_Bisection.thy\<close>)\<close>

sepref_register "PR_CONST dsc_split_pos_solve_newton_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition dsc_split_pos_solve_newton_impl [llvm_code] is
  "dsc_split_pos_solve_newton_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding dsc_split_pos_solve_newton_monadic_def
  unfolding split_pipeline_e0_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma dsc_split_pos_solve_newton_impl_hnr[sepref_fr_rules]:
  "(dsc_split_pos_solve_newton_impl, PR_CONST dsc_split_pos_solve_newton_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using dsc_split_pos_solve_newton_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST dsc_split_neg_solve_newton_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition dsc_split_neg_solve_newton_impl [llvm_code] is
  "dsc_split_neg_solve_newton_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding dsc_split_neg_solve_newton_monadic_def
  unfolding split_pipeline_e0_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma dsc_split_neg_solve_newton_impl_hnr[sepref_fr_rules]:
  "(dsc_split_neg_solve_newton_impl, PR_CONST dsc_split_neg_solve_newton_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using dsc_split_neg_solve_newton_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST dsc_isolate_all_split_newton_main"
  :: "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres"

sepref_definition dsc_isolate_all_split_newton_main_impl [llvm_code] is
  "dsc_isolate_all_split_newton_main" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
    gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  unfolding dsc_isolate_all_split_newton_main_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma dsc_isolate_all_split_newton_main_impl_hnr[sepref_fr_rules]:
  "(dsc_isolate_all_split_newton_main_impl, PR_CONST dsc_isolate_all_split_newton_main) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  using dsc_isolate_all_split_newton_main_impl.refine by (simp add: PR_CONST_def)

end
