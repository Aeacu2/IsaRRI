theory Split_Bail
  imports Bail_Solver Split_Newton
begin

text \<open>The bail solver's all-roots split pipeline: \<open>bail_split_pos_solve\<close> /
  \<open>bail_split_neg_solve\<close> / \<open>bail_isolate_all_split_main\<close>. The polynomial is split at \<open>0\<close> into
  its positive and negative halves (a Kioustelidis bound per half) and each half is isolated by
  the bail loop. Kept apart from the core loop so that the loop depends only on
  @{theory_text Newton}, not on the split pipeline (@{theory_text Split}).\<close>

subsection \<open>The positive and negative halves\<close>

definition bail_split_pos_solve_monadic ::
  "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"bail_split_pos_solve_monadic xs \<equiv> doN {
  ASSERT (1 \<le> length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
  kpos \<leftarrow> (PR_CONST kiou_bound_k_monadic) xs;
  ASSERT (kpos * length xs < max_snat LENGTH(gmp_poly_len) \<and>
          kpos < max_snat LENGTH(gmp_poly_len));
  Pinit \<leftarrow> (PR_CONST split_init_pow2_l0_monadic) kpos xs;
  ASSERT (0 < length Pinit \<and> length Pinit + 1 < max_snat LENGTH(gmp_poly_len));
  zl \<leftarrow> RETURN (mpz_from_int 0);
  rpos \<leftarrow> (PR_CONST mpz_pow2_monadic) kpos;
  accP \<leftarrow> (PR_CONST bail_main_list_monadic) split_pipeline_e0 zl rpos 0 Pinit;
  (PR_CONST mpzb_discard_monadic) rpos;
  (PR_CONST mpzb_discard_monadic) zl;
  RETURN accP
}"

definition bail_split_neg_solve_monadic ::
  "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"bail_split_neg_solve_monadic xs \<equiv> doN {
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  Qb \<leftarrow> (PR_CONST poly_clone_monadic) xs;
  ASSERT (length Qb + 1 < max_snat LENGTH(gmp_poly_len));
  Qb \<leftarrow> (PR_CONST poly_reflect_in_place_monadic) Qb;
  ASSERT (1 \<le> length Qb \<and> length Qb + 1 < max_snat LENGTH(gmp_poly_len));
  kneg \<leftarrow> (PR_CONST kiou_bound_k_monadic) Qb;
  ASSERT (kneg * length Qb < max_snat LENGTH(gmp_poly_len) \<and>
          kneg < max_snat LENGTH(gmp_poly_len));
  Qinit \<leftarrow> (PR_CONST split_init_pow2_l0_monadic) kneg Qb;
  (PR_CONST poly_free_monadic) Qb;
  ASSERT (0 < length Qinit \<and> length Qinit + 1 < max_snat LENGTH(gmp_poly_len));
  zln \<leftarrow> RETURN (mpz_from_int 0);
  rneg \<leftarrow> (PR_CONST mpz_pow2_monadic) kneg;
  accQ \<leftarrow> (PR_CONST bail_main_list_monadic) split_pipeline_e0 zln rneg 0 Qinit;
  (PR_CONST mpzb_discard_monadic) rneg;
  (PR_CONST mpzb_discard_monadic) zln;
  RETURN accQ
}"

definition bail_isolate_all_split_main ::
  "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres" where
"bail_isolate_all_split_main xs \<equiv> doN {
  ASSERT (2 \<le> length xs);
  accP \<leftarrow> (PR_CONST bail_split_pos_solve_monadic) xs;
  accQ \<leftarrow> (PR_CONST bail_split_neg_solve_monadic) xs;
  xs0 \<leftarrow> (PR_CONST dsc_split_zero_check_monadic) xs;
  RETURN (accP, accQ, xs0)
}"

sepref_register "PR_CONST bail_split_pos_solve_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition bail_split_pos_solve_impl [llvm_code] is
  "bail_split_pos_solve_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding bail_split_pos_solve_monadic_def
  unfolding split_pipeline_e0_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma bail_split_pos_solve_impl_hnr[sepref_fr_rules]:
  "(bail_split_pos_solve_impl, PR_CONST bail_split_pos_solve_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using bail_split_pos_solve_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST bail_split_neg_solve_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition bail_split_neg_solve_impl [llvm_code] is
  "bail_split_neg_solve_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding bail_split_neg_solve_monadic_def
  unfolding split_pipeline_e0_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma bail_split_neg_solve_impl_hnr[sepref_fr_rules]:
  "(bail_split_neg_solve_impl, PR_CONST bail_split_neg_solve_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using bail_split_neg_solve_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST bail_isolate_all_split_main"
  :: "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres"

sepref_definition bail_isolate_all_split_main_impl [llvm_code] is
  "bail_isolate_all_split_main" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
    gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  unfolding bail_isolate_all_split_main_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma bail_isolate_all_split_main_impl_hnr[sepref_fr_rules]:
  "(bail_isolate_all_split_main_impl, PR_CONST bail_isolate_all_split_main) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  using bail_isolate_all_split_main_impl.refine by (simp add: PR_CONST_def)

end
