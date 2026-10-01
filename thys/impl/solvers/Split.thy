theory Split
  imports "IsaRRI_LLVM.Carried_Kernel"
begin

text \<open>The split solvers' primitives: the ascending power-of-two dilation loop, the
  carried initialisation at \<open>l=0\<close> built from it, the \<open>l=0\<close>/\<open>d=1\<close> identity lemmas they need,
  the root-node exponent \<open>split_pipeline_e0\<close>, and the zero-root check. They do not depend on
  \<open>Bisection\<close> or \<open>Kiou_Bound\<close>, so the hybrid solver can use them without the bisection
  all-roots pipeline (\<open>Split_Bisection\<close>).\<close>

text \<open>The all-roots pipeline's root-node scheduling exponent (defined here rather than in
  \<open>Split_Newton.thy\<close>, so the hybrid solver reaches it without importing the Newton
  pipeline). Kept BELOW \<open>newton_pol_emin = 3\<close> so the seed cannot open the
  gate through the (otherwise-unreachable) \<open>emin\<close> arm — the gate is exactly \<open>256 \<le> dk\<close>, the
  depth threshold.\<close>
definition split_pipeline_e0 :: nat where "split_pipeline_e0 = 2"

lemma split_pipeline_e0_lt: "split_pipeline_e0 + 1 < max_snat LENGTH(gmp_poly_len)"
  by (simp add: split_pipeline_e0_def max_snat_def)

section \<open>Specialized ascending pow2 dilation (the l=0 init core)\<close>

text \<open>\<open>poly_shift_pow_in_place_monadic\<close> gives coefficient \<open>i\<close> the DESCENDING exponent
  \<open>m*(dg-i)\<close> (the denominator part of the general \<open>carried_init_inplace\<close> chain). The split's \<open>l=0\<close>
  init instead needs the ASCENDING dilation \<open>coeff i \<mapsto> coeff i * 2^(m*i)\<close> (the \<open>d=1\<close> box
  \<open>[0,2^kb]\<close>'s scale step, done as ONE \<open>mpz_mul_2exp\<close> pass instead of the generic-\<open>mpz_mul\<close>
  accumulator \<open>poly_scale_in_place_monadic\<close> would use). This reuses
  \<open>poly_shift_coeff_monadic\<close>/\<open>poly_shift_coeff_impl\<close> (the per-coefficient
  \<open>mpzb_shift_left_snat_keep_impl\<close> primitive) COMPLETELY UNCHANGED -- only the loop's exponent
  ARITHMETIC differs (\<open>m*i\<close> vs \<open>m*(dg-i)\<close>), so no new low-level HNR proof is needed at all.\<close>
definition poly_shift_pow_asc_loop_monadic :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_shift_pow_asc_loop_monadic m len xs \<equiv>
  for 0 len (\<lambda>i ys. doN {
    ASSERT (i < length ys);
    ASSERT (m * i < max_snat LENGTH(gmp_poly_len));
    (PR_CONST poly_shift_coeff_monadic) ys i (m * i)
  }) xs"

sepref_register "PR_CONST poly_shift_pow_asc_loop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_shift_pow_asc_loop_impl [llvm_code] is
  "uncurry2 poly_shift_pow_asc_loop_monadic" ::
  "[\<lambda>((m, len), xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      m * len < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_shift_pow_asc_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_shift_pow_asc_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_shift_pow_asc_loop_impl,
    uncurry2 (PR_CONST poly_shift_pow_asc_loop_monadic)) \<in>
    [\<lambda>((m, len), xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      m * len < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_shift_pow_asc_loop_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Abstract correctness: coefficient \<open>i\<close> becomes \<open>xs!i * 2^(m*i)\<close> -- the SAME per-index
  invariant shape as \<open>poly_shift_pow_loop_monadic_correct\<close>, with \<open>m*i\<close> in place of
  \<open>m*(dg-i)\<close> (monotone directly in \<open>i<len\<close>, no \<open>dg\<close>/complement arithmetic needed).\<close>
lemma poly_shift_pow_asc_loop_monadic_correct:
  assumes "length xs = len" and "m * len < max_snat LENGTH(gmp_poly_len)"
  shows "poly_shift_pow_asc_loop_monadic m len xs
    \<le> RETURN (map (\<lambda>i. xs ! i * 2 ^ (m * i)) [0..<len])"
  unfolding poly_shift_pow_asc_loop_monadic_def poly_shift_coeff_monadic_def
  apply (refine_vcg for_rule[where I="\<lambda>i ys. length ys = len \<and>
    (\<forall>j<len. ys ! j = (if j < i then xs ! j * 2 ^ (m * j) else xs ! j))"])
  subgoal by simp
  subgoal using assms by simp
  subgoal by simp
  subgoal by simp
  subgoal premises pre for i s
  proof -
    have iln: "i < len" using pre by simp
    have ile: "i \<le> len" using iln by (rule less_imp_le)
    have mim: "m * i \<le> m * len" by (rule mult_le_mono2[OF ile])
    show "m * i < max_snat LENGTH(gmp_poly_len)"
      using mim assms(2) by (rule le_less_trans)
  qed
  subgoal using assms
    by (auto simp: nth_list_update' less_Suc_eq intro!: nth_equalityI)
  subgoal by (auto intro!: nth_equalityI)
  done

definition poly_shift_pow_asc_in_place_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_shift_pow_asc_in_place_monadic m xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (m * len < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_shift_pow_asc_loop_monadic) m len xs
}"

sepref_register "PR_CONST poly_shift_pow_asc_in_place_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_shift_pow_asc_in_place_impl [llvm_code] is
  "uncurry poly_shift_pow_asc_in_place_monadic" ::
  "[\<lambda>(m, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      m * length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_shift_pow_asc_in_place_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_shift_pow_asc_in_place_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_shift_pow_asc_in_place_impl,
    uncurry (PR_CONST poly_shift_pow_asc_in_place_monadic)) \<in>
    [\<lambda>(m, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      m * length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_shift_pow_asc_in_place_impl.refine
  by (simp add: PR_CONST_def)

lemma poly_shift_pow_asc_in_place_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and "m * length xs < max_snat LENGTH(gmp_poly_len)"
  shows "poly_shift_pow_asc_in_place_monadic m xs
    \<le> RETURN (map (\<lambda>i. xs ! i * 2 ^ (m * i)) [0..<length xs])"
  unfolding poly_shift_pow_asc_in_place_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg poly_shift_pow_asc_loop_monadic_correct[THEN order_trans])
  using assms by auto

section \<open>Trivial identities the specialized \<open>l=0\<close> init needs\<close>

text \<open>At \<open>c=0\<close> a Ruffini step is just prepending \<open>a\<close> unchanged -- the shift-by-zero identity that
  makes \<open>taylor_shift_list 0 = id\<close>, needed because the specialized split init always shifts by the
  literal endpoint \<open>l=0\<close>.\<close>
lemma ruffini_step_zero: "ruffini_step 0 a qs = a # qs"
  by (induction qs arbitrary: a) simp_all

lemma taylor_shift_list_zero: "taylor_shift_list 0 xs = xs"
  by (induction xs) (simp_all add: ruffini_step_zero)

text \<open>At denominator \<open>d=1\<close> (seed exponent \<open>k=0\<close>) the fractional-shift scale is the identity --
  the split init always seeds with \<open>k=0\<close> (a plain \<open>[0,2^kb]\<close> box, not a nested dyadic one).\<close>
lemma scale_for_fractional_shift_one: "scale_for_fractional_shift 1 1 xs = xs"
  by (induction xs) simp_all


section \<open>Specialized \<open>l=0\<close> carried init\<close>

text \<open>The specialized \<open>l=0\<close> carried init: seed denominator exponent \<open>k=0\<close> AND left endpoint
  \<open>l=0\<close> make BOTH the general chain's descending \<open>shift_pow\<close> and its \<open>taylor_shift\<close> steps
  identities (multiply by \<open>2^0=1\<close>; shift by \<open>0\<close>) -- so they are not merely computed-but-trivial,
  they are SKIPPED entirely. What remains is copy, then the interval-width scale by
  \<open>r-l=2^kb\<close> -- exactly \<open>poly_shift_pow_asc_in_place_monadic\<close>, replacing the general
  chain's generic-\<open>mpz_mul\<close> accumulator (\<open>poly_scale_in_place_monadic\<close>) with ONE
  \<open>mpz_mul_2exp\<close> pass per coefficient.\<close>
definition split_init_pow2_l0_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"split_init_pow2_l0_monadic kb xs \<equiv> doN {
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (kb * length xs < max_snat LENGTH(gmp_poly_len));
  p \<leftarrow> (PR_CONST poly_copy_monadic) xs;
  ASSERT (length p + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (kb * length p < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_shift_pow_asc_in_place_monadic) kb p
}"

sepref_register "PR_CONST split_init_pow2_l0_monadic" :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition split_init_pow2_l0_impl [llvm_code] is
  "uncurry split_init_pow2_l0_monadic" ::
  "[\<lambda>(kb, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      kb * length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding split_init_pow2_l0_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma split_init_pow2_l0_impl_hnr[sepref_fr_rules]:
  "(uncurry split_init_pow2_l0_impl,
    uncurry (PR_CONST split_init_pow2_l0_monadic)) \<in>
    [\<lambda>(kb, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      kb * length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using split_init_pow2_l0_impl.refine
  by (simp add: PR_CONST_def)

text \<open>\<open>split_init_pow2_l0_monadic\<close> refines \<open>carried_init_same_den\<close> at \<open>l=0, d=1,
  r=2^kb\<close> exactly: unfold the abstract def with the \<open>l=0\<close>/\<open>d=1\<close> identities
  (\<open>taylor_shift_list_zero\<close>, \<open>scale_for_fractional_shift_one\<close>) and
  the ascending-dilation closed form (\<open>scale_poly_list_eq_map_upt\<close>, \<open>power_mult\<close>).\<close>
lemma split_init_pow2_l0_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and "kb * length xs < max_snat LENGTH(gmp_poly_len)"
  shows "split_init_pow2_l0_monadic kb xs \<le> RETURN (carried_init_same_den 0 1 (2 ^ kb) xs)"
proof -
  have target: "carried_init_same_den 0 1 (2 ^ kb) xs = map (\<lambda>i. xs ! i * 2 ^ (kb * i)) [0..<length xs]"
  proof -
    have "carried_init_same_den 0 1 (2 ^ kb) xs
        = scale_poly_list (2 ^ kb) (taylor_shift_list 0 (rev (scale_for_fractional_shift 1 1 (rev xs))))"
      unfolding carried_init_same_den_def by simp
    also have "\<dots> = scale_poly_list (2 ^ kb) (taylor_shift_list 0 xs)"
      by (simp add: scale_for_fractional_shift_one)
    also have "\<dots> = scale_poly_list (2 ^ kb) xs"
      by (simp add: taylor_shift_list_zero)
    also have "\<dots> = map (\<lambda>i. xs ! i * ((2::int) ^ kb) ^ i) [0..<length xs]"
      by (rule scale_poly_list_eq_map_upt)
    also have "\<dots> = map (\<lambda>i. xs ! i * 2 ^ (kb * i)) [0..<length xs]"
      by (simp add: power_mult)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding split_init_pow2_l0_monadic_def PR_CONST_def
    apply (refine_vcg poly_copy_correct[THEN order_trans])
    using assms apply simp
    using assms apply simp
    using assms apply simp
    apply (rule order_trans[OF poly_shift_pow_asc_in_place_monadic_correct])
    using assms apply simp
    using assms apply simp
    using target by simp
qed

text \<open>Standalone version of \<open>split_init_pow2_l0_monadic_correct\<close>'s internal \<open>target\<close>
  identity -- needed at the assembly layer to rewrite \<open>carried_init_same_den 0 1 (2^k) xs\<close>
  (the RETURN value of \<open>split_init_pow2_l0_monadic\<close>) into \<open>scale_poly_list (2^k) xs\<close>
  (the form the \<open>cl_pre\<close> bridge lemmas and squarefreeness-transfer facts are stated against).\<close>
lemma split_init_pow2_l0_eq_scale_poly_list:
  "carried_init_same_den 0 1 (2 ^ kb) xs = scale_poly_list (2 ^ kb) xs"
proof -
  have "carried_init_same_den 0 1 (2 ^ kb) xs
      = scale_poly_list (2 ^ kb) (taylor_shift_list 0 (rev (scale_for_fractional_shift 1 1 (rev xs))))"
    unfolding carried_init_same_den_def by simp
  also have "\<dots> = scale_poly_list (2 ^ kb) (taylor_shift_list 0 xs)"
    by (simp add: scale_for_fractional_shift_one)
  also have "\<dots> = scale_poly_list (2 ^ kb) xs"
    by (simp add: taylor_shift_list_zero)
  finally show ?thesis .
qed

section \<open>Zero-root check\<close>

text \<open>Exact-zero root check: \<open>ripoly (Poly xs) 0 = xs!0\<close>, no search needed. Borrow-read the sign
  directly (\<open>poly_coeff_sgn_monadic\<close>, Array.thy) instead of deep-copying \<open>xs!0\<close> just to check it
  against zero and discard the copy.\<close>
definition dsc_split_zero_check_monadic :: "gmp_poly \<Rightarrow> bool nres" where
"dsc_split_zero_check_monadic xs \<equiv> doN {
  ASSERT (0 < length xs);
  sgn0 \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs 0;
  RETURN (sgn0 = 0)
}"

sepref_register "PR_CONST dsc_split_zero_check_monadic" :: "gmp_poly \<Rightarrow> bool nres"

sepref_definition dsc_split_zero_check_impl [llvm_code] is
  "dsc_split_zero_check_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding dsc_split_zero_check_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma dsc_split_zero_check_impl_hnr[sepref_fr_rules]:
  "(dsc_split_zero_check_impl, PR_CONST dsc_split_zero_check_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using dsc_split_zero_check_impl.refine by (simp add: PR_CONST_def)

end
