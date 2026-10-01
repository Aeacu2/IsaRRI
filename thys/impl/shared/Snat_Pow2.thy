theory Snat_Pow2
imports Interval_Eval
begin

text \<open>Power-of-two and exponent arithmetic, and conversions between signed machine integers.
  Main definitions: \<open>N_of_monadic\<close>, \<open>snat_eq_monadic\<close>, \<open>split_exp_monadic\<close>,
  \<open>snat_to_slong_monadic\<close>.\<close>

type_synonym pow2_state = "nat \<times> nat"

abbreviation pow2_state_assn where
"pow2_state_assn \<equiv>
  snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"

definition pow2_cond :: "nat \<Rightarrow> pow2_state \<Rightarrow> bool" where
"pow2_cond k st \<equiv> (let (i, _) = st in i < k)"

sepref_register "PR_CONST pow2_cond"
  :: "nat \<Rightarrow> pow2_state \<Rightarrow> bool"

sepref_definition pow2_cond_impl [llvm_inline] is
  "uncurry (RETURN oo pow2_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    pow2_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow2_cond_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow2_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry pow2_cond_impl,
    uncurry (RETURN oo (PR_CONST pow2_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      pow2_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow2_cond_impl.refine
  by (simp add: PR_CONST_def)

definition pow2_body_monadic ::
  "nat \<Rightarrow> pow2_state \<Rightarrow> pow2_state nres" where
"pow2_body_monadic k st \<equiv> doN {
  let (i, n) = st;
  ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (n + n < max_snat LENGTH(gmp_poly_len));
  RETURN (i + 1, n + n)
}"

sepref_register "PR_CONST pow2_body_monadic"
  :: "nat \<Rightarrow> pow2_state \<Rightarrow> pow2_state nres"

sepref_definition pow2_body_impl [llvm_inline] is
  "uncurry pow2_body_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    pow2_state_assn\<^sup>d \<rightarrow>\<^sub>a pow2_state_assn"
  unfolding pow2_body_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow2_body_impl_hnr[sepref_fr_rules]:
  "(uncurry pow2_body_impl,
    uncurry (PR_CONST pow2_body_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      pow2_state_assn\<^sup>d \<rightarrow>\<^sub>a pow2_state_assn"
  using pow2_body_impl.refine
  by (simp add: PR_CONST_def)

definition pow2_monadic :: "nat \<Rightarrow> nat nres" where
"pow2_monadic k \<equiv> doN {
  st \<leftarrow> WHILET
    (\<lambda>st. (PR_CONST pow2_cond) k st)
    (\<lambda>st. (PR_CONST pow2_body_monadic) k st)
    (0, 1);
  let (_, n) = st;
  RETURN n
}"

sepref_register "PR_CONST pow2_monadic" :: "nat \<Rightarrow> nat nres"

sepref_definition pow2_impl [llvm_inline] is
  "pow2_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  unfolding pow2_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow2_impl_hnr[sepref_fr_rules]:
  "(pow2_impl, PR_CONST pow2_monadic) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
      snat_assn' TYPE(gmp_poly_len)"
  using pow2_impl.refine
  by (simp add: PR_CONST_def)

definition N_of_monadic :: "nat \<Rightarrow> nat nres" where
"N_of_monadic e \<equiv> doN {
  k \<leftarrow> (PR_CONST pow2_monadic) e;
  (PR_CONST pow2_monadic) k
}"

sepref_register "PR_CONST N_of_monadic" :: "nat \<Rightarrow> nat nres"

sepref_definition N_of_impl [llvm_inline] is
  "N_of_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  unfolding N_of_monadic_def
  by sepref

lemma N_of_impl_hnr[sepref_fr_rules]:
  "(N_of_impl, PR_CONST N_of_monadic) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
      snat_assn' TYPE(gmp_poly_len)"
  using N_of_impl.refine
  by (simp add: PR_CONST_def)

definition snat_eq_monadic :: "nat \<Rightarrow> nat \<Rightarrow> bool nres" where
"snat_eq_monadic x y \<equiv> RETURN (x = y)"

sepref_register "PR_CONST snat_eq_monadic" :: "nat \<Rightarrow> nat \<Rightarrow> bool nres"

sepref_definition snat_eq_impl [llvm_inline] is
  "uncurry snat_eq_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding snat_eq_monadic_def
  by sepref

lemma snat_eq_impl_hnr[sepref_fr_rules]:
  "(uncurry snat_eq_impl, uncurry (PR_CONST snat_eq_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using snat_eq_impl.refine
  by (simp add: PR_CONST_def)

definition split_exp_monadic :: "nat \<Rightarrow> nat nres" where
"split_exp_monadic e \<equiv> doN {
  if e = 0 then RETURN 1
  else if e = 1 then RETURN 1
  else doN {
    ASSERT (1 \<le> e);
    RETURN (e - 1)
  }
}"

sepref_register "PR_CONST split_exp_monadic" :: "nat \<Rightarrow> nat nres"

sepref_definition split_exp_impl [llvm_inline] is
  "split_exp_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  unfolding split_exp_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma split_exp_impl_hnr[sepref_fr_rules]:
  "(split_exp_impl, PR_CONST split_exp_monadic) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
      snat_assn' TYPE(gmp_poly_len)"
  using split_exp_impl.refine
  by (simp add: PR_CONST_def)


definition snat_to_slong_monadic :: "nat \<Rightarrow> int nres" where
"snat_to_slong_monadic n \<equiv> snat_sint_cast.mop TYPE(gmp_long_len) n"

sepref_register "PR_CONST snat_to_slong_monadic" :: "nat \<Rightarrow> int nres"

sepref_definition snat_to_slong_impl [llvm_inline] is
  "snat_to_slong_monadic" ::
  "[\<lambda>n. slong_bounds (int n)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_slong_assn"
  unfolding snat_to_slong_monadic_def slong_bounds_def
  by sepref

lemma snat_to_slong_impl_hnr[sepref_fr_rules]:
  "(snat_to_slong_impl, PR_CONST snat_to_slong_monadic) \<in>
    [\<lambda>n. slong_bounds (int n)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_slong_assn"
  using snat_to_slong_impl.refine
  by (simp add: PR_CONST_def)

lemma snat_to_slong_impl_hnr_unfolded[sepref_fr_rules]:
  "(snat_to_slong_impl, PR_CONST snat_to_slong_monadic) \<in>
    [\<lambda>n. min_sint LENGTH(gmp_long_len) \<le> int n \<and>
      int n < max_sint LENGTH(gmp_long_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_slong_assn"
  using snat_to_slong_impl.refine
  by (simp add: PR_CONST_def slong_bounds_def)


end
