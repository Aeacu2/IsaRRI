theory Poly_Ops
imports Array
begin

text \<open>Polynomial kernels over the GMP container, refining the \<open>Dsc_Int\<close> list transformations:
  the sign-change fold, \<open>scale_poly_list\<close>, \<open>ruffini_step\<close>, \<open>taylor_shift_list\<close>, the
  fractional Taylor shift, and the ET-Horner count. Each destructive GMP ownership step is
  documented where it is introduced.\<close>

definition sign_step_from_sgn :: "int \<Rightarrow> int \<times> nat \<Rightarrow> int \<times> nat" where
"sign_step_from_sgn s st \<equiv>
  (let (last_s, n) = st in
    if s = 0 then (last_s, n)
    else if last_s = 0 then (s, 0)
    else if s \<noteq> last_s then (s, n + 1)
    else (last_s, n))"

lemma sign_step_from_sgn_correct:
  "sign_step_from_sgn (sgn x) st = sign_step x st"
  by (cases st) (auto simp: sign_step_from_sgn_def sgn_0_0)

lemma sign_step_from_sgn_count_le_Suc:
  "snd (sign_step_from_sgn s (last_s, n)) \<le> Suc n"
  by (auto simp: sign_step_from_sgn_def)

definition sign_step_from_sgn_mop_monadic ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (int \<times> nat) nres" where
"sign_step_from_sgn_mop_monadic s last_s n \<equiv>
  (if s = 0 then RETURN (last_s, n)
   else if last_s = 0 then RETURN (s, 0)
   else if s \<noteq> last_s then RETURN (s, n + 1)
   else RETURN (last_s, n))"

lemma sign_step_from_sgn_mop_monadic_correct[simp]:
  "sign_step_from_sgn_mop_monadic s last_s n =
    RETURN (sign_step_from_sgn s (last_s, n))"
  by (auto simp: sign_step_from_sgn_mop_monadic_def sign_step_from_sgn_def)

sepref_register "PR_CONST sign_step_from_sgn_mop_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (int \<times> nat) nres"

sepref_definition sign_step_from_sgn_impl [llvm_inline] is
  "uncurry2 sign_step_from_sgn_mop_monadic" ::
  "[\<lambda>((s, last_s), n). n + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_sint_assn\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
    gmp_sint_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding sign_step_from_sgn_mop_monadic_def
  apply (annot_sint_const gmp_int_t)
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma sign_step_from_sgn_impl_hnr[sepref_fr_rules]:
  "(uncurry2 sign_step_from_sgn_impl,
    uncurry2 (PR_CONST sign_step_from_sgn_mop_monadic)) \<in>
    [\<lambda>((s, last_s), n). n + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_sint_assn\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_sint_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using sign_step_from_sgn_impl.refine
  by (simp add: PR_CONST_def)

definition sign_changes_init_mop_monadic :: "(nat \<times> int \<times> nat) nres" where
"sign_changes_init_mop_monadic \<equiv> RETURN (0, 0, 0)"

sepref_definition sign_changes_init_impl [llvm_inline] is
  "uncurry0 sign_changes_init_mop_monadic" ::
  "unit_assn\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_sint_assn \<times>\<^sub>a
      snat_assn' TYPE(gmp_poly_len)"
  unfolding sign_changes_init_mop_monadic_def
  apply (annot_sint_const gmp_int_t)
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemmas [sepref_fr_rules] = sign_changes_init_impl.refine

abbreviation sign_changes_state_assn where
"sign_changes_state_assn \<equiv>
  snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_sint_assn \<times>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"

lemma dsc_mk_free_invalid_prod[sepref_frame_free_rules]:
  "MK_FREE (invalid_assn A \<times>\<^sub>a invalid_assn B) (\<lambda>_. Mreturn ())"
  apply (rule mk_free_is_pure)
  apply (rule pure_prod)
   apply (rule invalid_pure)
  apply (rule invalid_pure)
  done

definition sign_changes_cond :: "nat \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> bool" where
"sign_changes_cond len st \<equiv>
  (let (i, last_s, cnt) = st in i < len)"

sepref_register "PR_CONST sign_changes_cond"
  :: "nat \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> bool"

sepref_definition sign_changes_cond_impl [llvm_inline] is
  "uncurry (RETURN oo sign_changes_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    sign_changes_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding sign_changes_cond_def
  unfolding Let_def
  by sepref

lemma sign_changes_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry sign_changes_cond_impl,
    uncurry (RETURN oo (PR_CONST sign_changes_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      sign_changes_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using sign_changes_cond_impl.refine
  by (simp add: PR_CONST_def)

definition sign_changes_body_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> (nat \<times> int \<times> nat) nres" where
"sign_changes_body_mop_monadic xs len st \<equiv> doN {
  let (i, last_s, cnt) = st;
  ASSERT (len = length xs);
  ASSERT (length xs < max_snat LENGTH(gmp_poly_len));
  ASSERT (i < len);
  ASSERT (i < length xs);
  ASSERT (cnt \<le> i);
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs i;
  ASSERT (cnt + 1 < max_snat LENGTH(gmp_poly_len));
  (last_s, cnt) \<leftarrow> (PR_CONST sign_step_from_sgn_mop_monadic) s last_s cnt;
  ASSERT (i < len);
  RETURN (i + 1, last_s, cnt)
}"

sepref_register "PR_CONST sign_changes_body_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> (nat \<times> int \<times> nat) nres"

sepref_definition sign_changes_body_impl [llvm_inline] is
  "uncurry2 sign_changes_body_mop_monadic" ::
  "[\<lambda>((xs, len), _). len = length xs \<and>
      length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      sign_changes_state_assn\<^sup>d \<rightarrow>
      sign_changes_state_assn"
  unfolding sign_changes_body_mop_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemmas [sepref_fr_rules] = sign_changes_body_impl.refine

lemma sign_changes_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 sign_changes_body_impl,
    uncurry2 (PR_CONST sign_changes_body_mop_monadic)) \<in>
    [\<lambda>((xs, len), _). len = length xs \<and>
      length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        sign_changes_state_assn\<^sup>d \<rightarrow>
        sign_changes_state_assn"
  using sign_changes_body_impl.refine
  by (simp add: PR_CONST_def)

definition sign_changes_result_mop_monadic :: "nat \<times> int \<times> nat \<Rightarrow> nat nres" where
"sign_changes_result_mop_monadic st \<equiv>
  (let (i, last_s, cnt) = st in RETURN cnt)"

sepref_register "PR_CONST sign_changes_result_mop_monadic"
  :: "nat \<times> int \<times> nat \<Rightarrow> nat nres"

sepref_definition sign_changes_result_impl [llvm_inline] is
  "sign_changes_result_mop_monadic" ::
  "sign_changes_state_assn\<^sup>d \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  unfolding sign_changes_result_mop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma sign_changes_result_impl_hnr[sepref_fr_rules]:
  "(sign_changes_result_impl,
    PR_CONST sign_changes_result_mop_monadic) \<in>
    sign_changes_state_assn\<^sup>d \<rightarrow>\<^sub>a
      snat_assn' TYPE(gmp_poly_len)"
  using sign_changes_result_impl.refine
  by (simp add: PR_CONST_def)

definition sign_changes_prefix_state :: "int list \<Rightarrow> nat \<Rightarrow> int \<times> nat" where
"sign_changes_prefix_state xs i \<equiv> fold sign_step (take i xs) (0, 0)"

lemma sign_changes_prefix_state_0[simp]:
  "sign_changes_prefix_state xs 0 = (0, 0)"
  by (simp add: sign_changes_prefix_state_def)

lemma sign_changes_prefix_state_Suc:
  assumes "i < length xs"
  shows "sign_step_from_sgn (sgn (xs ! i))
      (sign_changes_prefix_state xs i)
    = sign_changes_prefix_state xs (i + 1)"
  using assms
  by (simp add: sign_changes_prefix_state_def
    sign_step_from_sgn_correct take_Suc_conv_app_nth)

lemma sign_changes_prefix_state_length:
  "snd (sign_changes_prefix_state xs (length xs)) = sign_changes_fold xs"
  by (simp add: sign_changes_prefix_state_def sign_changes_fold_def)

lemma sign_changes_prefix_state_count_le:
  assumes "i \<le> length xs"
  shows "snd (sign_changes_prefix_state xs i) \<le> i"
  using assms
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then have i_lt: "i < length xs" by simp
  have step:
    "sign_changes_prefix_state xs (Suc i) =
      sign_step_from_sgn (sgn (xs ! i))
        (sign_changes_prefix_state xs i)"
    using sign_changes_prefix_state_Suc[OF i_lt]
    by simp
  obtain last_s n where st:
    "sign_changes_prefix_state xs i = (last_s, n)"
    by (cases "sign_changes_prefix_state xs i")
  have "snd (sign_changes_prefix_state xs (Suc i)) \<le> Suc n"
    unfolding step st
    by (rule sign_step_from_sgn_count_le_Suc)
  also have "... \<le> Suc i"
    using Suc.IH Suc.prems st by simp
  finally show ?case .
qed

lemma sign_changes_prefix_state_count_le_tuple[dest]:
  assumes "i \<le> length xs"
    and "sign_changes_prefix_state xs i = (last_s, n)"
  shows "n \<le> i"
  using sign_changes_prefix_state_count_le[OF assms(1)] assms(2)
  by simp

lemma sign_changes_loop_step_inv:
  fixes i :: nat
    and last_s :: int
    and cnt :: nat
  assumes "i < length xs"
    and "(last_s, cnt) = sign_changes_prefix_state xs i"
  shows "(case sign_step_from_sgn (sgn (xs ! i)) (last_s, cnt) of
      (last_s', cnt') \<Rightarrow>
        (last_s', cnt') = sign_changes_prefix_state xs (i + 1) \<and>
        cnt' \<le> i + 1)"
proof -
  have step:
    "sign_step_from_sgn (sgn (xs ! i)) (last_s, cnt) =
      sign_changes_prefix_state xs (i + 1)"
    using assms sign_changes_prefix_state_Suc by simp
  then show ?thesis
    using sign_changes_prefix_state_count_le[of "i + 1" xs] assms(1)
    by (cases "sign_changes_prefix_state xs (i + 1)") auto
qed

lemma sign_changes_step_prefix_state_eq:
  fixes i :: nat
    and last_s :: int
    and cnt :: nat
  assumes "i < length xs"
    and "sign_step_from_sgn (sgn (xs ! i))
      (sign_changes_prefix_state xs i) = (last_s, cnt)"
  shows "(last_s, cnt) = sign_changes_prefix_state xs (Suc i)"
  using assms sign_changes_prefix_state_Suc[of i xs]
  by simp

lemma sign_changes_step_prefix_state_count_le:
  fixes i :: nat
    and last_s :: int
    and cnt :: nat
  assumes "i < length xs"
    and "sign_step_from_sgn (sgn (xs ! i))
      (sign_changes_prefix_state xs i) = (last_s, cnt)"
  shows "cnt \<le> Suc i"
proof -
  have eq: "(last_s, cnt) = sign_changes_prefix_state xs (Suc i)"
    using sign_changes_step_prefix_state_eq[OF assms] .
  have "Suc i \<le> length xs"
    using assms(1) by simp
  then have "snd (sign_changes_prefix_state xs (Suc i)) \<le> Suc i"
    by (rule sign_changes_prefix_state_count_le)
  then show ?thesis
    using eq
    by (cases "sign_changes_prefix_state xs (Suc i)") auto
qed

definition poly_sign_changes_monadic :: "gmp_poly \<Rightarrow> nat nres" where
"poly_sign_changes_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  init \<leftarrow> sign_changes_init_mop_monadic;
  st \<leftarrow> WHILET (\<lambda>st. (PR_CONST sign_changes_cond) len st)
    (\<lambda>st. (PR_CONST sign_changes_body_mop_monadic) xs len st) init;
  (PR_CONST sign_changes_result_mop_monadic) st
}"

lemma poly_sign_changes_monadic_correct:
  assumes "length xs < max_snat LENGTH(gmp_poly_len)"
  shows "poly_sign_changes_monadic xs \<le> RETURN (sign_changes_fold xs)"
  using assms
  unfolding poly_sign_changes_monadic_def
    poly_length_monadic_def poly_coeff_sgn_monadic_def
    sign_changes_init_mop_monadic_def sign_changes_cond_def
    sign_changes_body_mop_monadic_def sign_changes_result_mop_monadic_def PR_CONST_def
  apply (refine_vcg WHILET_rule[
    where I="\<lambda>(i, last_s, cnt).
      i \<le> length xs \<and>
      (last_s, cnt) = sign_changes_prefix_state xs i \<and>
      cnt \<le> i"
      and R="measure (\<lambda>(i, _::int, _::nat). length xs - i)"])
  subgoal by simp
  subgoal by simp
  subgoal by auto
  subgoal by auto
  subgoal by (auto split: prod.splits)
  subgoal by (auto split: prod.splits)
  subgoal by (auto split: prod.splits)
  subgoal by linarith
  subgoal
    by (auto dest: sign_changes_step_prefix_state_eq
      sign_changes_step_prefix_state_count_le split: prod.splits)
  subgoal
    using sign_changes_prefix_state_length[of xs]
    by (cases "sign_changes_prefix_state xs (length xs)") auto
  done

sepref_register "PR_CONST poly_sign_changes_monadic"
  :: "gmp_poly \<Rightarrow> nat nres"

sepref_definition poly_sign_changes_impl [llvm_inline] is
  "poly_sign_changes_monadic" ::
  "[\<lambda>xs. length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding poly_sign_changes_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemma poly_sign_changes_impl_hnr[sepref_fr_rules]:
  "(poly_sign_changes_impl, PR_CONST poly_sign_changes_monadic) \<in>
    [\<lambda>xs. length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using poly_sign_changes_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Scale polynomial coefficients\<close>

lemma dsc_scale_poly_list_aux_snoc:
  "scale_poly_list_aux c acc (xs @ [x]) =
    scale_poly_list_aux c acc xs @ [x * acc * c ^ length xs]"
  by (induction xs arbitrary: acc) (simp_all add: algebra_simps)

lemma dsc_snat_rel_suc:
  fixes ii :: "'a::len2 word"
  assumes "(ii, i) \<in> snat_rel"
    and "Suc i < max_snat LENGTH('a)"
  shows "(ii + 1, Suc i) \<in> snat_rel"
  using assms unfolding snat_rel_def snat.rel_def in_br_conv
  by (auto simp: snat_eq_unat snat_invar_alt max_snat_def unat_word_ariths)

abbreviation poly_scale_state_assn where
"poly_scale_state_assn \<equiv>
  gmp_poly_assn \<times>\<^sub>a mpzb_assn"

definition poly_scale_body_mop_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow>
    (gmp_poly \<times> int) nres" where
"poly_scale_body_mop_monadic c xs i dst acc \<equiv> doN {
  ASSERT (i < length xs);
  coeff \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs i;
  coeff \<leftarrow> (PR_CONST mpz_mul.amop_r1) coeff acc;
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_push_coeff_monadic) dst coeff;
  acc \<leftarrow> (PR_CONST mpz_mul.amop_r1) acc c;
  RETURN (dst, acc)
}"

sepref_register "PR_CONST poly_scale_body_mop_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow>
    (gmp_poly \<times> int) nres"

sepref_definition poly_scale_body_impl [llvm_inline] is
  "uncurry4 poly_scale_body_mop_monadic" ::
  "[\<lambda>((((c, xs), i), dst), acc).
      i < length xs \<and>
      length dst + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
    poly_scale_state_assn"
  unfolding poly_scale_body_mop_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  apply (rule entails_refl)
  apply (simp add: CP_cond_def)
  done

lemmas [sepref_fr_rules] =
  poly_scale_body_impl.refine

lemma poly_scale_body_impl_hnr[sepref_fr_rules]:
  "(uncurry4 poly_scale_body_impl,
    uncurry4 (PR_CONST poly_scale_body_mop_monadic)) \<in>
    [\<lambda>((((c, xs), i), dst), acc).
      i < length xs \<and>
      length dst + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      poly_scale_state_assn"
  using poly_scale_body_impl.refine
  by (simp add: PR_CONST_def)

abbreviation poly_scale_loop_state_assn where
"poly_scale_loop_state_assn \<equiv>
  snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
    gmp_poly_assn \<times>\<^sub>a mpzb_assn"

definition poly_scale_cond ::
  "nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> bool" where
"poly_scale_cond len st \<equiv>
  (let (i, dst, acc) = st in i < len)"

sepref_register "PR_CONST poly_scale_cond"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> bool"

sepref_definition poly_scale_cond_impl [llvm_inline] is
  "uncurry (RETURN oo poly_scale_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    poly_scale_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding poly_scale_cond_def
  unfolding Let_def
  by sepref

lemma poly_scale_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_scale_cond_impl,
    uncurry (RETURN oo (PR_CONST poly_scale_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      poly_scale_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using poly_scale_cond_impl.refine
  by (simp add: PR_CONST_def)

definition poly_scale_loop_body_mop_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow>
    (nat \<times> gmp_poly \<times> int) nres" where
"poly_scale_loop_body_mop_monadic c xs len st \<equiv> doN {
  let (i, dst, acc) = st;
  ASSERT (i < len);
  ASSERT (i < length xs);
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  (dst, acc) \<leftarrow> (PR_CONST poly_scale_body_mop_monadic) c xs i dst acc;
  ASSERT (i < len);
  RETURN (i + 1, dst, acc)
}"

sepref_register "PR_CONST poly_scale_loop_body_mop_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow>
    (nat \<times> gmp_poly \<times> int) nres"

definition [llvm_code, llvm_inline]:
  "poly_scale_loop_body_impl c xs len st \<equiv> doM {
    let (i, dst, acc) = st;
    (dst, acc) \<leftarrow> poly_scale_body_impl c xs i dst acc;
    Mreturn (i + 1, dst, acc)
  }"

lemma poly_scale_loop_body_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_scale_loop_body_impl,
    uncurry3 (PR_CONST poly_scale_loop_body_mop_monadic)) \<in>
    [\<lambda>(((c, xs), len), _).
      len = length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        poly_scale_loop_state_assn\<^sup>d \<rightarrow>
      poly_scale_loop_state_assn"
  unfolding poly_scale_loop_body_impl_def
    poly_scale_loop_body_mop_monadic_def PR_CONST_def
  supply [vcg_rules] =
    poly_scale_body_impl.refine[to_hnr, THEN hn_refineD,
      unfolded hn_ctxt_def invalid_assn_def pure_def, simplified]
  apply sepref_to_hoare
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps)
  subgoal for a aa b ab ac ad ba bb bia bba ae af bc ag ai ah aj bd be ak bf s
    apply (rule exI[where x="Suc a"])
    apply (intro conjI)
     apply (rule dsc_snat_rel_suc)
      apply assumption
     apply simp
    apply (rule exI[where x=ak])
    apply (rule exI[where x=bf])
    apply (intro conjI)
     apply (simp add: refine_pw_simps pw_le_iff)
    apply assumption
    done
  done

definition poly_scale_result_mop_monadic ::
  "nat \<times> gmp_poly \<times> int \<Rightarrow> (gmp_poly \<times> int) nres" where
"poly_scale_result_mop_monadic st \<equiv>
  (let (i, dst, acc) = st in RETURN (dst, acc))"

sepref_register "PR_CONST poly_scale_result_mop_monadic"
  :: "nat \<times> gmp_poly \<times> int \<Rightarrow> (gmp_poly \<times> int) nres"

sepref_definition poly_scale_result_impl [llvm_inline] is
  "poly_scale_result_mop_monadic" ::
  "poly_scale_loop_state_assn\<^sup>d \<rightarrow>\<^sub>a
    poly_scale_state_assn"
  unfolding poly_scale_result_mop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_scale_result_impl_hnr[sepref_fr_rules]:
  "(poly_scale_result_impl,
    PR_CONST poly_scale_result_mop_monadic) \<in>
    poly_scale_loop_state_assn\<^sup>d \<rightarrow>\<^sub>a
      poly_scale_state_assn"
  using poly_scale_result_impl.refine
  by (simp add: PR_CONST_def)

definition poly_scale_with_acc_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> (gmp_poly \<times> int) nres" where
"poly_scale_with_acc_monadic c xs acc0 \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (len + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_empty_sz_monadic) len;
  init \<leftarrow> RETURN (0, dst, acc0);
  st \<leftarrow> WHILET (\<lambda>st. (PR_CONST poly_scale_cond) len st)
    (\<lambda>st. (PR_CONST poly_scale_loop_body_mop_monadic) c xs len st) init;
  (PR_CONST poly_scale_result_mop_monadic) st
}"

lemma poly_scale_with_acc_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_scale_with_acc_monadic c xs acc0
    \<le> RETURN (scale_poly_list_aux c acc0 xs, acc0 * c ^ length xs)"
  using assms
  unfolding poly_scale_with_acc_monadic_def
    poly_scale_cond_def
    poly_scale_loop_body_mop_monadic_def
    poly_scale_body_mop_monadic_def
    poly_scale_result_mop_monadic_def
    poly_length_monadic_def poly_empty_sz_monadic_def
    poly_copy_coeff_monadic_def poly_push_coeff_monadic_def
    mpz_mul.amop_r1_def PR_CONST_def
  apply (refine_vcg WHILET_rule[
    where I="\<lambda>(i, dst, acc).
      i \<le> length xs \<and>
      dst = scale_poly_list_aux c acc0 (take i xs) \<and>
      acc = acc0 * c ^ i"
      and R="measure (\<lambda>(i, _::gmp_poly, _::int). length xs - i)"])
  apply (auto simp: take_Suc_conv_app_nth
    scale_poly_list_aux_enumerate dsc_scale_poly_list_aux_snoc
    algebra_simps split: prod.splits)
  done

definition poly_scale_monadic :: "int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_scale_monadic c xs \<equiv> doN {
  acc \<leftarrow> RETURN (mpz_from_int 1);
  (dst, acc) \<leftarrow> (PR_CONST poly_scale_with_acc_monadic) c xs acc;
  (PR_CONST mpzb_discard_monadic) acc;
  RETURN dst
}"

lemma poly_scale_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_scale_monadic c xs \<le> RETURN (scale_poly_list c xs)"
  using poly_scale_with_acc_correct[OF assms, of c 1]
  unfolding poly_scale_monadic_def scale_poly_list_def
    mpzb_discard_monadic_def mpz_from_int_def PR_CONST_def
  apply refine_vcg
  apply (rule order_trans)
   apply assumption
  apply (simp add: pw_le_iff refine_pw_simps)
  done

sepref_register "PR_CONST poly_scale_with_acc_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> (gmp_poly \<times> int) nres"

sepref_definition poly_scale_with_acc_impl [llvm_inline] is
  "uncurry2 poly_scale_with_acc_monadic" ::
  "[\<lambda>((c, xs), _). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      poly_scale_state_assn"
  unfolding poly_scale_with_acc_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemmas [sepref_fr_rules] =
  poly_scale_with_acc_impl.refine

lemma poly_scale_with_acc_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_scale_with_acc_impl,
    uncurry2 (PR_CONST poly_scale_with_acc_monadic)) \<in>
    [\<lambda>((c, xs), _). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        poly_scale_state_assn"
  using poly_scale_with_acc_impl.refine
  by (simp add: PR_CONST_def)

sepref_register "PR_CONST poly_scale_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_scale_impl [llvm_inline] is
  "uncurry poly_scale_monadic" ::
  "[\<lambda>(c, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding poly_scale_monadic_def
  apply (annot_uint_const "TYPE(gmp_long_len)")
  by sepref

lemma poly_scale_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_scale_impl,
    uncurry (PR_CONST poly_scale_monadic)) \<in>
    [\<lambda>(c, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using poly_scale_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Ruffini step\<close>

abbreviation poly_ruffini_state_assn where
"poly_ruffini_state_assn \<equiv>
  gmp_poly_assn \<times>\<^sub>a mpzb_assn"

definition poly_ruffini_body_mop_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow>
    (gmp_poly \<times> int) nres" where
"poly_ruffini_body_mop_monadic c qs i dst prev \<equiv> doN {
  ASSERT (i < length qs);
  curr \<leftarrow> (PR_CONST poly_copy_coeff_monadic) qs i;
  prod \<leftarrow> RETURN (c * curr);
  prod \<leftarrow> (PR_CONST mpz_add.amop_r1) prod prev;
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_push_coeff_monadic) dst prod;
  (PR_CONST mpzb_discard_monadic) prev;
  RETURN (dst, curr)
}"

sepref_register "PR_CONST poly_ruffini_body_mop_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow>
    (gmp_poly \<times> int) nres"

sepref_definition poly_ruffini_body_impl [llvm_inline] is
  "uncurry4 poly_ruffini_body_mop_monadic" ::
  "[\<lambda>((((c, qs), i), dst), _).
      i < length qs \<and>
      length dst + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
    poly_ruffini_state_assn"
  unfolding poly_ruffini_body_mop_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemmas [sepref_fr_rules] =
  poly_ruffini_body_impl.refine

lemma poly_ruffini_body_impl_hnr[sepref_fr_rules]:
  "(uncurry4 poly_ruffini_body_impl,
    uncurry4 (PR_CONST poly_ruffini_body_mop_monadic)) \<in>
    [\<lambda>((((c, qs), i), dst), _).
      i < length qs \<and>
      length dst + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      poly_ruffini_state_assn"
  using poly_ruffini_body_impl.refine
  by (simp add: PR_CONST_def)

abbreviation poly_ruffini_loop_state_assn where
"poly_ruffini_loop_state_assn \<equiv>
  snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
    gmp_poly_assn \<times>\<^sub>a mpzb_assn"

definition poly_ruffini_cond ::
  "nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> bool" where
"poly_ruffini_cond len st \<equiv>
  (let (i, dst, prev) = st in i < len)"

sepref_register "PR_CONST poly_ruffini_cond"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> bool"

sepref_definition poly_ruffini_cond_impl [llvm_inline] is
  "uncurry (RETURN oo poly_ruffini_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    poly_ruffini_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding poly_ruffini_cond_def
  unfolding Let_def
  by sepref

lemma poly_ruffini_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_ruffini_cond_impl,
    uncurry (RETURN oo (PR_CONST poly_ruffini_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      poly_ruffini_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using poly_ruffini_cond_impl.refine
  by (simp add: PR_CONST_def)

definition poly_ruffini_loop_body_mop_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow>
    (nat \<times> gmp_poly \<times> int) nres" where
"poly_ruffini_loop_body_mop_monadic c qs len st \<equiv> doN {
  let (i, dst, prev) = st;
  ASSERT (i < len);
  ASSERT (i < length qs);
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  (dst, prev) \<leftarrow> (PR_CONST poly_ruffini_body_mop_monadic) c qs i dst prev;
  ASSERT (i < len);
  RETURN (i + 1, dst, prev)
}"

sepref_register "PR_CONST poly_ruffini_loop_body_mop_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow>
    (nat \<times> gmp_poly \<times> int) nres"

definition [llvm_code, llvm_inline]:
  "poly_ruffini_loop_body_impl c qs len st \<equiv> doM {
    let (i, dst, prev) = st;
    (dst, prev) \<leftarrow> poly_ruffini_body_impl c qs i dst prev;
    Mreturn (i + 1, dst, prev)
  }"

lemma poly_ruffini_loop_body_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_ruffini_loop_body_impl,
    uncurry3 (PR_CONST poly_ruffini_loop_body_mop_monadic)) \<in>
    [\<lambda>(((c, qs), len), _).
      len = length qs \<and>
      length qs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        poly_ruffini_loop_state_assn\<^sup>d \<rightarrow>
      poly_ruffini_loop_state_assn"
  unfolding poly_ruffini_loop_body_impl_def
    poly_ruffini_loop_body_mop_monadic_def PR_CONST_def
  supply [vcg_rules] =
    poly_ruffini_body_impl.refine[to_hnr, THEN hn_refineD,
      unfolded hn_ctxt_def invalid_assn_def pure_def, simplified]
  apply sepref_to_hoare
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps)
  subgoal for a aa b ab ac ad ba bb bia bba ae af bc ag ai ah aj bd be ak bf s
    apply (rule exI[where x="Suc a"])
    apply (intro conjI)
     apply (rule dsc_snat_rel_suc)
      apply assumption
     apply simp
    apply (rule exI[where x=ak])
    apply (rule exI[where x=bf])
    apply (intro conjI)
     apply (simp add: refine_pw_simps pw_le_iff)
    apply assumption
    done
  done

definition poly_ruffini_result_mop_monadic ::
  "nat \<times> gmp_poly \<times> int \<Rightarrow> gmp_poly nres" where
"poly_ruffini_result_mop_monadic st \<equiv> doN {
  let (i, dst, prev) = st;
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_push_coeff_monadic) dst prev
}"

sepref_register "PR_CONST poly_ruffini_result_mop_monadic"
  :: "nat \<times> gmp_poly \<times> int \<Rightarrow> gmp_poly nres"

sepref_definition poly_ruffini_result_impl [llvm_inline] is
  "poly_ruffini_result_mop_monadic" ::
  "[\<lambda>(_, dst, _). length dst + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    poly_ruffini_loop_state_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_ruffini_result_mop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_ruffini_result_impl_hnr[sepref_fr_rules]:
  "(poly_ruffini_result_impl,
    PR_CONST poly_ruffini_result_mop_monadic) \<in>
    [\<lambda>(_, dst, _). length dst + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      poly_ruffini_loop_state_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_ruffini_result_impl.refine
  by (simp add: PR_CONST_def)

definition poly_ruffini_with_prev_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> gmp_poly nres" where
"poly_ruffini_with_prev_monadic c qs prev0 \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) qs;
  ASSERT (len = length qs);
  ASSERT (len + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_empty_sz_monadic) (len + 1);
  init \<leftarrow> RETURN (0, dst, prev0);
  st \<leftarrow> WHILET (\<lambda>st. (PR_CONST poly_ruffini_cond) len st)
    (\<lambda>st. (PR_CONST poly_ruffini_loop_body_mop_monadic) c qs len st) init;
  ASSERT (case st of (_, dst, _) \<Rightarrow>
    length dst + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_ruffini_result_mop_monadic) st
}"

lemma dsc_ruffini_step_drop_Suc:
  assumes "i < length qs"
  shows "ruffini_step c prev (drop i qs) =
    (prev + c * (qs ! i)) #
      ruffini_step c (qs ! i) (drop (Suc i) qs)"
proof -
  have "drop i qs = qs ! i # drop (Suc i) qs"
    using assms by (simp add: Cons_nth_drop_Suc)
  then show ?thesis by simp
qed

lemma poly_ruffini_with_prev_monadic_correct:
  assumes "length qs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_ruffini_with_prev_monadic c qs prev0
    \<le> RETURN (ruffini_step c prev0 qs)"
  using assms
  unfolding poly_ruffini_with_prev_monadic_def
    poly_ruffini_cond_def
    poly_ruffini_loop_body_mop_monadic_def
    poly_ruffini_body_mop_monadic_def
    poly_ruffini_result_mop_monadic_def
    poly_length_monadic_def poly_empty_sz_monadic_def
    poly_copy_coeff_monadic_def poly_push_coeff_monadic_def
    mpzb_discard_monadic_def mpz_add.amop_r1_def PR_CONST_def
  apply (refine_vcg WHILET_rule[
    where I="\<lambda>(i, dst, prev).
      i \<le> length qs \<and>
      length dst = i \<and>
      dst @ ruffini_step c prev (drop i qs) = ruffini_step c prev0 qs"
      and R="measure (\<lambda>(i, _::gmp_poly, _::int). length qs - i)"])
  apply (auto simp: algebra_simps dsc_ruffini_step_drop_Suc split: prod.splits)
  done

sepref_register "PR_CONST poly_ruffini_with_prev_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> gmp_poly nres"

sepref_definition poly_ruffini_with_prev_impl [llvm_inline] is
  "uncurry2 poly_ruffini_with_prev_monadic" ::
  "[\<lambda>((c, qs), _). length qs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      gmp_poly_assn"
  unfolding poly_ruffini_with_prev_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemma poly_ruffini_with_prev_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_ruffini_with_prev_impl,
    uncurry2 (PR_CONST poly_ruffini_with_prev_monadic)) \<in>
    [\<lambda>((c, qs), _). length qs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        gmp_poly_assn"
  using poly_ruffini_with_prev_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Taylor shift list\<close>

abbreviation poly_taylor_loop_state_assn where
"poly_taylor_loop_state_assn \<equiv>
  snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"

definition poly_taylor_step_mop_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_poly nres" where
"poly_taylor_step_mop_monadic c xs len i acc \<equiv> doN {
  ASSERT (len = length xs);
  ASSERT (i < len);
  ASSERT (i + 1 \<le> len);
  ASSERT (length acc + 1 < max_snat LENGTH(gmp_poly_len));
  let idx = len - (i + 1);
  ASSERT (idx < length xs);
  a \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs idx;
  acc' \<leftarrow> (PR_CONST poly_ruffini_with_prev_monadic) c acc a;
  (PR_CONST poly_free_monadic) acc;
  RETURN acc'
}"

sepref_register "PR_CONST poly_taylor_step_mop_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_poly nres"

sepref_definition poly_taylor_step_impl [llvm_inline] is
  "uncurry4 poly_taylor_step_mop_monadic" ::
  "[\<lambda>((((c, xs), len), i), acc).
      len = length xs \<and>
      i < len \<and>
      length acc + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_taylor_step_mop_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemmas [sepref_fr_rules] =
  poly_taylor_step_impl.refine

lemma poly_taylor_step_impl_hnr[sepref_fr_rules]:
  "(uncurry4 poly_taylor_step_impl,
    uncurry4 (PR_CONST poly_taylor_step_mop_monadic)) \<in>
    [\<lambda>((((c, xs), len), i), acc).
      len = length xs \<and>
      i < len \<and>
      length acc + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_taylor_step_impl.refine
  by (simp add: PR_CONST_def)

lemma poly_taylor_step_mop_monadic_correct[refine_vcg]:
  assumes "len = length xs"
    and "i < len"
    and "length acc + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_taylor_step_mop_monadic c xs len i acc
    \<le> RETURN (ruffini_step c (xs ! (len - Suc i)) acc)"
  using assms
  unfolding poly_taylor_step_mop_monadic_def
    poly_copy_coeff_monadic_def PR_CONST_def
  apply refine_vcg
  apply simp_all
  subgoal
    apply (rule order_trans)
     apply (rule poly_ruffini_with_prev_monadic_correct)
     apply simp
    apply (clarsimp simp: pw_le_iff refine_pw_simps)
    done
  done

lemma poly_taylor_step_mop_monadic_invar[refine_vcg]:
  assumes "len = length xs"
    and "i < len"
    and "length acc = i"
    and "len + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_taylor_step_mop_monadic c xs len i acc
    \<le> SPEC (\<lambda>acc'.
      acc' = ruffini_step c (xs ! (len - Suc i)) acc \<and>
      length acc' = Suc i \<and>
      len - Suc i < len - i)"
  apply (rule order_trans)
   apply (rule poly_taylor_step_mop_monadic_correct)
     using assms apply simp_all
  done

definition poly_taylor_cond ::
  "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool" where
"poly_taylor_cond len st \<equiv>
  (let (i, acc) = st in i < len)"

sepref_register "PR_CONST poly_taylor_cond"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool"

sepref_definition poly_taylor_cond_impl [llvm_inline] is
  "uncurry (RETURN oo poly_taylor_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    poly_taylor_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding poly_taylor_cond_def
  unfolding Let_def
  by sepref

lemma poly_taylor_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_taylor_cond_impl,
    uncurry (RETURN oo (PR_CONST poly_taylor_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      poly_taylor_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using poly_taylor_cond_impl.refine
  by (simp add: PR_CONST_def)

definition poly_taylor_loop_body_mop_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow>
    (nat \<times> gmp_poly) nres" where
"poly_taylor_loop_body_mop_monadic c xs len st \<equiv> doN {
  let (i, acc) = st;
  ASSERT (i < len);
  ASSERT (len = length xs);
  ASSERT (length acc + 1 < max_snat LENGTH(gmp_poly_len));
  acc \<leftarrow> (PR_CONST poly_taylor_step_mop_monadic) c xs len i acc;
  ASSERT (i < len);
  RETURN (i + 1, acc)
}"

sepref_register "PR_CONST poly_taylor_loop_body_mop_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow>
    (nat \<times> gmp_poly) nres"

definition [llvm_code, llvm_inline]:
  "poly_taylor_loop_body_impl c xs len st \<equiv> doM {
    let (i, acc) = st;
    acc \<leftarrow> poly_taylor_step_impl c xs len i acc;
    Mreturn (i + 1, acc)
  }"

lemma poly_taylor_loop_body_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_taylor_loop_body_impl,
    uncurry3 (PR_CONST poly_taylor_loop_body_mop_monadic)) \<in>
    [\<lambda>(((c, xs), len), _).
      len = length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        poly_taylor_loop_state_assn\<^sup>d \<rightarrow>
      poly_taylor_loop_state_assn"
  unfolding poly_taylor_loop_body_impl_def
    poly_taylor_loop_body_mop_monadic_def PR_CONST_def
  supply [vcg_rules] =
    poly_taylor_step_impl.refine[to_hnr, THEN hn_refineD,
      unfolded hn_ctxt_def invalid_assn_def pure_def, simplified]
  apply sepref_to_hoare
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps)
  subgoal for a aa b ab ac ad ba bb bia bba ae af bc ag ai x s
    apply (rule exI[where x="Suc a"])
    apply (intro conjI)
     apply (rule dsc_snat_rel_suc)
      apply assumption
     apply simp
    apply (rule exI[where x=s])
    apply (intro conjI)
     apply (simp add: refine_pw_simps pw_le_iff)
    apply assumption
    done
  done

definition poly_taylor_result_mop_monadic ::
  "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_taylor_result_mop_monadic st \<equiv>
  (let (i, acc) = st in RETURN acc)"

sepref_register "PR_CONST poly_taylor_result_mop_monadic"
  :: "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_taylor_result_impl [llvm_inline] is
  "poly_taylor_result_mop_monadic" ::
  "poly_taylor_loop_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  unfolding poly_taylor_result_mop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_taylor_result_impl_hnr[sepref_fr_rules]:
  "(poly_taylor_result_impl,
    PR_CONST poly_taylor_result_mop_monadic) \<in>
    poly_taylor_loop_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  using poly_taylor_result_impl.refine
  by (simp add: PR_CONST_def)

lemma dsc_taylor_shift_list_drop_step:
  assumes "i < length xs"
  shows "taylor_shift_list c (drop (length xs - Suc i) xs) =
    ruffini_step c (xs ! (length xs - Suc i))
      (taylor_shift_list c (drop (length xs - i) xs))"
proof -
  let ?idx = "length xs - Suc i"
  have idx_lt: "?idx < length xs"
    using assms by simp
  have drop_eq: "drop ?idx xs = xs ! ?idx # drop (Suc ?idx) xs"
    using idx_lt by (simp add: Cons_nth_drop_Suc)
  have "Suc ?idx = length xs - i"
    using assms by simp
  then show ?thesis
    by (simp add: drop_eq)
qed

definition poly_taylor_shift_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_taylor_shift_monadic c xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (len + 1 < max_snat LENGTH(gmp_poly_len));
  acc \<leftarrow> (PR_CONST poly_empty_sz_monadic) len;
  init \<leftarrow> RETURN (0, acc);
  st \<leftarrow> WHILET (\<lambda>st. (PR_CONST poly_taylor_cond) len st)
    (\<lambda>st. (PR_CONST poly_taylor_loop_body_mop_monadic) c xs len st) init;
  (PR_CONST poly_taylor_result_mop_monadic) st
}"

lemma poly_taylor_shift_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_taylor_shift_monadic c xs
    \<le> RETURN (taylor_shift_list c xs)"
  using assms
  unfolding poly_taylor_shift_monadic_def
    poly_taylor_cond_def
    poly_taylor_loop_body_mop_monadic_def
    poly_taylor_result_mop_monadic_def
    poly_length_monadic_def poly_empty_sz_monadic_def
    PR_CONST_def
  apply (refine_vcg WHILET_rule[
    where I="\<lambda>(i, acc).
      i \<le> length xs \<and>
      length acc = i \<and>
      acc = taylor_shift_list c (drop (length xs - i) xs)"
      and R="measure (\<lambda>(i, _::gmp_poly). length xs - i)"])
  apply (auto simp: dsc_taylor_shift_list_drop_step split: prod.splits)
  done

sepref_register "PR_CONST poly_taylor_shift_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_taylor_shift_impl [llvm_inline] is
  "uncurry poly_taylor_shift_monadic" ::
  "[\<lambda>(c, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding poly_taylor_shift_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemma poly_taylor_shift_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_taylor_shift_impl,
    uncurry (PR_CONST poly_taylor_shift_monadic)) \<in>
    [\<lambda>(c, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using poly_taylor_shift_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Taylor shift by one\<close>

definition poly_ruffini_one_body_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow>
    (gmp_poly \<times> int) nres" where
"poly_ruffini_one_body_mop_monadic qs i dst prev \<equiv> doN {
  ASSERT (i < length qs);
  curr \<leftarrow> (PR_CONST poly_copy_coeff_monadic) qs i;
  prod \<leftarrow> RETURN (COPY curr);
  prod \<leftarrow> (PR_CONST mpz_add.amop_r1) prod prev;
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_push_coeff_monadic) dst prod;
  (PR_CONST mpzb_discard_monadic) prev;
  RETURN (dst, curr)
}"

sepref_register "PR_CONST poly_ruffini_one_body_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow>
    (gmp_poly \<times> int) nres"

sepref_definition poly_ruffini_one_body_impl [llvm_inline] is
  "uncurry3 poly_ruffini_one_body_mop_monadic" ::
  "[\<lambda>(((qs, i), dst), _).
      i < length qs \<and>
      length dst + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
    poly_ruffini_state_assn"
  unfolding poly_ruffini_one_body_mop_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_ruffini_one_body_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_ruffini_one_body_impl,
    uncurry3 (PR_CONST poly_ruffini_one_body_mop_monadic)) \<in>
    [\<lambda>(((qs, i), dst), _).
      i < length qs \<and>
      length dst + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      poly_ruffini_state_assn"
  using poly_ruffini_one_body_impl.refine
  by (simp add: PR_CONST_def)

definition poly_ruffini_one_loop_body_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow>
    (nat \<times> gmp_poly \<times> int) nres" where
"poly_ruffini_one_loop_body_mop_monadic qs len st \<equiv> doN {
  let (i, dst, prev) = st;
  ASSERT (i < len);
  ASSERT (i < length qs);
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  (dst, prev) \<leftarrow> (PR_CONST poly_ruffini_one_body_mop_monadic) qs i dst prev;
  ASSERT (i < len);
  RETURN (i + 1, dst, prev)
}"

sepref_register "PR_CONST poly_ruffini_one_loop_body_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow>
    (nat \<times> gmp_poly \<times> int) nres"

definition [llvm_code, llvm_inline]:
  "poly_ruffini_one_loop_body_impl qs len st \<equiv> doM {
    let (i, dst, prev) = st;
    (dst, prev) \<leftarrow> poly_ruffini_one_body_impl qs i dst prev;
    Mreturn (i + 1, dst, prev)
  }"

lemma poly_ruffini_one_loop_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_ruffini_one_loop_body_impl,
    uncurry2 (PR_CONST poly_ruffini_one_loop_body_mop_monadic)) \<in>
    [\<lambda>((qs, len), _).
      len = length qs \<and>
      length qs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        poly_ruffini_loop_state_assn\<^sup>d \<rightarrow>
      poly_ruffini_loop_state_assn"
  unfolding poly_ruffini_one_loop_body_impl_def
    poly_ruffini_one_loop_body_mop_monadic_def PR_CONST_def
  supply [vcg_rules] =
    poly_ruffini_one_body_impl.refine[to_hnr, THEN hn_refineD,
      unfolded hn_ctxt_def invalid_assn_def pure_def, simplified]
  apply sepref_to_hoare
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps)
  subgoal for a aa b ab ac ad ba bb bia bba ae af bc ag ai ah aj bd be s
    apply (rule exI[where x="Suc a"])
    apply (intro conjI)
     apply (rule dsc_snat_rel_suc)
      apply assumption
     apply simp
    apply (rule exI[where x=bd])
    apply (rule exI[where x=be])
    apply (intro conjI)
     apply (simp add: refine_pw_simps pw_le_iff)
    apply assumption
    done
  done

definition poly_ruffini_one_with_prev_monadic ::
  "gmp_poly \<Rightarrow> int \<Rightarrow> gmp_poly nres" where
"poly_ruffini_one_with_prev_monadic qs prev0 \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) qs;
  ASSERT (len = length qs);
  ASSERT (len + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_empty_sz_monadic) (len + 1);
  init \<leftarrow> RETURN (0, dst, prev0);
  st \<leftarrow> WHILET (\<lambda>st. (PR_CONST poly_ruffini_cond) len st)
    (\<lambda>st. (PR_CONST poly_ruffini_one_loop_body_mop_monadic) qs len st) init;
  ASSERT (case st of (_, dst, _) \<Rightarrow>
    length dst + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_ruffini_result_mop_monadic) st
}"

lemma poly_ruffini_one_with_prev_monadic_correct:
  assumes "length qs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_ruffini_one_with_prev_monadic qs prev0
    \<le> RETURN (ruffini_step 1 prev0 qs)"
  using assms
  unfolding poly_ruffini_one_with_prev_monadic_def
    poly_ruffini_cond_def
    poly_ruffini_one_loop_body_mop_monadic_def
    poly_ruffini_one_body_mop_monadic_def
    poly_ruffini_result_mop_monadic_def
    poly_length_monadic_def poly_empty_sz_monadic_def
    poly_copy_coeff_monadic_def poly_push_coeff_monadic_def
    mpzb_discard_monadic_def mpz_add.amop_r1_def PR_CONST_def
  apply (refine_vcg WHILET_rule[
    where I="\<lambda>(i, dst, prev).
      i \<le> length qs \<and>
      length dst = i \<and>
      dst @ ruffini_step 1 prev (drop i qs) = ruffini_step 1 prev0 qs"
      and R="measure (\<lambda>(i, _::gmp_poly, _::int). length qs - i)"])
  apply (auto simp: algebra_simps dsc_ruffini_step_drop_Suc COPY_def
    split: prod.splits)
  done

sepref_register "PR_CONST poly_ruffini_one_with_prev_monadic"
  :: "gmp_poly \<Rightarrow> int \<Rightarrow> gmp_poly nres"

sepref_definition poly_ruffini_one_with_prev_impl [llvm_inline] is
  "uncurry poly_ruffini_one_with_prev_monadic" ::
  "[\<lambda>(qs, _). length qs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      gmp_poly_assn"
  unfolding poly_ruffini_one_with_prev_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_fr_rules] =
    poly_ruffini_one_loop_body_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemma poly_ruffini_one_with_prev_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_ruffini_one_with_prev_impl,
    uncurry (PR_CONST poly_ruffini_one_with_prev_monadic)) \<in>
    [\<lambda>(qs, _). length qs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        gmp_poly_assn"
  using poly_ruffini_one_with_prev_impl.refine
  by (simp add: PR_CONST_def)

definition poly_taylor_step_one_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_poly nres" where
"poly_taylor_step_one_mop_monadic xs len i acc \<equiv> doN {
  ASSERT (len = length xs);
  ASSERT (i < len);
  ASSERT (i + 1 \<le> len);
  ASSERT (length acc + 1 < max_snat LENGTH(gmp_poly_len));
  let idx = len - (i + 1);
  ASSERT (idx < length xs);
  a \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs idx;
  acc' \<leftarrow> (PR_CONST poly_ruffini_one_with_prev_monadic) acc a;
  (PR_CONST poly_free_monadic) acc;
  RETURN acc'
}"

sepref_register "PR_CONST poly_taylor_step_one_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_poly nres"

sepref_definition poly_taylor_step_one_impl [llvm_inline] is
  "uncurry3 poly_taylor_step_one_mop_monadic" ::
  "[\<lambda>(((xs, len), i), acc).
      len = length xs \<and>
      i < len \<and>
      length acc + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_taylor_step_one_mop_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_taylor_step_one_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_taylor_step_one_impl,
    uncurry3 (PR_CONST poly_taylor_step_one_mop_monadic)) \<in>
    [\<lambda>(((xs, len), i), acc).
      len = length xs \<and>
      i < len \<and>
      length acc + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_taylor_step_one_impl.refine
  by (simp add: PR_CONST_def)

lemma poly_taylor_step_one_mop_monadic_correct[refine_vcg]:
  assumes "len = length xs"
    and "i < len"
    and "length acc + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_taylor_step_one_mop_monadic xs len i acc
    \<le> RETURN (ruffini_step 1 (xs ! (len - Suc i)) acc)"
  using assms
  unfolding poly_taylor_step_one_mop_monadic_def
    poly_copy_coeff_monadic_def PR_CONST_def
  apply refine_vcg
  apply simp_all
  subgoal
    apply (rule order_trans)
     apply (rule poly_ruffini_one_with_prev_monadic_correct)
     apply simp
    apply (clarsimp simp: pw_le_iff refine_pw_simps)
    done
  done

lemma poly_taylor_step_one_mop_monadic_invar[refine_vcg]:
  assumes "len = length xs"
    and "i < len"
    and "length acc = i"
    and "len + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_taylor_step_one_mop_monadic xs len i acc
    \<le> SPEC (\<lambda>acc'.
      acc' = ruffini_step 1 (xs ! (len - Suc i)) acc \<and>
      length acc' = Suc i \<and>
      len - Suc i < len - i)"
  apply (rule order_trans)
   apply (rule poly_taylor_step_one_mop_monadic_correct)
     using assms apply simp_all
  done

definition poly_taylor_one_loop_body_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow>
    (nat \<times> gmp_poly) nres" where
"poly_taylor_one_loop_body_mop_monadic xs len st \<equiv> doN {
  let (i, acc) = st;
  ASSERT (i < len);
  ASSERT (len = length xs);
  ASSERT (length acc + 1 < max_snat LENGTH(gmp_poly_len));
  acc \<leftarrow> (PR_CONST poly_taylor_step_one_mop_monadic) xs len i acc;
  ASSERT (i < len);
  RETURN (i + 1, acc)
}"

sepref_register "PR_CONST poly_taylor_one_loop_body_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow>
    (nat \<times> gmp_poly) nres"

definition [llvm_code, llvm_inline]:
  "poly_taylor_one_loop_body_impl xs len st \<equiv> doM {
    let (i, acc) = st;
    acc \<leftarrow> poly_taylor_step_one_impl xs len i acc;
    Mreturn (i + 1, acc)
  }"

lemma poly_taylor_one_loop_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_taylor_one_loop_body_impl,
    uncurry2 (PR_CONST poly_taylor_one_loop_body_mop_monadic)) \<in>
    [\<lambda>((xs, len), _).
      len = length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        poly_taylor_loop_state_assn\<^sup>d \<rightarrow>
      poly_taylor_loop_state_assn"
  unfolding poly_taylor_one_loop_body_impl_def
    poly_taylor_one_loop_body_mop_monadic_def PR_CONST_def
  supply [vcg_rules] =
    poly_taylor_step_one_impl.refine[to_hnr, THEN hn_refineD,
      unfolded hn_ctxt_def invalid_assn_def pure_def, simplified]
  apply sepref_to_hoare
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps)
  subgoal for a aa b ab ac ad ba bb bia bba ae af bc ag s
    apply (rule exI[where x="Suc a"])
    apply (intro conjI)
     apply (rule dsc_snat_rel_suc)
      apply assumption
     apply simp
    apply (rule exI[where x=s])
    apply (intro conjI)
     apply (simp add: refine_pw_simps pw_le_iff)
    apply assumption
    done
  done

definition poly_taylor_shift_one_monadic ::
  "gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_taylor_shift_one_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (len + 1 < max_snat LENGTH(gmp_poly_len));
  acc \<leftarrow> (PR_CONST poly_empty_sz_monadic) len;
  init \<leftarrow> RETURN (0, acc);
  st \<leftarrow> WHILET (\<lambda>st. (PR_CONST poly_taylor_cond) len st)
    (\<lambda>st. (PR_CONST poly_taylor_one_loop_body_mop_monadic) xs len st) init;
  (PR_CONST poly_taylor_result_mop_monadic) st
}"

lemma poly_taylor_shift_one_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_taylor_shift_one_monadic xs
    \<le> RETURN (taylor_shift_list 1 xs)"
  using assms
  unfolding poly_taylor_shift_one_monadic_def
    poly_taylor_cond_def
    poly_taylor_one_loop_body_mop_monadic_def
    poly_taylor_result_mop_monadic_def
    poly_length_monadic_def poly_empty_sz_monadic_def
    PR_CONST_def
  apply (refine_vcg WHILET_rule[
    where I="\<lambda>(i, acc).
      i \<le> length xs \<and>
      length acc = i \<and>
      acc = taylor_shift_list 1 (drop (length xs - i) xs)"
      and R="measure (\<lambda>(i, _::gmp_poly). length xs - i)"])
  apply (auto simp: dsc_taylor_shift_list_drop_step split: prod.splits)
  done

sepref_register "PR_CONST poly_taylor_shift_one_monadic"
  :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_taylor_shift_one_impl [llvm_inline] is
  "poly_taylor_shift_one_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding poly_taylor_shift_one_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_fr_rules] =
    poly_taylor_one_loop_body_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemma poly_taylor_shift_one_impl_hnr[sepref_fr_rules]:
  "(poly_taylor_shift_one_impl,
    PR_CONST poly_taylor_shift_one_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using poly_taylor_shift_one_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Reverse polynomial coefficients\<close>

definition poly_reverse_step_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_reverse_step_mop_monadic xs len i dst \<equiv> doN {
  ASSERT (len = length xs);
  ASSERT (i < len);
  let idx = len - (i + 1);
  ASSERT (idx < length xs);
  coeff \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs idx;
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_push_coeff_monadic) dst coeff
}"

sepref_register "PR_CONST poly_reverse_step_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_reverse_step_impl [llvm_inline] is
  "uncurry3 poly_reverse_step_mop_monadic" ::
  "[\<lambda>(((xs, len), i), dst).
      len = length xs \<and>
      i < len \<and>
      length dst + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_reverse_step_mop_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_reverse_step_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_reverse_step_impl,
    uncurry3 (PR_CONST poly_reverse_step_mop_monadic)) \<in>
    [\<lambda>(((xs, len), i), dst).
      len = length xs \<and>
      i < len \<and>
      length dst + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_reverse_step_impl.refine
  by (simp add: PR_CONST_def)

lemma poly_reverse_step_mop_monadic_correct[refine_vcg]:
  assumes "len = length xs"
    and "i < len"
    and "length dst + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_reverse_step_mop_monadic xs len i dst
    \<le> RETURN (dst @ [xs ! (len - Suc i)])"
  using assms
  unfolding poly_reverse_step_mop_monadic_def
    poly_copy_coeff_monadic_def poly_push_coeff_monadic_def PR_CONST_def
  by refine_vcg simp_all

lemma poly_reverse_step_mop_monadic_invar[refine_vcg]:
  assumes "len = length xs"
    and "i < len"
    and "length dst = i"
    and "len + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_reverse_step_mop_monadic xs len i dst
    \<le> SPEC (\<lambda>dst'.
      dst' = dst @ [xs ! (len - Suc i)] \<and>
      length dst' = Suc i \<and>
      len - Suc i < len - i)"
  apply (rule order_trans)
   apply (rule poly_reverse_step_mop_monadic_correct)
     using assms apply simp_all
  done

abbreviation poly_reverse_loop_state_assn where
"poly_reverse_loop_state_assn \<equiv>
  snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"

definition poly_reverse_cond ::
  "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool" where
"poly_reverse_cond len st \<equiv>
  (let (i, dst) = st in i < len)"

sepref_register "PR_CONST poly_reverse_cond"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool"

sepref_definition poly_reverse_cond_impl [llvm_inline] is
  "uncurry (RETURN oo poly_reverse_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    poly_reverse_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding poly_reverse_cond_def
  unfolding Let_def
  by sepref

lemma poly_reverse_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_reverse_cond_impl,
    uncurry (RETURN oo (PR_CONST poly_reverse_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      poly_reverse_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using poly_reverse_cond_impl.refine
  by (simp add: PR_CONST_def)

definition poly_reverse_loop_body_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow>
    (nat \<times> gmp_poly) nres" where
"poly_reverse_loop_body_mop_monadic xs len st \<equiv> doN {
  let (i, dst) = st;
  ASSERT (i < len);
  ASSERT (len = length xs);
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_reverse_step_mop_monadic) xs len i dst;
  ASSERT (i < len);
  RETURN (i + 1, dst)
}"

sepref_register "PR_CONST poly_reverse_loop_body_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow>
    (nat \<times> gmp_poly) nres"

definition [llvm_code, llvm_inline]:
  "poly_reverse_loop_body_impl xs len st \<equiv> doM {
    let (i, dst) = st;
    dst \<leftarrow> poly_reverse_step_impl xs len i dst;
    Mreturn (i + 1, dst)
  }"

lemma poly_reverse_loop_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_reverse_loop_body_impl,
    uncurry2 (PR_CONST poly_reverse_loop_body_mop_monadic)) \<in>
    [\<lambda>((xs, len), _).
      len = length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        poly_reverse_loop_state_assn\<^sup>d \<rightarrow>
      poly_reverse_loop_state_assn"
  unfolding poly_reverse_loop_body_impl_def
    poly_reverse_loop_body_mop_monadic_def PR_CONST_def
  supply [vcg_rules] =
    poly_reverse_step_impl.refine[to_hnr, THEN hn_refineD,
      unfolded hn_ctxt_def invalid_assn_def pure_def, simplified]
  apply sepref_to_hoare
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps)
  subgoal for a aa b ab ac ad ba bb bia bba ae af bc ag ai s
    apply (rule exI[where x="Suc a"])
    apply (intro conjI)
     apply (rule dsc_snat_rel_suc)
      apply assumption
     apply simp
    apply (rule exI[where x=ai])
    apply (intro conjI)
     apply (simp add: refine_pw_simps pw_le_iff)
    apply assumption
    done
  done

definition poly_reverse_result_mop_monadic ::
  "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_reverse_result_mop_monadic st \<equiv>
  (let (i, dst) = st in RETURN dst)"

sepref_register "PR_CONST poly_reverse_result_mop_monadic"
  :: "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_reverse_result_impl [llvm_inline] is
  "poly_reverse_result_mop_monadic" ::
  "poly_reverse_loop_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  unfolding poly_reverse_result_mop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_reverse_result_impl_hnr[sepref_fr_rules]:
  "(poly_reverse_result_impl,
    PR_CONST poly_reverse_result_mop_monadic) \<in>
    poly_reverse_loop_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  using poly_reverse_result_impl.refine
  by (simp add: PR_CONST_def)

lemma dsc_rev_drop_suc:
  assumes "i < length xs"
  shows "rev (drop (length xs - Suc i) xs) =
    rev (drop (length xs - i) xs) @ [xs ! (length xs - Suc i)]"
proof -
  let ?idx = "length xs - Suc i"
  have idx_lt: "?idx < length xs"
    using assms by simp
  have drop_eq: "drop ?idx xs = xs ! ?idx # drop (Suc ?idx) xs"
    using idx_lt by (simp add: Cons_nth_drop_Suc)
  have "Suc ?idx = length xs - i"
    using assms by simp
  then show ?thesis
    by (simp add: drop_eq)
qed

definition poly_reverse_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_reverse_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (len + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_empty_sz_monadic) len;
  init \<leftarrow> RETURN (0, dst);
  st \<leftarrow> WHILET (\<lambda>st. (PR_CONST poly_reverse_cond) len st)
    (\<lambda>st. (PR_CONST poly_reverse_loop_body_mop_monadic) xs len st) init;
  (PR_CONST poly_reverse_result_mop_monadic) st
}"

lemma poly_reverse_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_reverse_monadic xs \<le> RETURN (rev xs)"
  using assms
  unfolding poly_reverse_monadic_def
    poly_reverse_cond_def
    poly_reverse_loop_body_mop_monadic_def
    poly_reverse_result_mop_monadic_def
    poly_length_monadic_def poly_empty_sz_monadic_def
    PR_CONST_def
  apply (refine_vcg WHILET_rule[
    where I="\<lambda>(i, dst).
      i \<le> length xs \<and>
      length dst = i \<and>
      dst = rev (drop (length xs - i) xs)"
      and R="measure (\<lambda>(i, _::gmp_poly). length xs - i)"])
  apply (auto simp: dsc_rev_drop_suc split: prod.splits)
  done

sepref_register "PR_CONST poly_reverse_monadic"
  :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_reverse_impl [llvm_inline] is
  "poly_reverse_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding poly_reverse_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemma poly_reverse_impl_hnr[sepref_fr_rules]:
  "(poly_reverse_impl, PR_CONST poly_reverse_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using poly_reverse_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Fractional Taylor shift with numerator and denominator\<close>

definition poly_fractional_taylor_shift_nd_monadic ::
  "int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_fractional_taylor_shift_nd_monadic n d xs \<equiv> doN {
  rxs \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
  scaled_rxs \<leftarrow> (PR_CONST poly_scale_monadic) d rxs;
  (PR_CONST poly_free_monadic) rxs;
  ASSERT (length scaled_rxs + 1 < max_snat LENGTH(gmp_poly_len));
  scaled \<leftarrow> (PR_CONST poly_reverse_monadic) scaled_rxs;
  (PR_CONST poly_free_monadic) scaled_rxs;
  ASSERT (length scaled + 1 < max_snat LENGTH(gmp_poly_len));
  shifted \<leftarrow> (PR_CONST poly_taylor_shift_monadic) n scaled;
  (PR_CONST poly_free_monadic) scaled;
  RETURN shifted
}"

lemma poly_fractional_taylor_shift_nd_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_fractional_taylor_shift_nd_monadic n d xs
    \<le> RETURN (taylor_shift_list n
      (rev (scale_for_fractional_shift d 1 (rev xs))))"
  using assms
  unfolding poly_fractional_taylor_shift_nd_monadic_def PR_CONST_def
  apply (refine_vcg
    poly_reverse_monadic_correct[THEN order_trans]
    poly_scale_correct[THEN order_trans]
    poly_taylor_shift_monadic_correct[THEN order_trans]
    poly_free_monadic_rule)
  apply (simp_all add: scale_for_fractional_shift_eq_scale_poly_list)
  done

sepref_register "PR_CONST poly_fractional_taylor_shift_nd_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_fractional_taylor_shift_nd_impl [llvm_inline] is
  "uncurry2 poly_fractional_taylor_shift_nd_monadic" ::
  "[\<lambda>((_, _), xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
      gmp_poly_assn"
  unfolding poly_fractional_taylor_shift_nd_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemma poly_fractional_taylor_shift_nd_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_fractional_taylor_shift_nd_impl,
    uncurry2 (PR_CONST poly_fractional_taylor_shift_nd_monadic)) \<in>
    [\<lambda>((_, _), xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
        gmp_poly_assn"
  using poly_fractional_taylor_shift_nd_impl.refine
  by (simp add: PR_CONST_def)
lemma ruffini_step_append:
  "ruffini_step c a (qs @ [x]) = (ruffini_step c a qs)[length qs := last (ruffini_step c a qs) + c * x] @ [x]"
  by (induct qs arbitrary: a) (auto simp: list_update_append drop_upd_first)

lemma ruffini_step_in_place_step:
  assumes "ys' = take i ys @ ruffini_step c (ys ! i) (take (j - i) (drop (i + 1) ys)) @ drop (j + 1) ys"
    and "i \<le> j" and "j < length ys - 1"
  shows "ys'[j := ys' ! j + c * ys' ! (j + 1)] =
    take i ys @ ruffini_step c (ys ! i) (take (j + 1 - i) (drop (i + 1) ys)) @ drop (j + 2) ys"
proof -
  let ?qs = "take (j - i) (drop (Suc i) ys)"
  let ?a = "ys ! i"
  let ?x = "ys ! Suc j"

  have len_take: "length (take i ys) = i"
    using assms(2,3) by simp
  have len_ruff: "length (ruffini_step c ?a ?qs) = j - i + 1"
    using assms(2,3) by simp

  have ys'_eq: "ys' = take i ys @ ruffini_step c ?a ?qs @ ?x # drop (j + 2) ys"
    using assms(2,3)
    apply (subst assms(1))
    apply (simp add: Cons_nth_drop_Suc[symmetric])
    done

  have ruff_ne: "ruffini_step c ?a ?qs \<noteq> []"
    by (cases ?qs) auto

  have ys'_j: "ys' ! j = last (ruffini_step c ?a ?qs)"
    unfolding ys'_eq
    using assms ruff_ne by (simp add: nth_append len_take len_ruff last_conv_nth)

  have ys'_j1: "ys' ! (j + 1) = ?x"
    unfolding ys'_eq
    using assms by (simp add: nth_append len_take len_ruff Suc_diff_le)

  have upd_eq: "ys'[j := ys' ! j + c * ys' ! (j + 1)] =
    take i ys @ (ruffini_step c ?a ?qs)[j - i := ys' ! j + c * ys' ! (j + 1)] @ ?x # drop (j + 2) ys"
    unfolding ys'_eq
    using assms by (simp add: list_update_append len_take len_ruff Suc_diff_le)

  have append_eq: "(ruffini_step c ?a ?qs)[j - i := last (ruffini_step c ?a ?qs) + c * ?x] @ [?x] =
    ruffini_step c ?a (?qs @ [?x])"
    using ruffini_step_append[of c ?a ?qs ?x] assms by simp

  have qs_append: "?qs @ [?x] = take (j + 1 - i) (drop (Suc i) ys)"
    using assms(2,3)
    by (simp add: take_Suc_conv_app_nth Suc_diff_le)

  show ?thesis
    apply (unfold upd_eq)
    apply (unfold ys'_j ys'_j1)
    apply (simp add: append_eq del: ruffini_step.simps)
    apply (simp add: qs_append del: ruffini_step.simps)
    done
qed

lemma ruffini_step_in_place_step_one:
  assumes "ys' = take i ys @ ruffini_step 1 (ys ! i) (take (j - i) (drop (i + 1) ys)) @ drop (j + 1) ys"
    and "i \<le> j" and "j < length ys - 1"
  shows "ys'[j := ys' ! j + ys' ! (j + 1)] =
    take i ys @ ruffini_step 1 (ys ! i) (take (j + 1 - i) (drop (i + 1) ys)) @ drop (j + 2) ys"
  using ruffini_step_in_place_step[OF assms(1,2,3)] by simp

lemma taylor_shift_in_place_outer_step:
  assumes "ys' = take (i + 1) ys @ taylor_shift_list c (drop (i + 1) ys)"
    and "i < length ys - 1"
  shows "take i ys' @ ruffini_step c (ys' ! i) (drop (i + 1) ys') =
    take i ys @ taylor_shift_list c (drop i ys)"
proof -
  have i_lt: "i < length ys"
    using assms(2) by simp
  have i_le: "i \<le> length ys"
    using i_lt by simp
  have len_take: "length (take (i + 1) ys) = i + 1"
    using assms(2) by simp

  have take_i: "take i ys' = take i ys"
    unfolding assms(1)
    using assms(2)
    by (simp add: take_append len_take)

  have nth_i: "ys' ! i = ys ! i"
    unfolding assms(1)
    using assms(2)
    by (simp add: nth_append len_take)

  have drop_i1: "drop (i + 1) ys' = taylor_shift_list c (drop (i + 1) ys)"
    unfolding assms(1)
    using assms(2)
    by (simp add: drop_append len_take)

  show ?thesis
    unfolding take_i nth_i drop_i1
    using i_lt i_le
    by (simp add: Cons_nth_drop_Suc [symmetric])
qed

definition poly_taylor_inner_loop_monadic :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_taylor_inner_loop_monadic len i c xs \<equiv>
  for i (len - 1) (\<lambda>j xs. doN {
    ASSERT (j < length xs);
    let j1 = j + 1;
    ASSERT (j1 < length xs);
    ASSERT (j1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (j \<noteq> j1);
    (PR_CONST poly_addmul_coeff_monadic) xs j c j1
  }) xs"

definition poly_taylor_one_inner_loop_monadic :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_taylor_one_inner_loop_monadic len i xs \<equiv>
  for i (len - 1) (\<lambda>j xs. doN {
    ASSERT (j < length xs);
    let j1 = j + 1;
    ASSERT (j1 < length xs);
    ASSERT (j1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (j \<noteq> j1);
    (PR_CONST poly_add_coeff_monadic) xs j j1
  }) xs"

definition poly_taylor_shift_in_place_monadic :: "int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_taylor_shift_in_place_monadic c xs \<equiv> doN {
  len \<leftarrow> mop_list_length xs;
  ASSERT (len = length xs);
  if len \<le> 1 then RETURN xs
  else doN {
    ASSERT (1 < len);
    limit \<leftarrow> RETURN (len - 1);
    xs_final \<leftarrow> for 0 limit (\<lambda>k ys. doN {
      ASSERT (k < len - 1);
      ASSERT (1 < len);
      ASSERT (k \<le> len - 2);
      idx \<leftarrow> RETURN (len - 2 - k);
      ASSERT (idx < len - 1);
      ASSERT (length ys = len);
      ASSERT (idx \<le> len);
      ASSERT (length ys + 1 < max_snat LENGTH(gmp_poly_len));
      ys_next \<leftarrow> poly_taylor_inner_loop_monadic len idx c ys;
      RETURN ys_next
    }) xs;
    RETURN xs_final
  }
}"

lemma taylor_shift_list_len1:
  "length zs = 1 \<Longrightarrow> taylor_shift_list c zs = zs"
  by (cases zs) (auto simp: taylor_shift_list.simps)

lemma taylor_shift_list_drop_last:
  "length xs \<ge> 2 \<Longrightarrow> taylor_shift_list c (drop (length xs - 1) xs) = drop (length xs - 1) xs"
  apply (subgoal_tac "length (drop (length xs - 1) xs) = 1")
   apply (simp add: taylor_shift_list_len1)
  apply simp
  done

lemma butlast_drop: "butlast xs @ drop (length xs - Suc 0) xs = xs"
  apply (induct xs)
   apply simp
  apply (case_tac xs)
   apply simp_all
  done

lemma poly_taylor_inner_loop_monadic_correct:
  assumes "length xs = len" and "i < len" and "len + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_taylor_inner_loop_monadic len i c xs
    \<le> RETURN (take i xs @ ruffini_step c (xs ! i) (drop (i + 1) xs))"
  unfolding poly_taylor_inner_loop_monadic_def
    poly_addmul_coeff_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>j xs'.
    length xs' = len \<and>
    xs' = take i xs @ ruffini_step c (xs ! i) (take (j - i) (drop (i + 1) xs)) @ drop (j + 1) xs"])
  subgoal using assms by linarith
  apply (simp add: assms)
  apply (metis Suc_eq_plus1 append_eq_appendI append_take_drop_id
      assms(1,2) cancel_comm_monoid_add_class.diff_cancel
      hd_drop_conv_nth ruffini_step.simps(1) take_eq_Nil
      take_hd_drop)
  apply linarith
  apply linarith
  using assms apply linarith
  using assms apply linarith
  apply (metis length_list_update)
  apply (metis Suc_eq_plus1 add_2_eq_Suc' assms(1)
      ruffini_step_in_place_step)
  by (simp add: assms)
  

lemma poly_taylor_one_inner_loop_monadic_correct:
  assumes "length xs = len" and "i < len" and "len + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_taylor_one_inner_loop_monadic len i xs
    \<le> RETURN (take i xs @ ruffini_step 1 (xs ! i) (drop (i + 1) xs))"
  unfolding poly_taylor_one_inner_loop_monadic_def
    poly_add_coeff_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>j xs'.
    length xs' = len \<and>
    xs' = take i xs @ ruffini_step 1 (xs ! i) (take (j - i) (drop (i + 1) xs)) @ drop (j + 1) xs"])
  using assms apply auto[1]
  using assms apply blast
  apply (metis append_eq_appendI append_take_drop_id assms(1,2)
      cancel_comm_monoid_add_class.diff_cancel hd_drop_conv_nth
      ruffini_step.simps(1) semiring_norm(174) take_eq_Nil
      take_hd_drop)
  apply linarith
  apply linarith
  using assms apply linarith
  using assms apply linarith
  apply (metis length_list_update)
  apply (metis Suc_eq_plus1 add_2_eq_Suc' assms(1)
      ruffini_step_in_place_step_one)
  by (simp add: assms)

lemma poly_taylor_shift_in_place_monadic_correct:
  "length xs + 1 < max_snat LENGTH(gmp_poly_len) \<Longrightarrow>
   poly_taylor_shift_in_place_monadic c xs \<le> RETURN (taylor_shift_list c xs)"
  unfolding poly_taylor_shift_in_place_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>k xs'.
    length xs' = length xs \<and>
    xs' = take (length xs - 1 - k) xs @ taylor_shift_list c (drop (length xs - 1 - k) xs)"])
             apply blast
  using antisym_conv taylor_shift_list_len1 apply fastforce
           apply linarith
          apply blast
         apply force
        apply linarith 
       apply linarith
      apply blast
     apply simp
    apply linarith
   apply (rule order_trans[OF poly_taylor_inner_loop_monadic_correct])
      apply simp
     apply simp
    apply simp
   apply (simp add: Refine_Basic.RETURN_def) 
  apply (metis dsc_taylor_shift_list_drop_step less_diff_conv
      numeral_nat(7) semiring_norm(174))
  apply auto
  done
  
definition poly_taylor_shift_one_in_place_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_taylor_shift_one_in_place_monadic xs \<equiv> doN {
  len \<leftarrow> mop_list_length xs;
  ASSERT (len = length xs);
  if len \<le> 1 then RETURN xs
  else doN {
    ASSERT (1 < len);
    limit \<leftarrow> RETURN (len - 1);
    xs_final \<leftarrow> for 0 limit (\<lambda>k ys. doN {
      ASSERT (k < len - 1);
      ASSERT (1 < len);
      ASSERT (k \<le> len - 2);
      idx \<leftarrow> RETURN (len - 2 - k);
      ASSERT (idx < len - 1);
      ASSERT (length ys = len);
      ASSERT (idx \<le> len);
      ASSERT (length ys + 1 < max_snat LENGTH(gmp_poly_len));
      ys_next \<leftarrow> poly_taylor_one_inner_loop_monadic len idx ys;
      RETURN ys_next
    }) xs;
    RETURN xs_final
  }
}"

lemma poly_taylor_shift_one_in_place_monadic_correct:
  "length xs + 1 < max_snat LENGTH(gmp_poly_len) \<Longrightarrow>
   poly_taylor_shift_one_in_place_monadic xs \<le> RETURN (taylor_shift_list 1 xs)"
  unfolding poly_taylor_shift_one_in_place_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>k xs'.
    length xs' = length xs \<and>
    xs' = take (length xs - 1 - k) xs @ taylor_shift_list 1 (drop (length xs - 1 - k) xs)"])
               apply blast
  using antisym_conv taylor_shift_list_len1 apply fastforce
           apply linarith
          apply blast
         apply force
        apply linarith 
       apply linarith
      apply blast
     apply simp
    apply linarith
   apply (rule order_trans[OF poly_taylor_one_inner_loop_monadic_correct])
      apply simp
     apply simp
    apply simp
   apply (simp add: Refine_Basic.RETURN_def) 
  apply (metis dsc_taylor_shift_list_drop_step less_diff_conv
      numeral_nat(7) semiring_norm(174))
  apply auto
  done

sepref_register "PR_CONST poly_taylor_inner_loop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_taylor_inner_loop_impl [llvm_code] is
  "uncurry3 poly_taylor_inner_loop_monadic" ::
  "[\<lambda>(((len, i), c), xs). length xs = len \<and> 1 < len \<and> i \<le> len \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_taylor_inner_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_taylor_inner_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_taylor_inner_loop_impl,
    uncurry3 (PR_CONST poly_taylor_inner_loop_monadic)) \<in>
    [\<lambda>(((len, i), c), xs). length xs = len \<and> 1 < len \<and> i \<le> len \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_taylor_inner_loop_impl.refine
  by (simp add: PR_CONST_def)

sepref_register "PR_CONST poly_taylor_one_inner_loop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_taylor_one_inner_loop_impl [llvm_code] is
  "uncurry2 poly_taylor_one_inner_loop_monadic" ::
  "[\<lambda>((len, i), xs). length xs = len \<and> 1 < len \<and> i \<le> len \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_taylor_one_inner_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_taylor_one_inner_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_taylor_one_inner_loop_impl,
    uncurry2 (PR_CONST poly_taylor_one_inner_loop_monadic)) \<in>
    [\<lambda>((len, i), xs). length xs = len \<and> 1 < len \<and> i \<le> len \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_taylor_one_inner_loop_impl.refine
  by (simp add: PR_CONST_def)

subsection \<open>Taylor shift in-place loops: cond / body / result mop decomposition\<close>

text \<open>Sepref cannot synthesise a raw \<open>WHILET\<close> over a state containing a destructive
  \<open>gmp_poly\<close> component. Pattern: same as \<open>carried_left_shift_monadic\<close> and
  \<open>poly_ethorner_count_monadic\<close>.\<close>

abbreviation poly_taylor_ip_state_assn where
  "poly_taylor_ip_state_assn \<equiv>
    snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"

text \<open>Condition mop, shared by both Taylor-shift loops.\<close>

definition poly_taylor_ip_cond ::
  "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool" where
  "poly_taylor_ip_cond limit st \<equiv>
    (let (k, ys) = st in k < limit)"

sepref_register "PR_CONST poly_taylor_ip_cond"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool"

sepref_definition poly_taylor_ip_cond_impl [llvm_inline] is
  "uncurry (RETURN oo poly_taylor_ip_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a poly_taylor_ip_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding poly_taylor_ip_cond_def Let_def
  by sepref

lemma poly_taylor_ip_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_taylor_ip_cond_impl,
    uncurry (RETURN oo (PR_CONST poly_taylor_ip_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a poly_taylor_ip_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using poly_taylor_ip_cond_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Result mop, shared by both Taylor-shift loops.\<close>

definition poly_taylor_ip_result_mop_monadic ::
  "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres" where
  "poly_taylor_ip_result_mop_monadic st \<equiv>
    (let (k, ys) = st in RETURN ys)"

sepref_register "PR_CONST poly_taylor_ip_result_mop_monadic"
  :: "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_taylor_ip_result_impl [llvm_inline] is
  "poly_taylor_ip_result_mop_monadic" ::
  "poly_taylor_ip_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  unfolding poly_taylor_ip_result_mop_monadic_def Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_taylor_ip_result_impl_hnr[sepref_fr_rules]:
  "(poly_taylor_ip_result_impl,
    PR_CONST poly_taylor_ip_result_mop_monadic) \<in>
    poly_taylor_ip_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  using poly_taylor_ip_result_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Body mop for \<open>taylor_shift_in_place\<close> (with coefficient \<open>c\<close>).\<close>

definition poly_taylor_ip_body_mop_monadic ::
  "nat \<Rightarrow> int \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> (nat \<times> gmp_poly) nres" where
"poly_taylor_ip_body_mop_monadic len c st \<equiv> doN {
  let (k, ys) = st;
  ASSERT (k < len - 1);
  ASSERT (1 < len);
  ASSERT (k \<le> len - 2);
  idx \<leftarrow> RETURN (len - 2 - k);
  ASSERT (idx < len - 1);
  ASSERT (length ys = len);
  ASSERT (idx \<le> len);
  ASSERT (length ys + 1 < max_snat LENGTH(gmp_poly_len));
  ys' \<leftarrow> (PR_CONST poly_taylor_inner_loop_monadic) len idx c ys;
  ASSERT (k < len - 1);
  RETURN (k + 1, ys')
}"

sepref_register "PR_CONST poly_taylor_ip_body_mop_monadic"
  :: "nat \<Rightarrow> int \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> (nat \<times> gmp_poly) nres"

sepref_definition poly_taylor_ip_body_impl [llvm_inline] is
  "uncurry2 poly_taylor_ip_body_mop_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a poly_taylor_ip_state_assn\<^sup>d \<rightarrow>\<^sub>a
    poly_taylor_ip_state_assn"
  unfolding poly_taylor_ip_body_mop_monadic_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_taylor_ip_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_taylor_ip_body_impl,
    uncurry2 (PR_CONST poly_taylor_ip_body_mop_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a poly_taylor_ip_state_assn\<^sup>d \<rightarrow>\<^sub>a
      poly_taylor_ip_state_assn"
  using poly_taylor_ip_body_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Body mop for \<open>taylor_shift_one_in_place\<close> (\<open>c = 1\<close>, no \<open>c\<close> parameter).\<close>

definition poly_taylor_one_ip_body_mop_monadic ::
  "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> (nat \<times> gmp_poly) nres" where
"poly_taylor_one_ip_body_mop_monadic len st \<equiv> doN {
  let (k, ys) = st;
  ASSERT (k < len - 1);
  ASSERT (1 < len);
  ASSERT (k \<le> len - 2);
  idx \<leftarrow> RETURN (len - 2 - k);
  ASSERT (idx < len - 1);
  ASSERT (length ys = len);
  ASSERT (idx \<le> len);
  ASSERT (length ys + 1 < max_snat LENGTH(gmp_poly_len));
  ys' \<leftarrow> (PR_CONST poly_taylor_one_inner_loop_monadic) len idx ys;
  ASSERT (k < len - 1);
  RETURN (k + 1, ys')
}"

sepref_register "PR_CONST poly_taylor_one_ip_body_mop_monadic"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> (nat \<times> gmp_poly) nres"

sepref_definition poly_taylor_one_ip_body_impl [llvm_inline] is
  "uncurry poly_taylor_one_ip_body_mop_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a poly_taylor_ip_state_assn\<^sup>d \<rightarrow>\<^sub>a
    poly_taylor_ip_state_assn"
  unfolding poly_taylor_one_ip_body_mop_monadic_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_taylor_one_ip_body_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_taylor_one_ip_body_impl,
    uncurry (PR_CONST poly_taylor_one_ip_body_mop_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a poly_taylor_ip_state_assn\<^sup>d \<rightarrow>\<^sub>a
      poly_taylor_ip_state_assn"
  using poly_taylor_one_ip_body_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Outer \<open>taylor_shift_in_place\<close>, rewritten with \<open>WHILET\<close> + \<open>PR_CONST\<close> mops.\<close>

definition poly_taylor_shift_in_place_w_monadic :: "int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_taylor_shift_in_place_w_monadic c xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  if len \<le> 1 then RETURN xs
  else doN {
    ASSERT (1 < len);
    limit \<leftarrow> RETURN (len - 1);
    let init = (0::nat, xs);
    st \<leftarrow> WHILET
      (\<lambda>st. (PR_CONST poly_taylor_ip_cond) limit st)
      (\<lambda>st. (PR_CONST poly_taylor_ip_body_mop_monadic) len c st)
      init;
    (PR_CONST poly_taylor_ip_result_mop_monadic) st
  }
}"

lemma poly_taylor_shift_in_place_w_monadic_eq:
  "poly_taylor_shift_in_place_w_monadic c xs = poly_taylor_shift_in_place_monadic c xs"
  unfolding poly_taylor_shift_in_place_w_monadic_def
    poly_taylor_shift_in_place_monadic_def
    poly_taylor_ip_cond_def
    poly_taylor_ip_body_mop_monadic_def
    poly_taylor_ip_result_mop_monadic_def
    poly_length_monadic_def
    PR_CONST_def
  apply (subst for_by_while_gen[where conv_op="\<lambda>n. n"])
   apply simp
  apply (simp add: Let_def mop_list_length_alt op_list_length_def)
  done

sepref_register "PR_CONST poly_taylor_shift_in_place_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_taylor_shift_in_place_impl [llvm_code] is
  "uncurry poly_taylor_shift_in_place_monadic" ::
  "[\<lambda>(c, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_taylor_shift_in_place_w_monadic_eq[symmetric]
    poly_taylor_shift_in_place_w_monadic_def Let_def
  supply [sepref_fr_rules] =
    poly_taylor_ip_cond_impl_hnr
    poly_taylor_ip_body_impl_hnr
    poly_taylor_ip_result_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")
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

lemma poly_taylor_shift_in_place_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_taylor_shift_in_place_impl,
    uncurry (PR_CONST poly_taylor_shift_in_place_monadic)) \<in>
    [\<lambda>(c, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_taylor_shift_in_place_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Outer \<open>taylor_shift_one_in_place\<close>, rewritten with \<open>WHILET\<close> + \<open>PR_CONST\<close> mops.\<close>

definition poly_taylor_shift_one_in_place_w_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_taylor_shift_one_in_place_w_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  if len \<le> 1 then RETURN xs
  else doN {
    ASSERT (1 < len);
    limit \<leftarrow> RETURN (len - 1);
    let init = (0::nat, xs);
    st \<leftarrow> WHILET
      (\<lambda>st. (PR_CONST poly_taylor_ip_cond) limit st)
      (\<lambda>st. (PR_CONST poly_taylor_one_ip_body_mop_monadic) len st)
      init;
    (PR_CONST poly_taylor_ip_result_mop_monadic) st
  }
}"

lemma poly_taylor_shift_one_in_place_w_monadic_eq:
  "poly_taylor_shift_one_in_place_w_monadic xs = poly_taylor_shift_one_in_place_monadic xs"
  unfolding poly_taylor_shift_one_in_place_w_monadic_def
    poly_taylor_shift_one_in_place_monadic_def
    poly_taylor_ip_cond_def
    poly_taylor_one_ip_body_mop_monadic_def
    poly_taylor_ip_result_mop_monadic_def
    poly_length_monadic_def
    PR_CONST_def
  apply (subst for_by_while_gen[where conv_op="\<lambda>n. n"])
   apply simp
  apply (simp add: Let_def mop_list_length_alt op_list_length_def)
  done

sepref_definition poly_taylor_shift_one_in_place_impl [llvm_code] is
  "poly_taylor_shift_one_in_place_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_taylor_shift_one_in_place_w_monadic_eq[symmetric]
    poly_taylor_shift_one_in_place_w_monadic_def Let_def
  supply [sepref_fr_rules] =
    poly_taylor_ip_cond_impl_hnr
    poly_taylor_one_ip_body_impl_hnr
    poly_taylor_ip_result_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")
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

sepref_register "PR_CONST poly_taylor_shift_one_in_place_monadic"
  :: "gmp_poly \<Rightarrow> gmp_poly nres"

lemma poly_taylor_shift_one_in_place_impl_hnr[sepref_fr_rules]:
  "(poly_taylor_shift_one_in_place_impl,
    PR_CONST poly_taylor_shift_one_in_place_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_taylor_shift_one_in_place_impl.refine
  by (simp add: PR_CONST_def)

definition poly_ethorner_inner_loop_monadic :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_ethorner_inner_loop_monadic len i xs \<equiv> doN {
  ASSERT (2 <= len);
  let limit = len - 1 - i;
  for 0 limit (\<lambda>k xs. doN {
    ASSERT (k <= len - 2);
    let j = len - 2 - k;
    ASSERT (j < length xs);
    let j1 = j + 1;
    ASSERT (j1 < length xs);
    (PR_CONST poly_add_coeff_monadic) xs j j1
  }) xs
}"

sepref_register "PR_CONST poly_ethorner_inner_loop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_ethorner_inner_loop_impl [llvm_code] is
  "uncurry2 poly_ethorner_inner_loop_monadic" ::
  "[\<lambda>((len, i), xs). length xs = len \<and> 1 < len \<and> i + 1 < len \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_ethorner_inner_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_ethorner_inner_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_ethorner_inner_loop_impl,
    uncurry2 (PR_CONST poly_ethorner_inner_loop_monadic)) \<in>
    [\<lambda>((len, i), xs). length xs = len \<and> 1 < len \<and> i + 1 < len \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_ethorner_inner_loop_impl.refine
  by simp


subsection \<open>ET-Horner count loop: cond / body / result mop decomposition\<close>

text \<open>Required because a raw \<open>WHILET\<close> over a 4-tuple with a destructive \<open>gmp_poly\<close>
  component cannot be synthesised by a single \<open>by sepref\<close>. Pattern: same as
  \<open>carried_left_shift_monadic\<close>.\<close>

abbreviation poly_ethorner_count_state_assn where
  "poly_ethorner_count_state_assn \<equiv>
    (snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_sint_assn \<times>\<^sub>a
     snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a gmp_poly_assn"

text \<open>Condition mop.\<close>

definition poly_ethorner_count_cond ::
  "nat \<Rightarrow> (nat \<times> int \<times> nat) \<times> gmp_poly \<Rightarrow> bool" where
  "poly_ethorner_count_cond limit st \<equiv>
    (let (st1, xs) = st in let (i, last_s, cnt) = st1 in i < limit \<and> cnt < 2)"

sepref_register "PR_CONST poly_ethorner_count_cond"
  :: "nat \<Rightarrow> (nat \<times> int \<times> nat) \<times> gmp_poly \<Rightarrow> bool"

sepref_definition poly_ethorner_count_cond_impl [llvm_inline] is
  "uncurry (RETURN oo poly_ethorner_count_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a poly_ethorner_count_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding poly_ethorner_count_cond_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_ethorner_count_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_ethorner_count_cond_impl,
    uncurry (RETURN oo (PR_CONST poly_ethorner_count_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a poly_ethorner_count_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using poly_ethorner_count_cond_impl.refine
  by (simp add: PR_CONST_def)


text \<open>Body mop.\<close>

definition poly_ethorner_count_body_mop_monadic ::
  "nat \<Rightarrow> (nat \<times> int \<times> nat) \<times> gmp_poly \<Rightarrow> ((nat \<times> int \<times> nat) \<times> gmp_poly) nres" where
"poly_ethorner_count_body_mop_monadic len st \<equiv> doN {
  let (st1, xs) = st;
  let (i, last_s, cnt) = st1;
  ASSERT (length xs = len);
  ASSERT (1 < len);
  ASSERT (i + 1 < len);
  ASSERT (cnt < 2);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  xs' \<leftarrow> (PR_CONST poly_ethorner_inner_loop_monadic) len i xs;
  ASSERT (i < length xs');
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs' i;
  let new_cnt = (if last_s \<noteq> 0 \<and> s \<noteq> 0 \<and> last_s \<noteq> s then cnt + 1 else cnt);
  let new_last_s = (if s \<noteq> 0 then s else last_s);
  RETURN ((i + 1, new_last_s, new_cnt), xs')
}"

sepref_register "PR_CONST poly_ethorner_count_body_mop_monadic"
  :: "nat \<Rightarrow> (nat \<times> int \<times> nat) \<times> gmp_poly \<Rightarrow> ((nat \<times> int \<times> nat) \<times> gmp_poly) nres"

sepref_definition poly_ethorner_count_body_impl [llvm_inline] is
  "uncurry poly_ethorner_count_body_mop_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a poly_ethorner_count_state_assn\<^sup>d \<rightarrow>\<^sub>a poly_ethorner_count_state_assn"
  unfolding poly_ethorner_count_body_mop_monadic_def Let_def
  apply (annot_sint_const gmp_int_t)
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_ethorner_count_body_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_ethorner_count_body_impl,
    uncurry (PR_CONST poly_ethorner_count_body_mop_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a poly_ethorner_count_state_assn\<^sup>d \<rightarrow>\<^sub>a poly_ethorner_count_state_assn"
  using poly_ethorner_count_body_impl.refine
  by (simp add: PR_CONST_def)


text \<open>Result mop.\<close>

definition poly_ethorner_count_result_mop_monadic ::
  "(nat \<times> int \<times> nat) \<times> gmp_poly \<Rightarrow> (nat \<times> int \<times> gmp_poly) nres" where
  "poly_ethorner_count_result_mop_monadic st \<equiv>
    (let (st1, xs) = st in let (i, last_s, cnt) = st1 in RETURN (cnt, last_s, xs))"

sepref_register "PR_CONST poly_ethorner_count_result_mop_monadic"
  :: "(nat \<times> int \<times> nat) \<times> gmp_poly \<Rightarrow> (nat \<times> int \<times> gmp_poly) nres"

sepref_definition poly_ethorner_count_result_impl [llvm_inline] is
  "poly_ethorner_count_result_mop_monadic" ::
  "poly_ethorner_count_state_assn\<^sup>d \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_sint_assn \<times>\<^sub>a gmp_poly_assn"
  unfolding poly_ethorner_count_result_mop_monadic_def Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_ethorner_count_result_impl_hnr[sepref_fr_rules]:
  "(poly_ethorner_count_result_impl,
    PR_CONST poly_ethorner_count_result_mop_monadic) \<in>
    poly_ethorner_count_state_assn\<^sup>d \<rightarrow>\<^sub>a
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_sint_assn \<times>\<^sub>a gmp_poly_assn"
  using poly_ethorner_count_result_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Outer count definition, using the registered mops.\<close>

definition poly_ethorner_count_monadic :: "gmp_poly \<Rightarrow> nat nres" where
"poly_ethorner_count_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  if len \<le> 1 then doN { (PR_CONST poly_free_monadic) xs; RETURN 0 }
  else doN {
    ASSERT (1 < len);
    limit \<leftarrow> RETURN (len - 1);
    ASSERT (limit < length xs);
    s_last \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs limit;
    let init = ((0::nat, 0::int, 0::nat), xs);
    st \<leftarrow> WHILET
      (\<lambda>st. (PR_CONST poly_ethorner_count_cond) limit st)
      (\<lambda>st. (PR_CONST poly_ethorner_count_body_mop_monadic) len st)
      init;
    (cnt, last_s, xs_final) \<leftarrow> (PR_CONST poly_ethorner_count_result_mop_monadic) st;
    extra_f \<leftarrow> (if last_s \<noteq> 0 \<and> s_last \<noteq> 0 \<and> last_s \<noteq> s_last
                then RETURN (1::nat) else RETURN 0);
    ASSERT (cnt + extra_f < max_snat LENGTH(gmp_poly_len));
    final_cnt \<leftarrow> RETURN (cnt + extra_f);
    (PR_CONST poly_free_monadic) xs_final;
    RETURN final_cnt
  }
}"

sepref_register "PR_CONST poly_ethorner_count_monadic"
  :: "gmp_poly \<Rightarrow> nat nres"

sepref_definition poly_ethorner_count_impl [llvm_code] is
  "poly_ethorner_count_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding poly_ethorner_count_monadic_def Let_def
  supply [sepref_fr_rules] =
    poly_ethorner_count_cond_impl_hnr
    poly_ethorner_count_body_impl_hnr
    poly_ethorner_count_result_impl_hnr
  apply (annot_sint_const gmp_int_t)
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_ethorner_count_impl_hnr[sepref_fr_rules]:
  "(poly_ethorner_count_impl,
    PR_CONST poly_ethorner_count_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using poly_ethorner_count_impl.refine
  by (simp add: PR_CONST_def)

subsection \<open>ET-Horner pure model (for the count-correctness keystone)\<close>

text \<open>One descending inner-loop row as a pure function: index @{text m} with
  @{text "m \<ge> i"} becomes the suffix-sum @{term "sum_list (drop m ys)"}; indices
  below @{text i} are untouched. (Falsification of the naive binomial closed form
  and confirmation of this suffix-sum model were established by symbolic simulation.)\<close>
definition ethorner_row_fun :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
  "ethorner_row_fun i ys =
     map (\<lambda>m. if m < i then ys ! m else sum_list (drop m ys)) [0 ..< length ys]"

lemma length_ethorner_row_fun[simp]:
  "length (ethorner_row_fun i ys) = length ys"
  by (simp add: ethorner_row_fun_def)

lemma nth_ethorner_row_fun:
  "m < length ys \<Longrightarrow>
     ethorner_row_fun i ys ! m = (if m < i then ys ! m else sum_list (drop m ys))"
  by (simp add: ethorner_row_fun_def)

lemma take_ethorner_row_fun:
  "take i (ethorner_row_fun i ys) = take i ys"
  by (intro nth_equalityI) (auto simp: ethorner_row_fun_def)

text \<open>The whole outer loop as iterated rows @{text "0,1,\<dots>,i-1"} (row-major
  Taylor shift by 1).\<close>
fun ethorner_outer_step_fun :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
  "ethorner_outer_step_fun 0 ys = ys"
| "ethorner_outer_step_fun (Suc i) ys =
     ethorner_row_fun i (ethorner_outer_step_fun i ys)"

lemma length_ethorner_outer_step_fun[simp]:
  "length (ethorner_outer_step_fun i ys) = length ys"
  by (induction i) simp_all

text \<open>Once row @{text i} finishes, the prefix @{text "take (Suc i)"} is frozen.\<close>
lemma ethorner_outer_step_fun_take_frozen:
  "j \<le> i \<Longrightarrow>
     take j (ethorner_outer_step_fun i ys) = take j (ethorner_outer_step_fun j ys)"
proof (induction i)
  case 0 then show ?case by simp
next
  case (Suc i)
  show ?case
  proof (cases "j \<le> i")
    case True
    have "take j (ethorner_outer_step_fun (Suc i) ys)
        = take j (take i (ethorner_row_fun i (ethorner_outer_step_fun i ys)))"
      using True by (simp add: min.absorb1)
    also have "... = take j (take i (ethorner_outer_step_fun i ys))"
      by (simp add: take_ethorner_row_fun)
    also have "... = take j (ethorner_outer_step_fun i ys)"
      using True by (simp add: min.absorb1)
    also have "... = take j (ethorner_outer_step_fun j ys)" using Suc.IH True by simp
    finally show ?thesis .
  next
    case False with Suc.prems have "j = Suc i" by simp
    then show ?thesis by simp
  qed
qed

definition ethorner_tail :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
  "ethorner_tail i ys = drop i (ethorner_outer_step_fun i ys)"

lemma sum_list_drop_Suc:
  "i < length ys \<Longrightarrow> sum_list (drop i ys) = ys ! i + sum_list (drop (Suc i) ys)"
  by (metis Cons_nth_drop_Suc sum_list_simps(2))

lemma ethorner_row_fun_top: "ethorner_row_fun (length ys - 1) ys = ys"
proof (rule nth_equalityI)
  show "length (ethorner_row_fun (length ys - 1) ys) = length ys" by simp
next
  fix m assume "m < length (ethorner_row_fun (length ys - 1) ys)"
  hence m: "m < length ys" by simp
  show "ethorner_row_fun (length ys - 1) ys ! m = ys ! m"
  proof (cases "m < length ys - 1")
    case True then show ?thesis using m by (simp add: nth_ethorner_row_fun)
  next
    case False with m have "m = length ys - 1" by simp
    then show ?thesis using m
      by (simp add: nth_ethorner_row_fun sum_list_drop_Suc[OF m] last_conv_nth)
  qed
qed

lemma ethorner_row_fun_top_Suc0[simp]:
  "ethorner_row_fun (length ys - Suc 0) ys = ys"
  by (metis ethorner_row_fun_top One_nat_def)

lemma ethorner_row_fun_top_len:
  "length ys = len \<Longrightarrow> ethorner_row_fun (len - 1) ys = ys"
  by (metis ethorner_row_fun_top)

text \<open>The descending in-place update at index @{text "t-1"} turns row-state
  @{term "ethorner_row_fun t ys"} into @{term "ethorner_row_fun (t - 1) ys"}.\<close>
lemma ethorner_row_fun_update_step:
  assumes t: "0 < t" "t < length ys"
  shows "(ethorner_row_fun t ys)
            [t - 1 := ethorner_row_fun t ys ! (t - 1) + ethorner_row_fun t ys ! t]
       = ethorner_row_fun (t - 1) ys"
proof (rule nth_equalityI)
  show "length ((ethorner_row_fun t ys)
            [t - 1 := ethorner_row_fun t ys ! (t - 1) + ethorner_row_fun t ys ! t])
      = length (ethorner_row_fun (t - 1) ys)" by simp
next
  fix m assume "m < length ((ethorner_row_fun t ys)
            [t - 1 := ethorner_row_fun t ys ! (t - 1) + ethorner_row_fun t ys ! t])"
  hence m: "m < length ys" by simp
  have tm1: "t - 1 < length ys" using t by simp
  show "(ethorner_row_fun t ys)
            [t - 1 := ethorner_row_fun t ys ! (t - 1) + ethorner_row_fun t ys ! t] ! m
      = ethorner_row_fun (t - 1) ys ! m"
  proof (cases "m = t - 1")
    case True
    have a: "ethorner_row_fun t ys ! (t - 1) = ys ! (t - 1)"
      using t tm1 by (simp add: nth_ethorner_row_fun)
    have b: "ethorner_row_fun t ys ! t = sum_list (drop t ys)"
      using t m by (simp add: nth_ethorner_row_fun)
    have "ethorner_row_fun t ys ! (t - 1) + ethorner_row_fun t ys ! t = sum_list (drop (t - 1) ys)"
      using a b sum_list_drop_Suc[OF tm1] t by simp
    then show ?thesis using True t m tm1
      by (simp add: nth_list_update nth_ethorner_row_fun)
  next
    case False
    then show ?thesis using m t tm1
      by (auto simp: nth_list_update nth_ethorner_row_fun)
  qed
qed

text \<open>The update step in the descending loop's exact index shape
  (@{text "j = len - Suc(Suc ia)"}, source @{text "j+1 = len - Suc ia"}).\<close>
lemma ethorner_row_fun_loop_step:
  assumes "ia \<le> len - 2" "2 \<le> len" "length ys = len"
  shows "(ethorner_row_fun (len - Suc ia) ys)
            [len - Suc (Suc ia) := ethorner_row_fun (len - Suc ia) ys ! (len - Suc (Suc ia))
                                 + ethorner_row_fun (len - Suc ia) ys ! (len - Suc ia)]
       = ethorner_row_fun (len - Suc (Suc ia)) ys"
proof -
  have a: "0 < len - Suc ia" using assms by linarith
  have b: "len - Suc ia < length ys" using assms by linarith
  have c: "(len - Suc ia) - 1 = len - Suc (Suc ia)" by simp
  show ?thesis
    using ethorner_row_fun_update_step[OF a b] c by simp
qed

text \<open>A1: one ET-Horner inner-loop call refines to one pure row step.\<close>
lemma poly_ethorner_inner_loop_monadic_row:
  assumes "length ys = len" "2 \<le> len" "i < len"
  shows "poly_ethorner_inner_loop_monadic len i ys
    \<le> RETURN (ethorner_row_fun i ys)"
  using assms
  unfolding poly_ethorner_inner_loop_monadic_def poly_add_coeff_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>k xs'.
      length xs' = len \<and> xs' = ethorner_row_fun (len - 1 - k) ys"])
  by (auto simp: ethorner_row_fun_top_len ethorner_row_fun_loop_step)

subsection \<open>ET-Horner Descartes count: keystone correctness (classify trichotomy)\<close>

text \<open>The ET-Horner count loop computes the sign-variation count by an in-place
  row-by-row Horner pass. Its result is not \<open>min 2\<close> of the true count (the loop caps
  at \<open>cnt < 2\<close> but adds the boundary bit unconditionally, so it can return 3); the
  contract the drivers need is the 0/1/\<ge>2 trichotomy proved below as
  @{text poly_ethorner_count_monadic_classify}.\<close>

lemma length_ethorner_tail[simp]: "length (ethorner_tail i ys) = length ys - i"
  by (simp add: ethorner_tail_def)

lemma ethorner_tail_0[simp]: "ethorner_tail 0 ys = ys"
  by (simp add: ethorner_tail_def)

lemma ethorner_tail_nth:
  assumes "r < length ys - i"
  shows "ethorner_tail i ys ! r = ethorner_outer_step_fun i ys ! (i + r)"
  using assms by (simp add: ethorner_tail_def add.commute)

subsection \<open>C1: the tail recurrence (strict suffix sum)\<close>

lemma ethorner_tail_Suc_nth:
  assumes "r < length ys - Suc i"
  shows "ethorner_tail (Suc i) ys ! r = sum_list (drop (Suc (i + r)) (ethorner_outer_step_fun i ys))"
proof -
  have a: "Suc i + r < length ys" using assms by simp
  have "ethorner_tail (Suc i) ys ! r = ethorner_outer_step_fun (Suc i) ys ! (Suc i + r)"
    using assms by (simp add: ethorner_tail_def)
  also have "\<dots> = sum_list (drop (Suc i + r) (ethorner_outer_step_fun i ys))"
    using a by (simp add: nth_ethorner_row_fun)
  finally show ?thesis by (simp add: add.commute)
qed

subsection \<open>TBINOM: taylor coefficient as a binomial sum\<close>

lemma nth_ruffini_step_1:
  "i \<le> length qs \<Longrightarrow>
     ruffini_step 1 a qs ! i
       = (if i = 0 then a else qs ! (i - 1)) + (if i < length qs then qs ! i else 0)"
  by (induction qs arbitrary: a i) (auto simp: nth_Cons split: nat.splits)

lemma taylor_shift_list_nth_binom:
  "i < length ys \<Longrightarrow>
     taylor_shift_list 1 ys ! i = (\<Sum>t = i..<length ys. int (t choose i) * ys ! t)"
proof (induction ys arbitrary: i)
  case Nil then show ?case by simp
next
  case (Cons a as)
  have iL: "i \<le> length as" using Cons.prems by simp
  let ?n = "length as"
  let ?T = "taylor_shift_list 1 as"
  have nth: "taylor_shift_list 1 (a # as) ! i
           = (if i = 0 then a else ?T ! (i - 1)) + (if i < ?n then ?T ! i else 0)"
    using nth_ruffini_step_1[of i ?T a] iL by simp
  show ?case
  proof (cases i)
    case 0
    have R0: "(\<Sum>t = 0..<length (a # as). int (t choose 0) * (a # as) ! t)
            = a + (\<Sum>s = 0..<?n. as ! s)"
    proof -
      have "(\<Sum>t = 0..<Suc ?n. int (t choose 0) * (a # as) ! t)
          = int (0 choose 0) * (a # as) ! 0
          + (\<Sum>t = Suc 0..<Suc ?n. int (t choose 0) * (a # as) ! t)"
        by (rule sum.atLeast_Suc_lessThan[OF zero_less_Suc])
      moreover have "(\<Sum>t = Suc 0..<Suc ?n. int (t choose 0) * (a # as) ! t)
                   = (\<Sum>s = 0..<?n. int (Suc s choose 0) * (a # as) ! (Suc s))"
        by (rule sum.shift_bounds_Suc_ivl)
      ultimately show ?thesis by simp
    qed
    have L0: "taylor_shift_list 1 (a # as) ! 0 = a + (\<Sum>s = 0..<?n. as ! s)"
    proof (cases "?n = 0")
      case True then show ?thesis using nth 0 by simp
    next
      case False
      hence "0 < ?n" by simp
      have "?T ! 0 = (\<Sum>t = 0..<?n. int (t choose 0) * as ! t)"
        using Cons.IH[of 0] False by simp
      then show ?thesis using nth 0 \<open>0 < ?n\<close> by simp
    qed
    show ?thesis using 0 L0 R0 by simp
  next
    case (Suc i')
    have i1: "1 \<le> i" using Suc by simp
    have inL: "i - 1 < ?n" using iL Suc Cons.prems by simp
    have reix: "(\<Sum>t = i..<Suc ?n. int (t choose i) * (a # as) ! t)
              = (\<Sum>s = i - 1..<?n. int (Suc s choose i) * as ! s)"
      using i1 by (intro sum.reindex_bij_witness[where i=Suc and j="\<lambda>t. t - 1"])
                   (auto simp: nth_Cons split: nat.split)
    have split: "(\<Sum>s = i - 1..<?n. int (Suc s choose i) * as ! s)
               = (\<Sum>s = i - 1..<?n. int (s choose i) * as ! s)
               + (\<Sum>s = i - 1..<?n. int (s choose (i - 1)) * as ! s)"
      using Suc by (simp add: binomial_Suc_Suc distrib_right sum.distrib add.commute)
    have part2: "(\<Sum>s = i - 1..<?n. int (s choose (i - 1)) * as ! s) = ?T ! (i - 1)"
      using Cons.IH[of "i - 1"] inL by simp
    have part1: "(\<Sum>s = i - 1..<?n. int (s choose i) * as ! s) = (if i < ?n then ?T ! i else 0)"
    proof -
      have z: "int ((i - 1) choose i) = 0" using i1 by (simp add: binomial_eq_0_iff)
      have drop: "(\<Sum>s = i - 1..<?n. int (s choose i) * as ! s)
                = (\<Sum>s = i..<?n. int (s choose i) * as ! s)"
        using inL z Suc by (subst sum.atLeast_Suc_lessThan[OF inL]) simp
      show ?thesis
      proof (cases "i < ?n")
        case True
        have "(\<Sum>s = i..<?n. int (s choose i) * as ! s) = ?T ! i"
          using Cons.IH[of i] True by simp
        thus ?thesis using drop True by simp
      next
        case False
        hence "?n \<le> i" by simp
        hence "(\<Sum>s = i..<?n. int (s choose i) * as ! s) = 0" by simp
        thus ?thesis using drop False by simp
      qed
    qed
    have "taylor_shift_list 1 (a # as) ! i = ?T ! (i - 1) + (if i < ?n then ?T ! i else 0)"
      using nth Suc by simp
    also have "\<dots> = (\<Sum>t = i..<Suc ?n. int (t choose i) * (a # as) ! t)"
      using reix split part1 part2 by (simp add: add.commute)
    finally show ?thesis by simp
  qed
qed

subsection \<open>Shared combinatorial helpers\<close>

lemma sum_list_drop_nth:
  "sum_list (drop k xs) = (\<Sum>u = k..<length xs. xs ! u)"
proof -
  have "drop k xs = map ((!) xs) [k..<length xs]"
    by (metis drop_map drop_upt map_nth add.left_neutral)
  then show ?thesis
    by (simp add: interv_sum_list_conv_sum_set_nat)
qed

text \<open>Hockey-stick identity.\<close>
lemma choose_hockey:
  "(\<Sum>k = m..<N. (k choose m)) = (N choose Suc m)"
proof (induction N)
  case 0 show ?case by simp
next
  case (Suc N)
  show ?case
  proof (cases "m \<le> N")
    case True
    have "(\<Sum>k = m..<Suc N. (k choose m)) = (\<Sum>k = m..<N. (k choose m)) + (N choose m)"
      using True by simp
    also have "\<dots> = (N choose Suc m) + (N choose m)" by (simp add: Suc.IH)
    finally show ?thesis by simp
  next
    case False
    then show ?thesis by (simp add: binomial_eq_0)
  qed
qed

text \<open>Hockey-stick after the decreasing reindex r' -> u-r'-1, general lower bound a.\<close>
lemma hockey_shifted_gen:
  assumes "1 \<le> i" "a + i \<le> u"
  shows "(\<Sum>r' = a..<Suc (u - i). int ((u - r' - 1) choose (i - 1)))
       = int ((u - a) choose i)"
proof -
  have "(\<Sum>r' = a..<Suc (u - i). int ((u - r' - 1) choose (i - 1)))
      = (\<Sum>v = i - 1..<u - a. int (v choose (i - 1)))"
    using assms
    by (intro sum.reindex_bij_witness[where i="\<lambda>r'. u - r' - 1" and j="\<lambda>v. u - v - 1"]) auto
  also have "\<dots> = int (\<Sum>v = i - 1..<u - a. (v choose (i - 1)))"
    by (simp add: of_nat_sum)
  also have "\<dots> = int ((u - a) choose i)"
    using choose_hockey[of "i - 1" "u - a"] assms by simp
  finally show ?thesis .
qed

text \<open>The triangular Fubini swap.\<close>
lemma triangular_sum_swap:
  "(\<Sum>r' = b..<N - i. (\<Sum>u = r' + i..<N. F r' u))
   = (\<Sum>u = b + i..<N. (\<Sum>r' = b..<Suc (u - i). F r' u))"
proof -
  let ?g = "\<lambda>r' u. (if r' + i \<le> u \<and> r' < N - i then F r' u else 0)"
  have step1: "(\<Sum>r' = b..<N - i. (\<Sum>u = r' + i..<N. F r' u))
             = (\<Sum>r' = b..<N - i. (\<Sum>u = b + i..<N. ?g r' u))"
  proof (rule sum.cong[OF refl])
    fix r' assume r': "r' \<in> {b..<N - i}"
    hence rlt: "r' < N - i" and rge: "b \<le> r'" by auto
    have "(\<Sum>u = r' + i..<N. F r' u) = (\<Sum>u = r' + i..<N. ?g r' u)"
      using rlt by (intro sum.cong[OF refl]) auto
    also have "\<dots> = (\<Sum>u = b + i..<N. ?g r' u)"
      using rge by (intro sum.mono_neutral_left) auto
    finally show "(\<Sum>u = r' + i..<N. F r' u) = (\<Sum>u = b + i..<N. ?g r' u)" .
  qed
  have step2: "(\<Sum>r' = b..<N - i. (\<Sum>u = b + i..<N. ?g r' u))
             = (\<Sum>r' = b..<N. (\<Sum>u = b + i..<N. ?g r' u))"
    by (intro sum.mono_neutral_left) (auto intro!: sum.neutral)
  have step3: "(\<Sum>r' = b..<N. (\<Sum>u = b + i..<N. ?g r' u))
             = (\<Sum>u = b + i..<N. (\<Sum>r' = b..<N. ?g r' u))"
    by (rule sum.swap)
  have step4: "(\<Sum>u = b + i..<N. (\<Sum>r' = b..<N. ?g r' u))
             = (\<Sum>u = b + i..<N. (\<Sum>r' = b..<Suc (u - i). F r' u))"
  proof (rule sum.cong[OF refl])
    fix u assume u: "u \<in> {b + i..<N}"
    have "(\<Sum>r' = b..<N. ?g r' u) = (\<Sum>r' = b..<Suc (u - i). ?g r' u)"
      using u by (intro sum.mono_neutral_right) (auto simp: not_le)
    also have "\<dots> = (\<Sum>r' = b..<Suc (u - i). F r' u)"
      using u by (intro sum.cong[OF refl]) auto
    finally show "(\<Sum>r' = b..<N. ?g r' u) = (\<Sum>r' = b..<Suc (u - i). F r' u)" .
  qed
  show ?thesis using step1 step2 step3 step4 by simp
qed

text \<open>The double-sum that closes the per-element induction and EBINOM.\<close>
lemma binom_double_sum_swap_gen:
  assumes "1 \<le> i"
  shows "(\<Sum>r' = a..<N - i.
            (\<Sum>u = r' + i..<N. int ((u - r' - 1) choose (i - 1)) * c u))
       = (\<Sum>u = a + i..<N. int ((u - a) choose i) * c u)"
proof -
  have "(\<Sum>r' = a..<N - i.
            (\<Sum>u = r' + i..<N. int ((u - r' - 1) choose (i - 1)) * c u))
      = (\<Sum>u = a + i..<N.
            (\<Sum>r' = a..<Suc (u - i). int ((u - r' - 1) choose (i - 1)) * c u))"
    by (rule triangular_sum_swap)
  also have "\<dots> = (\<Sum>u = a + i..<N. int ((u - a) choose i) * c u)"
  proof (rule sum.cong[OF refl])
    fix u assume "u \<in> {a + i..<N}"
    hence u: "a + i \<le> u" by simp
    have "(\<Sum>r' = a..<Suc (u - i). int ((u - r' - 1) choose (i - 1)) * c u)
        = (\<Sum>r' = a..<Suc (u - i). int ((u - r' - 1) choose (i - 1))) * c u"
      by (rule sum_distrib_right[symmetric])
    also have "\<dots> = int ((u - a) choose i) * c u"
      using hockey_shifted_gen[OF assms u] by simp
    finally show "(\<Sum>r' = a..<Suc (u - i). int ((u - r' - 1) choose (i - 1)) * c u)
                = int ((u - a) choose i) * c u" .
  qed
  finally show ?thesis .
qed

subsection \<open>EBINOM / C2: the ET-Horner tail-sum equals the same binomial sum\<close>

text \<open>Cleaner form of C1, directly on the tail.\<close>
lemma ethorner_tail_tail_step:
  assumes "r < length ys - Suc i"
  shows "ethorner_tail (Suc i) ys ! r = sum_list (drop (Suc r) (ethorner_tail i ys))"
  using ethorner_tail_Suc_nth[OF assms]
  by (simp add: ethorner_tail_def drop_drop add.commute)

text \<open>The per-element closed form (i >= 1).\<close>
lemma ethorner_tail_nth_binom:
  "\<lbrakk> 1 \<le> i; r < length ys - i \<rbrakk> \<Longrightarrow>
     ethorner_tail i ys ! r
       = (\<Sum>u = r + i..<length ys. int ((u - r - 1) choose (i - 1)) * ys ! u)"
proof (induction i arbitrary: r)
  case 0 then show ?case by simp
next
  case (Suc i)
  show ?case
  proof (cases "i = 0")
    case True
    have "ethorner_tail (Suc 0) ys ! r = sum_list (drop (Suc r) ys)"
      using Suc.prems True by (simp add: ethorner_tail_tail_step)
    also have "\<dots> = (\<Sum>u = Suc r..<length ys. ys ! u)" by (simp add: sum_list_drop_nth)
    finally show ?thesis using True by simp
  next
    case False
    hence i1: "1 \<le> i" by simp
    have rL: "r < length ys - Suc i" using Suc.prems by simp
    have "ethorner_tail (Suc i) ys ! r = sum_list (drop (Suc r) (ethorner_tail i ys))"
      using rL by (simp add: ethorner_tail_tail_step)
    also have "\<dots> = (\<Sum>r' = Suc r..<length ys - i. ethorner_tail i ys ! r')"
      by (simp add: sum_list_drop_nth)
    also have "\<dots> = (\<Sum>r' = Suc r..<length ys - i.
                       (\<Sum>u = r' + i..<length ys. int ((u - r' - 1) choose (i - 1)) * ys ! u))"
      by (rule sum.cong[OF refl]) (simp add: Suc.IH[OF i1])
    also have "\<dots> = (\<Sum>u = Suc r + i..<length ys.
                       int ((u - r - 1) choose i) * ys ! u)"
      using binom_double_sum_swap_gen[OF i1, where a="Suc r" and N="length ys" and c="(!) ys"]
      by simp
    finally show ?thesis by simp
  qed
qed

lemma ethorner_tail_sum_binom:
  assumes "i < length ys"
  shows "sum_list (ethorner_tail i ys) = (\<Sum>t = i..<length ys. int (t choose i) * ys ! t)"
proof (cases "i = 0")
  case True
  have "sum_list (ethorner_tail i ys) = (\<Sum>t = 0..<length ys. ys ! t)"
    using True by (simp add: sum_list_sum_nth atLeast0LessThan)
  then show ?thesis using True by simp
next
  case False
  hence i1: "1 \<le> i" by simp
  have "sum_list (ethorner_tail i ys) = (\<Sum>r = 0..<length ys - i. ethorner_tail i ys ! r)"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> = (\<Sum>r = 0..<length ys - i.
                     (\<Sum>u = r + i..<length ys. int ((u - r - 1) choose (i - 1)) * ys ! u))"
    by (rule sum.cong[OF refl]) (simp add: ethorner_tail_nth_binom[OF i1])
  also have "\<dots> = (\<Sum>u = 0 + i..<length ys. int ((u - 0) choose i) * ys ! u)"
    by (rule binom_double_sum_swap_gen[OF i1])
  also have "\<dots> = (\<Sum>t = i..<length ys. int (t choose i) * ys ! t)" by simp
  finally show ?thesis .
qed

lemma C2:
  assumes "i < length ys"
  shows "sum_list (ethorner_tail i ys) = taylor_shift_list 1 ys ! i"
  using taylor_shift_list_nth_binom[OF assms] ethorner_tail_sum_binom[OF assms] by simp

subsection \<open>B3: coefficient i is finalized to its taylor value after row i\<close>

lemma ethorner_outer_step_nth_final:
  assumes "i < length ys"
  shows "ethorner_outer_step_fun (Suc i) ys ! i = taylor_shift_list 1 ys ! i"
proof -
  have "ethorner_outer_step_fun (Suc i) ys ! i
      = sum_list (drop i (ethorner_outer_step_fun i ys))"
    using assms by (simp add: nth_ethorner_row_fun)
  also have "\<dots> = sum_list (ethorner_tail i ys)" by (simp add: ethorner_tail_def)
  also have "\<dots> = taylor_shift_list 1 ys ! i" using C2[OF assms] .
  finally show ?thesis .
qed

subsection \<open>INV: the first i coefficients match taylor_shift_list; then W\<close>

lemma ethorner_outer_step_take:
  "i \<le> length ys \<Longrightarrow>
     take i (ethorner_outer_step_fun i ys) = take i (taylor_shift_list 1 ys)"
proof (induction i)
  case 0 then show ?case by simp
next
  case (Suc i)
  have iL: "i < length ys" using Suc.prems by simp
  have "take (Suc i) (ethorner_outer_step_fun (Suc i) ys)
      = take i (ethorner_outer_step_fun (Suc i) ys)
        @ [ethorner_outer_step_fun (Suc i) ys ! i]"
    using iL by (simp add: take_Suc_conv_app_nth)
  also have "take i (ethorner_outer_step_fun (Suc i) ys)
           = take i (ethorner_outer_step_fun i ys)"
    by (simp add: take_ethorner_row_fun)
  also have "\<dots> = take i (taylor_shift_list 1 ys)" using Suc.IH iL by simp
  also have "ethorner_outer_step_fun (Suc i) ys ! i = taylor_shift_list 1 ys ! i"
    using ethorner_outer_step_nth_final[OF iL] .
  finally show ?case
    using iL by (simp add: take_Suc_conv_app_nth)
qed

text \<open>The remaining crux: the two binomial-sum lemmas (TBINOM, EBINOM) above.
  The whole-array equality W is now derivable from INV + the leading-coefficient
  fact, but is NOT needed for the outer assembly (B3 already gives the per-row
  finalized coefficient directly from C2).\<close>

subsection \<open>Count half: the outer WHILET folds @{const sign_step} over the taylor coeffs\<close>

text \<open>The per-step count is monotone on reachable states (@{const sign_step} only
  resets @{text n} to 0 in the @{text "last_s = 0"} branch, where @{text "n = 0"}
  already).\<close>
lemma sign_step_snd_mono:
  "s = 0 \<longrightarrow> n = 0 \<Longrightarrow> n \<le> snd (sign_step x (s, n))"
  by (cases "x = 0"; cases "s = 0"; auto)

text \<open>Reachable fold states satisfy @{text "last_s = 0 \<longrightarrow> cnt = 0"}.\<close>
lemma sign_step_preserves_z:
  "fst acc = 0 \<longrightarrow> snd acc = 0 \<Longrightarrow>
   fst (sign_step x acc) = 0 \<longrightarrow> snd (sign_step x acc) = 0"
  by (cases acc) (auto simp: sgn_0_0 split: if_splits)

lemma fold_sign_step_z_gen:
  "fst acc = 0 \<longrightarrow> snd acc = 0 \<Longrightarrow>
   fst (fold sign_step xs acc) = 0 \<longrightarrow> snd (fold sign_step xs acc) = 0"
proof (induction xs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
    using Cons.IH[of "sign_step x acc"] sign_step_preserves_z[OF Cons.prems] by simp
qed

lemma fold_sign_step_z:
  "fst (fold sign_step xs (0, 0)) = 0 \<Longrightarrow> snd (fold sign_step xs (0, 0)) = 0"
  using fold_sign_step_z_gen[of "(0, 0)" xs] by simp

lemma fold_sign_step_snd_mono:
  "fst acc = 0 \<longrightarrow> snd acc = 0 \<Longrightarrow> snd acc \<le> snd (fold sign_step xs acc)"
proof (induction xs arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x xs)
  have step: "snd acc \<le> snd (sign_step x acc)"
    using Cons.prems by (cases acc) (simp add: sign_step_snd_mono)
  have "snd (sign_step x acc) \<le> snd (fold sign_step xs (sign_step x acc))"
    using Cons.IH[of "sign_step x acc"] sign_step_preserves_z[OF Cons.prems] by simp
  thus ?case using step by simp
qed

text \<open>One more processed coefficient = one more @{const sign_step}.\<close>
lemma fold_sign_step_take_Suc:
  "i < length zs \<Longrightarrow>
     fold sign_step (take (Suc i) zs) (0, 0)
       = sign_step (zs ! i) (fold sign_step (take i zs) (0, 0))"
  by (simp add: take_Suc_conv_app_nth)

text \<open>The count loop body's @{text "(new_last_s, new_cnt)"} update IS
  @{const sign_step}, given the reachable-state invariant.\<close>
lemma sign_step_eq_body:
  assumes "last_s = 0 \<longrightarrow> cnt = 0"
  shows "sign_step x (last_s, cnt)
       = ((if sgn x \<noteq> 0 then sgn x else last_s),
          (if last_s \<noteq> 0 \<and> sgn x \<noteq> 0 \<and> last_s \<noteq> sgn x then cnt + 1 else cnt))"
  using assms by (cases "x = 0") (auto simp: sgn_0_0 split: if_splits)

text \<open>The crux: at loop exit, the running count plus the boundary bit classifies
  exactly like the full sign-change count of the taylor shift. Two cases: the loop
  ran to the end (@{text "i = len-1"}) so the result is the EXACT fold, or it
  capped early (@{text "cnt \<ge> 2"}) so both sides are @{text "\<ge> 2"}.\<close>
lemma ethorner_count_final_classify:
  assumes len: "2 \<le> length ys"
    and i: "i \<le> length ys - 1"
    and st: "(last_s, cnt) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)"
    and exit: "\<not> (i < length ys - 1 \<and> cnt < 2)"
  defines "ef \<equiv> (if last_s \<noteq> 0 \<and> sgn (ys ! (length ys - 1)) \<noteq> 0
                    \<and> last_s \<noteq> sgn (ys ! (length ys - 1)) then 1 else (0::nat))"
  shows "(cnt + ef = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0)
       \<and> (cnt + ef = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1)
       \<and> (2 \<le> cnt + ef) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys))"
proof -
  let ?tl = "taylor_shift_list 1 ys"
  have lentl: "length ?tl = length ys" by simp
  have ysne: "ys \<noteq> []" using len by auto
  have tlne: "?tl \<noteq> []" using len lentl by fastforce
  have rz: "last_s = 0 \<longrightarrow> cnt = 0"
    using st fold_sign_step_z[of "take i ?tl"] by (metis fst_conv snd_conv)
  have bnd: "sgn (?tl ! (length ys - 1)) = sgn (ys ! (length ys - 1))"
  proof -
    have "?tl ! (length ys - 1) = last ?tl" using tlne lentl by (simp add: last_conv_nth)
    also have "\<dots> = last ys" using ysne by (simp add: last_taylor_shift_list)
    also have "\<dots> = ys ! (length ys - 1)" using ysne by (simp add: last_conv_nth)
    finally show ?thesis by simp
  qed
  have snd_eq: "snd (sign_step (?tl ! (length ys - 1)) (last_s, cnt))
              = (if last_s \<noteq> 0 \<and> sgn (?tl ! (length ys - 1)) \<noteq> 0
                   \<and> last_s \<noteq> sgn (?tl ! (length ys - 1)) then cnt + 1 else cnt)"
    by (simp only: sign_step_eq_body[OF rz] snd_conv)
  have valeq: "cnt + ef = snd (sign_step (?tl ! (length ys - 1)) (last_s, cnt))"
    unfolding snd_eq ef_def bnd by (simp split: if_split)
  show ?thesis
  proof (cases "i = length ys - 1")
    case True
    have tk: "take i ?tl = butlast ?tl" using True lentl by (simp add: butlast_conv_take)
    have ln: "?tl ! (length ys - 1) = last ?tl" using tlne lentl by (simp add: last_conv_nth)
    have "cnt + ef = snd (sign_step (last ?tl) (fold sign_step (butlast ?tl) (0, 0)))"
      using valeq st tk ln by simp
    also have "\<dots> = snd (fold sign_step (butlast ?tl @ [last ?tl]) (0, 0))"
      by (simp add: fold_append)
    also have "butlast ?tl @ [last ?tl] = ?tl" using tlne by simp
    finally have "cnt + ef = sign_changes_fold ?tl" by (simp add: sign_changes_fold_def)
    thus ?thesis by simp
  next
    case False
    with i exit have c2: "2 \<le> cnt" by auto
    have mono: "cnt \<le> snd (fold sign_step (drop i ?tl) (last_s, cnt))"
      using fold_sign_step_snd_mono[of "(last_s, cnt)" "drop i ?tl"] rz by simp
    have foldeq: "sign_changes_fold ?tl = snd (fold sign_step (drop i ?tl) (last_s, cnt))"
    proof -
      have "sign_changes_fold ?tl = snd (fold sign_step (take i ?tl @ drop i ?tl) (0, 0))"
        by (simp add: sign_changes_fold_def)
      also have "\<dots> = snd (fold sign_step (drop i ?tl) (fold sign_step (take i ?tl) (0, 0)))"
        by (simp only: fold_append comp_apply)
      also have "\<dots> = snd (fold sign_step (drop i ?tl) (last_s, cnt))" by (simp flip: st)
      finally show ?thesis .
    qed
    from mono c2 foldeq have "2 \<le> sign_changes_fold ?tl" by simp
    thus ?thesis using c2 by simp
  qed
qed

text \<open>One outer-loop body step preserves the invariant and advances @{text i}.\<close>
lemma ethorner_count_body_pres:
  assumes len2: "2 \<le> length ys"
    and iU: "i < length ys - 1"
    and cU: "c < 2"
    and lenxs: "length xs = length ys"
    and xseq: "xs = ethorner_outer_step_fun i ys"
    and steq: "(ls, c) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)"
    and bound: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_ethorner_count_body_mop_monadic (length ys) ((i, ls, c), xs)
    \<le> SPEC (\<lambda>((i', ls', c'), xs').
          i' = Suc i \<and> i' \<le> length ys - 1 \<and> length xs' = length ys
        \<and> xs' = ethorner_outer_step_fun i' ys
        \<and> (ls', c') = fold sign_step (take i' (taylor_shift_list 1 ys)) (0, 0))"
proof -
  let ?tl = "taylor_shift_list 1 ys"
  let ?os = "ethorner_outer_step_fun i ys"
  have iL: "i < length ys" using iU by simp
  have rz: "ls = 0 \<longrightarrow> c = 0"
    using steq fold_sign_step_z[of "take i ?tl"] by (metis fst_conv snd_conv)
  have row: "ethorner_row_fun i ?os = ethorner_outer_step_fun (Suc i) ys" by simp
  have sgn_i: "sgn (ethorner_row_fun i ?os ! i) = sgn (?tl ! i)"
    using row ethorner_outer_step_nth_final[OF iL] by simp
  have iLtl: "i < length ?tl" using iL by simp
  have newstate:
    "((if sgn (?tl ! i) \<noteq> 0 then sgn (?tl ! i) else ls),
      (if ls \<noteq> 0 \<and> sgn (?tl ! i) \<noteq> 0 \<and> ls \<noteq> sgn (?tl ! i) then c + 1 else c))
     = fold sign_step (take (Suc i) ?tl) (0, 0)"
    using sign_step_eq_body[OF rz, of "?tl ! i"]
          fold_sign_step_take_Suc[OF iLtl] steq by simp
  have bodyval: "poly_ethorner_count_body_mop_monadic (length ys) ((i, ls, c), ?os)
     \<le> RETURN ((Suc i,
          (if sgn (?tl ! i) \<noteq> 0 then sgn (?tl ! i) else ls),
          (if ls \<noteq> 0 \<and> sgn (?tl ! i) \<noteq> 0 \<and> ls \<noteq> sgn (?tl ! i) then c + 1 else c)),
        ethorner_row_fun i ?os)"
    unfolding poly_ethorner_count_body_mop_monadic_def poly_coeff_sgn_monadic_def
      PR_CONST_def Let_def
    apply (refine_vcg poly_ethorner_inner_loop_monadic_row[THEN order_trans])
    apply (all \<open>(hypsubst_thin)?\<close>)
    apply (simp_all add: sgn_i len2 cU)
    using iU bound by simp_all
  show ?thesis
    unfolding xseq
    apply (rule order_trans[OF bodyval])
    apply (rule RETURN_rule)
    apply (simp only: prod.case)
    apply (intro conjI)
    subgoal by simp
    subgoal using iU by simp
    subgoal by simp
    subgoal by (rule row)
    subgoal by (rule newstate)
    done
qed

lemma sign_changes_fold_short:
  "length (zs::int list) \<le> 1 \<Longrightarrow> sign_changes_fold zs = 0"
proof -
  assume "length zs \<le> 1"
  then consider "zs = []" | a where "zs = [a]" by (cases zs) auto
  thus "sign_changes_fold zs = 0" by cases (auto simp: sign_changes_fold_def)
qed

lemma scf_taylor_short[simp]:
  "length (ys :: int list) \<le> Suc 0 \<Longrightarrow> sign_changes_fold (taylor_shift_list 1 ys) = 0"
  \<comment> \<open>NB: the obvious \<open>metis ... sign_changes_fold_short\<close> here is PATHOLOGICAL
     (~5+ min, possibly non-terminating -- diagnosed via \<open>isabelle build -v\<close>'s
     per-command timing); the search-free instantiation below is instant. The
     \<open>int list\<close> annotation is needed because \<open>sign_changes_fold_short\<close> is int-typed.\<close>
  using sign_changes_fold_short[of "taylor_shift_list 1 ys"] by simp

text \<open>Count upper bound: each @{const sign_step} bumps the count by at most one,
  so the fold count is bounded by the number of processed coefficients. Needed for
  the result-fits-in-snat side conditions.\<close>
lemma fold_sign_step_snd_le:
  "snd (fold sign_step zs acc) \<le> snd acc + length zs"
proof (induction zs arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x zs)
  have step: "snd (sign_step x acc) \<le> snd acc + 1"
    by (cases acc) (auto split: if_splits)
  have "snd (fold sign_step (x # zs) acc) = snd (fold sign_step zs (sign_step x acc))"
    by simp
  also have "\<dots> \<le> snd (sign_step x acc) + length zs" using Cons.IH .
  also have "\<dots> \<le> snd acc + length (x # zs)" using step by simp
  finally show ?case .
qed

text \<open>Post-loop classify, packaged so the premise shapes match exactly the goals
  @{method refine_vcg} leaves. Yields the FULL @{thm [source]
  ethorner_count_final_classify} trichotomy (with the boundary @{text ef} still an
  @{text "if"}); each keystone post goal then selects a conjunct after its own
  @{text ef} hypothesis collapses the @{text "if"}.\<close>
lemma ethorner_post_full:
  fixes ys :: "int list"
  assumes l2: "Suc 0 < length ys"
    and inv: "i \<le> length ys - Suc 0 \<and> length b = length ys
              \<and> (last_s, cnt) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)"
    and ncond: "i < length ys - Suc 0 \<longrightarrow>
              \<not> (case fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)
                  of (l, c) \<Rightarrow> c < 2)"
  shows "(cnt + (if last_s \<noteq> 0 \<and> sgn (ys ! (length ys - Suc 0)) \<noteq> 0
                  \<and> last_s \<noteq> sgn (ys ! (length ys - Suc 0)) then 1 else 0) = 0)
           = (sign_changes_fold (taylor_shift_list 1 ys) = 0)
       \<and> (cnt + (if last_s \<noteq> 0 \<and> sgn (ys ! (length ys - Suc 0)) \<noteq> 0
                  \<and> last_s \<noteq> sgn (ys ! (length ys - Suc 0)) then 1 else 0) = 1)
           = (sign_changes_fold (taylor_shift_list 1 ys) = 1)
       \<and> (2 \<le> cnt + (if last_s \<noteq> 0 \<and> sgn (ys ! (length ys - Suc 0)) \<noteq> 0
                  \<and> last_s \<noteq> sgn (ys ! (length ys - Suc 0)) then 1 else 0))
           = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys))"
proof -
  have l2': "2 \<le> length ys" using l2 by simp
  have iaa: "i \<le> length ys - 1" using inv by (simp add: One_nat_def)
  have st: "(last_s, cnt) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)"
    using inv by simp
  have ex: "\<not> (i < length ys - 1 \<and> cnt < 2)"
    using ncond by (simp add: st[symmetric] One_nat_def split: prod.splits)
  show ?thesis
    using ethorner_count_final_classify[OF l2' iaa st ex] by (simp add: One_nat_def)
qed

text \<open>The keystone: WHILET assembly from @{thm [source] ethorner_count_body_pres}
  (one loop step preserves the invariant) and @{thm [source] ethorner_count_final_classify}
  (loop exit + boundary -> classify), via @{method refine_vcg} + @{thm WHILET_rule}.
  After @{method refine_vcg} + @{method simp_all} nine obligations remain: the loop
  BODY (goal 1, atomic state -- @{thm [source] ethorner_count_body_pres} only matches
  once the state is destructured); two result-fits-in-snat side conditions (goals 2,6,
  via @{thm [source] fold_sign_step_snd_le}); and six classify conjuncts (goals 3-5
  the boundary @{text "ef=1"} case, 7-9 the @{text "ef=0"} case, all from
  @{thm [source] ethorner_post_full}).\<close>
lemma poly_ethorner_count_monadic_classify:
  assumes "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_ethorner_count_monadic ys
    \<le> SPEC (\<lambda>c.
        (c = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0) \<and>
        (c = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1) \<and>
        (2 \<le> c) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys)))"
  using assms
  unfolding poly_ethorner_count_monadic_def poly_ethorner_count_cond_def
    poly_ethorner_count_result_mop_monadic_def poly_length_monadic_def
    poly_coeff_sgn_monadic_def PR_CONST_def Let_def
  apply (refine_vcg ethorner_count_body_pres
      WHILET_rule[where R="measure (\<lambda>((i, ls, c), xs::int list). length ys - 1 - i)"
        and I="\<lambda>((i, ls, c), xs).
             i \<le> length ys - 1 \<and> length xs = length ys
           \<and> xs = ethorner_outer_step_fun i ys
           \<and> (ls, c) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)"])
  apply (simp_all add: scf_taylor_short)
  \<comment> \<open>Goal 1: the loop body. Destructure the atomic state so
     @{thm [source] ethorner_count_body_pres} unifies, then let @{method refine_vcg}
     run it and discharge the residual invariant/measure side conditions.\<close>
  subgoal premises prems for s
  proof -
    obtain i ls c xs where seq: "s = ((i, ls, c), xs)" by (metis prod.collapse)
    show ?thesis
      unfolding seq
      apply (refine_vcg ethorner_count_body_pres)
      using prems assms by (auto simp: seq One_nat_def split: prod.splits)
  qed
  \<comment> \<open>Goal 2: @{text "Suc bb < max_snat 64"} (boundary @{text "ef = 1"}).\<close>
  subgoal premises prems for s a b aa ba ab bb bc
  proof -
    from prems(3) have "(ab, bb) = fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)"
      by simp
    then have bbeq: "bb = snd (fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0))"
      by (metis snd_conv)
    have "bb \<le> length ys - Suc 0"
      using fold_sign_step_snd_le[of "take aa (taylor_shift_list 1 ys)" "(0, 0)"] bbeq prems(3)
      by simp
    thus ?thesis using prems(1) prems(2) by linarith
  qed
  \<comment> \<open>Goals 3-5: classify conjuncts, boundary @{text "ef = 1"}.\<close>
  subgoal premises prems for s a b aa ba ab bb bc
    using ethorner_post_full[OF prems(2) prems(3) prems(4)] prems(10)
    by (auto split: if_splits)
  subgoal premises prems for s a b aa ba ab bb bc
    using ethorner_post_full[OF prems(2) prems(3) prems(4)] prems(10)
    by (auto split: if_splits)
  subgoal premises prems for s a b aa ba ab bb bc
    using ethorner_post_full[OF prems(2) prems(3) prems(4)] prems(10)
    by (auto split: if_splits)
  \<comment> \<open>Goal 6: @{text "bb < max_snat 64"} (boundary @{text "ef = 0"}).\<close>
  subgoal premises prems for s a b aa ba ab bb bc
  proof -
    from prems(3) have "(ab, bb) = fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)"
      by simp
    then have bbeq: "bb = snd (fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0))"
      by (metis snd_conv)
    have "bb \<le> length ys - Suc 0"
      using fold_sign_step_snd_le[of "take aa (taylor_shift_list 1 ys)" "(0, 0)"] bbeq prems(3)
      by simp
    thus ?thesis using prems(1) prems(2) by linarith
  qed
  \<comment> \<open>Goals 7-9: classify conjuncts, boundary @{text "ef = 0"}.\<close>
  subgoal premises prems for s a b aa ba ab bb bc
    using ethorner_post_full[OF prems(2) prems(3) prems(4)] prems(10)
    by (auto split: if_splits)
  subgoal premises prems for s a b aa ba ab bb bc
    using ethorner_post_full[OF prems(2) prems(3) prems(4)] prems(10)
    by (auto split: if_splits)
  subgoal premises prems for s a b aa ba ab bb bc
    using ethorner_post_full[OF prems(2) prems(3) prems(4)] prems(10)
    by (auto split: if_splits)
  done

end
