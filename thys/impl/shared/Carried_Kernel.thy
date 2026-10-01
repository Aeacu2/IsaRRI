theory Carried_Kernel
  imports Dyadic_Interval "IsaRRI_Spec.Carried_Frame"
begin

text \<open>Carried-transform kernel ops (left homothety, right transform, ET-Horner count).
  Layer: SEPREF. The abstract \<open>int list\<close> targets (\<open>carried_left\<close> / \<open>carried_right\<close> /
  \<open>carried_left_coeff\<close> / \<open>carried_descartes_count\<close> / \<open>carried_init_same_den\<close> /
  \<open>carried_left_shift_cond\<close>) are monad-free and live in \<open>IsaRRI_Spec.Carried_Frame\<close>; the ops
  below refine onto them.

  Main exports: \<open>carried_left_shift_monadic\<close> / \<open>carried_right_monadic\<close> /
  \<open>carried_left_right_monadic\<close> (the split step) and \<open>carried_descartes_count_monadic\<close>
  (the ET-Horner count, classify trichotomy — never exact — see
  \<open>carried_descartes_count_monadic_classify\<close>), each with an \<open>_impl\<close> Sepref definition and
  \<open>_correct\<close>/\<open>_classify\<close> lemma. Consumed by \<open>Bisection.thy\<close>.\<close>


lemma length_carried_left[simp]:
  "length (carried_left xs) = length xs"
  by (simp add: carried_left_def)

lemma nth_carried_left:
  assumes "i < length xs"
  shows "carried_left xs ! i = carried_left_coeff xs i"
  using assms
  unfolding carried_left_def carried_left_coeff_def
  by (simp add: rev_scale_rev_descending enumerate_eq_zip)


lemma poly_free_monadic_bind_rule[refine_vcg]:
  assumes "f () \<le> M"
  shows "poly_free_monadic xs \<bind> f \<le> M"
  using assms poly_free_monadic_rule[of xs]
  by (auto simp: pw_le_iff refine_pw_simps)

lemma poly_reverse_monadic_nofailI:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "nofail (poly_reverse_monadic xs)"
  using poly_reverse_monadic_correct[OF assms]
  by (auto simp: pw_le_iff refine_pw_simps)

lemma poly_reverse_monadic_inresD:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and "inres (poly_reverse_monadic xs) y"
  shows "y = rev xs"
  using poly_reverse_monadic_correct[OF assms(1)] assms(2)
  by (auto simp: pw_le_iff refine_pw_simps)

lemma poly_reverse_monadic_scaled_rev_inresD:
  assumes "Suc (length xs) < max_snat LENGTH(gmp_poly_len)"
    and "inres (poly_reverse_monadic (scale_poly_list 2 (rev xs))) y"
  shows "y = rev (scale_poly_list 2 (rev xs))"
proof -
  have len: "length (scale_poly_list 2 (rev xs)) + 1 <
      max_snat LENGTH(gmp_poly_len)"
    using assms(1) by simp
  show ?thesis
    using poly_reverse_monadic_correct[OF len] assms(2)
    by (auto simp: pw_le_iff refine_pw_simps)
qed

definition poly_clone_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_clone_monadic xs \<equiv> doN {
  one \<leftarrow> RETURN (mpz_from_int 1);
  dst \<leftarrow> (PR_CONST poly_scale_monadic) one xs;
  (PR_CONST mpzb_discard_monadic) one;
  RETURN dst
}"

lemma dsc_scale_poly_list_aux_one_one[simp]:
  "scale_poly_list_aux (1::int) 1 xs = xs"
  by (induction xs) simp_all

lemma poly_clone_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_clone_monadic xs \<le> RETURN xs"
  using assms
  unfolding poly_clone_monadic_def mpzb_discard_monadic_def
    mpz_from_int_def PR_CONST_def
  apply refine_vcg
  apply (rule order_trans)
   apply (rule poly_scale_correct)
   apply simp
  apply (simp add: scale_poly_list_def)
  done

sepref_register "PR_CONST poly_clone_monadic"
  :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_clone_impl [llvm_inline] is
  "poly_clone_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding poly_clone_monadic_def
  apply (annot_uint_const "TYPE(gmp_long_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_clone_impl_hnr[sepref_fr_rules]:
  "(poly_clone_impl, PR_CONST poly_clone_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using poly_clone_impl.refine
  by (simp add: PR_CONST_def)

definition carried_init_same_den_monadic ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"carried_init_same_den_monadic l d r xs \<equiv> doN {
  shifted \<leftarrow> (PR_CONST poly_fractional_taylor_shift_nd_monadic) l d xs;
  ASSERT (length shifted + 1 < max_snat LENGTH(gmp_poly_len));
  width \<leftarrow> RETURN (COPY r);
  width \<leftarrow> (PR_CONST mpz_sub.amop_r1) width l;
  res \<leftarrow> (PR_CONST poly_scale_monadic) width shifted;
  (PR_CONST mpzb_discard_monadic) width;
  (PR_CONST poly_free_monadic) shifted;
  RETURN res
}"

lemma carried_init_same_den_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_init_same_den_monadic l d r xs
    \<le> RETURN (carried_init_same_den l d r xs)"
  using assms
  unfolding carried_init_same_den_monadic_def
    carried_init_same_den_def PR_CONST_def
  apply (refine_vcg
    poly_fractional_taylor_shift_nd_monadic_correct[THEN order_trans]
    poly_scale_correct[THEN order_trans]
    poly_free_monadic_bind_rule
    poly_free_monadic_rule)
  apply (simp_all add: COPY_def mpzb_discard_monadic_def
    mpz_sub.amop_r1_def mpz_sub.aop_r1_def
    pw_le_iff refine_pw_simps)
  done

sepref_register "PR_CONST carried_init_same_den_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition carried_init_same_den_impl [llvm_code] is
  "uncurry3 carried_init_same_den_monadic" ::
  "[\<lambda>(((_, _), _), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding carried_init_same_den_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma carried_init_same_den_impl_hnr[sepref_fr_rules]:
  "(uncurry3 carried_init_same_den_impl,
    uncurry3 (PR_CONST carried_init_same_den_monadic)) \<in>
    [\<lambda>(((_, _), _), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using carried_init_same_den_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Fully IN-PLACE carried init, matching the non-carried route.
  The allocating @{const carried_init_same_den_monadic} does reverse + scale(d) + reverse +
  allocating taylor_shift + allocating scale (~5 allocations; the reverses and scale(1) do nothing for d=1).
  In-place version: 1 allocation (copy) + in-place ops. The denominator dilation
  \<open>rev(scale_for_fractional_shift(2^k)(rev xs)) = (coeff i *= 2^(k(deg-i)))\<close> IS
  @{const poly_shift_pow_in_place_monadic} with m=k — so we thread the EXPONENT k (the wrapper has it),
  no log2/sizeinbase. \<open>carried_init_inplace_monadic_correct\<close> below shows it
  refines the same @{const carried_init_same_den} target with \<open>d = 2^k\<close>. The Newton route reuses
  this op as its window-child transform.\<close>
\<comment> \<open>Skip-shift support at \<open>m = 0\<close> (left block): \<open>taylor_shift_list 0 = id\<close>, so a carried init at
   offset \<open>l = 0\<close> needs no Taylor shift at all. Guarded transparently inside
   \<open>carried_init_inplace_monadic\<close> below (SPEC unchanged), so every \<open>l = 0\<close> caller
   (the block \<open>m = 0\<close> window try) skips the \<open>O(deg\<^sup>2)\<close> shift for one \<open>mpz_sgn\<close> test.\<close>
lemma ruffini_step_0: "ruffini_step 0 a qs = a # qs"
  by (induction qs arbitrary: a) simp_all

lemma taylor_shift_list_0: "taylor_shift_list 0 xs = xs"
  by (induction xs) (simp_all add: ruffini_step_0)

lemma carried_init_same_den_left_block:
  "carried_init_same_den 0 d r xs = scale_poly_list r (rev (scale_for_fractional_shift d 1 (rev xs)))"
  by (simp add: carried_init_same_den_def taylor_shift_list_0)

definition carried_init_inplace_monadic ::
  "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"carried_init_inplace_monadic l k r xs \<equiv> doN {
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length xs - 1) < max_snat LENGTH(gmp_poly_len));
  p \<leftarrow> (PR_CONST poly_copy_monadic) xs;
  ASSERT (length p + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length p - 1) < max_snat LENGTH(gmp_poly_len));
  p \<leftarrow> (PR_CONST poly_shift_pow_in_place_monadic) k p;
  ASSERT (length p + 1 < max_snat LENGTH(gmp_poly_len));
  sgn_l \<leftarrow> (PR_CONST mpz_sgn_mop) l;
  p \<leftarrow> (if sgn_l = 0 then RETURN p
         else (PR_CONST poly_taylor_shift_in_place_monadic) l p);
  width \<leftarrow> RETURN (COPY r);
  width \<leftarrow> (PR_CONST mpz_sub.amop_r1) width l;
  ASSERT (length p + 1 < max_snat LENGTH(gmp_poly_len));
  p \<leftarrow> (PR_CONST poly_scale_in_place_monadic) width p;
  (PR_CONST mpzb_discard_monadic) width;
  RETURN p
}"

sepref_register "PR_CONST carried_init_inplace_monadic"
  :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition carried_init_inplace_impl [llvm_code] is
  "uncurry3 carried_init_inplace_monadic" ::
  "[\<lambda>(((l, k), r), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length xs - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding carried_init_inplace_monadic_def
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma carried_init_inplace_impl_hnr[sepref_fr_rules]:
  "(uncurry3 carried_init_inplace_impl,
    uncurry3 (PR_CONST carried_init_inplace_monadic)) \<in>
    [\<lambda>(((l, k), r), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length xs - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using carried_init_inplace_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Abstract correctness of the fully in-place carried init: the chain
  \<open>copy \<cdot> shift_pow_in_place(k) \<cdot> taylor_shift_in_place(l) \<cdot> scale_in_place(r-l)\<close> refines the
  same @{const carried_init_same_den} target (with denominator \<open>d = 2^k\<close>) as the old
  allocating @{const carried_init_same_den_monadic}. Modelled on
  @{thm [source] carried_init_same_den_monadic_correct}: the shift-pow step plays the role of
  @{term "rev (scale_for_fractional_shift (2^k) 1 (rev xs))"} via
  @{thm [source] shift_pow_map_eq_rev_scale_for_fractional_shift}, then the in-place
  taylor-shift and dilation match @{const taylor_shift_list} / @{const scale_poly_list}. No
  intermediate frees (the single @{const poly_copy_monadic} buffer is mutated in place).\<close>
lemma carried_init_inplace_monadic_correct:
  assumes "0 < length xs"
    and "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and "k * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "carried_init_inplace_monadic l k r xs
    \<le> RETURN (carried_init_same_den l (2 ^ k) r xs)"
  using assms
  unfolding carried_init_inplace_monadic_def
    carried_init_same_den_def PR_CONST_def mpz_sgn_mop_def
  apply (refine_vcg
    poly_copy_correct[THEN order_trans]
    poly_shift_pow_in_place_monadic_correct[THEN order_trans]
    poly_taylor_shift_in_place_monadic_correct[THEN order_trans]
    poly_scale_in_place_correct[THEN order_trans])
  \<comment> \<open>the \<open>l = 0\<close> guard: \<open>sgn l = 0\<close> means the Taylor shift is the identity
     (@{thm [source] taylor_shift_list_0}), so \<open>RETURN p\<close> already matches the target.\<close>
  apply (simp_all add: COPY_def mpzb_discard_monadic_def
    mpz_sub.amop_r1_def mpz_sub.aop_r1_def
    shift_pow_map_eq_rev_scale_for_fractional_shift
    taylor_shift_list_0 sgn_eq_0_iff
    pw_le_iff refine_pw_simps)
  done

definition carried_left_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"carried_left_monadic xs \<equiv> doN {
  rxs \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
  two \<leftarrow> RETURN (mpz_from_int 2);
  scaled \<leftarrow> (PR_CONST poly_scale_monadic) two rxs;
  (PR_CONST mpzb_discard_monadic) two;
  (PR_CONST poly_free_monadic) rxs;
  ASSERT (length scaled + 1 < max_snat LENGTH(gmp_poly_len));
  res \<leftarrow> (PR_CONST poly_reverse_monadic) scaled;
  (PR_CONST poly_free_monadic) scaled;
  RETURN res
}"

lemma carried_left_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_left_monadic xs
    \<le> RETURN (carried_left xs)"
  using assms
  unfolding carried_left_monadic_def carried_left_def PR_CONST_def
  apply (refine_vcg
    poly_reverse_monadic_correct[THEN order_trans]
    poly_scale_correct[THEN order_trans]
    poly_free_monadic_rule)
  apply (simp_all add: scale_for_fractional_shift_eq_scale_poly_list
    mpzb_discard_monadic_def mpz_from_int_def
    pw_le_iff refine_pw_simps)
  apply (auto intro: poly_reverse_monadic_nofailI)
  apply (subgoal_tac "x = rev (scale_poly_list 2 (rev xs))")
   apply simp
  apply (rule poly_reverse_monadic_scaled_rev_inresD)
   apply simp
  apply assumption
  done

sepref_register "PR_CONST carried_left_monadic"
  :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition carried_left_impl [llvm_inline] is
  "carried_left_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding carried_left_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_uint_const "TYPE(gmp_long_len)")
  by sepref

lemma carried_left_impl_hnr[sepref_fr_rules]:
  "(carried_left_impl,
    PR_CONST carried_left_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using carried_left_impl.refine
  by (simp add: PR_CONST_def)

definition carried_left_shift_step_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"carried_left_shift_step_monadic xs len i dst \<equiv> doN {
  ASSERT (len = length xs);
  ASSERT (i < len);
  coeff \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs i;
  let sh = len - (i + 1);
  ASSERT (sh < max_snat LENGTH(gmp_poly_len));
  coeff \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) coeff sh;
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_push_coeff_monadic) dst coeff
}"

lemma carried_left_shift_step_monadic_correct[refine_vcg]:
  assumes "len = length xs"
    and "i < len"
    and "length dst + 1 < max_snat LENGTH(gmp_poly_len)"
    and "len + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_left_shift_step_monadic xs len i dst
    \<le> RETURN (dst @ [carried_left_coeff xs i])"
proof -
  have exp_bound: "len - Suc i < max_snat LENGTH(gmp_poly_len)"
    using assms by simp
  show ?thesis
    unfolding carried_left_shift_step_monadic_def
      poly_copy_coeff_monadic_def poly_push_coeff_monadic_def
      carried_left_coeff_def PR_CONST_def
    using assms exp_bound
    apply (refine_vcg mpz_shift_left_snat_monadic_spec_plain[THEN order_trans])
    apply simp_all
    done
qed

lemma carried_left_shift_step_monadic_invar[refine_vcg]:
  assumes "len = length xs"
    and "i < len"
    and "length dst + 1 < max_snat LENGTH(gmp_poly_len)"
    and "len + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_left_shift_step_monadic xs len i dst
    \<le> SPEC (\<lambda>dst'.
      dst' = dst @ [carried_left_coeff xs i] \<and>
      len - Suc i < len - i)"
  apply (rule order_trans)
   apply (rule carried_left_shift_step_monadic_correct)
       using assms apply simp_all
  done

sepref_register "PR_CONST carried_left_shift_step_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition carried_left_shift_step_impl [llvm_inline] is
  "uncurry3 carried_left_shift_step_monadic" ::
  "[\<lambda>(((xs, len), i), dst).
      len = length xs \<and>
      i < len \<and>
      length dst + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      len + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding carried_left_shift_step_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] = mpz_shift_left_snat_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma carried_left_shift_step_impl_hnr[sepref_fr_rules]:
  "(uncurry3 carried_left_shift_step_impl,
    uncurry3 (PR_CONST carried_left_shift_step_monadic)) \<in>
    [\<lambda>(((xs, len), i), dst).
      len = length xs \<and>
      i < len \<and>
      length dst + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      len + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using carried_left_shift_step_impl.refine
  by (simp add: PR_CONST_def)

abbreviation carried_left_shift_loop_state_assn where
"carried_left_shift_loop_state_assn \<equiv>
  snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"


sepref_register "PR_CONST carried_left_shift_cond"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool"

sepref_definition carried_left_shift_cond_impl [llvm_inline] is
  "uncurry (RETURN oo carried_left_shift_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    carried_left_shift_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding carried_left_shift_cond_def
  unfolding Let_def
  by sepref

lemma carried_left_shift_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry carried_left_shift_cond_impl,
    uncurry (RETURN oo (PR_CONST carried_left_shift_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      carried_left_shift_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using carried_left_shift_cond_impl.refine
  by (simp add: PR_CONST_def)

definition carried_left_shift_loop_body_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow>
    (nat \<times> gmp_poly) nres" where
"carried_left_shift_loop_body_mop_monadic xs len st \<equiv> doN {
  let (i, dst) = st;
  ASSERT (i < len);
  ASSERT (len = length xs);
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST carried_left_shift_step_monadic) xs len i dst;
  ASSERT (i < len);
  RETURN (i + 1, dst)
}"

sepref_register "PR_CONST carried_left_shift_loop_body_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow>
    (nat \<times> gmp_poly) nres"

definition [llvm_code]:
  "carried_left_shift_loop_body_impl xs len st \<equiv> doM {
    let (i, dst) = st;
    dst \<leftarrow> carried_left_shift_step_impl xs len i dst;
    Mreturn (i + 1, dst)
  }"

lemma carried_left_shift_loop_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 carried_left_shift_loop_body_impl,
    uncurry2 (PR_CONST carried_left_shift_loop_body_mop_monadic)) \<in>
    [\<lambda>((xs, len), _).
      len = length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        carried_left_shift_loop_state_assn\<^sup>d \<rightarrow>
      carried_left_shift_loop_state_assn"
  unfolding carried_left_shift_loop_body_impl_def
    carried_left_shift_loop_body_mop_monadic_def PR_CONST_def
  supply [vcg_rules] =
    carried_left_shift_step_impl.refine[to_hnr, THEN hn_refineD,
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

definition carried_left_shift_result_mop_monadic ::
  "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres" where
"carried_left_shift_result_mop_monadic st \<equiv>
  (let (i, dst) = st in RETURN dst)"

sepref_register "PR_CONST carried_left_shift_result_mop_monadic"
  :: "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition carried_left_shift_result_impl [llvm_inline] is
  "carried_left_shift_result_mop_monadic" ::
  "carried_left_shift_loop_state_assn\<^sup>d \<rightarrow>\<^sub>a
    gmp_poly_assn"
  unfolding carried_left_shift_result_mop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma carried_left_shift_result_impl_hnr[sepref_fr_rules]:
  "(carried_left_shift_result_impl,
    PR_CONST carried_left_shift_result_mop_monadic) \<in>
    carried_left_shift_loop_state_assn\<^sup>d \<rightarrow>\<^sub>a
      gmp_poly_assn"
  using carried_left_shift_result_impl.refine
  by (simp add: PR_CONST_def)

definition carried_left_shift_monadic ::
  "gmp_poly \<Rightarrow> gmp_poly nres" where
"carried_left_shift_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (len + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_empty_sz_monadic) len;
  init \<leftarrow> RETURN (0, dst);
  st \<leftarrow> WHILET (\<lambda>st. (PR_CONST carried_left_shift_cond) len st)
    (\<lambda>st. (PR_CONST carried_left_shift_loop_body_mop_monadic) xs len st)
    init;
  (PR_CONST carried_left_shift_result_mop_monadic) st
}"

lemma carried_left_shift_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_left_shift_monadic xs
    \<le> RETURN (carried_left xs)"
  using assms
  unfolding carried_left_shift_monadic_def
    carried_left_shift_cond_def
    carried_left_shift_loop_body_mop_monadic_def
    carried_left_shift_result_mop_monadic_def
    poly_length_monadic_def poly_empty_sz_monadic_def PR_CONST_def
  apply (refine_vcg WHILET_rule[
    where I="\<lambda>(i, dst).
      i \<le> length xs \<and> dst = take i (carried_left xs)"
      and R="measure (\<lambda>(i, _::gmp_poly). length xs - i)"])
  apply (auto simp: take_Suc_conv_app_nth nth_carried_left
    split: prod.splits)
  done

sepref_register "PR_CONST carried_left_shift_monadic"
  :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition carried_left_shift_impl [llvm_code] is
  "carried_left_shift_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding carried_left_shift_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    carried_left_shift_cond_impl_hnr
    carried_left_shift_loop_body_impl_hnr
    carried_left_shift_result_impl_hnr
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

lemma carried_left_shift_impl_hnr[sepref_fr_rules]:
  "(carried_left_shift_impl,
    PR_CONST carried_left_shift_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using carried_left_shift_impl.refine
  by (simp add: PR_CONST_def)

definition carried_right_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"carried_right_monadic xs \<equiv> doN {
  left \<leftarrow> (PR_CONST carried_left_monadic) xs;
  ASSERT (length left + 1 < max_snat LENGTH(gmp_poly_len));
  one \<leftarrow> RETURN (mpz_from_int 1);
  right \<leftarrow> (PR_CONST poly_taylor_shift_monadic) one left;
  (PR_CONST mpzb_discard_monadic) one;
  (PR_CONST poly_free_monadic) left;
  RETURN right
}"

lemma carried_right_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_right_monadic xs
    \<le> RETURN (carried_right xs)"
  using assms
  unfolding carried_right_monadic_def carried_right_def PR_CONST_def
  apply (refine_vcg
    carried_left_monadic_correct[THEN order_trans]
    poly_taylor_shift_monadic_correct[THEN order_trans]
    poly_free_monadic_rule)
  apply (simp_all add: carried_left_def
    mpzb_discard_monadic_def mpz_from_int_def
    pw_le_iff refine_pw_simps)
  done

sepref_register "PR_CONST carried_right_monadic"
  :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition carried_right_impl [llvm_inline] is
  "carried_right_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding carried_right_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_uint_const "TYPE(gmp_long_len)")
  by sepref

lemma carried_right_impl_hnr[sepref_fr_rules]:
  "(carried_right_impl,
    PR_CONST carried_right_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using carried_right_impl.refine
  by (simp add: PR_CONST_def)

definition carried_left_right_monadic ::
  "gmp_poly \<Rightarrow> (gmp_poly \<times> gmp_poly) nres" where
"carried_left_right_monadic xs \<equiv> doN {
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (1 * (length xs - 1) < max_snat LENGTH(gmp_poly_len));
  left \<leftarrow> (PR_CONST poly_shift_pow_in_place_monadic) 1 xs;
  ASSERT (length left + 1 < max_snat LENGTH(gmp_poly_len));
  right \<leftarrow> (PR_CONST poly_copy_monadic) left;
  ASSERT (length right + 1 < max_snat LENGTH(gmp_poly_len));
  right \<leftarrow> (PR_CONST poly_taylor_shift_one_in_place_monadic) right;
  RETURN (left, right)
}"

lemma carried_left_right_monadic_correct:
  assumes "0 < length xs"
    and "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_left_right_monadic xs
    \<le> RETURN (carried_left xs, carried_right xs)"
  \<comment> \<open>Re-derived now that \<open>shift_pow_in_place\<close>'s HNR is PROVEN (the in-place left/right split is certified):
     left \<open>= shift_pow_in_place 1 xs = carried_left xs\<close> (each coeff \<open>i := xs!i*2^(len-1-i)\<close>, the left
     homothety, @{thm nth_carried_left}); right \<open>= taylor_shift_one (copy left) = carried_right xs\<close>
     (@{thm poly_copy_correct}, @{thm poly_taylor_shift_one_in_place_monadic_correct}).\<close>
proof -
  have left_eq:
    "map (\<lambda>i. xs ! i * 2 ^ (length xs - Suc i)) [0..<length xs] = carried_left xs"
    by (intro nth_equalityI)
       (simp_all add: nth_carried_left carried_left_coeff_def)
  show ?thesis
    using assms
    unfolding carried_left_right_monadic_def PR_CONST_def
    apply (refine_vcg
      poly_shift_pow_in_place_monadic_correct[THEN order_trans]
      poly_copy_correct[THEN order_trans]
      poly_taylor_shift_one_in_place_monadic_correct[THEN order_trans])
    apply (simp_all add: left_eq carried_right_def pw_le_iff refine_pw_simps)
    done
qed

sepref_register "PR_CONST carried_left_right_monadic"
  :: "gmp_poly \<Rightarrow> (gmp_poly \<times> gmp_poly) nres"

sepref_definition carried_left_right_impl [llvm_code] is
  "carried_left_right_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn \<times>\<^sub>a gmp_poly_assn"
  unfolding carried_left_right_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma carried_left_right_impl_hnr[sepref_fr_rules]:
  "(carried_left_right_impl,
    PR_CONST carried_left_right_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn \<times>\<^sub>a gmp_poly_assn"
  using carried_left_right_impl.refine
  by (simp add: PR_CONST_def)

definition carried_descartes_count_monadic :: "gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_monadic xs \<equiv> doN {
  rxs \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_ethorner_count_monadic) rxs
}"

text \<open>Control-flow form consumed by the carried bisection driver: the ET-Horner
  count classifies into the same 0/1/\<ge>2 buckets as the exact Descartes count.
  The result is not \<open>min 2\<close> of the true count (the loop can return 3), and the exact and
  \<open>min 2\<close> equality forms are false. Proven from @{thm [source]
  poly_ethorner_count_monadic_classify}.\<close>
lemma carried_descartes_count_monadic_classify:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_monadic xs \<le> SPEC (\<lambda>cnt.
           (cnt = 0) = (carried_descartes_count xs = 0) \<and>
           (cnt = 1) = (carried_descartes_count xs = 1) \<and>
           (2 \<le> cnt) = (2 \<le> carried_descartes_count xs))"
  using assms
  unfolding carried_descartes_count_monadic_def carried_descartes_count_def PR_CONST_def
  apply (refine_vcg
      poly_reverse_monadic_correct[THEN order_trans]
      poly_ethorner_count_monadic_classify[THEN order_trans])
  apply (simp_all add: length_rev)
  done

sepref_register "PR_CONST carried_descartes_count_monadic"
  :: "gmp_poly \<Rightarrow> nat nres"

sepref_definition carried_descartes_count_impl [llvm_code] is
  "carried_descartes_count_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding carried_descartes_count_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma carried_descartes_count_impl_hnr[sepref_fr_rules]:
  "(carried_descartes_count_impl,
    PR_CONST carried_descartes_count_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using carried_descartes_count_impl.refine
  by (simp add: PR_CONST_def)

definition carried_descartes_count_keep_monadic ::
  "gmp_poly \<Rightarrow> (nat \<times> gmp_poly) nres" where
"carried_descartes_count_keep_monadic xs \<equiv> doN {
  cnt \<leftarrow> (PR_CONST carried_descartes_count_monadic) xs;
  RETURN (cnt, xs)
}"

sepref_register "PR_CONST carried_descartes_count_keep_monadic"
  :: "gmp_poly \<Rightarrow> (nat \<times> gmp_poly) nres"

sepref_definition carried_descartes_count_keep_impl [llvm_code] is
  "carried_descartes_count_keep_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow>
      (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a gmp_poly_assn"
  unfolding carried_descartes_count_keep_monadic_def
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

lemma carried_descartes_count_keep_impl_hnr[sepref_fr_rules]:
  "(carried_descartes_count_keep_impl,
    PR_CONST carried_descartes_count_keep_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
        (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a gmp_poly_assn"
  using carried_descartes_count_keep_impl.refine
  by (simp add: PR_CONST_def)

end
