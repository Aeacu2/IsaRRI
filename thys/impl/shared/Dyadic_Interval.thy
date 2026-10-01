theory Dyadic_Interval
imports Interval
begin

text \<open>GMP-backed dyadic interval vectors. An endpoint is a GMP numerator together with a shared
  natural exponent \<open>k\<close>, denoting \<open>n / 2^k\<close>. Bisection needs only numerator doubling and addition:
  \<open>[l/2^k, r/2^k] \<rightarrow> [2l/2^(k+1), (l+r)/2^(k+1)]\<close> and \<open>[(l+r)/2^(k+1), 2r/2^(k+1)]\<close>, so the
  representation avoids rational denominator growth.
  Main definitions: the \<open>dyadic_\<close> vector family and \<open>carried_push_mid_monadic\<close> / \<open>_impl\<close>.\<close>

abbreviation gmp_dyadic_exp_list_assn where
"gmp_dyadic_exp_list_assn \<equiv>
  al_assn' TYPE(gmp_poly_len) (snat_assn' TYPE(gmp_poly_len))"

type_synonym gmp_dyadic_interval_vec =
  "gmp_poly \<times> gmp_poly \<times> nat list"

abbreviation gmp_dyadic_interval_vec_assn where
"gmp_dyadic_interval_vec_assn \<equiv>
  gmp_poly_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a
    gmp_dyadic_exp_list_assn"

definition mpz_double_shift_monadic :: "int \<Rightarrow> int nres" where
"mpz_double_shift_monadic x \<equiv> doN {
  (PR_CONST mpz_mul_2exp.amop_r1) x 1
}"

lemma int_shiftl_one_eq_double[simp]:
  "((x::int) << 1) = 2 * x"
  by (simp add: shiftl_def push_bit_eq_mult algebra_simps)

lemma mpz_double_shift_monadic_spec_shift:
  "(PR_CONST mpz_double_shift_monadic) x \<le> RETURN (x << 1)"
  unfolding mpz_double_shift_monadic_def
    mpz_mul_2exp.amop_r1_def mpz_mul_2exp.aop_r1_def PR_CONST_def
  apply refine_vcg
  apply simp_all
  done

lemma mpz_double_shift_monadic_spec[refine_vcg]:
  "(PR_CONST mpz_double_shift_monadic) x \<le> RETURN (2 * x)"
  using mpz_double_shift_monadic_spec_shift[of x]
  by (simp add: int_shiftl_one_eq_double algebra_simps)

lemma mpz_double_shift_monadic_spec_plain[refine_vcg]:
  "mpz_double_shift_monadic x \<le> RETURN (2 * x)"
  using mpz_double_shift_monadic_spec[of x]
  by (simp add: PR_CONST_def)

sepref_register "PR_CONST mpz_double_shift_monadic" :: "int \<Rightarrow> int nres"

sepref_definition mpz_double_shift_impl [llvm_inline] is
  "mpz_double_shift_monadic" ::
  "mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  unfolding mpz_double_shift_monadic_def
  apply (annot_unat_const "TYPE(gmp_bitcnt_len)")
  by sepref

lemma mpz_double_shift_impl_hnr[sepref_fr_rules]:
  "(mpz_double_shift_impl, PR_CONST mpz_double_shift_monadic) \<in>
    mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  using mpz_double_shift_impl.refine
  by (simp add: PR_CONST_def)

lemma mpz_double_shift_monadic_eq_RETURN[simp]:
  "mpz_double_shift_monadic x = RETURN (2 * x)"
  unfolding mpz_double_shift_monadic_def
    mpz_mul_2exp.amop_r1_def mpz_mul_2exp.aop_r1_def PR_CONST_def
  by (simp add: int_shiftl_one_eq_double algebra_simps)

definition mpz_shift_left_snat_monadic :: "int \<Rightarrow> nat \<Rightarrow> int nres" where
"mpz_shift_left_snat_monadic x k \<equiv> doN {
  k_bit \<leftarrow> (PR_CONST (snat_unat_cast.mop TYPE(gmp_bitcnt_len))) k;
  (PR_CONST mpz_mul_2exp.amop_r1) x k_bit
}"

lemma mpz_shift_left_snat_monadic_spec_shift:
  assumes "k < max_snat LENGTH(gmp_poly_len)"
  shows "(PR_CONST mpz_shift_left_snat_monadic) x k \<le> RETURN (x << k)"
proof -
  have k_unat: "k < max_unat LENGTH(gmp_bitcnt_len)"
    using assms
    by (simp add: max_snat_def max_unat_def)
  show ?thesis
    unfolding mpz_shift_left_snat_monadic_def
      mpz_mul_2exp.amop_r1_def mpz_mul_2exp.aop_r1_def PR_CONST_def
    using k_unat
    apply refine_vcg
    apply simp_all
    done
qed

lemma mpz_shift_left_snat_monadic_spec:
  assumes "k < max_snat LENGTH(gmp_poly_len)"
  shows "(PR_CONST mpz_shift_left_snat_monadic) x k \<le>
    RETURN (x * (2::int) ^ k)"
  using mpz_shift_left_snat_monadic_spec_shift[OF assms, of x]
  by (simp add: shiftl_def push_bit_eq_mult algebra_simps)

lemma mpz_shift_left_snat_monadic_spec_plain[refine_vcg]:
  assumes "k < max_snat LENGTH(gmp_poly_len)"
  shows "mpz_shift_left_snat_monadic x k \<le>
    RETURN (x * (2::int) ^ k)"
  using mpz_shift_left_snat_monadic_spec[OF assms, of x]
  by (simp add: PR_CONST_def)

sepref_register "PR_CONST mpz_shift_left_snat_monadic"
  :: "int \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition mpz_shift_left_snat_impl [llvm_inline] is
  "uncurry mpz_shift_left_snat_monadic" ::
  "[\<lambda>(_, k). k < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  unfolding mpz_shift_left_snat_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [simp] = max_snat_def max_unat_def
  supply [sepref_bounds_simps] = snat_in_bounds_aux
  by sepref

lemma mpz_shift_left_snat_impl_hnr[sepref_fr_rules]:
  "(uncurry mpz_shift_left_snat_impl,
    uncurry (PR_CONST mpz_shift_left_snat_monadic)) \<in>
    [\<lambda>(_, k). k < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  using mpz_shift_left_snat_impl.refine
  by (simp add: PR_CONST_def)

text \<open>In-place per-coefficient kernels. Each mutates the existing handle array in place (no
  @{const poly_empty_sz_monadic}), following @{const poly_add_coeff_monadic}: the implementation
  fetches the slot's mpz via @{const arl_nth} and mutates it via a Sepref-generated scalar op. A raw
  GMP call would skip the @{term mpzb_assn} representation handling and corrupt the coefficient; see
  @{const mpz_shift_left_snat_monadic} for the shift twin. The HNR is
  \<open>poly_shift_coeff_impl_hnr\<close>.\<close>

text \<open>Scalar in-place multiply \<open>r := r * a\<close> keeping ownership of both operands, the multiplication
  twin of @{const mpzb_add_impl} (\<open>Scalar\<close>). A hand-written coefficient op (\<open>arl_nth\<close>, mutate,
  \<open>Mreturn p\<close>) must use a mutator that keeps ownership, whose Hoare triple ends in \<open>ri' = ri\<close>
  (mutate in place, the slot stays owned). A destructive op such as @{const mpz_mul.amop_r1}, whose
  HNR is \<open>\<^sup>d\<close>, makes Sepref orphan the option slot and corrupts the coefficient.\<close>

definition [llvm_code, llvm_inline]:
  "mpzb_mul_impl r a \<equiv> doM {
    mpzb_open r;
    mpzb_open a;
    raw_mpz_mul r r a;
    mpzb_close a;
    mpzb_close r;
    Mreturn r
  }"

lemma mpzb_mul_impl_rule[vcg_rules]:
  "llvm_htriple
    (mpzb_assn r ri \<and>* mpzb_assn a ai)
    (mpzb_mul_impl ri ai)
    (\<lambda>ri'. mpzb_assn (r * a) ri' \<and>* mpzb_assn a ai \<and>* \<up>(ri' = ri))"
  unfolding mpzb_mul_impl_def
  apply vcg'
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pure_unit_rel_eq_empty)
  apply (fact Defer_Slot.remove_slot)
  done

text \<open>Scalar in-place shift-left by a bit count \<open>r := r << k\<close> (\<open>= r * 2^k\<close>) KEEPING ownership of \<open>r\<close> (htriple
  ends \<open>ri' = ri\<close>). Defined as the locale's proven in-place op @{const mpz_mul_2exp.aop_r1_impl}; its htriple is
  the \<^bold>\<open>in-place\<close> conjunct \<open>spec_mx2\<close> of @{thm [source] mpz_mul_2exp.vcg_rule} (the \<open>op ai ai bi\<close> case). This is the
  keep-ownership inner op the per-coeff shift needs: the sepref \<open>^d\<close> shift @{const mpz_shift_left_snat_impl}
  hides \<open>ri'=ri\<close> (drops the locale's \<open>[r=a]\<^sub>c\<close>), orphaning the option slot.\<close>
definition [llvm_code, llvm_inline]:
  "mpzb_mul_2exp_impl \<equiv> mpz_mul_2exp.aop_r1_impl"

lemma mpzb_mul_2exp_impl_rule_heap:
  "llvm_htriple
    (mpzb_assn x ri \<and>* unat_assn k ki)
    (mpzb_mul_2exp_impl ri ki)
    (\<lambda>ri'. mpzb_assn (x << k) ri' \<and>* unat_assn k ki \<and>* \<up>(ri' = ri))"
  unfolding mpzb_mul_2exp_impl_def mpz_mul_2exp.aop_r1_impl_def
  supply [vcg_rules] = mpz_mul_2exp.vcg_rule[THEN conjunct2]
  by vcg'

text \<open>The shift amount as the bit count's \<^bold>\<open>value\<close> \<open>unat ki\<close> (no @{const unat_assn} in the pre), so it composes
  after a cast that extracts the unat to a pure premise. \<open>(ki, unat ki) \<in> unat_rel\<close> always (\<open>unat ki < max_unat\<close>),
  so the heap-form's @{const unat_assn} reduces to \<open>\<box>\<close>.\<close>
lemma mpzb_mul_2exp_impl_rule[vcg_rules]:
  "llvm_htriple
    (mpzb_assn x ri)
    (mpzb_mul_2exp_impl ri ki)
    (\<lambda>ri'. mpzb_assn (x << unat ki) ri' \<and>* \<up>(ri' = ri))"
  using mpzb_mul_2exp_impl_rule_heap[of x ri "unat ki" ki]
  by (simp add: pure_app_eq pure_true_conv sep_algebra_simps unat_rel_def unat.rel_def in_br_conv)

text \<open>Keep-ownership in-place shift by a \<^bold>\<open>snat\<close> amount \<open>r := r * 2^sh\<close>: cast the signed-nat shift to the
  bit-count via the same-size @{const ll_ucast} (\<open>snat_unat_cast\<close>), then the keep-shift. Clean htriple
  with \<open>ri'=ri\<close>, ready for the per-coeff shift focus.\<close>
definition [llvm_code, llvm_inline]:
  "mpzb_shift_left_snat_keep_impl r sh \<equiv> doM {
    k_bit \<leftarrow> ll_ucast sh;
    mpzb_mul_2exp_impl r k_bit
  }"

lemma mpzb_shift_left_snat_keep_impl_rule[vcg_rules]:
  fixes shi :: "gmp_poly_len word"
  shows "llvm_htriple
    (mpzb_assn x ri \<and>* \<upharpoonleft>snat.assn sh shi)
    (mpzb_shift_left_snat_keep_impl ri shi)
    (\<lambda>ri'. mpzb_assn (x * 2 ^ sh) ri' \<and>* \<upharpoonleft>snat.assn sh shi \<and>* \<up>(ri' = ri))"
  unfolding mpzb_shift_left_snat_keep_impl_def
  apply vcg'
   apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
     dr_assn_pure_asm_prefix_def in_unat_rel_conv_assn[symmetric]
     in_snat_rel_conv_assn[symmetric] pure_part_pure pred_lift_extract_simps
     unat_rel_def unat.rel_def snat_rel_def in_br_conv shiftl_def push_bit_eq_mult)
  apply (simp add: DEFER_SLOT_def SOLVE_AUTO_DEFER_def snats_def max_snat_def
    max_unat_def snat_in_bounds_aux)
  done

subsection \<open>In-place scale (dilation \<open>x \<mapsto> c\<cdot>x\<close>): coeff i \<open>:=\<close> xs!i \<open>*\<close> c^i\<close>

text \<open>\<^bold>\<open>In-place dilation.\<close> The count frame needs the dilation \<open>scale_poly_list\<close> (\<open>x \<mapsto> c\<cdot>x\<close>), whose
  coefficient \<open>i\<close> is \<open>xs!i * c^i\<close> (see \<open>scale_poly_list_nth\<close> and \<open>scale_poly_list_aux\<close>), not the
  scalar multiple @{const smult_list}, which multiplies every coefficient by \<open>c\<close> and gives a
  different polynomial with a different Descartes count. The in-place version threads an owned GMP
  power accumulator \<open>acc = c^i\<close> through the loop, as the allocating @{const poly_scale_monadic} does
  (it loops over \<open>(i, dst, acc)\<close> with \<open>acc = acc0 * c^i\<close>). Per coefficient: \<open>coeff i := coeff i * acc\<close>
  (the ownership-keeping @{const mpzb_mul_impl}), then \<open>acc := acc * c\<close>. The trailing accumulator is
  discarded after the loop. The HNR is \<open>poly_scale_coeff_impl_hnr\<close>.\<close>

definition poly_scale_coeff_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> (gmp_poly \<times> int) nres" where
"poly_scale_coeff_monadic xs i acc \<equiv> doN {
  ASSERT (i < length xs);
  RETURN (xs[i := xs ! i * acc], acc)
}"

sepref_register "PR_CONST poly_scale_coeff_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> (gmp_poly \<times> int) nres"

text \<open>Multiply the slot's coefficient by the current power accumulator \<open>acc = c^i\<close>, in place, keeping
  ownership of both the slot and \<open>acc\<close>.\<close>
definition [llvm_code, llvm_inline]:
  "poly_scale_coeff_impl p i acc \<equiv> doM {
    target \<leftarrow> arl_nth p i;
    mpzb_mul_impl target acc;
    Mreturn (p, acc)
  }"

text \<open>Length extraction for a focused-coeff pre carrying a trailing kept scalar \<open>mpzb_assn x ptr\<close> (the
  accumulator). The \<open>snat \<and>* mpzb\<close>-tail twin of @{thm [source] gmp_poly_raw_slots_snat_lenD}; proved like
  @{thm [source] gmp_poly_raw_slots_coeff_lenD} (split the pure conjunction, frame the list_assn).\<close>
lemma gmp_poly_raw_slots_snat_coeff_lenD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn x ptr)
    \<Longrightarrow> length ptrs = length xs"
  by (auto dest!: pure_part_split_conj gmp_poly_slots_len_frameD)

text \<open>Single-slot UPDATE focus: re-inserting a (possibly different) value \<open>x\<close> into the carved slot \<open>i\<close>
  yields the option-slot list of \<open>xs[i := x]\<close>. The update twin of @{thm [source] gmp_poly_slots_unfocus_coeff}
  (which only restores the original \<open>xs ! i\<close>). Derived from @{thm [source] gmp_poly_slots_focus_coeff}
  instantiated at \<open>xs[i := x]\<close>.\<close>
lemma gmp_poly_slots_unfocus_coeff_update:
  assumes "i < length xs"
  shows "(mpzb_assn x (ptrs ! i) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) ((map Some xs)[i := None]) ptrs) =
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some (xs[i := x])) ptrs"
  using gmp_poly_slots_focus_coeff[where xs="xs[i := x]" and i=i and ptrs=ptrs] assms
  by (simp add: map_update nth_list_update_eq)

text \<open>Focused htriple: carve slot \<open>i\<close>, multiply its mpz by the kept accumulator \<open>acc\<close> in place (the proven
  keep-ownership @{const mpzb_mul_impl}, \<open>ri' = ri\<close>), return the (unchanged-handle) array paired with the
  kept \<open>acc\<close>. Models @{thm [source] poly_addmul_coeff_impl_focused_rule} (single slot, external scalar).\<close>
lemma poly_scale_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn acc aci \<and>* mpzb_assn xi (ptrs ! i) \<and>* F)
    (poly_scale_coeff_impl p ii aci)
    (\<lambda>r. F \<and>* raw_al_assn ptrs (fst r) \<and>*
      mpzb_assn acc (snd r) \<and>* mpzb_assn (xi * acc) (ptrs ! i))"
  using assms
  unfolding poly_scale_coeff_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

text \<open>Lift the focused rule to the full option-slot list: slot \<open>i\<close> becomes \<open>xs ! i * acc\<close>.\<close>
lemma poly_scale_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn acc aci)
    (poly_scale_coeff_impl p ii aci)
    (\<lambda>r. raw_al_assn ptrs (fst r) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (xs[i := xs ! i * acc])) ptrs \<and>*
      mpzb_assn acc (snd r))"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_scale_coeff_impl_focused_rule[
      where ptrs=ptrs and i=i
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          ((map Some xs)[i := None]) ptrs"
        and xi="xs ! i" and acc=acc])
    using assms apply simp
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
    gmp_poly_slots_unfocus_coeff_update
    pred_lift_extract_simps pure_def snat.assn_is_rel snat_rel_def)
  done

text \<open>Lift to @{const gmp_poly_assn}.\<close>
lemma poly_scale_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn acc aci)
    (poly_scale_coeff_impl p ii aci)
    (\<lambda>r. gmp_poly_assn (xs[i := xs ! i * acc]) (fst r) \<and>* mpzb_assn acc (snd r))"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_snat_coeff_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_scale_coeff_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def sep_algebra_simps)
    subgoal for r s
      apply (rule exI[where x=ptrs])
      apply (simp add: sep_algebra_simps)
      done
    done
  done

lemma poly_scale_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_scale_coeff_impl,
    uncurry2 (PR_CONST poly_scale_coeff_monadic)) \<in>
    [\<lambda>((xs, i), acc). i < length xs]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  apply sepref_to_hoare
  unfolding poly_scale_coeff_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for acc aci i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_scale_coeff_impl_rule[where acc=acc])
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps prod_assn_def
      dest!: pure_part_split_conj)
    done
  done

text \<open>Per-step accumulator update \<open>acc := acc * c\<close> (keep-ownership of both).\<close>
definition poly_scale_step_acc_monadic :: "int \<Rightarrow> int \<Rightarrow> int nres" where
"poly_scale_step_acc_monadic acc c \<equiv> RETURN (acc * c)"

sepref_register "PR_CONST poly_scale_step_acc_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]:
  "poly_scale_step_acc_impl acc c \<equiv> doM {
    mpzb_mul_impl acc c
  }"

lemma poly_scale_step_acc_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_scale_step_acc_impl,
    uncurry (PR_CONST poly_scale_step_acc_monadic)) \<in>
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  apply sepref_to_hoare
  unfolding poly_scale_step_acc_monadic_def poly_scale_step_acc_impl_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  done

text \<open>The loop's final-multiply guard \<open>i+1 < len\<close> as its own registered op: inline snat arithmetic
  or comparison in a heap-monadic loop body defeats Sepref's opt phase (as for the
  \<open>half_eval_cond\<close> loop-condition op).\<close>
definition scale_more_mop :: "nat \<Rightarrow> nat \<Rightarrow> bool nres" where
"scale_more_mop i len \<equiv> doN { ASSERT (0 < len); RETURN (i < len - 1) }"
  \<comment> \<open>\<open>i < len-1\<close> \<equiv> \<open>i+1 < len\<close> for all \<open>nat\<close> (index \<open>i\<close> is not the last). Stated with monus and \<open><\<close>
     rather than \<open>i+1\<close> to avoid an snat-addition overflow guard; the snat monus needs the
     \<open>ASSERT (0 < len)\<close> guard, discharged at the call site by \<open>i < len\<close>.\<close>

sepref_register "PR_CONST scale_more_mop" :: "nat \<Rightarrow> nat \<Rightarrow> bool nres"

sepref_definition scale_more_impl [llvm_inline] is
  "uncurry scale_more_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding scale_more_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma scale_more_impl_hnr[sepref_fr_rules]:
  "(uncurry scale_more_impl, uncurry (PR_CONST scale_more_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using scale_more_impl.refine by (simp add: PR_CONST_def)

definition poly_scale_loop_monadic ::
  "nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> (gmp_poly \<times> int) nres" where
"poly_scale_loop_monadic len c xs acc0 \<equiv>
  for 0 len (\<lambda>i st. doN {
    let (ys, acc) = st;
    ASSERT (i < length ys);
    (ys, acc) \<leftarrow> (PR_CONST poly_scale_coeff_monadic) ys i acc;
    \<comment> \<open>SKIP the final acc multiply. On the last index (\<open>i+1 = len\<close>)
       the new power \<open>acc0*c^len\<close> is never read — the sole caller
       (\<open>poly_scale_in_place_monadic\<close>) discards \<open>acc\<close> — and it is the LARGEST
       multiply of the pass (\<open>acc\<close> has grown to \<open>~c^(len-1)\<close> bits). Guarding it leaves every
       scaled coefficient \<open>i \<mapsto> xs!i*acc0*c^i\<close> unchanged; only the discarded final \<open>acc\<close>
       drops from \<open>acc0*c^len\<close> to \<open>acc0*c^(len-1)\<close>.\<close>
    more \<leftarrow> (PR_CONST scale_more_mop) i len;
    acc \<leftarrow> (if more then (PR_CONST poly_scale_step_acc_monadic) acc c else RETURN acc);
    RETURN (ys, acc)
  }) (xs, acc0)"

sepref_register "PR_CONST poly_scale_loop_monadic"
  :: "nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> (gmp_poly \<times> int) nres"

sepref_definition poly_scale_loop_impl [llvm_code] is
  "uncurry3 poly_scale_loop_monadic" ::
  "[\<lambda>(((len, c), xs), acc). length xs = len \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  unfolding poly_scale_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  \<comment> \<open>The guarded final multiply (\<open>if i+1<len then step else RETURN acc\<close>) merges an owned mpz
     across branches, which bare \<open>by sepref\<close> cannot synthesise; it uses the explicit \<open>sepref_dbg\<close>
     chain with \<open>trans_keep\<close> and \<open>mpzb_assn_free\<close>, as the other owned-mpz loop bodies here do.\<close>
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
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

lemma poly_scale_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_scale_loop_impl,
    uncurry3 (PR_CONST poly_scale_loop_monadic)) \<in>
    [\<lambda>(((len, c), xs), acc). length xs = len \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  using poly_scale_loop_impl.refine
  by (simp add: PR_CONST_def)

definition poly_scale_in_place_monadic :: "int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_scale_in_place_monadic c xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  acc0 \<leftarrow> RETURN (mpz_from_int 1);
  (dst, acc) \<leftarrow> (PR_CONST poly_scale_loop_monadic) len c xs acc0;
  (PR_CONST mpzb_discard_monadic) acc;
  RETURN dst
}"

sepref_register "PR_CONST poly_scale_in_place_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_scale_in_place_impl [llvm_code] is
  "uncurry poly_scale_in_place_monadic" ::
  "[\<lambda>(c, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_scale_in_place_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_uint_const "TYPE(gmp_long_len)")
  by sepref

lemma poly_scale_in_place_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_scale_in_place_impl,
    uncurry (PR_CONST poly_scale_in_place_monadic)) \<in>
    [\<lambda>(c, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_scale_in_place_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Abstract correctness of the in-place dilation loop: with accumulator \<open>acc = acc0 * c^i\<close>,
  coefficient \<open>i\<close> becomes \<open>xs!i * acc0 * c^i\<close> and the final accumulator is \<open>acc0 * c^len\<close>. Proved by a
  for-loop per-index invariant, the same shape as the shift-pow loop correctness proof below.\<close>
lemma poly_scale_loop_correct:
  assumes "length xs = len"
  shows "poly_scale_loop_monadic len c xs acc0
    \<le> SPEC (\<lambda>(ys, _). ys = map (\<lambda>j. xs ! j * acc0 * c ^ j) [0..<len])"
  \<comment> \<open>The final accumulator (\<open>acc0*c^(len-1)\<close>, the last multiply skipped) is
     a DISCARDED value, so the conclusion pins only the scaled poly (@{const poly_scale_in_place_monadic}
     below still refines @{const scale_poly_list} exactly). The invariant carries
     \<open>acc = acc0*c^(min i (len-1))\<close> — for every processed index \<open>i < len\<close> this is \<open>acc0*c^i\<close>, so
     each coefficient is scaled correctly — but that value never has to be matched at \<open>i = len\<close>.\<close>
  unfolding poly_scale_loop_monadic_def poly_scale_coeff_monadic_def
    poly_scale_step_acc_monadic_def scale_more_mop_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>i st. case st of (ys, acc) \<Rightarrow>
    length ys = len \<and> acc = acc0 * c ^ (min i (len - 1)) \<and>
    (\<forall>j<len. ys ! j = (if j < i then xs ! j * acc0 * c ^ j else xs ! j))"])
  using assms
  by (auto simp: nth_list_update' less_Suc_eq algebra_simps min_def
    intro!: nth_equalityI)

text \<open>@{const scale_poly_list} as an index map over \<open>[0..<len]\<close> — the form the in-place loop produces.\<close>
lemma scale_poly_list_eq_map_upt:
  "scale_poly_list c xs = map (\<lambda>i. xs ! i * c ^ i) [0..<length xs]"
  by (intro nth_equalityI)
     (auto simp: scale_poly_list_eq_map enumerate_eq_zip nth_zip case_prod_beta)

text \<open>@{const poly_scale_in_place_monadic} refines the abstract dilation @{const scale_poly_list}
  (coefficient \<open>i\<close> scaled by \<open>c^i\<close>) — the count-frame width scale.\<close>
lemma poly_scale_in_place_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_scale_in_place_monadic c xs \<le> RETURN (scale_poly_list c xs)"
  unfolding poly_scale_in_place_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg poly_scale_loop_correct[THEN order_trans])
  using assms
  by (auto simp: scale_poly_list_eq_map_upt mpz_from_int_def
    mpzb_discard_monadic_def pw_le_iff refine_pw_simps)

text \<open>Bridge: the in-place shift-by-power transform (coefficient \<open>i\<close> times \<open>2^(k*(deg-i))\<close>) is exactly
  the reversed fractional-shift scale @{term "rev (scale_for_fractional_shift (2^k) 1 (rev xs))"} used by
  the carried same-denominator init. Load-bearing for the in-place carried init correctness.\<close>
lemma shift_pow_map_eq_rev_scale_for_fractional_shift:
  fixes xs :: "int list"
  shows "map (\<lambda>i. xs ! i * 2 ^ (k * (length xs - Suc i))) [0..<length xs]
       = rev (scale_for_fractional_shift (2 ^ k) 1 (rev xs))"
proof (rule nth_equalityI)
  show "length (map (\<lambda>i. xs ! i * 2 ^ (k * (length xs - Suc i))) [0..<length xs])
      = length (rev (scale_for_fractional_shift (2 ^ k) 1 (rev xs)))"
    by simp
next
  fix j assume "j < length (map (\<lambda>i. xs ! i * 2 ^ (k * (length xs - Suc i))) [0..<length xs])"
  hence j: "j < length xs" by simp
  hence m: "length xs - Suc j < length xs" by simp
  have "rev (scale_for_fractional_shift (2 ^ k) 1 (rev xs)) ! j
      = scale_for_fractional_shift (2 ^ k) 1 (rev xs) ! (length xs - Suc j)"
    using j by (simp add: rev_nth)
  also have "\<dots> = (rev xs) ! (length xs - Suc j) * (2 ^ k) ^ (length xs - Suc j)"
    using m by (simp add: scale_for_fractional_shift_eq_map enumerate_eq_zip nth_zip)
  also have "(rev xs) ! (length xs - Suc j) = xs ! j"
    using j by (simp add: rev_nth)
  also have "(2 ^ k) ^ (length xs - Suc j) = (2::int) ^ (k * (length xs - Suc j))"
    by (simp add: power_mult)
  finally show "map (\<lambda>i. xs ! i * 2 ^ (k * (length xs - Suc i))) [0..<length xs] ! j
      = rev (scale_for_fractional_shift (2 ^ k) 1 (rev xs)) ! j"
    using j by simp
qed

subsection \<open>In-place shift-left-by-power: coeff i \<open><<=\<close> m*(deg-i)\<close>

text \<open>One kernel for both per-coefficient power-of-two scalings used in the count-frame transform:
  the dyadic start-scale (m = k: coeff i \<open>*=\<close> 2^(k*(deg-i))) and the carried left
  homothety (m = 1: coeff i \<open>*=\<close> 2^(deg-i)). deg = len-1. The per-coeff shift reuses the proven scalar
  @{const mpz_shift_left_snat_monadic} impl (which does the snat\<rightarrow>bitcnt cast) on the slot's mpz in place.
  (\<open>mult\<close> is avoided as a variable name: it parses as the constant @{const Groups.times_class.times}.)\<close>

definition poly_shift_coeff_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly nres" where
"poly_shift_coeff_monadic xs i sh \<equiv> doN {
  ASSERT (i < length xs);
  RETURN (xs[i := xs ! i * 2 ^ sh])
}"

sepref_register "PR_CONST poly_shift_coeff_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly nres"

definition [llvm_code, llvm_inline]:
  "poly_shift_coeff_impl p i sh \<equiv> doM {
    target \<leftarrow> arl_nth p i;
    mpzb_shift_left_snat_keep_impl target sh;
    Mreturn p
  }"

text \<open>Focused htriple: shift slot \<open>i\<close>'s mpz left by \<open>sh\<close> in place (the keep-ownership
  @{const mpzb_shift_left_snat_keep_impl}, \<open>ri'=ri\<close>), keeping the snat \<open>sh\<close>. Single-slot update returning
  the (unchanged-handle) array, modeled on @{thm [source] poly_scale_coeff_impl_focused_rule}.\<close>
lemma poly_shift_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii shi :: "gmp_poly_len word"
  assumes "i < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<upharpoonleft>snat.assn sh shi \<and>*
      mpzb_assn xi (ptrs ! i) \<and>* F)
    (poly_shift_coeff_impl p ii shi)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      (mpzb_assn (xi * 2 ^ sh) (ptrs ! i) \<and>* F) \<and>* \<upharpoonleft>snat.assn sh shi)"
  using assms
  unfolding poly_shift_coeff_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

text \<open>Lift to the option-slot list: slot \<open>i\<close> becomes \<open>xs ! i * 2 ^ sh\<close>.\<close>
lemma poly_shift_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii shi :: "gmp_poly_len word"
  assumes "i < length xs"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* \<upharpoonleft>snat.assn sh shi)
    (poly_shift_coeff_impl p ii shi)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (xs[i := xs ! i * 2 ^ sh])) ptrs \<and>* \<upharpoonleft>snat.assn sh shi)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_shift_coeff_impl_focused_rule[
      where ptrs=ptrs and i=i and sh=sh
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          ((map Some xs)[i := None]) ptrs"
        and xi="xs ! i"])
    using assms apply simp
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps
    gmp_poly_slots_unfocus_coeff_update)
  done

text \<open>Lift to @{const gmp_poly_assn}.\<close>
lemma poly_shift_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii shi :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<upharpoonleft>snat.assn sh shi)
    (poly_shift_coeff_impl p ii shi)
    (\<lambda>p'. gmp_poly_assn (xs[i := xs ! i * 2 ^ sh]) p' \<and>* \<upharpoonleft>snat.assn sh shi)"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_two_snat_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_shift_coeff_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def sep_algebra_simps)
    subgoal for p' s
      apply (rule exI[where x=ptrs])
      apply (simp add: sep_algebra_simps)
      done
    done
  done

lemma poly_shift_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_shift_coeff_impl,
    uncurry2 (PR_CONST poly_shift_coeff_monadic)) \<in>
    [\<lambda>((xs, i), sh). i < length xs \<and> sh < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_shift_coeff_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for sh shi i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_shift_coeff_impl_rule[where sh=sh])
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps
      snat.assn_is_rel snat_rel_def pure_def)
    done
  done

section \<open>In-place reflection sign-flip
  (negate odd-index coefficients only, zero general multiplies)\<close>

text \<open>Per-coefficient in-place negation \<open>xs[i] := -xs!i\<close>, using the focus/unfocus pattern of
  @{const poly_shift_coeff_monadic}/@{const poly_shift_coeff_impl} with a different leaf: instead of
  @{const mpzb_shift_left_snat_keep_impl}, the single-argument in-place \<open>mpz_neg.aop_r_impl\<close>
  (\<open>GMP_Bindings\<close>, locale \<open>mpz_unary_spec_m_axiom\<close>), i.e. GMP's \<open>mpz_neg\<close> called with the same
  pointer for both arguments (aliasing that GMP permits for unary operations), returning the same
  handle (\<open>r'=r\<close>). No allocation and no multiplication.\<close>

definition poly_negate_coeff_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly nres" where
"poly_negate_coeff_monadic xs i \<equiv> doN {
  ASSERT (i < length xs);
  RETURN (xs[i := - (xs ! i)])
}"

sepref_register "PR_CONST poly_negate_coeff_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly nres"

definition [llvm_code, llvm_inline]:
  "poly_negate_coeff_impl p i \<equiv> doM {
    target \<leftarrow> arl_nth p i;
    mpz_neg.aop_r_impl target;
    Mreturn p
  }"

text \<open>Raw htriple for \<open>mpz_neg.aop_r_impl\<close>, the KEEP-ownership in-place negate (\<open>ri'=ri\<close>). Derived
  from the locale's OWN combined vcg rule \<open>mpz_neg.vcg_rule\<close> (\<open>spec_m = spec_m2 \<and> spec\<close>), taking
  \<open>conjunct1\<close> (\<open>spec_m2\<close>, the aliased-argument in-place case: \<open>fi ai ai\<close>) -- the SAME derivation
  pattern @{thm [source] mpzb_mul_2exp_impl_rule_heap} uses for the binary \<open>mpz_mul_2exp\<close> locale
  (which takes \<open>conjunct2\<close> there since its \<open>spec_mx\<close> pairing puts the in-place case second).\<close>
lemma mpz_neg_aop_r_impl_rule[vcg_rules]:
  "llvm_htriple
    (mpzb_assn x ri)
    (mpz_neg.aop_r_impl ri)
    (\<lambda>ri'. mpzb_assn (- x) ri' \<and>* \<up>(ri' = ri))"
  unfolding mpz_neg.aop_r_impl_def
  supply [vcg_rules] = mpz_neg.vcg_rule[THEN conjunct1]
  by vcg'

text \<open>Focused htriple: negate slot \<open>i\<close>'s mpz in place. Modeled directly on
  @{thm [source] poly_shift_coeff_impl_focused_rule}.\<close>
lemma poly_negate_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn xi (ptrs ! i) \<and>* F)
    (poly_negate_coeff_impl p ii)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      (mpzb_assn (- xi) (ptrs ! i) \<and>* F))"
  using assms
  unfolding poly_negate_coeff_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

text \<open>Lift to the option-slot list.\<close>
lemma poly_negate_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii)
    (poly_negate_coeff_impl p ii)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (xs[i := - (xs ! i)])) ptrs)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_negate_coeff_impl_focused_rule[
      where ptrs=ptrs and i=i
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          ((map Some xs)[i := None]) ptrs"
        and xi="xs ! i"])
    using assms apply simp
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps
    gmp_poly_slots_unfocus_coeff_update)
  done

text \<open>Lift to @{const gmp_poly_assn}.\<close>
lemma poly_negate_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii)
    (poly_negate_coeff_impl p ii)
    (\<lambda>p'. gmp_poly_assn (xs[i := - (xs ! i)]) p')"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_snat_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_negate_coeff_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def sep_algebra_simps)
    subgoal for p' s
      apply (rule exI[where x=ptrs])
      apply (simp add: sep_algebra_simps)
      done
    done
  done

lemma poly_negate_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_negate_coeff_impl,
    uncurry (PR_CONST poly_negate_coeff_monadic)) \<in>
    [\<lambda>(xs, i). i < length xs]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_negate_coeff_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_negate_coeff_impl_rule)
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps
      snat.assn_is_rel snat_rel_def pure_def)
    done
  done

text \<open>The full reflection loop: negate ODD-index coefficients only, matching
  \<open>refl_list xs = map (\<lambda>i. if even i then xs!i else - xs!i) [0..<length xs]\<close>
  (\<open>Kiou_Bound_Spec.thy\<close> -- a separate session this file does not import; the target here is
  stated as the plain \<open>map\<close> formula directly, see \<open>poly_reflect_in_place_correct\<close> below).
  Rather than a per-index CONDITIONAL negate (which Sepref's
  \<open>for\<close>-loop synthesis cannot compose -- the two branches' destructive \<open>gmp_poly\<close> frames don't
  merge automatically, confirmed: synthesis collapses the array assertion to \<open>hn_val UNIV\<close>), this
  loop walks ONLY the odd positions directly: \<open>j\<close> ranges over \<open>0..<len div 2\<close> and each step
  UNCONDITIONALLY negates coefficient \<open>2*j+1\<close> -- no branch inside the loop body at all, matching
  the same unconditional-loop shape as \<open>poly_shift_pow_loop_monadic\<close> below.\<close>
text \<open>The index arithmetic \<open>2*j+1\<close> as its own registered op: a heap-op body may contain only
  registered-op calls, ASSERTs, destructuring and a final tuple \<open>RETURN\<close>; inline arithmetic inside a
  \<open>for\<close>-loop body blocks the \<open>opt\<close> phase and collapses the destructive \<open>gmp_poly\<close> frame to
  \<open>hn_val UNIV\<close>.\<close>
definition poly_reflect_odd_idx_monadic :: "nat \<Rightarrow> nat nres" where
"poly_reflect_odd_idx_monadic j \<equiv> doN {
  ASSERT (2 * j + 1 < max_snat LENGTH(gmp_poly_len));
  RETURN (2 * j + 1)
}"

sepref_register "PR_CONST poly_reflect_odd_idx_monadic" :: "nat \<Rightarrow> nat nres"

sepref_definition poly_reflect_odd_idx_impl [llvm_inline] is
  "poly_reflect_odd_idx_monadic" ::
  "[\<lambda>j. 2 * j + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding poly_reflect_odd_idx_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_reflect_odd_idx_impl_hnr[sepref_fr_rules]:
  "(poly_reflect_odd_idx_impl, PR_CONST poly_reflect_odd_idx_monadic) \<in>
    [\<lambda>j. 2 * j + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using poly_reflect_odd_idx_impl.refine by (simp add: PR_CONST_def)

definition poly_reflect_loop_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_reflect_loop_monadic len xs \<equiv>
  for 0 (len div 2) (\<lambda>j ys. doN {
    ASSERT (2 * j + 1 < max_snat LENGTH(gmp_poly_len));
    idx \<leftarrow> (PR_CONST poly_reflect_odd_idx_monadic) j;
    ASSERT (idx < length ys);
    (PR_CONST poly_negate_coeff_monadic) ys idx
  }) xs"

sepref_register "PR_CONST poly_reflect_loop_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_reflect_loop_impl [llvm_inline] is
  "uncurry poly_reflect_loop_monadic" ::
  "[\<lambda>(len, xs). length xs = len]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_reflect_loop_monadic_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_fr_rules] = poly_negate_coeff_impl_hnr poly_reflect_odd_idx_impl_hnr
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

lemma poly_reflect_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_reflect_loop_impl, uncurry (PR_CONST poly_reflect_loop_monadic)) \<in>
    [\<lambda>(len, xs). length xs = len]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_reflect_loop_impl.refine by (simp add: PR_CONST_def)

definition poly_reflect_in_place_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_reflect_in_place_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  (PR_CONST poly_reflect_loop_monadic) len xs
}"

sepref_register "PR_CONST poly_reflect_in_place_monadic" :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_reflect_in_place_impl [llvm_code] is
  "poly_reflect_in_place_monadic" ::
  "gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  unfolding poly_reflect_in_place_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_reflect_in_place_impl_hnr[sepref_fr_rules]:
  "(poly_reflect_in_place_impl, PR_CONST poly_reflect_in_place_monadic) \<in>
    gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  using poly_reflect_in_place_impl.refine by (simp add: PR_CONST_def)

text \<open>Correctness: the loop's per-\<open>j\<close> invariant says indices \<open>< 2*j\<close> are fully reflected; since
  even indices are already correct without any operation (the touched index at step \<open>j\<close> is only
  \<open>2*j+1\<close>), the boundary case (\<open>len\<close> odd, the untouched top index \<open>len-1\<close> is even) is benign.\<close>
lemma poly_reflect_loop_correct:
  assumes "length xs = len" and "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_reflect_loop_monadic len xs
    \<le> RETURN (map (\<lambda>j. if even j then xs ! j else - (xs ! j)) [0..<len])"
  unfolding poly_reflect_loop_monadic_def poly_negate_coeff_monadic_def
    poly_reflect_odd_idx_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>j ys.
    length ys = len \<and>
    (\<forall>k<len. ys ! k = (if k < 2 * j then (if even k then xs ! k else - (xs ! k)) else xs ! k))"])
  using assms
  subgoal by simp
  subgoal using assms by simp
  subgoal by simp
  subgoal premises p
    using p assms div_mult_mod_eq[of len 2] by linarith
  subgoal by simp
  subgoal by simp
  subgoal by (auto simp: nth_list_update' less_Suc_eq)
  subgoal by (auto intro!: nth_equalityI; presburger)
  done

text \<open>The target is stated as the plain \<open>map\<close> formula rather than via \<open>refl_list\<close>, which is defined
  in \<open>Kiou_Bound_Spec\<close>. Callers with \<open>refl_list\<close> in scope (\<open>Kiou_Bound_Reflect\<close>) bridge the one-line
  equality (\<open>refl_list_def\<close> is this \<open>map\<close> formula).\<close>
lemma poly_reflect_in_place_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_reflect_in_place_monadic xs
    \<le> RETURN (map (\<lambda>j. if even j then xs ! j else - (xs ! j)) [0..<length xs])"
  unfolding poly_reflect_in_place_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg poly_reflect_loop_correct[THEN order_trans])
  using assms
  by auto

definition poly_shift_pow_loop_monadic :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_shift_pow_loop_monadic m dg len xs \<equiv>
  for 0 len (\<lambda>i ys. doN {
    ASSERT (i < length ys);
    ASSERT (i \<le> dg);
    ASSERT (m * (dg - i) < max_snat LENGTH(gmp_poly_len));
    (PR_CONST poly_shift_coeff_monadic) ys i (m * (dg - i))
  }) xs"

sepref_register "PR_CONST poly_shift_pow_loop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_shift_pow_loop_impl [llvm_code] is
  "uncurry3 poly_shift_pow_loop_monadic" ::
  "[\<lambda>(((m, dg), len), xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      m * dg < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_shift_pow_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_shift_pow_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_shift_pow_loop_impl,
    uncurry3 (PR_CONST poly_shift_pow_loop_monadic)) \<in>
    [\<lambda>(((m, dg), len), xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      m * dg < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_shift_pow_loop_impl.refine
  by (simp add: PR_CONST_def)

definition poly_shift_pow_in_place_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_shift_pow_in_place_monadic m xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (0 < len);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_shift_pow_loop_monadic) m (len - 1) len xs
}"

sepref_register "PR_CONST poly_shift_pow_in_place_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_shift_pow_in_place_impl [llvm_code] is
  "uncurry poly_shift_pow_in_place_monadic" ::
  "[\<lambda>(m, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      m * (length xs - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_shift_pow_in_place_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_shift_pow_in_place_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_shift_pow_in_place_impl,
    uncurry (PR_CONST poly_shift_pow_in_place_monadic)) \<in>
    [\<lambda>(m, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      m * (length xs - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_shift_pow_in_place_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Abstract correctness of the shift-pow loop/wrapper: coefficient \<open>i\<close> is multiplied by
  \<open>2^(m*(deg-i))\<close> (the descending power-of-two dilation). Foundational for the carried in-place
  init's \<open>_correct\<close> (where with m=k it equals \<open>rev (scale_for_fractional_shift (2^k) 1 (rev xs))\<close>).\<close>
lemma poly_shift_pow_loop_monadic_correct:
  assumes "length xs = len" and "len \<le> Suc dg"
    and "m * dg < max_snat LENGTH(gmp_poly_len)"
  shows "poly_shift_pow_loop_monadic m dg len xs
    \<le> RETURN (map (\<lambda>i. xs ! i * 2 ^ (m * (dg - i))) [0..<len])"
  unfolding poly_shift_pow_loop_monadic_def poly_shift_coeff_monadic_def
  apply (refine_vcg for_rule[where I="\<lambda>i ys. length ys = len \<and>
    (\<forall>j<len. ys ! j = (if j < i then xs ! j * 2 ^ (m * (dg - j)) else xs ! j))"])
  using assms
  by (auto simp: nth_list_update' less_Suc_eq
    intro!: nth_equalityI intro: le_less_trans[OF mult_le_mono2[OF diff_le_self]])

lemma poly_shift_pow_in_place_monadic_correct:
  assumes "0 < length xs"
    and "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and "m * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "poly_shift_pow_in_place_monadic m xs
    \<le> RETURN (map (\<lambda>i. xs ! i * 2 ^ (m * (length xs - 1 - i))) [0..<length xs])"
  unfolding poly_shift_pow_in_place_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg
    poly_shift_pow_loop_monadic_correct[where dg = "length xs - 1", THEN order_trans])
  using assms by (auto simp: diff_diff_left)

subsection \<open>In-place reverse: swap handle pointers, zero allocation\<close>

text \<open>For the non-carried count the working buffer is owned and immediately consumed by the
  ET-Horner count, so the per-node \<open>reverse\<close> is done in place by swapping the mpz handle pointers in
  the array (no fresh mpz, no @{const poly_empty_sz_monadic}). @{const arl_upd} is a pure pointer
  write (no free; @{const poly_put_coeff_monadic} uses it on \<open>None\<close> slots); the swap captures both
  handles first, so neither is freed and each lands in exactly one slot. The abstract value is
  \<open>rev\<close>; the HNR is \<open>poly_swap_coeff_impl_hnr\<close>. The carried count still needs a copy, because \<open>Q\<close>
  must survive a split.\<close>

definition poly_swap_coeff_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly nres" where
"poly_swap_coeff_monadic xs i j \<equiv> doN {
  ASSERT (i < length xs);
  ASSERT (j < length xs);
  RETURN (xs[i := xs ! j, j := xs ! i])
}"

sepref_register "PR_CONST poly_swap_coeff_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly nres"

definition [llvm_code, llvm_inline]:
  "poly_swap_coeff_impl p i j \<equiv> doM {
    a \<leftarrow> arl_nth p i;
    b \<leftarrow> arl_nth p j;
    p \<leftarrow> arl_upd p i b;
    p \<leftarrow> arl_upd p j a;
    Mreturn p
  }"

text \<open>The swap unfocus: focus both slots out, then re-insert with the handle pointers exchanged. No
  reindex / None-independence lemma is needed — @{thm [source] gmp_poly_slots_insert_some} threads the
  swapped ptr forward at each insert. Covers \<open>i = j\<close> (then both updates are no-ops) so the HNR precondition
  need not exclude it.\<close>
lemma gmp_poly_slots_swap_eq:
  assumes "i < length xs" and "j < length xs"
  shows "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
      (map Some (xs[i := xs ! j, j := xs ! i])) (ptrs[i := ptrs ! j, j := ptrs ! i])
    = \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs"
proof (cases "i = j")
  case True
  thus ?thesis by simp
next
  case False
  have ins_i: "(mpzb_assn (xs ! j) (ptrs ! j) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) ((map Some xs)[i := None, j := None]) ptrs)
    = \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        ((map Some xs)[i := None, j := None, i := Some (xs ! j)]) (ptrs[i := ptrs ! j])"
    by (rule gmp_poly_slots_insert_some) (use assms False in simp_all)
  have ins_j: "(mpzb_assn (xs ! i) (ptrs ! i) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          ((map Some xs)[i := None, j := None, i := Some (xs ! j)]) (ptrs[i := ptrs ! j]))
    = \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        ((map Some xs)[i := None, j := None, i := Some (xs ! j), j := Some (xs ! i)])
        (ptrs[i := ptrs ! j, j := ptrs ! i])"
    by (rule gmp_poly_slots_insert_some) (use assms False in simp_all)
  have slots_eq: "(map Some xs)[i := None, j := None, i := Some (xs ! j), j := Some (xs ! i)]
      = map Some (xs[i := xs ! j, j := xs ! i])"
    using assms False by (intro nth_equalityI) (auto simp: nth_list_update)
  have chain: "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs
      = \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (map Some (xs[i := xs ! j, j := xs ! i])) (ptrs[i := ptrs ! j, j := ptrs ! i])"
  proof -
    have "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs
      = (mpzb_assn (xs ! i) (ptrs ! i) \<and>* mpzb_assn (xs ! j) (ptrs ! j) \<and>*
          \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) ((map Some xs)[i := None, j := None]) ptrs)"
      by (rule gmp_poly_slots_focus_two_coeff[OF assms False])
    also have "\<dots> = \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        ((map Some xs)[i := None, j := None, i := Some (xs ! j), j := Some (xs ! i)])
        (ptrs[i := ptrs ! j, j := ptrs ! i])"
      by (simp only: sep_conj_assoc ins_i ins_j)
    also have "\<dots> = \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (xs[i := xs ! j, j := xs ! i])) (ptrs[i := ptrs ! j, j := ptrs ! i])"
      by (simp only: slots_eq)
    finally show ?thesis .
  qed
  show ?thesis using chain by (rule sym)
qed

text \<open>In-bounds @{const arl_upd} on the raw handle array (mirrors @{thm [source] dsc_arl_nth_rule_bounded}).\<close>
lemma dsc_arl_upd_rule_bounded:
  fixes p :: "('a::llvm_rep, gmp_poly_len) array_list" and ii :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (raw_al_assn xs p \<and>* \<upharpoonleft>snat.assn i ii)
    (arl_upd p ii v)
    (\<lambda>p'. raw_al_assn (xs[i := v]) p' \<and>* \<up>(p' = p))"
  apply (rule htriple_ent_pre[
    where P'="raw_al_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs)"])
   using assms
   apply (simp add: entails_def sep_algebra_simps sep_conj_ac
     pred_lift_extract_simps SOLVE_AUTO_DEFER_def)
  apply (rule arl_upd_rule)
  done

text \<open>Raw-array swap of two handle pointers: reads both, writes them exchanged; the slot ownership is frame.\<close>
lemma poly_swap_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii jj :: "gmp_poly_len word"
  assumes "i < length ptrs" and "j < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* F \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<upharpoonleft>snat.assn j jj)
    (poly_swap_coeff_impl p ii jj)
    (\<lambda>p'. raw_al_assn (ptrs[i := ptrs ! j, j := ptrs ! i]) p' \<and>* F)"
  using assms
  unfolding poly_swap_coeff_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms(1)] dsc_arl_nth_rule_bounded[OF assms(2)]
    dsc_arl_upd_rule_bounded
  by vcg'

text \<open>Lift to @{const gmp_poly_assn}: the value list and the ptr array swap together
  (@{thm [source] gmp_poly_slots_swap_eq}).\<close>
lemma poly_swap_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii jj :: "gmp_poly_len word"
  assumes "i < length xs" and "j < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<upharpoonleft>snat.assn j jj)
    (poly_swap_coeff_impl p ii jj)
    (\<lambda>p'. gmp_poly_assn (xs[i := xs ! j, j := xs ! i]) p')"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_two_snat_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_swap_coeff_impl_ptrs_rule[
       where ptrs=ptrs and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs"])
      using assms apply simp
     using assms apply simp
    apply (clarsimp simp: entails_def)
    subgoal for r s
      apply (rule exI[where x="ptrs[i := ptrs ! j, j := ptrs ! i]"])
      apply (subst gmp_poly_slots_swap_eq[OF assms])
      apply assumption
      done
    done
  done

lemma poly_swap_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_swap_coeff_impl,
    uncurry2 (PR_CONST poly_swap_coeff_monadic)) \<in>
    [\<lambda>((xs, i), j). i < length xs \<and> j < length xs]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_swap_coeff_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for j jj i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_swap_coeff_impl_rule[where i=i and j=j])
       apply assumption
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps)
    done
  done

definition poly_reverse_swap_loop_monadic :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_reverse_swap_loop_monadic dg half xs \<equiv>
  for 0 half (\<lambda>i ys. doN {
    ASSERT (i < length ys);
    ASSERT (i \<le> dg);
    ASSERT (dg - i < length ys);
    (PR_CONST poly_swap_coeff_monadic) ys i (dg - i)
  }) xs"

sepref_register "PR_CONST poly_reverse_swap_loop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_reverse_swap_loop_impl [llvm_code] is
  "uncurry2 poly_reverse_swap_loop_monadic" ::
  "[\<lambda>((dg, half), xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_reverse_swap_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_reverse_swap_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_reverse_swap_loop_impl,
    uncurry2 (PR_CONST poly_reverse_swap_loop_monadic)) \<in>
    [\<lambda>((dg, half), xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_reverse_swap_loop_impl.refine
  by (simp add: PR_CONST_def)

definition poly_reverse_in_place_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_reverse_in_place_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (0 < len);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_reverse_swap_loop_monadic) (len - 1) (len div 2) xs
}"

sepref_register "PR_CONST poly_reverse_in_place_monadic"
  :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_reverse_in_place_impl [llvm_code] is
  "poly_reverse_in_place_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_reverse_in_place_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

text \<open>Step: one swap \<open>i \<leftrightarrow> (len-1-i)\<close> extends the reversed-ends invariant from width \<open>i\<close> to \<open>i+1\<close>.\<close>
lemma reverse_swap_inv_step:
  fixes i :: nat
  assumes len: "length ys = length xs"
    and inv: "\<forall>j < length xs. ys ! j = (if j < i \<or> length xs - i \<le> j then rev xs ! j else xs ! j)"
    and i: "i < length xs div 2"
  shows "\<forall>j < length xs. ys[i := ys ! (length xs - Suc i), length xs - Suc i := ys ! i] ! j
    = (if j < Suc i \<or> length xs - Suc i \<le> j then rev xs ! j else xs ! j)"
proof (intro allI impI)
  fix j assume j: "j < length xs"
  let ?n = "length xs" let ?m = "length xs - Suc i"
  from i have im: "i < ?m" and iln: "i < ?n" and mln: "?m < ?n" by linarith+
  show "ys[i := ys ! ?m, ?m := ys ! i] ! j = (if j < Suc i \<or> ?m \<le> j then rev xs ! j else xs ! j)"
  proof (cases "j = i")
    case True
    have c: "\<not> (?m < i \<or> length xs - i \<le> ?m)" using i by presburger
    have "ys[i := ys ! ?m, ?m := ys ! i] ! i = ys ! ?m"
      using im len by (simp add: nth_list_update)
    also have "\<dots> = xs ! ?m" using inv[rule_format, OF mln] c by simp
    also have "\<dots> = rev xs ! i" using iln by (simp add: rev_nth)
    finally show ?thesis using True i by simp
  next
    case ji: False
    show ?thesis
    proof (cases "j = ?m")
      case True
      have cc: "\<not> (i < i \<or> length xs - i \<le> i)" using i by presburger
      have e: "length xs - Suc ?m = i" using iln by presburger
      have "ys[i := ys ! ?m, ?m := ys ! i] ! ?m = ys ! i"
        using im len by (simp add: nth_list_update)
      also have "\<dots> = xs ! i" using inv[rule_format, OF iln] cc by simp
      also have "\<dots> = rev xs ! ?m" using mln e by (simp add: rev_nth)
      finally show ?thesis using True by simp
    next
      case False
      hence yj: "ys[i := ys ! ?m, ?m := ys ! i] ! j = ys ! j"
        using ji len by (simp add: nth_list_update)
      have "(j < i \<or> length xs - i \<le> j) = (j < Suc i \<or> ?m \<le> j)"
        using ji False iln by presburger
      thus ?thesis using yj inv[rule_format, OF j] by simp
    qed
  qed
qed

text \<open>Final: at \<open>i = len div 2\<close> the invariant forces @{term "ys = rev xs"} (middle empty, or a fixed centre).\<close>
lemma reverse_swap_inv_final:
  assumes len: "length ys = length xs"
    and inv: "\<forall>j < length xs. ys ! j =
      (if j < length xs div 2 \<or> length xs - length xs div 2 \<le> j then rev xs ! j else xs ! j)"
  shows "ys = rev xs"
proof (intro nth_equalityI)
  show "length ys = length (rev xs)" using len by simp
  fix j assume "j < length ys"
  hence jn: "j < length xs" using len by simp
  show "ys ! j = rev xs ! j"
  proof (cases "j < length xs div 2 \<or> length xs - length xs div 2 \<le> j")
    case True thus ?thesis using inv jn by simp
  next
    case False
    hence "j = length xs - Suc j" by presburger
    hence "rev xs ! j = xs ! j" using jn by (simp add: rev_nth)
    thus ?thesis using inv jn False by simp
  qed
qed

text \<open>Abstract correctness of the swap-based in-place reverse: swapping \<open>i \<leftrightarrow> (len-1-i)\<close> for
  \<open>i < len div 2\<close> yields @{term "rev xs"}.\<close>
lemma poly_reverse_swap_loop_monadic_correct:
  assumes dg: "dg = length xs - 1" and half: "half = length xs div 2"
  shows "poly_reverse_swap_loop_monadic dg half xs \<le> RETURN (rev xs)"
  unfolding poly_reverse_swap_loop_monadic_def poly_swap_coeff_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>i ys.
    length ys = length xs \<and>
    (\<forall>j < length xs. ys ! j = (if j < i \<or> length xs - i \<le> j then rev xs ! j else xs ! j))"])
  using dg half
  by (auto simp: nth_list_update rev_nth
    intro: reverse_swap_inv_step reverse_swap_inv_final reverse_swap_inv_final[symmetric])

text \<open>@{const poly_reverse_in_place_monadic} computes @{term "rev xs"} (the reverse needed before
  the ET-Horner count). Reuses @{thm poly_reverse_swap_loop_monadic_correct}.\<close>
lemma poly_reverse_in_place_monadic_correct:
  assumes "0 < length xs"
    and "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_reverse_in_place_monadic xs \<le> RETURN (rev xs)"
  using assms
  unfolding poly_reverse_in_place_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg poly_reverse_swap_loop_monadic_correct[THEN order_trans])
  apply auto
  done

lemma poly_reverse_in_place_impl_hnr[sepref_fr_rules]:
  "(poly_reverse_in_place_impl,
    (PR_CONST poly_reverse_in_place_monadic)) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_reverse_in_place_impl.refine
  by (simp add: PR_CONST_def)

subsection \<open>Plain per-coefficient copy (the optimal 2nd-child clone — no \<open>scale 1\<close> ×1 overhead)\<close>

text \<open>The carried split's right child needs an independent deep copy of the left child (the irreducible 2nd-child
  duplicate). Today it is @{term \<open>poly_clone_monadic = poly_scale_monadic 1\<close>}, which runs an O(deg) multiply-by-1
  loop (\<open>mpz_mul\<close> by 1 ≈ a limb copy) + 2 scalar mpz on top of the necessary O(deg) coefficient copy — roughly
  DOUBLE the per-coeff work. This is a plain copy: @{const poly_empty_sz_monadic} + push a fresh copy of each
  coefficient, no multiply. Abstract = identity (\<open>= xs\<close>); proven below.\<close>

definition poly_copy_loop_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_copy_loop_monadic xs len dst \<equiv>
  for 0 len (\<lambda>i d. doN {
    ASSERT (i < length xs);
    ASSERT (length d + 1 < max_snat LENGTH(gmp_poly_len));
    c \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs i;
    (PR_CONST poly_push_coeff_monadic) d c
  }) dst"

sepref_register "PR_CONST poly_copy_loop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_copy_loop_impl [llvm_code] is
  "uncurry2 poly_copy_loop_monadic" ::
  "[\<lambda>((xs, len), dst). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_copy_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_copy_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_copy_loop_impl,
    uncurry2 (PR_CONST poly_copy_loop_monadic)) \<in>
    [\<lambda>((xs, len), dst). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_copy_loop_impl.refine
  by (simp add: PR_CONST_def)

definition poly_copy_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_copy_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_empty_sz_monadic) len;
  (PR_CONST poly_copy_loop_monadic) xs len dst
}"

sepref_register "PR_CONST poly_copy_monadic" :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition poly_copy_impl [llvm_code] is
  "poly_copy_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding poly_copy_monadic_def
  by sepref

lemma poly_copy_impl_hnr[sepref_fr_rules]:
  "(poly_copy_impl, (PR_CONST poly_copy_monadic)) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using poly_copy_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Correctness: the plain copy is the identity (a deep copy with the same coefficients).\<close>

lemma poly_copy_loop_monadic_correct:
  assumes "length dst + length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_copy_loop_monadic xs (length xs) dst \<le> RETURN (dst @ xs)"
  unfolding poly_copy_loop_monadic_def poly_copy_coeff_monadic_def
    poly_push_coeff_monadic_def
  apply (refine_vcg for_rule[where I="\<lambda>i d. d = dst @ take i xs"])
  using assms apply (auto simp: take_Suc_conv_app_nth)
  done

lemma poly_copy_correct:
  assumes A: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_copy_monadic xs \<le> RETURN xs"
proof -
  have L: "poly_copy_loop_monadic xs (length xs) [] \<le> RETURN xs"
    using poly_copy_loop_monadic_correct[where dst="[]" and xs=xs] A by simp
  show ?thesis
    unfolding poly_copy_monadic_def poly_length_monadic_def
      poly_empty_sz_monadic_def PR_CONST_def
    apply refine_vcg
    using A L by (auto simp: RETURN_def)
qed

definition dyadic_interval_vec_invar ::
  "gmp_dyadic_interval_vec \<Rightarrow> bool" where
"dyadic_interval_vec_invar v \<equiv>
  (let (lns, rns, ks) = v in
    length lns = length rns \<and> length lns = length ks)"

definition dyadic_rat :: "int \<Rightarrow> nat \<Rightarrow> rat" where
"dyadic_rat n k \<equiv> rat_of_int n / (2::rat) ^ k"

definition dyadic_interval_of_triple ::
  "(int \<times> int) \<times> nat \<Rightarrow> rat \<times> rat" where
"dyadic_interval_of_triple t \<equiv>
  (let ((l_num, r_num), k) = t in
    (dyadic_rat l_num k, dyadic_rat r_num k))"

definition dyadic_interval_vec_triples ::
  "gmp_dyadic_interval_vec \<Rightarrow> ((int \<times> int) \<times> nat) list" where
"dyadic_interval_vec_triples v \<equiv>
  (let (lns, rns, ks) = v in zip (zip lns rns) ks)"

definition dyadic_interval_vec_to_list ::
  "gmp_dyadic_interval_vec \<Rightarrow> (rat \<times> rat) list" where
"dyadic_interval_vec_to_list v \<equiv>
  map dyadic_interval_of_triple
    (dyadic_interval_vec_triples v)"

lemma dyadic_interval_vec_triples_simps:
  "dyadic_interval_vec_triples (lns, rns, ks) =
    zip (zip lns rns) ks"
  unfolding dyadic_interval_vec_triples_def by simp

lemma dyadic_interval_vec_to_list_simps:
  "dyadic_interval_vec_to_list (lns, rns, ks) =
    map dyadic_interval_of_triple (zip (zip lns rns) ks)"
  unfolding dyadic_interval_vec_to_list_def
  by (simp add: dyadic_interval_vec_triples_simps)

lemma dyadic_interval_vec_invar_empty[simp]:
  "dyadic_interval_vec_invar ([], [], [])"
  unfolding dyadic_interval_vec_invar_def by simp

lemma dyadic_interval_vec_triples_empty[simp]:
  "dyadic_interval_vec_triples ([], [], []) = []"
  by (simp add: dyadic_interval_vec_triples_simps)

lemma dyadic_interval_vec_to_list_empty[simp]:
  "dyadic_interval_vec_to_list ([], [], []) = []"
  by (simp add: dyadic_interval_vec_to_list_simps)

lemma dyadic_interval_vec_triples_length:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "length (dyadic_interval_vec_triples (lns, rns, ks)) =
    length lns"
  using assms
  unfolding dyadic_interval_vec_invar_def
  by (simp add: dyadic_interval_vec_triples_simps)

lemma dyadic_interval_vec_to_list_length:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "length (dyadic_interval_vec_to_list (lns, rns, ks)) =
    length lns"
  unfolding dyadic_interval_vec_to_list_def
  by (simp add: dyadic_interval_vec_triples_length[OF assms])

lemma dyadic_interval_vec_triples_nth:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "i < length lns"
  shows "dyadic_interval_vec_triples (lns, rns, ks) ! i =
    ((lns ! i, rns ! i), ks ! i)"
  using assms
  unfolding dyadic_interval_vec_invar_def
  by (simp add: dyadic_interval_vec_triples_simps)

lemma dyadic_interval_vec_to_list_nth:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "i < length lns"
  shows "dyadic_interval_vec_to_list (lns, rns, ks) ! i =
    (dyadic_rat (lns ! i) (ks ! i),
     dyadic_rat (rns ! i) (ks ! i))"
proof -
  have len: "i < length
      (dyadic_interval_vec_triples (lns, rns, ks))"
    using assms dyadic_interval_vec_triples_length[OF assms(1)]
    by simp
  show ?thesis
    using dyadic_interval_vec_triples_nth[OF assms]
    unfolding dyadic_interval_vec_to_list_def
      dyadic_interval_of_triple_def
    by (simp add: len)
qed

lemma dyadic_interval_vec_invar_push[simp]:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "dyadic_interval_vec_invar
    (lns @ [l_num], rns @ [r_num], ks @ [k])"
  using assms
  unfolding dyadic_interval_vec_invar_def
  by simp

lemma dyadic_interval_vec_triples_push:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "dyadic_interval_vec_triples
      (lns @ [l_num], rns @ [r_num], ks @ [k]) =
    dyadic_interval_vec_triples (lns, rns, ks) @
      [((l_num, r_num), k)]"
  using assms
  unfolding dyadic_interval_vec_invar_def
  by (simp add: dyadic_interval_vec_triples_simps)

lemma dyadic_interval_vec_to_list_push:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "dyadic_interval_vec_to_list
      (lns @ [l_num], rns @ [r_num], ks @ [k]) =
    dyadic_interval_vec_to_list (lns, rns, ks) @
      [dyadic_interval_of_triple ((l_num, r_num), k)]"
  using assms
  unfolding dyadic_interval_vec_to_list_def
  by (simp add: dyadic_interval_vec_triples_push)

lemma dyadic_interval_vec_invar_push_children[simp]:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "dyadic_interval_vec_invar
    (lns @ [ln1, ln2], rns @ [rn1, rn2], ks @ [k1, k2])"
  using assms
  unfolding dyadic_interval_vec_invar_def
  by simp

lemma dyadic_interval_vec_triples_push_children:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "dyadic_interval_vec_triples
      (lns @ [ln1, ln2], rns @ [rn1, rn2], ks @ [k1, k2]) =
    dyadic_interval_vec_triples (lns, rns, ks) @
      [((ln1, rn1), k1), ((ln2, rn2), k2)]"
  using assms
  unfolding dyadic_interval_vec_invar_def
  by (simp add: dyadic_interval_vec_triples_simps)

lemma dyadic_interval_vec_to_list_push_children:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "dyadic_interval_vec_to_list
      (lns @ [ln1, ln2], rns @ [rn1, rn2], ks @ [k1, k2]) =
    dyadic_interval_vec_to_list (lns, rns, ks) @
      [dyadic_interval_of_triple ((ln1, rn1), k1),
       dyadic_interval_of_triple ((ln2, rn2), k2)]"
  using assms
  unfolding dyadic_interval_vec_to_list_def
  by (simp add: dyadic_interval_vec_triples_push_children)

definition dyadic_interval_vec_pushable ::
  "gmp_dyadic_interval_vec \<Rightarrow> bool" where
"dyadic_interval_vec_pushable v \<equiv>
  (let (lns, rns, ks) = v in
    length lns + 1 < max_snat LENGTH(gmp_poly_len) \<and>
    length rns + 1 < max_snat LENGTH(gmp_poly_len) \<and>
    length ks + 1 < max_snat LENGTH(gmp_poly_len))"

definition dyadic_interval_vec_pushable2 ::
  "gmp_dyadic_interval_vec \<Rightarrow> bool" where
"dyadic_interval_vec_pushable2 v \<equiv>
  (let (lns, rns, ks) = v in
    length lns + 2 < max_snat LENGTH(gmp_poly_len) \<and>
    length rns + 2 < max_snat LENGTH(gmp_poly_len) \<and>
    length ks + 2 < max_snat LENGTH(gmp_poly_len))"

definition dyadic_exp_push2_monadic ::
  "nat list \<Rightarrow> nat \<Rightarrow> nat list nres" where
"dyadic_exp_push2_monadic ks k \<equiv> doN {
  ASSERT (length ks + 2 < max_snat LENGTH(gmp_poly_len));
  ks \<leftarrow> mop_list_append ks k;
  ASSERT (length ks + 1 < max_snat LENGTH(gmp_poly_len));
  mop_list_append ks k
}"

lemma dyadic_exp_push2_monadic_spec:
  assumes "length ks + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "dyadic_exp_push2_monadic ks k \<le> SPEC (\<lambda>ks'. ks' = ks @ [k, k])"
  using assms
  unfolding dyadic_exp_push2_monadic_def
  by refine_vcg auto

sepref_register "PR_CONST dyadic_exp_push2_monadic"
  :: "nat list \<Rightarrow> nat \<Rightarrow> nat list nres"

sepref_definition dyadic_exp_push2_impl [llvm_inline] is
  "uncurry dyadic_exp_push2_monadic" ::
  "[\<lambda>(ks, _). length ks + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_dyadic_exp_list_assn"
  unfolding dyadic_exp_push2_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma dyadic_exp_push2_impl_hnr[sepref_fr_rules]:
  "(uncurry dyadic_exp_push2_impl,
    uncurry (PR_CONST dyadic_exp_push2_monadic)) \<in>
    [\<lambda>(ks, _). length ks + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
        gmp_dyadic_exp_list_assn"
  using dyadic_exp_push2_impl.refine
  by (simp add: PR_CONST_def)

definition dyadic_exp_copy_get_monadic ::
  "nat list \<Rightarrow> nat \<Rightarrow> (nat list \<times> nat) nres" where
"dyadic_exp_copy_get_monadic ks i \<equiv> doN {
  ASSERT (i < length ks);
  k \<leftarrow> mop_list_get ks i;
  RETURN (ks, k)
}"

lemma dyadic_exp_copy_get_monadic_spec:
  assumes "i < length ks"
  shows "dyadic_exp_copy_get_monadic ks i \<le>
    SPEC (\<lambda>(ks', k). ks' = ks \<and> k = ks ! i)"
  using assms
  unfolding dyadic_exp_copy_get_monadic_def
  by refine_vcg auto

sepref_register "PR_CONST dyadic_exp_copy_get_monadic"
  :: "nat list \<Rightarrow> nat \<Rightarrow> (nat list \<times> nat) nres"

sepref_definition dyadic_exp_copy_get_impl [llvm_inline] is
  "uncurry dyadic_exp_copy_get_monadic" ::
  "[\<lambda>(ks, i). i < length ks]\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_dyadic_exp_list_assn \<times>\<^sub>a
        snat_assn' TYPE(gmp_poly_len)"
  unfolding dyadic_exp_copy_get_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma dyadic_exp_copy_get_impl_hnr[sepref_fr_rules]:
  "(uncurry dyadic_exp_copy_get_impl,
    uncurry (PR_CONST dyadic_exp_copy_get_monadic)) \<in>
    [\<lambda>(ks, i). i < length ks]\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
        gmp_dyadic_exp_list_assn \<times>\<^sub>a
          snat_assn' TYPE(gmp_poly_len)"
  using dyadic_exp_copy_get_impl.refine
  by (simp add: PR_CONST_def)

definition dyadic_exp_pop_last_monadic ::
  "nat list \<Rightarrow> (nat \<times> nat list) nres" where
"dyadic_exp_pop_last_monadic ks \<equiv> doN {
  ASSERT (ks \<noteq> []);
  mop_list_pop_last ks
}"

lemma dyadic_exp_pop_last_monadic_spec:
  assumes "ks \<noteq> []"
  shows "dyadic_exp_pop_last_monadic ks \<le>
    RETURN (last ks, butlast ks)"
  using assms
  unfolding dyadic_exp_pop_last_monadic_def
  by refine_vcg auto

sepref_register "PR_CONST dyadic_exp_pop_last_monadic"
  :: "nat list \<Rightarrow> (nat \<times> nat list) nres"

sepref_definition dyadic_exp_pop_last_impl [llvm_inline] is
  "dyadic_exp_pop_last_monadic" ::
  "[\<lambda>ks. ks \<noteq> []]\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d \<rightarrow>
      (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a
        gmp_dyadic_exp_list_assn"
  unfolding dyadic_exp_pop_last_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma dyadic_exp_pop_last_impl_hnr[sepref_fr_rules]:
  "(dyadic_exp_pop_last_impl,
    PR_CONST dyadic_exp_pop_last_monadic) \<in>
    [\<lambda>ks. ks \<noteq> []]\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d \<rightarrow>
        (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a
          gmp_dyadic_exp_list_assn"
  using dyadic_exp_pop_last_impl.refine
  by (simp add: PR_CONST_def)

definition mpz_pow2_monadic :: "nat \<Rightarrow> int nres" where
"mpz_pow2_monadic k \<equiv> doN {
  one \<leftarrow> RETURN (mpz_from_int 1);
  (PR_CONST mpz_shift_left_snat_monadic) one k
}"

lemma mpz_pow2_monadic_spec:
  assumes "k < max_snat LENGTH(gmp_poly_len)"
  shows "mpz_pow2_monadic k \<le> RETURN ((2::int) ^ k)"
proof -
  show ?thesis
    unfolding mpz_pow2_monadic_def
    apply refine_vcg
    subgoal
      apply (rule order_trans[
        OF mpz_shift_left_snat_monadic_spec[OF assms, of "mpz_from_int 1"]])
      by (simp add: mpz_from_int_def)
    done
qed

sepref_register "PR_CONST mpz_pow2_monadic" :: "nat \<Rightarrow> int nres"

sepref_definition mpz_pow2_impl [llvm_inline] is
  "mpz_pow2_monadic" ::
  "[\<lambda>k. k < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  unfolding mpz_pow2_monadic_def
  unfolding Let_def
  apply (annot_uint_const "TYPE(gmp_long_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma mpz_pow2_impl_hnr[sepref_fr_rules]:
  "(mpz_pow2_impl, PR_CONST mpz_pow2_monadic) \<in>
    [\<lambda>k. k < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  using mpz_pow2_impl.refine
  by (simp add: PR_CONST_def)

definition dyadic_interval_vec_empty_sz_monadic ::
  "nat \<Rightarrow> gmp_dyadic_interval_vec nres" where
"dyadic_interval_vec_empty_sz_monadic n \<equiv> doN {
  lns \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
  rns \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
  let ks = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  RETURN (lns, rns, ks)
}"

lemma dyadic_interval_vec_empty_sz_monadic_spec:
  "dyadic_interval_vec_empty_sz_monadic n \<le>
    SPEC (\<lambda>v. dyadic_interval_vec_invar v \<and>
      dyadic_interval_vec_triples v = [] \<and>
      dyadic_interval_vec_to_list v = [])"
  unfolding dyadic_interval_vec_empty_sz_monadic_def
    poly_empty_sz_monadic_def PR_CONST_def
  by refine_vcg auto

sepref_register "PR_CONST dyadic_interval_vec_empty_sz_monadic"
  :: "nat \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition dyadic_interval_vec_empty_sz_impl [llvm_inline] is
  "dyadic_interval_vec_empty_sz_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>d \<rightarrow>\<^sub>a
    gmp_dyadic_interval_vec_assn"
  unfolding dyadic_interval_vec_empty_sz_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma dyadic_interval_vec_empty_sz_impl_hnr[sepref_fr_rules]:
  "(dyadic_interval_vec_empty_sz_impl,
    PR_CONST dyadic_interval_vec_empty_sz_monadic) \<in>
      (snat_assn' TYPE(gmp_poly_len))\<^sup>d \<rightarrow>\<^sub>a
        gmp_dyadic_interval_vec_assn"
  using dyadic_interval_vec_empty_sz_impl.refine
  by (simp add: PR_CONST_def)

definition dyadic_interval_vec_length_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> nat nres" where
"dyadic_interval_vec_length_monadic v \<equiv> doN {
  let (lns, _, _) = v;
  (PR_CONST poly_length_monadic) lns
}"

lemma dyadic_interval_vec_length_monadic_spec:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "dyadic_interval_vec_length_monadic (lns, rns, ks) \<le>
    SPEC (\<lambda>n. n =
      length (dyadic_interval_vec_triples (lns, rns, ks)) \<and>
      n = length (dyadic_interval_vec_to_list (lns, rns, ks)))"
  using assms
  unfolding dyadic_interval_vec_length_monadic_def poly_length_monadic_def
    PR_CONST_def
  by (simp add: dyadic_interval_vec_triples_length
    dyadic_interval_vec_to_list_length)

sepref_register "PR_CONST dyadic_interval_vec_length_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> nat nres"

sepref_definition dyadic_interval_vec_length_impl [llvm_inline] is
  "dyadic_interval_vec_length_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  unfolding dyadic_interval_vec_length_monadic_def
  unfolding Let_def
  by sepref

lemma dyadic_interval_vec_length_impl_hnr[sepref_fr_rules]:
  "(dyadic_interval_vec_length_impl,
    PR_CONST dyadic_interval_vec_length_monadic) \<in>
      gmp_dyadic_interval_vec_assn\<^sup>k \<rightarrow>\<^sub>a
        snat_assn' TYPE(gmp_poly_len)"
  using dyadic_interval_vec_length_impl.refine
  by (simp add: PR_CONST_def)

definition dyadic_interval_vec_push_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_dyadic_interval_vec nres" where
"dyadic_interval_vec_push_monadic v l_num r_num k \<equiv> doN {
  let (lns, rns, ks) = v;
  ASSERT (dyadic_interval_vec_pushable v);
  lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) lns l_num;
  rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) rns r_num;
  ASSERT (length ks + 1 < max_snat LENGTH(gmp_poly_len));
  ks \<leftarrow> mop_list_append ks k;
  RETURN (lns, rns, ks)
}"

lemma dyadic_interval_vec_push_monadic_spec:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "dyadic_interval_vec_pushable (lns, rns, ks)"
  shows "dyadic_interval_vec_push_monadic (lns, rns, ks) l_num r_num k \<le>
    SPEC (\<lambda>v. dyadic_interval_vec_invar v \<and>
      dyadic_interval_vec_triples v =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num, r_num), k)] \<and>
      dyadic_interval_vec_to_list v =
        dyadic_interval_vec_to_list (lns, rns, ks) @
          [dyadic_interval_of_triple ((l_num, r_num), k)])"
  using assms
  unfolding dyadic_interval_vec_push_monadic_def
    dyadic_interval_vec_pushable_def
    poly_push_coeff_monadic_def PR_CONST_def
  by refine_vcg (auto simp: dyadic_interval_vec_triples_push
    dyadic_interval_vec_to_list_push)

sepref_register "PR_CONST dyadic_interval_vec_push_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_dyadic_interval_vec nres"

sepref_definition dyadic_interval_vec_push_impl [llvm_inline] is
  "uncurry3 dyadic_interval_vec_push_monadic" ::
  "[\<lambda>(((v, _), _), _). dyadic_interval_vec_pushable v]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding dyadic_interval_vec_push_monadic_def
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

lemma dyadic_interval_vec_push_impl_hnr[sepref_fr_rules]:
  "(uncurry3 dyadic_interval_vec_push_impl,
    uncurry3 (PR_CONST dyadic_interval_vec_push_monadic)) \<in>
    [\<lambda>(((v, _), _), _). dyadic_interval_vec_pushable v]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
        gmp_dyadic_interval_vec_assn"
  using dyadic_interval_vec_push_impl.refine
  by (simp add: PR_CONST_def)

definition dyadic_interval_vec_push_point_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_dyadic_interval_vec nres" where
"dyadic_interval_vec_push_point_monadic acc n k \<equiv> doN {
  l_num \<leftarrow> RETURN (COPY n);
  r_num \<leftarrow> RETURN (COPY n);
  ASSERT (dyadic_interval_vec_pushable acc);
  (PR_CONST dyadic_interval_vec_push_monadic) acc l_num r_num k
}"

lemma dyadic_interval_vec_push_point_monadic_spec:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "dyadic_interval_vec_pushable (lns, rns, ks)"
  shows "dyadic_interval_vec_push_point_monadic (lns, rns, ks) n k \<le>
    SPEC (\<lambda>v. dyadic_interval_vec_invar v \<and>
      dyadic_interval_vec_triples v =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((n, n), k)] \<and>
      dyadic_interval_vec_to_list v =
        dyadic_interval_vec_to_list (lns, rns, ks) @
          [dyadic_interval_of_triple ((n, n), k)])"
  using assms
  unfolding dyadic_interval_vec_push_point_monadic_def PR_CONST_def
  apply refine_vcg
  apply (rule order_trans[OF dyadic_interval_vec_push_monadic_spec])
    apply simp_all
  done

sepref_register "PR_CONST dyadic_interval_vec_push_point_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_dyadic_interval_vec nres"

sepref_definition dyadic_interval_vec_push_point_impl [llvm_inline] is
  "uncurry2 dyadic_interval_vec_push_point_monadic" ::
  "[\<lambda>((acc, _), _). dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding dyadic_interval_vec_push_point_monadic_def
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

lemma dyadic_interval_vec_push_point_impl_hnr[sepref_fr_rules]:
  "(uncurry2 dyadic_interval_vec_push_point_impl,
    uncurry2 (PR_CONST dyadic_interval_vec_push_point_monadic)) \<in>
    [\<lambda>((acc, _), _). dyadic_interval_vec_pushable acc]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
        gmp_dyadic_interval_vec_assn"
  using dyadic_interval_vec_push_point_impl.refine
  by (simp add: PR_CONST_def)

definition dyadic_interval_vec_push_children_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_dyadic_interval_vec nres" where
"dyadic_interval_vec_push_children_monadic todo l_num r_num k \<equiv> doN {
  let (lns, rns, ks) = todo;
  mid_src \<leftarrow> RETURN (COPY l_num);
  mid \<leftarrow> (PR_CONST mpz_add.amop_r1) mid_src r_num;
  l2 \<leftarrow> (PR_CONST mpz_double_shift_monadic) l_num;
  r2 \<leftarrow> (PR_CONST mpz_double_shift_monadic) r_num;
  mid_l \<leftarrow> RETURN (COPY mid);
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  let k' = k + 1;
  ASSERT (dyadic_interval_vec_pushable2 todo);
  lns \<leftarrow> (PR_CONST poly_push2_coeffs_monadic) lns l2 mid_l;
  rns \<leftarrow> (PR_CONST poly_push2_coeffs_monadic) rns mid r2;
  ks \<leftarrow> (PR_CONST dyadic_exp_push2_monadic) ks k';
  RETURN (lns, rns, ks)
}"

lemma dyadic_interval_vec_push_children_monadic_spec:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and "k + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "dyadic_interval_vec_push_children_monadic
      (lns, rns, ks) l_num r_num k \<le>
    SPEC (\<lambda>v. dyadic_interval_vec_invar v \<and>
      dyadic_interval_vec_triples v =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num + l_num, l_num + r_num), k + 1),
           ((l_num + r_num, r_num + r_num), k + 1)] \<and>
      dyadic_interval_vec_to_list v =
        dyadic_interval_vec_to_list (lns, rns, ks) @
          [dyadic_interval_of_triple
            ((l_num + l_num, l_num + r_num), k + 1),
           dyadic_interval_of_triple
            ((l_num + r_num, r_num + r_num), k + 1)])"
  using assms
  unfolding dyadic_interval_vec_push_children_monadic_def
    dyadic_interval_vec_pushable2_def
    poly_push2_coeffs_monadic_def poly_push_coeff_monadic_def
    dyadic_exp_push2_monadic_def
    mpz_add.amop_r1_def mpz_add.aop_r1_def PR_CONST_def
  apply (refine_vcg mpz_double_shift_monadic_spec_plain)
  apply (auto simp: dyadic_interval_vec_triples_push_children
    dyadic_interval_vec_to_list_push_children algebra_simps)
  done

sepref_register "PR_CONST dyadic_interval_vec_push_children_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_dyadic_interval_vec nres"

sepref_definition dyadic_interval_vec_push_children_impl [llvm_inline] is
  "uncurry3 dyadic_interval_vec_push_children_monadic" ::
  "[\<lambda>(((todo, _), _), k).
      dyadic_interval_vec_pushable2 todo \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding dyadic_interval_vec_push_children_monadic_def
  unfolding dyadic_interval_vec_pushable2_def
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

lemma dyadic_interval_vec_push_children_impl_hnr[sepref_fr_rules]:
  "(uncurry3 dyadic_interval_vec_push_children_impl,
    uncurry3 (PR_CONST dyadic_interval_vec_push_children_monadic)) \<in>
    [\<lambda>(((todo, _), _), k).
      dyadic_interval_vec_pushable2 todo \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
        gmp_dyadic_interval_vec_assn"
  using dyadic_interval_vec_push_children_impl.refine
  by (simp add: PR_CONST_def)

definition dyadic_interval_vec_copy_get_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> nat \<Rightarrow>
    (int \<times> int \<times> nat) nres" where
"dyadic_interval_vec_copy_get_monadic v i \<equiv> doN {
  let (lns, rns, ks) = v;
  ASSERT (i < length lns);
  ASSERT (i < length rns);
  ASSERT (i < length ks);
  l_num \<leftarrow> (PR_CONST poly_copy_coeff_monadic) lns i;
  r_num \<leftarrow> (PR_CONST poly_copy_coeff_monadic) rns i;
  k \<leftarrow> mop_list_get ks i;
  RETURN (l_num, r_num, k)
}"

lemma dyadic_interval_vec_copy_get_monadic_spec:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "i < length lns"
  shows "dyadic_interval_vec_copy_get_monadic (lns, rns, ks) i \<le>
    SPEC (\<lambda>(l_num, r_num, k).
      ((l_num, r_num), k) =
        dyadic_interval_vec_triples (lns, rns, ks) ! i \<and>
      (dyadic_rat l_num k, dyadic_rat r_num k) =
        dyadic_interval_vec_to_list (lns, rns, ks) ! i)"
proof -
  have i_rns: "i < length rns"
    using assms unfolding dyadic_interval_vec_invar_def by simp
  have i_ks: "i < length ks"
    using assms unfolding dyadic_interval_vec_invar_def by simp
  have triple_nth:
    "((lns ! i, rns ! i), ks ! i) =
      dyadic_interval_vec_triples (lns, rns, ks) ! i"
    using dyadic_interval_vec_triples_nth[OF assms] by simp
  have rat_nth:
    "(dyadic_rat (lns ! i) (ks ! i),
      dyadic_rat (rns ! i) (ks ! i)) =
      dyadic_interval_vec_to_list (lns, rns, ks) ! i"
    using dyadic_interval_vec_to_list_nth[OF assms] by simp
  show ?thesis
    unfolding dyadic_interval_vec_copy_get_monadic_def
      poly_copy_coeff_monadic_def
    using assms i_rns i_ks triple_nth rat_nth
    apply refine_vcg
    apply (simp_all add: PR_CONST_def)
    done
qed

sepref_register "PR_CONST dyadic_interval_vec_copy_get_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> nat \<Rightarrow>
      (int \<times> int \<times> nat) nres"

sepref_definition dyadic_interval_vec_copy_get_impl [llvm_inline] is
  "uncurry dyadic_interval_vec_copy_get_monadic" ::
  "[\<lambda>(v, i). case v of (lns, rns, ks) \<Rightarrow>
      i < length lns \<and> i < length rns \<and> i < length ks]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      mpzb_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a
        snat_assn' TYPE(gmp_poly_len)"
  unfolding dyadic_interval_vec_copy_get_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

lemma dyadic_interval_vec_copy_get_impl_hnr[sepref_fr_rules]:
  "(uncurry dyadic_interval_vec_copy_get_impl,
    uncurry (PR_CONST dyadic_interval_vec_copy_get_monadic)) \<in>
    [\<lambda>(v, i). case v of (lns, rns, ks) \<Rightarrow>
      i < length lns \<and> i < length rns \<and> i < length ks]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
        mpzb_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a
          snat_assn' TYPE(gmp_poly_len)"
  using dyadic_interval_vec_copy_get_impl.refine
  by (simp add: PR_CONST_def)

definition dyadic_interval_vec_pop_last_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow>
    ((int \<times> int \<times> nat) \<times> gmp_dyadic_interval_vec) nres" where
"dyadic_interval_vec_pop_last_monadic v \<equiv> doN {
  let (lns, rns, ks) = v;
  ASSERT (dyadic_interval_vec_invar v);
  ASSERT (lns \<noteq> []);
  (l_num, lns) \<leftarrow> (PR_CONST poly_pop_coeff_monadic) lns;
  (r_num, rns) \<leftarrow> (PR_CONST poly_pop_coeff_monadic) rns;
  (k, ks) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) ks;
  RETURN ((l_num, r_num, k), (lns, rns, ks))
}"

lemma dyadic_interval_vec_pop_last_monadic_spec:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "lns \<noteq> []"
  shows "dyadic_interval_vec_pop_last_monadic (lns, rns, ks) \<le>
    RETURN ((last lns, last rns, last ks),
      (butlast lns, butlast rns, butlast ks))"
  using assms
  unfolding dyadic_interval_vec_pop_last_monadic_def
    dyadic_interval_vec_invar_def
    poly_pop_coeff_monadic_def dyadic_exp_pop_last_monadic_def
    PR_CONST_def
  by refine_vcg auto

sepref_register "PR_CONST dyadic_interval_vec_pop_last_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow>
      ((int \<times> int \<times> nat) \<times> gmp_dyadic_interval_vec) nres"

sepref_definition dyadic_interval_vec_pop_last_impl [llvm_inline] is
  "dyadic_interval_vec_pop_last_monadic" ::
  "[\<lambda>v. dyadic_interval_vec_invar v \<and>
      (case v of (lns, _, _) \<Rightarrow> lns \<noteq> [])]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
      (mpzb_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a
        snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a
        gmp_dyadic_interval_vec_assn"
  unfolding dyadic_interval_vec_pop_last_monadic_def
  unfolding dyadic_interval_vec_invar_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma dyadic_interval_vec_pop_last_impl_hnr[sepref_fr_rules]:
  "(dyadic_interval_vec_pop_last_impl,
    PR_CONST dyadic_interval_vec_pop_last_monadic) \<in>
    [\<lambda>v. dyadic_interval_vec_invar v \<and>
      (case v of (lns, _, _) \<Rightarrow> lns \<noteq> [])]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
        (mpzb_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a
          snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a
          gmp_dyadic_interval_vec_assn"
  using dyadic_interval_vec_pop_last_impl.refine
  by (simp add: PR_CONST_def)

definition dyadic_interval_vec_free_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> unit nres" where
"dyadic_interval_vec_free_monadic v \<equiv> doN {
  let (lns, rns, ks) = v;
  (PR_CONST poly_free_monadic) lns;
  (PR_CONST poly_free_monadic) rns;
  mop_free ks;
  RETURN ()
}"

sepref_register "PR_CONST dyadic_interval_vec_free_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> unit nres"

sepref_definition dyadic_interval_vec_free_impl [llvm_inline] is
  "dyadic_interval_vec_free_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  unfolding dyadic_interval_vec_free_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = al_assn_free
  by sepref

lemma dyadic_interval_vec_free_impl_hnr[sepref_fr_rules]:
  "(dyadic_interval_vec_free_impl,
    PR_CONST dyadic_interval_vec_free_monadic) \<in>
      gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  using dyadic_interval_vec_free_impl.refine
  by (simp add: PR_CONST_def)


definition gmp_dyadic_interval_vec_nonempty ::
  "gmp_dyadic_interval_vec \<Rightarrow> bool nres" where
"gmp_dyadic_interval_vec_nonempty v \<equiv> doN {
  n \<leftarrow> (PR_CONST dyadic_interval_vec_length_monadic) v;
  RETURN (0 < n)
}"

sepref_register "PR_CONST gmp_dyadic_interval_vec_nonempty"
  :: "gmp_dyadic_interval_vec \<Rightarrow> bool nres"

sepref_definition gmp_dyadic_interval_vec_nonempty_impl [llvm_inline] is
  "gmp_dyadic_interval_vec_nonempty" ::
  "gmp_dyadic_interval_vec_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding gmp_dyadic_interval_vec_nonempty_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma gmp_dyadic_interval_vec_nonempty_impl_hnr[sepref_fr_rules]:
  "(gmp_dyadic_interval_vec_nonempty_impl,
    PR_CONST gmp_dyadic_interval_vec_nonempty) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using gmp_dyadic_interval_vec_nonempty_impl.refine
  by (simp add: PR_CONST_def)
definition carried_push_mid_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_dyadic_interval_vec nres" where
"carried_push_mid_monadic acc l_num r_num k \<equiv> doN {
  let (lns, rns, ks) = acc;
  mid_src \<leftarrow> RETURN (COPY l_num);
  mid \<leftarrow> (PR_CONST mpz_add.amop_r1) mid_src r_num;
  ASSERT (dyadic_interval_vec_pushable acc);
  mid_l \<leftarrow> RETURN (COPY mid);
  lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) lns mid_l;
  rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) rns mid;
  ASSERT (length ks + 1 < max_snat LENGTH(gmp_poly_len));
  ks \<leftarrow> mop_list_append ks (k + 1);
  RETURN (lns, rns, ks)
}"

sepref_register "PR_CONST carried_push_mid_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_dyadic_interval_vec nres"

sepref_definition carried_push_mid_impl [llvm_inline] is
  "uncurry3 carried_push_mid_monadic" ::
  "[\<lambda>(((acc, _), _), k).
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding carried_push_mid_monadic_def
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

lemma carried_push_mid_impl_hnr[sepref_fr_rules]:
  "(uncurry3 carried_push_mid_impl,
    uncurry3 (PR_CONST carried_push_mid_monadic)) \<in>
    [\<lambda>(((acc, _), _), k).
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable acc]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
        gmp_dyadic_interval_vec_assn"
  using carried_push_mid_impl.refine
  by (simp add: PR_CONST_def)

end
