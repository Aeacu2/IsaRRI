theory Interval_Eval
imports Interval Dyadic_Interval
begin

text \<open>Homothety evaluation and interval-endpoint infrastructure, shared by every solver.
  Main definitions: the \<open>hom_eval*\<close> state and result records and the interval endpoint-pair ops.

  Intervals are represented as endpoint pairs \<open>((na, da), (nb, db))\<close>, meaning \<open>[na/da, nb/db]\<close>.
  Polynomial coefficients and Descartes transformations are GMP values.\<close>

type_synonym rat_pair = "int \<times> int"
type_synonym interval = "rat_pair \<times> rat_pair"

abbreviation rat_pair_assn where
"rat_pair_assn \<equiv> gmp_slong_assn \<times>\<^sub>a gmp_slong_assn"

abbreviation interval_assn where
"interval_assn \<equiv> rat_pair_assn \<times>\<^sub>a rat_pair_assn"

abbreviation interval_list_assn where
"interval_list_assn \<equiv> al_assn' TYPE(gmp_poly_len) interval_assn"

definition slong_bounds :: "int \<Rightarrow> bool" where
"slong_bounds x \<equiv>
  min_sint LENGTH(gmp_long_len) \<le> x \<and> x < max_sint LENGTH(gmp_long_len)"

definition interval_mid_bounds ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"interval_mid_bounds na da nb db \<equiv>
  slong_bounds (na * db) \<and>
  slong_bounds (nb * da) \<and>
  slong_bounds (na * db + nb * da) \<and>
  slong_bounds (da * db) \<and>
  slong_bounds (2 * (da * db))"

definition interval_mid_monadic ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> rat_pair nres" where
"interval_mid_monadic na da nb db \<equiv> doN {
  ASSERT (interval_mid_bounds na da nb db);
  na_db \<leftarrow> mul_sss.op LENGTH(gmp_long_len) na db;
  nb_da \<leftarrow> mul_sss.op LENGTH(gmp_long_len) nb da;
  num \<leftarrow> add_sss.op LENGTH(gmp_long_len) na_db nb_da;
  da_db \<leftarrow> mul_sss.op LENGTH(gmp_long_len) da db;
  two \<leftarrow> RETURN 2;
  den \<leftarrow> mul_sss.op LENGTH(gmp_long_len) two da_db;
  RETURN (num, den)
}"

sepref_register "PR_CONST interval_mid_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> rat_pair nres"

sepref_definition interval_mid_impl [llvm_inline] is
  "uncurry3 interval_mid_monadic" ::
  "[\<lambda>(((na, da), nb), db). interval_mid_bounds na da nb db]\<^sub>a
    gmp_slong_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k *\<^sub>a
      gmp_slong_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k \<rightarrow> rat_pair_assn"
  unfolding interval_mid_monadic_def interval_mid_bounds_def
    slong_bounds_def
  supply [sepref_fr_rules] = mul_sss.hnr add_sss.hnr
  apply (annot_sint_const "TYPE(gmp_long_len)")
  by sepref

lemma interval_mid_impl_hnr[sepref_fr_rules]:
  "(uncurry3 interval_mid_impl, uncurry3 (PR_CONST interval_mid_monadic)) \<in>
    [\<lambda>(((na, da), nb), db). interval_mid_bounds na da nb db]\<^sub>a
      gmp_slong_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k *\<^sub>a
        gmp_slong_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k \<rightarrow> rat_pair_assn"
  using interval_mid_impl.refine
  by (simp add: PR_CONST_def)

lemma interval_assn_is_pure[safe_constraint_rules]:
  "is_pure interval_assn"
  by (simp add: is_pure_conv)

lemma rat_pair_assn_is_pure[safe_constraint_rules]:
  "is_pure rat_pair_assn"
  by (simp add: is_pure_conv)

lemma interval_assn_mk_free[sepref_frame_free_rules]:
  "MK_FREE interval_assn (\<lambda>_. Mreturn ())"
  by (rule mk_free_is_pure[OF interval_assn_is_pure])

lemma rat_pair_assn_mk_free[sepref_frame_free_rules]:
  "MK_FREE rat_pair_assn (\<lambda>_. Mreturn ())"
  by (rule mk_free_is_pure[OF rat_pair_assn_is_pure])

type_synonym hom_eval_state = "nat \<times> int \<times> int"

abbreviation hom_eval_state_assn where
"hom_eval_state_assn \<equiv>
  snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn"

definition poly_hom_eval_cond ::
  "nat \<Rightarrow> hom_eval_state \<Rightarrow> bool" where
"poly_hom_eval_cond bd st \<equiv>
  (let (i, acc, dpow) = st in i < bd)"

sepref_register "PR_CONST poly_hom_eval_cond"
  :: "nat \<Rightarrow> hom_eval_state \<Rightarrow> bool"

sepref_definition poly_hom_eval_cond_impl [llvm_inline] is
  "uncurry (RETURN oo poly_hom_eval_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    hom_eval_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding poly_hom_eval_cond_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma poly_hom_eval_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_hom_eval_cond_impl,
    uncurry (RETURN oo (PR_CONST poly_hom_eval_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      hom_eval_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using poly_hom_eval_cond_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Borrowed-coefficient addmul for the midpoint Horner evaluation: read \<open>xs[idx]\<close> in place via
  @{const arl_nth} and accumulate \<open>acc += xs[idx]*dpow\<close> with @{const mpzb_addmul_impl}, which keeps
  ownership, rather than a per-iteration @{const poly_copy_coeff_monadic} and
  @{const mpzb_discard_monadic}. The abstract value is unchanged, so the \<open>hom_eval\<close> invariant lemmas
  still apply. The HNR is \<open>poly_hom_eval_addmul_impl_hnr\<close> (option-slot focus, as in
  @{thm [source] poly_addmul_coeff_impl_focused_rule}).\<close>
definition poly_hom_eval_addmul_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int nres" where
"poly_hom_eval_addmul_monadic acc xs idx dpow \<equiv> doN {
  ASSERT (idx < length xs);
  RETURN (acc + xs ! idx * dpow)
}"

sepref_register "PR_CONST poly_hom_eval_addmul_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]:
  "poly_hom_eval_addmul_impl acc p idx dpow \<equiv> doM {
    src \<leftarrow> arl_nth p idx;
    mpzb_addmul_impl acc src dpow
  }"

text \<open>General length extraction: the leading \<open>raw \<and>* list\<close> fixes \<open>length ptrs = length xs\<close> regardless of any
  trailing frame \<open>F\<close> (here \<open>mpzb acc \<and>* snat idx \<and>* mpzb dpow\<close>). Frames the @{const list_assn}.\<close>
lemma gmp_poly_raw_slots_frame_lenD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>* F)
    \<Longrightarrow> length ptrs = length xs"
  by (auto dest!: pure_part_split_conj gmp_poly_slots_len_frameD)

text \<open>Scalar return-entailment, the @{const mpzb_assn} twin of @{thm [source] gmp_poly_assn_return_entails}.\<close>
lemma dsc_mpzb_return_entails:
  "mpzb_assn v r \<turnstile> (EXS x. mpzb_assn x r \<and>* \<up>(x = v))"
  by (rule entails_exI[where x=v]) (simp add: sep_algebra_simps)

text \<open>Focused htriple: read slot \<open>idx\<close> (kept, the poly is unchanged) and accumulate \<open>acc += xs!idx * dpow\<close>
  into the external owned \<open>acc\<close> via the proven keep-ownership @{const mpzb_addmul_impl}. Models the
  read-only focus of @{thm [source] poly_copy_coeff_impl_focused_rule} with an addmul sink.\<close>
lemma poly_hom_eval_addmul_impl_focused_rule:
  fixes p :: gmp_poly_raw and idxi :: "gmp_poly_len word"
  assumes "idx < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* mpzb_assn acc aci \<and>* \<upharpoonleft>snat.assn idx idxi \<and>*
      mpzb_assn dpow di \<and>* mpzb_assn xidx (ptrs ! idx) \<and>* F)
    (poly_hom_eval_addmul_impl aci p idxi di)
    (\<lambda>r. raw_al_assn ptrs p \<and>* (mpzb_assn xidx (ptrs ! idx) \<and>* F) \<and>*
      mpzb_assn dpow di \<and>* mpzb_assn (acc + xidx * dpow) r)"
  using assms
  unfolding poly_hom_eval_addmul_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

text \<open>Lift to the option-slot list: the poly is unchanged (slot \<open>idx\<close> read-only); only \<open>acc\<close> is updated.\<close>
lemma poly_hom_eval_addmul_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and idxi :: "gmp_poly_len word"
  assumes "idx < length xs"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      mpzb_assn acc aci \<and>* \<upharpoonleft>snat.assn idx idxi \<and>* mpzb_assn dpow di)
    (poly_hom_eval_addmul_impl aci p idxi di)
    (\<lambda>r. raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      mpzb_assn dpow di \<and>* mpzb_assn (acc + xs ! idx * dpow) r)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_hom_eval_addmul_impl_focused_rule[
      where ptrs=ptrs and idx=idx
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          ((map Some xs)[idx := None]) ptrs"
        and xidx="xs ! idx" and acc=acc and dpow=dpow])
    using assms apply simp
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
    gmp_poly_slots_unfocus_coeff
    pred_lift_extract_simps pure_def snat.assn_is_rel snat_rel_def)
  done

text \<open>Lift to @{const gmp_poly_assn} (kept).\<close>
lemma poly_hom_eval_addmul_impl_rule:
  fixes p :: gmp_poly_raw and idxi :: "gmp_poly_len word"
  assumes "idx < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* mpzb_assn acc aci \<and>*
      \<upharpoonleft>snat.assn idx idxi \<and>* mpzb_assn dpow di)
    (poly_hom_eval_addmul_impl aci p idxi di)
    (\<lambda>r. gmp_poly_assn xs p \<and>* mpzb_assn dpow di \<and>*
      mpzb_assn (acc + xs ! idx * dpow) r)"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_frame_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_hom_eval_addmul_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def sep_algebra_simps)
    subgoal for r s
      apply (rule exI[where x=ptrs])
      apply (simp add: sep_algebra_simps)
      done
    done
  done

text \<open>HNR glue. After \<open>htriple_ent_pre/post\<close> + the impl_rule (\<open>[where acc/dpow]\<close> to tie the schematic abstract
  scalars; the \<open>subgoal for\<close> needs 10 names — the kept poly handle destructures to an arl triple), two residual
  entailments remain: a pure \<open>\<and>*\<close>-reorder \<open>mpzb acc \<and>* poly \<turnstile> poly \<and>* mpzb acc\<close> (the hnr arg order is acc-first,
  the impl_rule poly-first) and the \<open>\<exists>\<close>-result + \<open>snat\<close> post. KEY: \<open>sep_conj_left_commute\<close> must be a \<^bold>\<open>separate\<close>
  \<open>simp\<close> AFTER the snat \<open>clarsimp simp: entails_def\<close> — folded into that clarsimp it HANGS (the sep-conj unfolds to
  heap splits and the permutative rule diverges); applied on the already-reduced folded goal it closes in one
  step. The post closes with \<open>clarsimp simp: entails_def \<dots> dest!: pure_part_split_conj\<close> (the same single-mpzb
  pattern as @{thm [source] poly_copy_coeff_impl_hnr}).\<close>
lemma poly_hom_eval_addmul_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_hom_eval_addmul_impl,
    uncurry3 (PR_CONST poly_hom_eval_addmul_monadic)) \<in>
    [\<lambda>(((acc, xs), idx), dpow). idx < length xs]\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn"
  apply sepref_to_hoare
  unfolding poly_hom_eval_addmul_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for dpow di idx idxi xs ph1 ph2 ph3 accv acch
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_hom_eval_addmul_impl_rule[where acc=accv and dpow=dpow])
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
     apply (simp add: sep_conj_left_commute)?
    apply (clarsimp simp: entails_def sep_algebra_simps
      dest!: pure_part_split_conj)
    done
  done

text \<open>Borrowed-coefficient PLAIN add for the shift-Horner half-eval —
  read \<open>xs[idx]\<close> in place via @{const arl_nth} and accumulate \<open>acc += xs[idx]\<close> with the
  keep-ownership @{const mpzb_add_impl}. The @{const poly_hom_eval_addmul_monadic} twin
  WITHOUT the \<open>dpow\<close> multiplier — used by the shift-based Horner loop, where the running
  \<open>acc \<lless> 1\<close> already carries the place value, so an \<open>addmul\<close> by a materialised 1 would cost
  a multiplication per step for nothing. Abstract value \<open>acc + xs!idx\<close>; option-slot focus modelled verbatim on
  @{thm [source] poly_hom_eval_addmul_impl_rule}, with @{const mpzb_add_impl} in place of the
  addmul sink.\<close>
definition poly_acc_add_coeff_monadic ::
  "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> int nres" where
"poly_acc_add_coeff_monadic acc xs idx \<equiv> doN {
  ASSERT (idx < length xs);
  RETURN (acc + xs ! idx)
}"

sepref_register "PR_CONST poly_acc_add_coeff_monadic"
  :: "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]:
  "poly_acc_add_coeff_impl acc p idx \<equiv> doM {
    src \<leftarrow> arl_nth p idx;
    mpzb_add_impl acc src
  }"

text \<open>Focused htriple: read slot \<open>idx\<close> (kept, the poly is unchanged) and accumulate
  \<open>acc += xs!idx\<close> into the external owned \<open>acc\<close> via the proven keep-ownership
  @{const mpzb_add_impl}. The \<open>dpow\<close>-free twin of
  @{thm [source] poly_hom_eval_addmul_impl_focused_rule}.\<close>
lemma poly_acc_add_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw and idxi :: "gmp_poly_len word"
  assumes "idx < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* mpzb_assn acc aci \<and>* \<upharpoonleft>snat.assn idx idxi \<and>*
      mpzb_assn xidx (ptrs ! idx) \<and>* F)
    (poly_acc_add_coeff_impl aci p idxi)
    (\<lambda>r. raw_al_assn ptrs p \<and>* (mpzb_assn xidx (ptrs ! idx) \<and>* F) \<and>*
      mpzb_assn (acc + xidx) r)"
  using assms
  unfolding poly_acc_add_coeff_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

text \<open>Lift to the option-slot list: the poly is unchanged (slot \<open>idx\<close> read-only); only \<open>acc\<close> is updated.\<close>
lemma poly_acc_add_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and idxi :: "gmp_poly_len word"
  assumes "idx < length xs"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      mpzb_assn acc aci \<and>* \<upharpoonleft>snat.assn idx idxi)
    (poly_acc_add_coeff_impl aci p idxi)
    (\<lambda>r. raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      mpzb_assn (acc + xs ! idx) r)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_acc_add_coeff_impl_focused_rule[
      where ptrs=ptrs and idx=idx
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          ((map Some xs)[idx := None]) ptrs"
        and xidx="xs ! idx" and acc=acc])
    using assms apply simp
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
    gmp_poly_slots_unfocus_coeff
    pred_lift_extract_simps pure_def snat.assn_is_rel snat_rel_def)
  done

text \<open>Lift to @{const gmp_poly_assn} (kept).\<close>
lemma poly_acc_add_coeff_impl_rule:
  fixes p :: gmp_poly_raw and idxi :: "gmp_poly_len word"
  assumes "idx < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* mpzb_assn acc aci \<and>* \<upharpoonleft>snat.assn idx idxi)
    (poly_acc_add_coeff_impl aci p idxi)
    (\<lambda>r. gmp_poly_assn xs p \<and>* mpzb_assn (acc + xs ! idx) r)"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_frame_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_acc_add_coeff_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def sep_algebra_simps)
    subgoal for r s
      apply (rule exI[where x=ptrs])
      apply (simp add: sep_algebra_simps)
      done
    done
  done

text \<open>HNR glue, the \<open>dpow\<close>-free twin of @{thm [source] poly_hom_eval_addmul_impl_hnr}.\<close>
lemma poly_acc_add_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_acc_add_coeff_impl,
    uncurry2 (PR_CONST poly_acc_add_coeff_monadic)) \<in>
    [\<lambda>((acc, xs), idx). idx < length xs]\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  apply sepref_to_hoare
  unfolding poly_acc_add_coeff_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for idx idxi xs ph1 ph2 ph3 accv acch
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_acc_add_coeff_impl_rule[where acc=accv])
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
     apply (simp add: sep_conj_c)?
    apply (clarsimp simp: entails_def sep_algebra_simps
      dest!: pure_part_split_conj)
    done
  done

definition poly_hom_eval_body_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> hom_eval_state \<Rightarrow>
    hom_eval_state nres" where
"poly_hom_eval_body_mop_monadic xs bd n d st \<equiv> doN {
  let (i, acc, dpow) = st;
  ASSERT (bd + 1 = length xs);
  ASSERT (i < bd);
  let idx = bd - (i + 1);
  ASSERT (idx < length xs);
  acc \<leftarrow> (PR_CONST mpz_mul.amop_r1) acc n;
  acc \<leftarrow> (PR_CONST poly_hom_eval_addmul_monadic) acc xs idx dpow;
  dpow \<leftarrow> (PR_CONST mpz_mul.amop_r1) dpow d;
  ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
  RETURN (i + 1, acc, dpow)
}"

sepref_register "PR_CONST poly_hom_eval_body_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> hom_eval_state \<Rightarrow>
    hom_eval_state nres"

sepref_definition poly_hom_eval_body_impl [llvm_inline] is
  "uncurry4 poly_hom_eval_body_mop_monadic" ::
  "[\<lambda>((((xs, bd), _), _), i, acc, dpow).
      bd + 1 = length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      hom_eval_state_assn\<^sup>d \<rightarrow> hom_eval_state_assn"
  unfolding poly_hom_eval_body_mop_monadic_def
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

lemma poly_hom_eval_body_impl_hnr[sepref_fr_rules]:
  "(uncurry4 poly_hom_eval_body_impl,
    uncurry4 (PR_CONST poly_hom_eval_body_mop_monadic)) \<in>
    [\<lambda>((((xs, bd), _), _), i, acc, dpow).
      bd + 1 = length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        hom_eval_state_assn\<^sup>d \<rightarrow> hom_eval_state_assn"
  using poly_hom_eval_body_impl.refine
  by (simp add: PR_CONST_def)

definition poly_hom_eval_finish_monadic ::
  "int \<Rightarrow> int \<Rightarrow> hom_eval_state \<Rightarrow> bool nres" where
"poly_hom_eval_finish_monadic gn gd st \<equiv> doN {
  let (i, acc, dpow) = st;
  s \<leftarrow> RETURN ((PR_CONST mpz_sgn) acc);
  (PR_CONST mpzb_discard_monadic) acc;
  (PR_CONST mpzb_discard_monadic) dpow;
  (PR_CONST mpzb_discard_monadic) gn;
  (PR_CONST mpzb_discard_monadic) gd;
  RETURN (s = 0)
}"

sepref_register "PR_CONST poly_hom_eval_finish_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> hom_eval_state \<Rightarrow> bool nres"

definition [llvm_code, llvm_inline]:
  "poly_hom_eval_finish_impl gn gd st \<equiv> doM {
    let (i, acc, dpow) = st;
    s \<leftarrow> mpzb_sgn_impl acc;
    mpzb_discard_impl acc;
    mpzb_discard_impl dpow;
    mpzb_discard_impl gn;
    mpzb_discard_impl gd;
    ll_icmp_eq s (0::gmp_int_t)
  }"

lemma int_word_dvd_zero:
  fixes r :: gmp_int_t
  assumes "(4294967296::int) dvd uint r"
  shows "r = 0"
proof (rule ccontr)
  assume "r \<noteq> 0"
  then have nz: "uint r \<noteq> 0"
    by (simp add: uint_0_iff)
  have "\<bar>(4294967296::int)\<bar> \<le> \<bar>uint r\<bar>"
    by (rule dvd_imp_le_int[OF nz assms])
  moreover have "\<bar>uint r\<bar> < (4294967296::int)"
    using uint_lt2p[of r] uint_ge_0[of r]
    by simp
  ultimately show False by simp
qed

lemma int_word_mod_nonzero:
  fixes r :: gmp_int_t
  assumes "uint r mod (4294967296::int) \<noteq> 0"
  shows "r \<noteq> 0"
  using assms
  by (auto simp: uint_0_iff)

lemma poly_hom_eval_finish_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_hom_eval_finish_impl,
    uncurry2 (PR_CONST poly_hom_eval_finish_monadic)) \<in>
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      hom_eval_state_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn"
  unfolding poly_hom_eval_finish_impl_def
    poly_hom_eval_finish_monadic_def PR_CONST_def
    mpzb_discard_impl_def
  apply sepref_to_hoare
  apply (clarsimp simp: refine_pw_simps)
  apply vcg'
  apply (all \<open>(vcg')?\<close>)
  apply (auto simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps bool1_rel_def bool.rel_def pure_def
    mpzb_discard_monadic_def sint_rel_def sint.rel_def br_def
    word_eq_iff_signed sint_word_ariths ll_icmp_eq_def
    op_lift_cmp_def wpa_return POSTCOND_def STATE_def EXTRACT_def
    word_to_lint_def lint_to_word_def bool_to_lint_def
    ltrue_def lfalse_def from_bool_def
    int_word_dvd_zero int_word_mod_nonzero)
  done

definition poly_hom_eval_zero_nd_monadic ::
  "int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
"poly_hom_eval_zero_nd_monadic n d xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (0 < len);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  let bd = len - 1;
  gn \<leftarrow> RETURN (mpz_from_int n);
  gd \<leftarrow> RETURN (mpz_from_int d);
  acc \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs bd;
  dpow \<leftarrow> RETURN (mpz_from_int d);
  st \<leftarrow> WHILET
    (\<lambda>st. (PR_CONST poly_hom_eval_cond) bd st)
    (\<lambda>st. (PR_CONST poly_hom_eval_body_mop_monadic) xs bd gn gd st)
    (0, acc, dpow);
  (PR_CONST poly_hom_eval_finish_monadic) gn gd st
}"

sepref_register "PR_CONST poly_hom_eval_zero_nd_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

sepref_definition poly_hom_eval_zero_nd_impl [llvm_inline] is
  "uncurry2 poly_hom_eval_zero_nd_monadic" ::
  "[\<lambda>((_, _), xs).
      0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_slong_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding poly_hom_eval_zero_nd_monadic_def
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

lemma poly_hom_eval_zero_nd_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_hom_eval_zero_nd_impl,
    uncurry2 (PR_CONST poly_hom_eval_zero_nd_monadic)) \<in>
    [\<lambda>((_, _), xs).
      0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_slong_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using poly_hom_eval_zero_nd_impl.refine
  by (simp add: PR_CONST_def)

definition poly_hom_eval_zero_mpz_monadic ::
  "int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
"poly_hom_eval_zero_mpz_monadic n d xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (0 < len);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  let bd = len - 1;
  gn \<leftarrow> RETURN (COPY n);
  gd \<leftarrow> RETURN (COPY d);
  acc \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs bd;
  dpow \<leftarrow> RETURN (COPY d);
  st \<leftarrow> WHILET
    (\<lambda>st. (PR_CONST poly_hom_eval_cond) bd st)
    (\<lambda>st. (PR_CONST poly_hom_eval_body_mop_monadic) xs bd gn gd st)
    (0, acc, dpow);
  (PR_CONST poly_hom_eval_finish_monadic) gn gd st
}"

sepref_register "PR_CONST poly_hom_eval_zero_mpz_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

sepref_definition poly_hom_eval_zero_mpz_impl [llvm_inline] is
  "uncurry2 poly_hom_eval_zero_mpz_monadic" ::
  "[\<lambda>((_, _), xs).
      0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding poly_hom_eval_zero_mpz_monadic_def
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

lemma poly_hom_eval_zero_mpz_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_hom_eval_zero_mpz_impl,
    uncurry2 (PR_CONST poly_hom_eval_zero_mpz_monadic)) \<in>
    [\<lambda>((_, _), xs).
      0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using poly_hom_eval_zero_mpz_impl.refine
  by (simp add: PR_CONST_def)

definition poly_hom_eval_inv ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> hom_eval_state \<Rightarrow> bool" where
"poly_hom_eval_inv xs bd n d st \<equiv>
  (let (i, acc, dpow) = st in
    i \<le> bd \<and>
    bd + 1 = length xs \<and>
    d \<noteq> 0 \<and>
    dpow = d ^ Suc i \<and>
    rat_of_int acc / rat_of_int (d ^ i) =
      poly (map_poly rat_of_int (Poly (drop (bd - i) xs)))
        (rat_of_int n / rat_of_int d))"

lemma poly_hom_eval_drop_step:
  assumes "i < bd" and "bd + 1 = length xs"
  shows "drop (bd - Suc i) xs =
    xs ! (bd - Suc i) # drop (bd - i) xs"
proof -
  let ?idx = "bd - Suc i"
  have idx_lt: "?idx < length xs"
    using assms by simp
  have "Suc ?idx = bd - i"
    using assms by simp
  moreover have "drop ?idx xs = xs ! ?idx # drop (Suc ?idx) xs"
    using idx_lt by (simp add: Cons_nth_drop_Suc)
  ultimately show ?thesis
    by simp
qed

lemma poly_hom_eval_init:
  assumes "bd + 1 = length xs"
  shows "rat_of_int (xs ! bd) / rat_of_int (d ^ 0) =
    poly (map_poly rat_of_int (Poly (drop bd xs)))
      (rat_of_int n / rat_of_int d)"
proof -
  have bd_lt: "bd < length xs"
    using assms by simp
  have drop_bd: "drop bd xs = [xs ! bd]"
  proof -
    have "drop bd xs = xs ! bd # drop (Suc bd) xs"
      using bd_lt by (simp add: Cons_nth_drop_Suc)
    also have "drop (Suc bd) xs = []"
      using assms by simp
    finally show ?thesis by simp
  qed
  have map_const: "map_poly rat_of_int [:xs ! bd:] = [:rat_of_int (xs ! bd):]"
    by (rule poly_eqI) (simp add: coeff_map_poly coeff_pCons split: nat.splits)
  show ?thesis
    by (simp add: drop_bd map_const)
qed

lemma rat_div_mult_right:
  fixes a b c :: rat
  shows "(a / b) * c = a * c / b"
    and "c * (a / b) = a * c / b"
  by (simp_all add: divide_inverse algebra_simps)

lemma poly_pCons_eval_rat:
  fixes c n d :: int and q :: "int poly"
  shows "poly (map_poly rat_of_int (pCons c q))
      (rat_of_int n / rat_of_int d) =
    rat_of_int c +
      rat_of_int n * poly (map_poly rat_of_int q)
        (rat_of_int n / rat_of_int d) / rat_of_int d"
proof -
  have map_pCons:
    "map_poly rat_of_int (pCons c q) =
      pCons (rat_of_int c) (map_poly rat_of_int q)"
    by (rule poly_eqI) (simp add: coeff_map_poly coeff_pCons split: nat.splits)
  have "poly (map_poly rat_of_int (pCons c q))
      (rat_of_int n / rat_of_int d) =
    poly (pCons (rat_of_int c) (map_poly rat_of_int q))
      (rat_of_int n / rat_of_int d)"
    by (simp add: map_pCons)
  also have "\<dots> =
    rat_of_int c +
      (rat_of_int n / rat_of_int d) *
        poly (map_poly rat_of_int q)
          (rat_of_int n / rat_of_int d)"
    by (simp add: poly_pCons)
  also have "\<dots> =
    rat_of_int c +
      rat_of_int n * poly (map_poly rat_of_int q)
        (rat_of_int n / rat_of_int d) / rat_of_int d"
    by (simp add: rat_div_mult_right)
  finally show ?thesis .
qed

lemma poly_hom_eval_inv_step:
  assumes d0: "d \<noteq> 0"
    and i_lt: "i < bd"
    and len: "bd + 1 = length xs"
    and inv: "rat_of_int acc / rat_of_int (d ^ i) =
      poly (map_poly rat_of_int (Poly (drop (bd - i) xs)))
        (rat_of_int n / rat_of_int d)"
  shows "rat_of_int (acc * n + xs ! (bd - Suc i) * d ^ Suc i) /
      rat_of_int (d ^ Suc i) =
    poly (map_poly rat_of_int (Poly (drop (bd - Suc i) xs)))
      (rat_of_int n / rat_of_int d)"
proof -
  let ?x = "rat_of_int n / rat_of_int d"
  have d_rat0: "rat_of_int d \<noteq> 0"
    using d0 by simp
  have "rat_of_int (acc * n + xs ! (bd - Suc i) * d ^ Suc i) /
      rat_of_int (d ^ Suc i) =
    rat_of_int acc / rat_of_int (d ^ i) * ?x +
      rat_of_int (xs ! (bd - Suc i))"
    using d_rat0
    by (simp add: field_simps)
  also have "\<dots> =
    poly (map_poly rat_of_int (Poly (drop (bd - i) xs))) ?x * ?x +
      rat_of_int (xs ! (bd - Suc i))"
    using inv by simp
  also have "\<dots> =
    rat_of_int (xs ! (bd - Suc i)) +
      ?x * poly (map_poly rat_of_int (Poly (drop (bd - i) xs))) ?x"
    by (simp add: algebra_simps)
  also have "\<dots> =
    poly (map_poly rat_of_int
      (Poly (xs ! (bd - Suc i) # drop (bd - i) xs))) ?x"
    by (simp add: poly_pCons_eval_rat)
  also have "\<dots> =
    poly (map_poly rat_of_int (Poly (drop (bd - Suc i) xs))) ?x"
    using poly_hom_eval_drop_step[OF i_lt len]
    by simp
  finally show ?thesis .
qed

lemma poly_hom_eval_inv_step_alt:
  assumes d0: "d \<noteq> 0"
    and i_lt: "i < bd"
    and len: "bd + 1 = length xs"
    and inv: "rat_of_int acc / rat_of_int (d ^ i) =
      poly (map_poly rat_of_int (Poly (drop (bd - i) xs)))
        (rat_of_int n / rat_of_int d)"
  shows "rat_of_int (xs ! (bd - Suc i)) +
      rat_of_int acc * rat_of_int n /
        (rat_of_int d * rat_of_int d ^ i) =
    poly (map_poly rat_of_int (Poly (drop (bd - Suc i) xs)))
      (rat_of_int n / rat_of_int d)"
proof -
  have d_rat0: "rat_of_int d \<noteq> 0"
    using d0 by simp
  have step:
    "rat_of_int (acc * n + xs ! (bd - Suc i) * d ^ Suc i) /
      rat_of_int (d ^ Suc i) =
    poly (map_poly rat_of_int (Poly (drop (bd - Suc i) xs)))
      (rat_of_int n / rat_of_int d)"
    by (rule poly_hom_eval_inv_step[OF d0 i_lt len inv])
  have "rat_of_int (acc * n + xs ! (bd - Suc i) * d ^ Suc i) /
      rat_of_int (d ^ Suc i) =
    rat_of_int (xs ! (bd - Suc i)) +
      rat_of_int acc * rat_of_int n /
        (rat_of_int d * rat_of_int d ^ i)"
    using d_rat0 by (simp add: field_simps)
  then show ?thesis
    using step by simp
qed

lemma poly_hom_eval_body_mop_monadic_spec:
  assumes inv: "poly_hom_eval_inv xs bd n d st"
    and cond: "poly_hom_eval_cond bd st"
    and bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_hom_eval_body_mop_monadic xs bd n d st \<le>
    SPEC (poly_hom_eval_inv xs bd n d)"
  using assms
  unfolding poly_hom_eval_body_mop_monadic_def
    poly_hom_eval_cond_def
    poly_hom_eval_inv_def
    poly_hom_eval_addmul_monadic_def
    mpz_mul.amop_r1_def mpz_mul.aop_r1_def
    PR_CONST_def
  apply refine_vcg
  apply (auto simp: poly_hom_eval_inv_step
    poly_hom_eval_inv_step_alt
    split: prod.splits)
  done

lemma poly_hom_eval_body_mop_monadic_spec_decrease:
  assumes inv: "poly_hom_eval_inv xs bd n d st"
    and cond: "poly_hom_eval_cond bd st"
    and bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_hom_eval_body_mop_monadic xs bd n d st \<le>
    SPEC (\<lambda>st'.
      poly_hom_eval_inv xs bd n d st' \<and>
      (case (st, st') of ((i, _, _), (i', _, _)) \<Rightarrow>
        bd - i' < bd - i))"
  using assms
  unfolding poly_hom_eval_body_mop_monadic_def
    poly_hom_eval_cond_def
    poly_hom_eval_inv_def
    poly_hom_eval_addmul_monadic_def
    mpz_mul.amop_r1_def mpz_mul.aop_r1_def
    PR_CONST_def
  apply refine_vcg
  apply (auto simp: poly_hom_eval_inv_step
    poly_hom_eval_inv_step_alt
    split: prod.splits)
  done

lemma poly_hom_eval_finish_monadic_spec:
  assumes inv: "poly_hom_eval_inv xs bd n d st"
    and ncond: "\<not> poly_hom_eval_cond bd st"
  shows "poly_hom_eval_finish_monadic gn gd st \<le>
    RETURN (poly (map_poly rat_of_int (Poly xs))
      (rat_of_int n / rat_of_int d) = 0)"
proof -
  obtain i acc dpow where st_eq: "st = (i, acc, dpow)"
    by (cases st) auto
  have inv_tuple:
    "i \<le> bd \<and>
     bd + 1 = length xs \<and>
     d \<noteq> 0 \<and>
     dpow = d ^ Suc i \<and>
     rat_of_int acc / rat_of_int (d ^ i) =
      poly (map_poly rat_of_int (Poly (drop (bd - i) xs)))
        (rat_of_int n / rat_of_int d)"
    using inv st_eq
    unfolding poly_hom_eval_inv_def
    by simp
  have le: "i \<le> bd"
    using inv_tuple by blast
  have nlt: "\<not> i < bd"
    using ncond st_eq
    unfolding poly_hom_eval_cond_def
    by simp
  have d0: "d \<noteq> 0"
    using inv_tuple by blast
  have i_eq: "i = bd"
    using le nlt by simp
  have den0: "rat_of_int (d ^ bd) \<noteq> 0"
    using d0 by simp
  have acc_eq_direct: "rat_of_int acc / rat_of_int (d ^ i) =
    poly (map_poly rat_of_int (Poly (drop (bd - i) xs)))
      (rat_of_int n / rat_of_int d)"
    using inv_tuple by blast
  have acc_poly: "rat_of_int acc / rat_of_int (d ^ bd) =
    poly (map_poly rat_of_int (Poly xs))
      (rat_of_int n / rat_of_int d)"
    using acc_eq_direct i_eq by simp
  have zero_eq: "(sgn acc = 0) =
    (poly (map_poly rat_of_int (Poly xs))
      (rat_of_int n / rat_of_int d) = 0)"
    using acc_poly den0 by (auto simp: sgn_0_0)
  show ?thesis
    unfolding poly_hom_eval_finish_monadic_def st_eq
      mpzb_discard_monadic_def PR_CONST_def
    by (simp add: refine_pw_simps zero_eq)
qed

lemma poly_hom_eval_zero_mpz_monadic_spec:
  assumes dpos: "0 < d"
    and len0: "0 < length xs"
    and bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_hom_eval_zero_mpz_monadic n d xs \<le>
    RETURN (poly (map_poly rat_of_int (Poly xs))
      (rat_of_int n / rat_of_int d) = 0)"
  using assms
  unfolding poly_hom_eval_zero_mpz_monadic_def
    poly_length_monadic_def poly_copy_coeff_monadic_def
    PR_CONST_def COPY_def
  apply (refine_vcg WHILET_rule[
    where I="poly_hom_eval_inv xs (length xs - 1) n d"
      and R="measure (\<lambda>(i, _::int, _::int). length xs - 1 - i)"])
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal
    unfolding poly_hom_eval_inv_def
    using poly_hom_eval_init[of "length xs - 1" xs d n]
    by (auto simp: last_conv_nth)
  subgoal
    apply (rule order_trans)
     apply (rule poly_hom_eval_body_mop_monadic_spec_decrease)
       apply (auto simp: poly_hom_eval_cond_def
        poly_hom_eval_inv_def split: prod.splits)
    done
  subgoal
    apply (rule order_trans)
     apply (rule poly_hom_eval_finish_monadic_spec)
      apply assumption
     apply assumption
    apply simp
    done
  done


section \<open>Horner shift-and-add midpoint zero test (\<open>Q(1/2)=0\<close>)\<close>

text \<open>The specialised midpoint test \<open>Q(1/2)=0\<close>, a sibling of the general
  \<open>poly_hom_eval_zero_mpz_monadic\<close> evaluator above that replaces its general \<open>n/d\<close> Horner step with a
  shift-and-add for \<open>n=1, d=2\<close>, so it performs no general \<open>mpz_mul\<close>. It lives here because
  \<open>half_eval_body_mop_monadic\<close> needs ops from both \<open>Dyadic_Interval\<close> (\<open>mpz_shift_left_snat_monadic\<close>)
  and this theory (\<open>poly_acc_add_coeff_monadic\<close>).

  Numerator \<open>N = (\<Sum>i. c_i 2^(deg-i))\<close> via Horner \<open>acc := (acc << 1) + xs!i\<close> from \<open>i=1\<close>, seeded
  \<open>acc = xs!0\<close>. Each step is one shift (\<open>mpz_shift_left_snat_monadic\<close>) and one borrowing add
  (\<open>poly_hom_eval_addmul_monadic\<close> with \<open>dpow = 1\<close>, i.e. \<open>acc + xs!i\<cdot>1\<close>).
  \<open>Q(1/2)=0 \<longleftrightarrow> N=0 \<longleftrightarrow> sign acc = 0\<close>.\<close>

definition half_eval_finish_monadic :: "nat \<times> int \<Rightarrow> bool nres" where
"half_eval_finish_monadic st \<equiv> doN {
  let (i, acc) = st;
  s \<leftarrow> RETURN ((PR_CONST mpz_sgn) acc);
  (PR_CONST mpzb_discard_monadic) acc;
  RETURN (s = 0)
}"

sepref_register "PR_CONST half_eval_finish_monadic" :: "nat \<times> int \<Rightarrow> bool nres"

definition half_eval_cond :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> bool" where
"half_eval_cond len st \<equiv> (let (i, acc) = st in i < len)"

sepref_register "PR_CONST half_eval_cond" :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> bool"

definition half_eval_body_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> int \<Rightarrow> (nat \<times> int) nres" where
"half_eval_body_mop_monadic xs len st \<equiv> doN {
  let (i, acc) = st;
  ASSERT (i < len);
  ASSERT (i < length xs);
  acc \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) acc 1;
  acc \<leftarrow> (PR_CONST poly_acc_add_coeff_monadic) acc xs i;
  ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
  RETURN (i + 1, acc)
}"

sepref_register "PR_CONST half_eval_body_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> int \<Rightarrow> (nat \<times> int) nres"

definition half_eval_zero_monadic :: "gmp_poly \<Rightarrow> bool nres" where
"half_eval_zero_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (0 < len);
  acc0 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 0;
  st \<leftarrow> WHILET
    (\<lambda>st. (PR_CONST half_eval_cond) len st)
    (\<lambda>st. (PR_CONST half_eval_body_mop_monadic) xs len st)
    (1, acc0);
  (PR_CONST half_eval_finish_monadic) st
}"

sepref_register "PR_CONST half_eval_zero_monadic" :: "gmp_poly \<Rightarrow> bool nres"

abbreviation half_eval_state_assn where
"half_eval_state_assn \<equiv> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a mpzb_assn"

sepref_definition half_eval_cond_impl [llvm_inline] is
  "uncurry (RETURN oo half_eval_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a half_eval_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding half_eval_cond_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma half_eval_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry half_eval_cond_impl, uncurry (RETURN oo (PR_CONST half_eval_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a half_eval_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using half_eval_cond_impl.refine by (simp add: PR_CONST_def)

sepref_definition half_eval_body_impl [llvm_inline] is
  "uncurry2 half_eval_body_mop_monadic" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      half_eval_state_assn\<^sup>d \<rightarrow>\<^sub>a half_eval_state_assn"
  unfolding half_eval_body_mop_monadic_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_fr_rules] = mpz_shift_left_snat_impl_hnr poly_acc_add_coeff_impl_hnr
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

lemma half_eval_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 half_eval_body_impl, uncurry2 (PR_CONST half_eval_body_mop_monadic)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      half_eval_state_assn\<^sup>d \<rightarrow>\<^sub>a half_eval_state_assn"
  using half_eval_body_impl.refine by (simp add: PR_CONST_def)

definition [llvm_code, llvm_inline]:
  "half_eval_finish_impl st \<equiv> doM {
    let (i, acc) = st;
    s \<leftarrow> mpzb_sgn_impl acc;
    mpzb_discard_impl acc;
    ll_icmp_eq s (0::gmp_int_t)
  }"

lemma half_eval_finish_impl_hnr[sepref_fr_rules]:
  "(half_eval_finish_impl, PR_CONST half_eval_finish_monadic) \<in>
    half_eval_state_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn"
  unfolding half_eval_finish_impl_def half_eval_finish_monadic_def PR_CONST_def
    mpzb_discard_impl_def
  apply sepref_to_hoare
  apply (clarsimp simp: refine_pw_simps)
  apply vcg'
  apply (all \<open>(vcg')?\<close>)
  apply (auto simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps bool1_rel_def bool.rel_def pure_def
    mpzb_discard_monadic_def sint_rel_def sint.rel_def br_def
    word_eq_iff_signed sint_word_ariths ll_icmp_eq_def
    op_lift_cmp_def wpa_return POSTCOND_def STATE_def EXTRACT_def
    word_to_lint_def lint_to_word_def bool_to_lint_def
    ltrue_def lfalse_def from_bool_def
    int_word_dvd_zero int_word_mod_nonzero)
  done

lemma poly_Poly_nth_sum:
  fixes ys :: "'a::comm_ring_1 list"
  shows "poly (Poly ys) a = (\<Sum>i<length ys. ys ! i * a ^ i)"
proof (induction ys)
  case Nil
  show ?case by simp
next
  case (Cons y ys)
  have step: "poly (Poly (y # ys)) a = y + a * poly (Poly ys) a"
    by simp
  have shift0: "(\<Sum>i<Suc (length ys). (y # ys) ! i * a ^ i) =
      (y # ys) ! 0 * a ^ 0 + (\<Sum>i<length ys. (y # ys) ! Suc i * a ^ Suc i)"
    by (rule sum.lessThan_Suc_shift)
  have shift: "(\<Sum>i<length (y # ys). (y # ys) ! i * a ^ i) =
      y + a * (\<Sum>i<length ys. ys ! i * a ^ i)"
    unfolding length_Cons shift0
    by (simp add: sum_distrib_left algebra_simps)
  show ?case
    unfolding step Cons.IH shift by simp
qed

lemma poly_map_poly_rat_of_int_nth_sum:
  "poly (map_poly rat_of_int (Poly ys)) (a::rat) = (\<Sum>i<length ys. rat_of_int (ys ! i) * a ^ i)"
proof (induction ys)
  case Nil
  show ?case by simp
next
  case (Cons y ys)
  have poly_cons: "Poly (y # ys) = pCons y (Poly ys)"
    by (rule Poly.simps(2))
  have step: "poly (map_poly rat_of_int (Poly (y # ys))) a =
      rat_of_int y + a * poly (map_poly rat_of_int (Poly ys)) a"
    unfolding poly_cons of_int_hom.map_poly_pCons_hom by simp
  have shift0: "(\<Sum>i<Suc (length ys). rat_of_int ((y # ys) ! i) * a ^ i) =
      rat_of_int ((y # ys) ! 0) * a ^ 0 +
        (\<Sum>i<length ys. rat_of_int ((y # ys) ! Suc i) * a ^ Suc i)"
    by (rule sum.lessThan_Suc_shift)
  have shift: "(\<Sum>i<length (y # ys). rat_of_int ((y # ys) ! i) * a ^ i) =
      rat_of_int y + a * (\<Sum>i<length ys. rat_of_int (ys ! i) * a ^ i)"
    unfolding length_Cons shift0
    by (simp add: sum_distrib_left algebra_simps)
  show ?case
    unfolding step Cons.IH shift by simp
qed

lemma reverse_eval_recip:
  assumes ne: "xs \<noteq> []"
  shows "rat_of_int (poly (Poly (rev xs)) (2::int)) =
    (2::rat) ^ (length xs - 1) * poly (map_poly rat_of_int (Poly xs)) (1 / 2)"
proof -
  define n where "n = length xs"
  have n0: "0 < n" using ne by (simp add: n_def)
  have lhs: "poly (Poly (rev xs)) (2::int) = (\<Sum>i<n. xs ! (n - 1 - i) * (2::int) ^ i)"
    unfolding poly_Poly_nth_sum n_def
    by (rule sum.cong) (auto simp: rev_nth n_def)
  have reindex: "(\<Sum>i<n. xs ! (n - 1 - i) * (2::int) ^ i) = (\<Sum>j<n. xs ! j * (2::int) ^ (n - 1 - j))"
    by (rule sum.reindex_bij_witness[where i = "\<lambda>i. n - 1 - i" and j = "\<lambda>j. n - 1 - j"]) auto
  have rhs: "poly (map_poly rat_of_int (Poly xs)) (1 / 2 :: rat) =
      (\<Sum>i<n. rat_of_int (xs ! i) * (1 / 2) ^ i)"
    unfolding n_def
    by (rule poly_map_poly_rat_of_int_nth_sum)
  have scale: "(2::rat) ^ (n - 1) * (\<Sum>i<n. rat_of_int (xs ! i) * (1 / 2) ^ i) =
      (\<Sum>i<n. rat_of_int (xs ! i) * (2::rat) ^ (n - 1 - i))"
    apply (simp add: sum_distrib_left)
    apply (rule sum.cong, simp)
    using n0
    apply (simp add: power_diff field_simps power_add[symmetric])
    done
  have goal_int: "rat_of_int (poly (Poly (rev xs)) (2::int)) =
      (\<Sum>j<n. rat_of_int (xs ! j) * (2::rat) ^ (n - 1 - j))"
    unfolding n_def[symmetric] lhs reindex
    by (simp add: of_int_sum)
  show ?thesis
    unfolding n_def[symmetric] goal_int rhs
    by (rule scale[symmetric])
qed

lemma poly_rev_zero_iff:
  assumes ne: "xs \<noteq> []"
  shows "(poly (Poly (rev xs)) (2::int) = 0) =
    (poly (map_poly rat_of_int (Poly xs)) (rat_of_int 1 / rat_of_int 2) = 0)"
proof -
  have p2ne0: "(2::rat) ^ (length xs - 1) \<noteq> 0" by simp
  have "(poly (Poly (rev xs)) (2::int) = 0) =
      (rat_of_int (poly (Poly (rev xs)) (2::int)) = 0)" by simp
  also have "\<dots> = ((2::rat) ^ (length xs - 1) *
      poly (map_poly rat_of_int (Poly xs)) (1 / 2) = 0)"
    using reverse_eval_recip[OF ne] by simp
  also have "\<dots> = (poly (map_poly rat_of_int (Poly xs)) (1 / 2) = 0)"
    using p2ne0 by simp
  finally show ?thesis by simp
qed

lemma half_eval_zero_monadic_correct:
  assumes ne: "0 < length xs" and lb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "half_eval_zero_monadic xs \<le> RETURN (poly (map_poly rat_of_int (Poly xs))
      (rat_of_int 1 / rat_of_int 2) = 0)"
proof -
  have wl: "WHILET
      (\<lambda>st. (PR_CONST half_eval_cond) (length xs) st)
      (\<lambda>st. (PR_CONST half_eval_body_mop_monadic) xs (length xs) st)
      (Suc 0, xs ! 0)
    \<le> SPEC (\<lambda>(i, acc). i = length xs \<and> acc = poly (Poly (rev (take i xs))) (2::int))"
    apply (rule WHILET_rule[where
        R = "measure (\<lambda>(i, acc). length xs - i)"
        and I = "\<lambda>(i, acc). 1 \<le> i \<and> i \<le> length xs
          \<and> acc = poly (Poly (rev (take i xs))) (2::int)"])
    subgoal by simp
    subgoal using ne by (simp add: take_Suc_conv_app_nth)
    subgoal for st
      unfolding half_eval_body_mop_monadic_def half_eval_cond_def
        poly_acc_add_coeff_monadic_def mpz_shift_left_snat_monadic_def
        mpz_mul_2exp.amop_r1_def mpz_mul_2exp.aop_r1_def
        snat_unat_cast.mop_def PR_CONST_def
      apply refine_vcg
      using lb
      apply (auto simp: max_snat_def max_unat_def take_Suc_conv_app_nth)
      done
    subgoal by (auto simp: take_all half_eval_cond_def)
    done
  have wl_step: "WHILET
      (\<lambda>st. (PR_CONST half_eval_cond) (length xs) st)
      (\<lambda>st. (PR_CONST half_eval_body_mop_monadic) xs (length xs) st)
      (Suc 0, xs ! 0)
    \<le> SPEC (\<lambda>st. half_eval_finish_monadic st
        \<le> RES {poly (map_poly rat_of_int (Poly xs)) (rat_of_int 1 / rat_of_int 2) = 0})"
    apply (rule SPEC_cons_rule[OF wl])
    using ne
    apply (clarsimp simp: half_eval_finish_monadic_def mpzb_discard_monadic_def PR_CONST_def
      refine_pw_simps sgn_0_0 poly_rev_zero_iff length_greater_0_conv)
    done
  show ?thesis
    unfolding half_eval_zero_monadic_def
      poly_length_monadic_def poly_copy_coeff_monadic_def PR_CONST_def
    apply (refine_vcg)
    using ne lb
    apply (simp_all)
    apply (rule order_trans[OF wl_step[unfolded PR_CONST_def]])
    apply (rule SPEC_rule)
    apply simp
    done
qed

sepref_definition half_eval_zero_impl [llvm_code] is
  "half_eval_zero_monadic" ::
  "[\<lambda>xs. 0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding half_eval_zero_monadic_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_fr_rules] = mpz_shift_left_snat_impl_hnr poly_acc_add_coeff_impl_hnr
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

lemma half_eval_zero_impl_hnr[sepref_fr_rules]:
  "(half_eval_zero_impl, PR_CONST half_eval_zero_monadic) \<in>
    [\<lambda>xs. 0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using half_eval_zero_impl.refine by (simp add: PR_CONST_def)

text \<open>snat \<rightarrow> owned mpz literal. Also used by \<open>Newton.thy\<close>, through this file's import.\<close>
definition mpz_of_snat_monadic :: "nat \<Rightarrow> int nres" where
"mpz_of_snat_monadic n \<equiv> doN {
  ni \<leftarrow> snat_sint_cast.mop TYPE(gmp_long_len) n;
  RETURN (mpz_from_int ni)
}"

lemma mpz_of_snat_monadic_correct:
  assumes "int n < max_sint LENGTH(gmp_long_len)"
  shows "mpz_of_snat_monadic n \<le> RETURN (int n)"
  using assms
  unfolding mpz_of_snat_monadic_def snat_sint_cast.mop_def
  by (auto simp: pw_le_iff refine_pw_simps)

sepref_register "PR_CONST mpz_of_snat_monadic" :: "nat \<Rightarrow> int nres"

sepref_definition mpz_of_snat_impl [llvm_inline] is
  "mpz_of_snat_monadic" ::
  "[\<lambda>n. slong_bounds (int n)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  unfolding mpz_of_snat_monadic_def slong_bounds_def
  apply (annot_sint_const "TYPE(gmp_long_len)")?
  by sepref

lemma mpz_of_snat_impl_hnr[sepref_fr_rules]:
  "(mpz_of_snat_impl, PR_CONST mpz_of_snat_monadic) \<in>
    [\<lambda>n. slong_bounds (int n)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  using mpz_of_snat_impl.refine
  by (simp add: PR_CONST_def)

text \<open>In-place \<open>x := x + u\<close> / \<open>x := x - u\<close> for a small unsigned constant \<open>u\<close> via GMP's immediate
  operations \<open>raw_mpz_add_ui\<close>/\<open>raw_mpz_sub_ui\<close>, with no materialised mpz temporary. As for
  \<open>mpz_shift_left_snat_monadic\<close>: an snat\<rightarrow>uint cast (\<open>snat_uint_cast\<close>, whose abstract map is
  @{term int}) followed by the destructive-first \<open>mpz_add_ui.amop_r1\<close>/\<open>mpz_sub_ui.amop_r1\<close> (external
  \<open>uint\<close> operand at \<open>gmp_long_len\<close>, the C \<open>unsigned long\<close>). \<open>x\<close> is consumed and returned updated;
  \<open>mpz_sub_ui\<close> is total (\<open>mpz\<close> is signed), so there is no \<open>u \<le> x\<close> side condition.\<close>
definition mpz_add_ui_snat_monadic :: "int \<Rightarrow> nat \<Rightarrow> int nres" where
"mpz_add_ui_snat_monadic x u \<equiv> doN {
  u_ui \<leftarrow> (PR_CONST (snat_uint_cast.mop TYPE(gmp_long_len))) u;
  (PR_CONST mpz_add_ui.amop_r1) x u_ui
}"

lemma mpz_add_ui_snat_monadic_spec[refine_vcg]:
  assumes "u < max_snat LENGTH(gmp_long_len)"
  shows "mpz_add_ui_snat_monadic x u \<le> RETURN (x + int u)"
  using assms
  unfolding mpz_add_ui_snat_monadic_def snat_uint_cast.mop_def
    mpz_add_ui.amop_r1_def mpz_add_ui.aop_r1_def PR_CONST_def
  by (auto simp: pw_le_iff refine_pw_simps max_snat_def max_uint_def)

sepref_register "PR_CONST mpz_add_ui_snat_monadic" :: "int \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition mpz_add_ui_snat_impl [llvm_inline] is
  "uncurry mpz_add_ui_snat_monadic" ::
  "[\<lambda>(_, u). u < max_snat LENGTH(gmp_long_len)]\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  unfolding mpz_add_ui_snat_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [simp] = max_snat_def max_unat_def max_uint_def
  supply [sepref_bounds_simps] = snat_in_bounds_aux
  by sepref

lemma mpz_add_ui_snat_impl_hnr[sepref_fr_rules]:
  "(uncurry mpz_add_ui_snat_impl,
    uncurry (PR_CONST mpz_add_ui_snat_monadic)) \<in>
    [\<lambda>(_, u). u < max_snat LENGTH(gmp_long_len)]\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  using mpz_add_ui_snat_impl.refine
  by (simp add: PR_CONST_def)

definition mpz_sub_ui_snat_monadic :: "int \<Rightarrow> nat \<Rightarrow> int nres" where
"mpz_sub_ui_snat_monadic x u \<equiv> doN {
  u_ui \<leftarrow> (PR_CONST (snat_uint_cast.mop TYPE(gmp_long_len))) u;
  (PR_CONST mpz_sub_ui.amop_r1) x u_ui
}"

lemma mpz_sub_ui_snat_monadic_spec[refine_vcg]:
  assumes "u < max_snat LENGTH(gmp_long_len)"
  shows "mpz_sub_ui_snat_monadic x u \<le> RETURN (x - int u)"
  using assms
  unfolding mpz_sub_ui_snat_monadic_def snat_uint_cast.mop_def
    mpz_sub_ui.amop_r1_def mpz_sub_ui.aop_r1_def PR_CONST_def
  by (auto simp: pw_le_iff refine_pw_simps max_snat_def max_uint_def)

sepref_register "PR_CONST mpz_sub_ui_snat_monadic" :: "int \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition mpz_sub_ui_snat_impl [llvm_inline] is
  "uncurry mpz_sub_ui_snat_monadic" ::
  "[\<lambda>(_, u). u < max_snat LENGTH(gmp_long_len)]\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  unfolding mpz_sub_ui_snat_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [simp] = max_snat_def max_unat_def max_uint_def
  supply [sepref_bounds_simps] = snat_in_bounds_aux
  by sepref

lemma mpz_sub_ui_snat_impl_hnr[sepref_fr_rules]:
  "(uncurry mpz_sub_ui_snat_impl,
    uncurry (PR_CONST mpz_sub_ui_snat_monadic)) \<in>
    [\<lambda>(_, u). u < max_snat LENGTH(gmp_long_len)]\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  using mpz_sub_ui_snat_impl.refine
  by (simp add: PR_CONST_def)

end
