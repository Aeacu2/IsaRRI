theory Poly_Vec
  imports Carried_Kernel
begin

text \<open>Vector-of-polynomials container: an array-list of option slots, each holding an
  owned \<open>gmp_poly\<close>. Every solver's \<open>todo\<close> column is built on it.
  Main definitions: \<open>gmp_poly_vec_slots_assn\<close> / \<open>gmp_poly_vec_assn\<close> and the push/pop/free
  operations over them. Ownership: a slot is emptied on pop, so a popped index must not be read
  again before it is re-stored.\<close>

type_synonym gmp_poly_vec_raw = "(gmp_poly_raw, gmp_poly_len) array_list"
type_synonym gmp_poly_vec_slots = "gmp_poly option list"

definition gmp_poly_vec_slots_assn ::
  "gmp_poly_vec_slots \<Rightarrow> gmp_poly_vec_raw \<Rightarrow> assn" where
"gmp_poly_vec_slots_assn slots p \<equiv>
  EXS ptrs. raw_al_assn ptrs p \<and>*
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) slots ptrs"

definition gmp_poly_vec_assn ::
  "gmp_poly list \<Rightarrow> gmp_poly_vec_raw \<Rightarrow> assn" where
"gmp_poly_vec_assn qs p \<equiv>
  gmp_poly_vec_slots_assn (map Some qs) p"

lemma gmp_poly_vec_slots_lenD[vcg_prep_ext_rules]:
  "pure_part
    (\<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) slots ptrs)
    \<Longrightarrow> length ptrs = length slots"
  by (drule list_assn_pure_part) simp

lemma gmp_poly_vec_raw_slots_len_extract:
  "raw_al_assn ptrs p \<and>*
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) slots ptrs
    \<turnstile>
    raw_al_assn ptrs p \<and>*
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) slots ptrs
    \<and>* \<up>(length ptrs = length slots)"
  apply (rule entails_pureI)
  apply (auto dest!: pure_part_split_conj gmp_poly_vec_slots_lenD
    simp: sep_algebra_simps)
  done

lemma gmp_poly_vec_raw_slots_lenD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) slots ptrs)
    \<Longrightarrow> length ptrs = length slots"
  apply (drule pure_part_split_conj)
  apply (auto dest!: gmp_poly_vec_slots_lenD)
  done

lemma gmp_poly_vec_raw_slots_poly_lenD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) slots ptrs \<and>*
      gmp_poly_assn q qptr)
    \<Longrightarrow> length ptrs = length slots"
  apply (drule pure_part_split_conj)
  apply (elim conjE)
  apply (drule pure_part_split_conj)
  apply (auto dest!: gmp_poly_vec_slots_lenD)
  done

definition poly_vec_empty_sz_monadic :: "nat \<Rightarrow> gmp_poly list nres" where
"poly_vec_empty_sz_monadic n \<equiv> RETURN []"

sepref_register "PR_CONST poly_vec_empty_sz_monadic"
  :: "nat \<Rightarrow> gmp_poly list nres"

definition [llvm_code, llvm_inline]:
  "poly_vec_empty_sz_impl (n :: gmp_poly_len word) \<equiv>
    arl_new_sz TYPE(gmp_poly_raw) n"

lemma poly_vec_empty_sz_impl_rule:
  "llvm_htriple
    (\<upharpoonleft>snat.assn n ni)
    (poly_vec_empty_sz_impl ni)
    (\<lambda>p. gmp_poly_vec_assn [] p)"
  unfolding poly_vec_empty_sz_impl_def
    gmp_poly_vec_assn_def gmp_poly_vec_slots_assn_def
  by vcg'

lemma poly_vec_empty_sz_impl_hnr[sepref_fr_rules]:
  "(poly_vec_empty_sz_impl, PR_CONST poly_vec_empty_sz_monadic) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>d \<rightarrow>\<^sub>a gmp_poly_vec_assn"
  apply sepref_to_hoare
  unfolding poly_vec_empty_sz_monadic_def
  apply (clarsimp simp: refine_pw_simps in_snat_rel_conv_assn)
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule poly_vec_empty_sz_impl_rule)
    apply (auto simp: entails_def sep_conj_def pred_lift_extract_simps
      list_assn_empty1_conv)
  done

definition poly_vec_length_monadic :: "gmp_poly list \<Rightarrow> nat nres" where
"poly_vec_length_monadic qs \<equiv> RETURN (length qs)"

sepref_register "PR_CONST poly_vec_length_monadic"
  :: "gmp_poly list \<Rightarrow> nat nres"

definition [llvm_code, llvm_inline]:
  "poly_vec_length_impl p \<equiv> arl_len p"

lemma poly_vec_length_impl_hnr[sepref_fr_rules]:
  "(poly_vec_length_impl, PR_CONST poly_vec_length_monadic)
    \<in> gmp_poly_vec_assn\<^sup>k \<rightarrow>\<^sub>a
      snat_assn' TYPE(gmp_poly_len)"
  apply sepref_to_hoare
  unfolding poly_vec_length_impl_def
    poly_vec_length_monadic_def gmp_poly_vec_assn_def
    gmp_poly_vec_slots_assn_def
  apply vcg'
  apply (rule ENTAILS_drule[OF gmp_poly_vec_raw_slots_len_extract])
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps snat.assn_is_rel snat_rel_def
    dest!: dsc_snat_pure_relD)
  apply blast
  apply (fact Defer_Slot.remove_slot)
  done

definition poly_vec_push_monadic ::
  "gmp_poly list \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly list nres" where
"poly_vec_push_monadic qs q \<equiv> doN {
  ASSERT (length qs + 1 < max_snat LENGTH(gmp_poly_len));
  RETURN (qs @ [q])
}"

sepref_register "PR_CONST poly_vec_push_monadic"
  :: "gmp_poly list \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly list nres"

definition [llvm_code, llvm_inline]:
  "poly_vec_push_impl p q \<equiv> arl_push_back p q"

lemma gmp_poly_vec_append_entails_raw:
  assumes "length ptrs = length qs"
  shows "raw_al_assn (ptrs @ [qptr]) p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) (map Some qs) ptrs \<and>*
      gmp_poly_assn q qptr
    \<turnstile>
      (EXS ptrs'. raw_al_assn ptrs' p \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
          (map Some qs @ [Some q]) ptrs')"
  apply (rule entails_exI[where x="ptrs @ [qptr]"])
  using assms
  by (simp add: sep_algebra_simps)

lemma poly_vec_push_impl_rule:
  fixes p :: gmp_poly_vec_raw
  assumes "length qs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "llvm_htriple
    (gmp_poly_vec_assn qs p \<and>* gmp_poly_assn q qptr)
    (poly_vec_push_impl p qptr)
    (\<lambda>p'. gmp_poly_vec_assn (qs @ [q]) p')"
  using assms
  unfolding poly_vec_push_impl_def gmp_poly_vec_assn_def
    gmp_poly_vec_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_vec_raw_slots_poly_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre[
       where P'="(raw_al_assn ptrs p \<and>*
         \<up>\<^sub>d(length ptrs + 1 < max_snat LENGTH(gmp_poly_len))) \<and>*
         (\<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) (map Some qs) ptrs \<and>*
          gmp_poly_assn q qptr)"])
      prefer 2
      apply (rule frame_rule[
        where F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) (map Some qs) ptrs \<and>*
          gmp_poly_assn q qptr"])
      apply (rule arl_push_back_rule)
     apply (simp add: entails_def sep_algebra_simps SOLVE_AUTO_DEFER_def)
    apply (rule gmp_poly_vec_append_entails_raw)
    apply simp
    done
  done

lemma poly_vec_push_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_vec_push_impl,
    uncurry (PR_CONST poly_vec_push_monadic)) \<in>
    [\<lambda>(qs, _). length qs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
        gmp_poly_vec_assn"
  apply sepref_to_hoare
  unfolding poly_vec_push_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for q qptr qs p
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_vec_push_impl_rule)
     apply simp
    apply (clarsimp simp: entails_def sep_algebra_simps)
    done
  done

definition poly_vec_push2_monadic ::
  "gmp_poly list \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly list nres" where
"poly_vec_push2_monadic qs q1 q2 \<equiv> doN {
  ASSERT (length qs + 2 < max_snat LENGTH(gmp_poly_len));
  qs \<leftarrow> (PR_CONST poly_vec_push_monadic) qs q1;
  ASSERT (length qs + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_vec_push_monadic) qs q2
}"

lemma poly_vec_push2_monadic_correct:
  assumes "length qs + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_vec_push2_monadic qs q1 q2 \<le> RETURN (qs @ [q1, q2])"
  using assms
  unfolding poly_vec_push2_monadic_def poly_vec_push_monadic_def PR_CONST_def
  by refine_vcg auto

sepref_register "PR_CONST poly_vec_push2_monadic"
  :: "gmp_poly list \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly list nres"

sepref_definition poly_vec_push2_impl [llvm_inline] is
  "uncurry2 poly_vec_push2_monadic" ::
  "[\<lambda>((qs, _), _). length qs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_vec_assn"
  unfolding poly_vec_push2_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma poly_vec_push2_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_vec_push2_impl,
    uncurry2 (PR_CONST poly_vec_push2_monadic)) \<in>
    [\<lambda>((qs, _), _). length qs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_vec_assn"
  using poly_vec_push2_impl.refine
  by (simp add: PR_CONST_def)

lemma gmp_poly_vec_list_assn_last:
  assumes "qs \<noteq> []"
    and "length ptrs = length qs"
  shows "\<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) (map Some qs) ptrs =
    (gmp_poly_assn (last qs) (last ptrs) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
        (map Some (butlast qs)) (butlast ptrs))"
proof -
  have ptrs_ne: "ptrs \<noteq> []"
    using assms by auto
  have qs_split: "map Some qs = map Some (butlast qs) @ [Some (last qs)]"
  proof -
    have "qs = butlast qs @ [last qs]"
      using assms(1) by simp
    then have "map Some qs = map Some (butlast qs @ [last qs])"
      by simp
    also have "... = map Some (butlast qs) @ [Some (last qs)]"
      by (simp add: map_append)
    finally show ?thesis .
  qed
  have ptrs_split: "ptrs = butlast ptrs @ [last ptrs]"
    using ptrs_ne by simp
  have len: "length (map Some (butlast qs)) = length (butlast ptrs)"
    using assms by simp
  have one:
    "\<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
      [Some (last qs)] [last ptrs] =
      gmp_poly_assn (last qs) (last ptrs)"
    by (simp add: sep_algebra_simps)
  show ?thesis
  proof -
    have "\<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) (map Some qs) ptrs =
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
        (map Some (butlast qs) @ [Some (last qs)]) (butlast ptrs @ [last ptrs])"
      by (subst qs_split, subst ptrs_split, rule refl)
    also have "... =
      (\<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
        (map Some (butlast qs)) (butlast ptrs) \<and>*
        gmp_poly_assn (last qs) (last ptrs))"
      using len by (simp only: list_assn_append one)
    also have "... =
      (gmp_poly_assn (last qs) (last ptrs) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
          (map Some (butlast qs)) (butlast ptrs))"
      by (simp add: sep_conj_commute)
    finally show ?thesis .
  qed
qed

definition poly_vec_pop_last_monadic ::
  "gmp_poly list \<Rightarrow> (gmp_poly \<times> gmp_poly list) nres" where
"poly_vec_pop_last_monadic qs \<equiv> doN {
  ASSERT (qs \<noteq> []);
  RETURN (last qs, butlast qs)
}"

sepref_register "PR_CONST poly_vec_pop_last_monadic"
  :: "gmp_poly list \<Rightarrow> (gmp_poly \<times> gmp_poly list) nres"

definition [llvm_code, llvm_inline]:
  "poly_vec_pop_last_impl p \<equiv> arl_pop_back p"

lemma poly_vec_pop_last_monadic_post_entails:
  assumes "qptr = last ptrs"
  shows "raw_al_assn (butlast ptrs) p' \<and>*
      gmp_poly_assn (last qs) (last ptrs) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
        (map Some (butlast qs)) (butlast ptrs)
    \<turnstile>
      gmp_poly_assn (last qs) qptr \<and>*
      gmp_poly_vec_assn (butlast qs) p'"
  using assms
  unfolding gmp_poly_vec_assn_def gmp_poly_vec_slots_assn_def
  apply (simp add: sep_conj_exists)
  apply (rule entails_exI[where x="butlast ptrs"])
  apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
    pred_lift_extract_simps)
  done

lemma poly_vec_pop_last_monadic_eq_entails:
  "gmp_poly_assn q y \<and>* raw_al_assn xs p \<and>* \<up>(x = y) \<and>* R
    \<turnstile> gmp_poly_assn q x \<and>* raw_al_assn xs p \<and>* R"
  by (auto simp: entails_def sep_conj_def pred_lift_extract_simps)

lemma poly_vec_pop_last_monadic_eq_entails_return_order:
  "raw_al_assn xs p \<and>* \<up>(x = y) \<and>* gmp_poly_assn q y \<and>* R
    \<turnstile> gmp_poly_assn q x \<and>* raw_al_assn xs p \<and>* R"
  apply (rule entails_trans[where
    Q="gmp_poly_assn q y \<and>* raw_al_assn xs p \<and>* \<up>(x = y) \<and>* R"])
   apply (simp add: sep_conj_ac)
  apply (rule poly_vec_pop_last_monadic_eq_entails)
  done

lemma poly_vec_pop_last_monadic_pre_entails:
  assumes "qs \<noteq> []"
    and "length ptrs = length qs"
  shows "raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) (map Some qs) ptrs
    \<turnstile>
      (raw_al_assn ptrs p \<and>* \<up>\<^sub>d(ptrs \<noteq> [])) \<and>*
      (gmp_poly_assn (last qs) (last ptrs) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
          (map Some (butlast qs)) (butlast ptrs))"
proof -
  have ptrs_ne: "ptrs \<noteq> []"
    using assms by auto
  have list_eq:
    "\<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) (map Some qs) ptrs =
      (gmp_poly_assn (last qs) (last ptrs) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
          (map Some (butlast qs)) (butlast ptrs))"
    by (rule gmp_poly_vec_list_assn_last[OF assms])
  show ?thesis
    unfolding list_eq
    using ptrs_ne
    by (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
      SOLVE_AUTO_DEFER_def)
qed

lemma poly_vec_pop_last_monadic_arl_post_entails:
  "((case r of
      (x, ali) \<Rightarrow> raw_al_assn (butlast ptrs) ali \<and>* \<up>(x = last ptrs)) \<and>*
      gmp_poly_assn (last qs) (last ptrs) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
        (map Some (butlast qs)) (butlast ptrs))
    \<turnstile>
      (case r of
        (qptr, p') \<Rightarrow>
          gmp_poly_assn (last qs) qptr \<and>*
          gmp_poly_vec_assn (butlast qs) p')"
  apply (cases r)
  unfolding gmp_poly_vec_assn_def gmp_poly_vec_slots_assn_def
  apply clarsimp
  apply (simp add: sep_conj_exists)
  apply (rule entails_exI[where x="butlast ptrs"])
  apply (rule poly_vec_pop_last_monadic_eq_entails_return_order)
  done

lemma poly_vec_pop_last_impl_ptrs_rule:
  fixes p :: gmp_poly_vec_raw
  assumes "qs \<noteq> []"
    and "length ptrs = length qs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) (map Some qs) ptrs)
    (poly_vec_pop_last_impl p)
    (\<lambda>(qptr, p'). gmp_poly_assn (last qs) qptr \<and>*
      gmp_poly_vec_assn (butlast qs) p')"
proof -
  let ?slots =
    "\<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) (map Some qs) ptrs"
  let ?rest =
    "gmp_poly_assn (last qs) (last ptrs) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn)))
        (map Some (butlast qs)) (butlast ptrs)"
  let ?mid =
    "\<lambda>r. ((case r of
      (x, ali) \<Rightarrow> raw_al_assn (butlast ptrs) ali \<and>* \<up>(x = last ptrs)) \<and>* ?rest)"

  have pre_ent: "raw_al_assn ptrs p \<and>* ?slots
    \<turnstile> (raw_al_assn ptrs p \<and>* \<up>\<^sub>d(ptrs \<noteq> [])) \<and>* ?rest"
    using assms by (rule poly_vec_pop_last_monadic_pre_entails)

  have hpop: "llvm_htriple
    ((raw_al_assn ptrs p \<and>* \<up>\<^sub>d(ptrs \<noteq> [])) \<and>* ?rest)
    (arl_pop_back p)
    ?mid"
    apply (rule frame_rule[where F="?rest"])
    apply (rule arl_pop_back_rule)
    done

  have hpre: "llvm_htriple
    (raw_al_assn ptrs p \<and>* ?slots)
    (arl_pop_back p)
    ?mid"
    using pre_ent hpop by (rule htriple_ent_pre)

  have post_ent:
    "\<And>r. ?mid r \<turnstile>
      (case r of
        (qptr, p') \<Rightarrow>
          gmp_poly_assn (last qs) qptr \<and>*
          gmp_poly_vec_assn (butlast qs) p')"
    by (rule poly_vec_pop_last_monadic_arl_post_entails)

  show ?thesis
    unfolding poly_vec_pop_last_impl_def
    using post_ent hpre
    by (rule htriple_ent_post)
qed

lemma poly_vec_pop_last_impl_rule:
  fixes p :: gmp_poly_vec_raw
  assumes "qs \<noteq> []"
  shows "llvm_htriple
    (gmp_poly_vec_assn qs p)
    (poly_vec_pop_last_impl p)
    (\<lambda>(qptr, p'). gmp_poly_assn (last qs) qptr \<and>*
      gmp_poly_vec_assn (butlast qs) p')"
proof -
  let ?raw =
    "EXS ptrs. raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) (map Some qs) ptrs"

  have pre_ent: "gmp_poly_vec_assn qs p \<turnstile> ?raw"
    unfolding gmp_poly_vec_assn_def gmp_poly_vec_slots_assn_def
    by simp

  have hraw: "llvm_htriple
    ?raw
    (poly_vec_pop_last_impl p)
    (\<lambda>(qptr, p'). gmp_poly_assn (last qs) qptr \<and>*
      gmp_poly_vec_assn (butlast qs) p')"
    apply (rule dsc_htriple_ex_preI)
    subgoal for ptrs
      apply (rule htriple_pure_preI)
      apply (frule gmp_poly_vec_raw_slots_lenD)
      apply (rule poly_vec_pop_last_impl_ptrs_rule)
       apply (simp add: assms)
      apply simp
      done
    done

  show ?thesis
    using pre_ent hraw
    by (rule htriple_ent_pre)
qed

lemma poly_vec_pop_last_impl_hnr[sepref_fr_rules]:
  "(poly_vec_pop_last_impl, PR_CONST poly_vec_pop_last_monadic) \<in>
    [\<lambda>qs. qs \<noteq> []]\<^sub>a gmp_poly_vec_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a gmp_poly_vec_assn"
  apply sepref_to_hoare
  unfolding poly_vec_pop_last_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for qs p
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_vec_pop_last_impl_rule)
     apply simp
    apply (clarsimp simp: entails_def sep_algebra_simps)
    done
  done

lemma gmp_poly_vec_empty_slots_frame_entails_emp:
  "\<box> \<and>* \<upharpoonleft>(list_assn (oelem_assn (mk_assn gmp_poly_assn))) [] ptrs
    \<turnstile> \<box>"
  by (cases ptrs) (auto simp: entails_def sep_conj_def sep_algebra_simps)

definition poly_vec_free_empty_monadic :: "gmp_poly list \<Rightarrow> unit nres" where
"poly_vec_free_empty_monadic qs \<equiv> doN {
  ASSERT (qs = []);
  RETURN ()
}"

sepref_register "PR_CONST poly_vec_free_empty_monadic"
  :: "gmp_poly list \<Rightarrow> unit nres"

definition [llvm_code, llvm_inline]:
  "poly_vec_free_empty_impl p \<equiv> arl_free p"

lemma poly_vec_free_empty_impl_rule:
  assumes "qs = []"
  shows "llvm_htriple
    (gmp_poly_vec_assn qs p)
    (poly_vec_free_empty_impl p)
    (\<lambda>_. \<box>)"
  using assms
  unfolding poly_vec_free_empty_impl_def
    gmp_poly_vec_assn_def gmp_poly_vec_slots_assn_def
  apply simp
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (cases ptrs)
     apply (simp add: sep_algebra_simps)
     apply (rule arl_free_rule)
    apply (simp add: list_assn_empty1_conv)
    done
  done

lemma poly_vec_free_empty_impl_hnr[sepref_fr_rules]:
  "(poly_vec_free_empty_impl,
    PR_CONST poly_vec_free_empty_monadic) \<in>
    [\<lambda>qs. qs = []]\<^sub>a gmp_poly_vec_assn\<^sup>d \<rightarrow> unit_assn"
  apply sepref_to_hoare
  unfolding poly_vec_free_empty_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for qs p
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_vec_free_empty_impl_rule)
     apply simp
    apply (clarsimp simp: entails_def sep_algebra_simps)
    done
  done

end
