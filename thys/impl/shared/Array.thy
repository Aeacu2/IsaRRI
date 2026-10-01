theory Array
imports Scalar
begin

text \<open>GMP polynomial container: the representation relating an abstract \<open>gmp_poly\<close> to a
  heap-owned container of GMP coefficients.
  Main definitions: \<open>gmp_poly_assn\<close> and the option-slot ownership infrastructure later containers
  reuse.

  An LLVM array stores pointers to GMP blocks; each block is owned by an \<open>mpzb_assn\<close> element
  resource; get/copy/replace/free operations make the ownership transfer explicit. A plain
  \<open>array_assn mpzb_assn\<close> would not do, because \<open>mpzb_assn\<close> owns heap state, so element extraction
  and restoration need dedicated rules.\<close>

type_synonym gmp_poly_len = 64
type_synonym gmp_poly_raw = "(mpz_t, gmp_poly_len) array_list"
type_synonym gmp_poly_slots = "int option list"

text \<open>The raw arraylist stores only GMP block pointers. Ownership of each block is
  tracked separately by the option-element list assertion:
  \<^item> \<open>Some x\<close> owns an \<open>mpzb_assn x\<close> at the stored pointer.
  \<^item> \<open>None\<close> is a temporary hole with no coefficient ownership.

  Performance implications:
  \<^item> \<open>arl_len\<close> is O(1), since the arraylist stores length in its header.
  \<^item> \<open>arl_resize\<close> copies only \<open>mpz_t\<close> pointers, not GMP limb data.
  \<^item> GMP blocks remain at stable addresses across arraylist resizes.
  \<^item> Future batch kernels can reserve capacity once and then mutate pointed-to
    GMP blocks in place.\<close>
definition gmp_poly_slots_assn ::
  "gmp_poly_slots \<Rightarrow> gmp_poly_raw \<Rightarrow> assn" where
"gmp_poly_slots_assn slots p \<equiv>
  EXS ptrs. raw_al_assn ptrs p \<and>*
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs"

definition gmp_poly_assn ::
  "gmp_poly \<Rightarrow> gmp_poly_raw \<Rightarrow> assn" where
"gmp_poly_assn xs p \<equiv> gmp_poly_slots_assn (map Some xs) p"

lemma gmp_poly_slots_lenD[vcg_prep_ext_rules]:
  "pure_part
    (\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs)
    \<Longrightarrow> length ptrs = length xs"
  by (drule list_assn_pure_part) simp

lemma gmp_poly_slots_len_frameD:
  "pure_part
    (\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs
      \<and>* F)
    \<Longrightarrow> length ptrs = length xs"
  apply (drule pure_part_split_conj)
  apply (auto dest!: gmp_poly_slots_lenD)
  done

lemma gmp_poly_raw_slots_len_extract:
  "raw_al_assn ptrs p \<and>*
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs
    \<turnstile>
    raw_al_assn ptrs p \<and>*
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs
    \<and>* \<up>(length ptrs = length xs)"
  apply (rule entails_pureI)
  apply (auto dest!: pure_part_split_conj gmp_poly_slots_lenD
    simp: sep_algebra_simps)
  done

lemma dsc_snat_pure_relD:
  "\<flat>\<^sub>psnat.assn n r \<Longrightarrow> (r, n) \<in> snat.rel"
  unfolding dr_assn_pure_asm_prefix_def
  by (simp add: snat.assn_is_rel snat_rel_def)

lemma dsc_pure_part_left_pureD:
  "pure_part (\<up>P \<and>* Q) \<Longrightarrow> P"
  by (drule pure_part_split_conj) simp

lemma dsc_pure_part_pure_assn_pureD:
  "pure_part (\<up>P \<and>* A \<and>* \<up>Q) \<Longrightarrow> P \<and> Q"
  apply (drule pure_part_split_conj)
  apply (auto dest!: pure_part_split_conj)
  done

lemma dsc_snat_mpzb_pure_relD:
  "pure_part (\<upharpoonleft>snat.assn i ii \<and>* mpzb_assn x ptr)
    \<Longrightarrow> (ii, i) \<in> snat.rel"
  by (auto dest!: pure_part_split_conj
    simp: snat.assn_is_rel snat_rel_def pure_def)

lemma gmp_poly_slots_focus_coeff:
  assumes "i < length xs"
  shows "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs =
    (mpzb_assn (xs ! i) (ptrs ! i) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        ((map Some xs)[i := None]) ptrs)"
  using assms
  by (subst lo_extract_elem) simp_all

lemma gmp_poly_slots_focus_some:
  assumes "i < length slots"
    and "slots ! i = Some x"
  shows "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs =
    (mpzb_assn x (ptrs ! i) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (slots[i := None]) ptrs)"
  using assms
  by (subst lo_extract_elem) simp_all

lemma gmp_poly_slots_unfocus_coeff:
  assumes "i < length xs"
  shows "(mpzb_assn (xs ! i) (ptrs ! i) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        ((map Some xs)[i := None]) ptrs) =
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs"
  using gmp_poly_slots_focus_coeff[OF assms, of ptrs]
  by simp

lemma gmp_poly_slots_insert_some:
  assumes "i < length slots"
    and "slots ! i = None"
  shows "(mpzb_assn x ptr \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs) =
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
      (slots[i := Some x]) (ptrs[i := ptr])"
  using lo_insert_elem[OF assms, of "mk_assn mpzb_assn" x ptrs ptr]
  by (simp add: sep_algebra_simps)

lemma gmp_poly_slots_set_coeff_eq:
  assumes "i < length xs"
  shows "((map Some xs)[i := None])[i := Some x] = map Some (xs[i := x])"
  using assms
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    with Cons.prems have "j < length xs" by simp
    from Cons.IH[OF this] Suc show ?thesis by simp
  qed
qed

lemma gmp_poly_slots_focus_two_coeff:
  assumes "i < length xs"
    and "j < length xs"
    and "i \<noteq> j"
  shows "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs =
    (mpzb_assn (xs ! i) (ptrs ! i) \<and>*
      mpzb_assn (xs ! j) (ptrs ! j) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (((map Some xs)[i := None])[j := None]) ptrs)"
proof -
  let ?slots_i = "(map Some xs)[i := None]"
  have focus_i:
    "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs =
      (mpzb_assn (xs ! i) (ptrs ! i) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) ?slots_i ptrs)"
    by (rule gmp_poly_slots_focus_coeff[OF assms(1)])
  have slot_j: "?slots_i ! j = Some (xs ! j)"
    using assms by simp
  have focus_j:
    "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) ?slots_i ptrs =
      (mpzb_assn (xs ! j) (ptrs ! j) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (?slots_i[j := None]) ptrs)"
    using gmp_poly_slots_focus_some[OF _ slot_j, of ptrs]
      assms by simp
  show ?thesis
    by (simp add: focus_i focus_j sep_algebra_simps)
qed

lemma gmp_poly_slots_focus_two_coeff_update:
  assumes "i < length xs"
    and "j < length xs"
    and "i \<noteq> j"
  shows "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
      (map Some (xs[i := x])) ptrs =
    (mpzb_assn x (ptrs ! i) \<and>*
      mpzb_assn (xs ! j) (ptrs ! j) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (((map Some xs)[i := None])[j := None]) ptrs)"
proof -
  have j_upd: "(xs[i := x]) ! j = xs ! j"
    using assms by simp
  have slots_eq:
    "((map Some (xs[i := x]))[i := None])[j := None] =
      ((map Some xs)[i := None])[j := None]"
    using assms
    apply (intro nth_equalityI)
     apply simp
    apply (simp add: nth_list_update)
    done
  have focus_fact: "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (xs[i := x])) ptrs =
      (mpzb_assn ((xs[i := x]) ! i) (ptrs ! i) \<and>*
        mpzb_assn ((xs[i := x]) ! j) (ptrs ! j) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (((map Some (xs[i := x]))[i := None])[j := None]) ptrs)"
    apply (rule gmp_poly_slots_focus_two_coeff)
    using assms
    apply simp_all
    done
  show ?thesis
    using assms
    by (simp add: focus_fact j_upd slots_eq)
qed

lemma poly_put_coeff_monadic_post_entails:
  assumes "i < length slots"
    and "slots ! i = None"
  shows "(raw_al_assn (ptrs[i := ptr]) r \<and>* \<up>(r = p)) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs \<and>*
      mpzb_assn x ptr
    \<turnstile>
    raw_al_assn (ptrs[i := ptr]) r \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (slots[i := Some x]) (ptrs[i := ptr])"
proof -
  have slot_insert:
    "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
      (slots[i := Some x]) (ptrs[i := ptr]) =
      (mpzb_assn x ptr \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs)"
    using gmp_poly_slots_insert_some[OF assms, of x ptr ptrs]
    by simp
  show ?thesis
    unfolding slot_insert
    apply fri
    done
qed

lemma dsc_htriple_ex_preI:
  assumes "\<And>x. llvm_htriple (P x) c Q"
  shows "llvm_htriple (EXS x. P x) c Q"
  apply (rule htripleI)
  apply (clarsimp simp: STATE_extract)
  subgoal for s asf x
    by (rule htripleD[OF assms])
  done

lemma dsc_htriple_raw_ex_preI:
  assumes "\<And>x. llvm_htriple (P x) c Q"
  shows "llvm_htriple (\<lambda>s. \<exists>x. P x s) c Q"
proof (rule htripleI)
  fix st asf
  assume S: "STATE asf (\<lambda>s. \<exists>x. P x s) st"
  then obtain x where SX: "STATE asf (P x) st"
    unfolding STATE_def by blast
  from htripleD[OF assms[of x] SX]
  show "wpa asf c (\<lambda>r st'. STATE asf (Q r) st') st" .
qed

lemma dsc_htriple_bindI:
  assumes "llvm_htriple P m Q"
    and "\<And>x. llvm_htriple (Q x) (f x) R"
  shows "llvm_htriple P (doM {x \<leftarrow> m; f x}) R"
proof (rule htripleI)
  fix st asf
  assume S: "STATE asf P st"
  show "wpa asf (doM {x \<leftarrow> m; f x})
    (\<lambda>r st'. STATE asf (R r) st') st"
    apply (rule wpa_bindI)
    apply (rule wpa_monoI[OF htripleD[OF assms(1) S]])
       apply (rule htripleD[OF assms(2)])
       apply assumption
      apply simp_all
    done
qed

lemma gmp_poly_raw_slots_snat_lenD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii)
    \<Longrightarrow> length ptrs = length xs"
  by (auto dest!: pure_part_split_conj gmp_poly_slots_lenD)

lemma gmp_poly_raw_slots_two_snat_lenD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* \<upharpoonleft>snat.assn j jj)
    \<Longrightarrow> length ptrs = length xs"
  by (auto dest!: pure_part_split_conj gmp_poly_slots_lenD)

lemma gmp_poly_raw_slots_coeff_lenD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      mpzb_assn x ptr)
    \<Longrightarrow> length ptrs = length xs"
  apply (drule pure_part_split_conj)
  apply (auto dest!: gmp_poly_slots_len_frameD)
  done

lemma gmp_poly_slots_len_generalD:
  "pure_part
    (\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs)
    \<Longrightarrow> length ptrs = length slots"
  by (drule list_assn_pure_part) simp

lemma gmp_poly_raw_slots_snat_len_generalD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs \<and>*
      \<upharpoonleft>snat.assn i ii)
    \<Longrightarrow> length ptrs = length slots"
  by (auto dest!: pure_part_split_conj gmp_poly_slots_len_generalD)

lemma gmp_poly_raw_slots_snat_coeff_len_generalD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn x ptr)
    \<Longrightarrow> length ptrs = length slots"
  by (auto dest!: pure_part_split_conj gmp_poly_slots_len_generalD)

lemma gmp_poly_raw_slots_snat_coeff_snat_lenD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn c ci \<and>*
      \<upharpoonleft>snat.assn j jj)
    \<Longrightarrow> length ptrs = length xs"
  by (auto dest!: pure_part_split_conj gmp_poly_slots_lenD)

lemma gmp_poly_raw_slots_len_general_extract:
  "raw_al_assn ptrs p \<and>*
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs
    \<turnstile>
    raw_al_assn ptrs p \<and>*
    \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs
    \<and>* \<up>(length ptrs = length slots)"
  apply (rule entails_pureI)
  apply (auto dest!: pure_part_split_conj gmp_poly_slots_len_generalD
    simp: sep_algebra_simps)
  done

definition poly_length_monadic :: "gmp_poly \<Rightarrow> nat nres" where
"poly_length_monadic xs \<equiv> RETURN (length xs)"

sepref_decl_op (no_def) poly_length_monadic: poly_length_monadic
  :: "\<langle>int_rel\<rangle>list_rel \<rightarrow>\<^sub>f nat_rel"
  unfolding poly_length_monadic_def
  apply (rule frefI)
  apply (intro nres_relI)
  apply (auto simp: refine_pw_simps list_rel_imp_same_length)
  done

sepref_register "PR_CONST poly_length_monadic"
  :: "gmp_poly \<Rightarrow> nat nres"

definition [llvm_code, llvm_inline]: "poly_length_impl p \<equiv> arl_len p"

lemma poly_length_impl_hnr[sepref_fr_rules]:
  "(poly_length_impl, PR_CONST poly_length_monadic)
    \<in> gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  apply sepref_to_hoare
  unfolding poly_length_impl_def poly_length_monadic_def
    gmp_poly_assn_def gmp_poly_slots_assn_def
  supply [vcg_prep_ext_rules] = gmp_poly_slots_lenD
  apply vcg'
  apply (rule ENTAILS_drule[OF gmp_poly_raw_slots_len_extract])
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps snat.assn_is_rel snat_rel_def
    dest!: dsc_snat_pure_relD)
  apply blast
  apply (fact Defer_Slot.remove_slot)
  done

definition poly_slots_length_monadic ::
  "gmp_poly_slots \<Rightarrow> nat nres" where
"poly_slots_length_monadic slots \<equiv> RETURN (length slots)"

sepref_register "PR_CONST poly_slots_length_monadic"
  :: "gmp_poly_slots \<Rightarrow> nat nres"

definition [llvm_code, llvm_inline]:
  "poly_slots_length_impl p \<equiv> arl_len p"

lemma poly_slots_length_impl_hnr[sepref_fr_rules]:
  "(poly_slots_length_impl, PR_CONST poly_slots_length_monadic)
    \<in> gmp_poly_slots_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  apply sepref_to_hoare
  unfolding poly_slots_length_impl_def
    poly_slots_length_monadic_def gmp_poly_slots_assn_def
  supply [vcg_prep_ext_rules] = gmp_poly_slots_len_generalD
  apply vcg'
  apply (rule ENTAILS_drule[OF gmp_poly_raw_slots_len_general_extract])
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps snat.assn_is_rel snat_rel_def
    dest!: dsc_snat_pure_relD)
  apply blast
  apply (fact Defer_Slot.remove_slot)
  done

definition poly_coeff_sgn_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int nres" where
"poly_coeff_sgn_monadic xs i \<equiv> doN {
  ASSERT (i < length xs);
  RETURN (sgn (xs ! i))
}"

sepref_decl_op (no_def) poly_coeff_sgn_monadic: poly_coeff_sgn_monadic
  :: "[\<lambda>(xs, i). i < length xs]\<^sub>f
      \<langle>int_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> int_rel"
  unfolding poly_coeff_sgn_monadic_def
  apply (rule frefI)
  apply (intro nres_relI)
  apply (auto simp: refine_pw_simps list_rel_imp_same_length
    list_all2_conv_all_nth)
  done

sepref_register "PR_CONST poly_coeff_sgn_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]: "poly_coeff_sgn_impl p i \<equiv> doM {
  a \<leftarrow> arl_nth p i;
  mpzb_sgn_impl a
}"

lemma dsc_arl_nth_rule_bounded:
  fixes p :: "('a::llvm_rep, gmp_poly_len) array_list"
    and ii :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (raw_al_assn xs p \<and>* \<upharpoonleft>snat.assn i ii)
    (arl_nth p ii)
    (\<lambda>x. raw_al_assn xs p \<and>* \<up>(x = xs ! i))"
  apply (rule htriple_ent_pre[
    where P'="raw_al_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<up>\<^sub>d(i < length xs)"])
   using assms
   apply (simp add: entails_def sep_algebra_simps sep_conj_ac
     pred_lift_extract_simps SOLVE_AUTO_DEFER_def)
  apply (rule arl_nth_rule)
  done

lemma poly_coeff_sgn_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn x (ptrs ! i) \<and>* F)
    (poly_coeff_sgn_impl p ii)
    (\<lambda>ri. raw_al_assn ptrs p \<and>* (mpzb_assn x (ptrs ! i) \<and>* F) \<and>*
      gmp_sint_assn (sgn x) ri)"
  using assms
  unfolding poly_coeff_sgn_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

lemma poly_coeff_sgn_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii)
    (poly_coeff_sgn_impl p ii)
    (\<lambda>ri. raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      gmp_sint_assn (sgn (xs ! i)) ri)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_coeff_sgn_impl_focused_rule[
      where ptrs=ptrs and i=i
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        ((map Some xs)[i := None]) ptrs"
        and x="xs ! i"])
    using assms apply simp
   using assms
  apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps
    gmp_poly_slots_unfocus_coeff)
  done

lemma poly_coeff_sgn_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii)
    (poly_coeff_sgn_impl p ii)
    (\<lambda>ri. gmp_poly_assn xs p \<and>* gmp_sint_assn (sgn (xs ! i)) ri)"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_snat_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_coeff_sgn_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def)
    subgoal for r s
      apply (rule exI[where x=ptrs])
      apply assumption
      done
    done
  done

lemma poly_coeff_sgn_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_coeff_sgn_impl, uncurry (PR_CONST poly_coeff_sgn_monadic))
  \<in> [\<lambda>(xs, i). i < length xs]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_sint_assn"
  apply sepref_to_hoare
  unfolding poly_coeff_sgn_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply (clarsimp)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_coeff_sgn_impl_rule)
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps
      pred_lift_extract_simps sint_rel_def pure_def)
    done
  done

lemma dsc_mpzb_copy_rule[vcg_rules]:
  "llvm_htriple
    (mpzb_assn x xi)
    (mpzb_copy xi)
    (\<lambda>ri. mpzb_assn x xi \<and>* mpzb_assn x ri)"
  unfolding mpzb_copy_def
  supply [simp] = ll_bpto_def mpzbr_assn_def
  by vcg

definition poly_empty_sz_monadic :: "nat \<Rightarrow> gmp_poly nres" where
"poly_empty_sz_monadic n \<equiv> RETURN []"

sepref_register "PR_CONST poly_empty_sz_monadic"
  :: "nat \<Rightarrow> gmp_poly nres"

definition [llvm_code, llvm_inline]:
  "poly_empty_sz_impl (n :: gmp_poly_len word) \<equiv>
    arl_new_sz TYPE(mpz_t) n"

lemma poly_empty_sz_impl_rule:
  "llvm_htriple
    (\<upharpoonleft>snat.assn n ni)
    (poly_empty_sz_impl ni)
    (\<lambda>p. gmp_poly_assn [] p)"
  unfolding poly_empty_sz_impl_def gmp_poly_assn_def
    gmp_poly_slots_assn_def
  by vcg'

lemma gmp_poly_assn_return_entails:
  "gmp_poly_assn xs p \<turnstile>
    (EXS ys. gmp_poly_assn ys p \<and>* \<up>(ys = xs))"
  apply (rule entails_exI[where x=xs])
  apply (simp add: sep_algebra_simps)
  done

lemma poly_empty_sz_impl_hnr[sepref_fr_rules]:
  "(poly_empty_sz_impl, PR_CONST poly_empty_sz_monadic) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_empty_sz_monadic_def
  apply (clarsimp simp: refine_pw_simps in_snat_rel_conv_assn)
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule poly_empty_sz_impl_rule)
  apply (clarsimp simp: entails_def sep_algebra_simps)
  done

definition poly_push_coeff_monadic ::
  "gmp_poly \<Rightarrow> int \<Rightarrow> gmp_poly nres" where
"poly_push_coeff_monadic xs x \<equiv> doN {
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  RETURN (xs @ [x])
}"

sepref_register "PR_CONST poly_push_coeff_monadic"
  :: "gmp_poly \<Rightarrow> int \<Rightarrow> gmp_poly nres"

definition [llvm_code, llvm_inline]:
  "poly_push_coeff_impl p x \<equiv> arl_push_back p x"

lemma poly_append_coeff_entails_raw:
  assumes "length ptrs = length xs"
  shows "raw_al_assn (ptrs @ [ptr]) p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      mpzb_assn x ptr
    \<turnstile>
      (EXS ptrs'. raw_al_assn ptrs' p \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (map Some xs @ [Some x]) ptrs')"
  apply (rule entails_exI[where x="ptrs @ [ptr]"])
  using assms
  by (simp add: sep_algebra_simps)

lemma poly_push_coeff_impl_rule:
  fixes p :: gmp_poly_raw
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* mpzb_assn x ptr)
    (poly_push_coeff_impl p ptr)
    (\<lambda>p'. gmp_poly_assn (xs @ [x]) p')"
  using assms
  unfolding poly_push_coeff_impl_def gmp_poly_assn_def
    gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_coeff_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre[
       where P'="(raw_al_assn ptrs p \<and>*
         \<up>\<^sub>d(length ptrs + 1 < max_snat LENGTH(gmp_poly_len))) \<and>*
         (\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
          mpzb_assn x ptr)"])
      prefer 2
      apply (rule frame_rule[
        where F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
          mpzb_assn x ptr"])
      apply (rule arl_push_back_rule)
     apply (simp add: entails_def sep_algebra_simps SOLVE_AUTO_DEFER_def)
    apply (rule poly_append_coeff_entails_raw)
    apply assumption
    done
  done

lemma poly_push_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_push_coeff_impl,
    uncurry (PR_CONST poly_push_coeff_monadic)) \<in>
    [\<lambda>(xs, _). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_push_coeff_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for x ptr xs p
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_push_coeff_impl_rule)
     apply simp
    apply (clarsimp simp: entails_def sep_algebra_simps)
    done
  done

lemma gmp_poly_raw_slots_lenD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs)
    \<Longrightarrow> length ptrs = length xs"
  apply (drule pure_part_split_conj)
  apply (auto dest!: gmp_poly_slots_lenD)
  done

lemma poly_list_assn_last:
  assumes "xs \<noteq> []"
    and "length ptrs = length xs"
  shows "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs =
    (mpzb_assn (last xs) (last ptrs) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (butlast xs)) (butlast ptrs))"
proof -
  have ptrs_ne: "ptrs \<noteq> []"
    using assms by auto
  have xs_split: "map Some xs = map Some (butlast xs) @ [Some (last xs)]"
  proof -
    have "xs = butlast xs @ [last xs]"
      using assms(1) by simp
    then have "map Some xs = map Some (butlast xs @ [last xs])"
      by simp
    also have "... = map Some (butlast xs) @ [Some (last xs)]"
      by (simp add: map_append)
    finally show ?thesis .
  qed
  have ptrs_split: "ptrs = butlast ptrs @ [last ptrs]"
    using ptrs_ne by simp
  have len: "length (map Some (butlast xs)) = length (butlast ptrs)"
    using assms by simp
  have one:
    "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
      [Some (last xs)] [last ptrs] =
      mpzb_assn (last xs) (last ptrs)"
    by (simp add: sep_algebra_simps)
  show ?thesis
  proof -
    have "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs =
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (butlast xs) @ [Some (last xs)]) (butlast ptrs @ [last ptrs])"
      by (subst xs_split, subst ptrs_split, rule refl)
    also have "... =
      (\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (butlast xs)) (butlast ptrs) \<and>*
        mpzb_assn (last xs) (last ptrs))"
      using len by (simp only: list_assn_append one)
    also have "... =
      (mpzb_assn (last xs) (last ptrs) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (map Some (butlast xs)) (butlast ptrs))"
      by (simp add: sep_conj_commute)
    finally show ?thesis .
  qed
qed

definition poly_pop_coeff_monadic ::
  "gmp_poly \<Rightarrow> (int \<times> gmp_poly) nres" where
"poly_pop_coeff_monadic xs \<equiv> doN {
  ASSERT (xs \<noteq> []);
  RETURN (last xs, butlast xs)
}"

sepref_register "PR_CONST poly_pop_coeff_monadic"
  :: "gmp_poly \<Rightarrow> (int \<times> gmp_poly) nres"

definition [llvm_code, llvm_inline]:
  "poly_pop_coeff_impl p \<equiv> arl_pop_back p"

lemma poly_pop_coeff_monadic_eq_entails:
  "mpzb_assn x y \<and>* raw_al_assn xs p \<and>* \<up>(xptr = y) \<and>* R
    \<turnstile> mpzb_assn x xptr \<and>* raw_al_assn xs p \<and>* R"
  by (auto simp: entails_def sep_conj_def pred_lift_extract_simps)

lemma poly_pop_coeff_monadic_eq_entails_return_order:
  "raw_al_assn xs p \<and>* \<up>(xptr = y) \<and>* mpzb_assn x y \<and>* R
    \<turnstile> mpzb_assn x xptr \<and>* raw_al_assn xs p \<and>* R"
  apply (rule entails_trans[where
    Q="mpzb_assn x y \<and>* raw_al_assn xs p \<and>* \<up>(xptr = y) \<and>* R"])
   apply (simp add: sep_conj_ac)
  apply (rule poly_pop_coeff_monadic_eq_entails)
  done

lemma poly_pop_coeff_monadic_pre_entails:
  assumes "xs \<noteq> []"
    and "length ptrs = length xs"
  shows "raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs
    \<turnstile>
      (raw_al_assn ptrs p \<and>* \<up>\<^sub>d(ptrs \<noteq> [])) \<and>*
      (mpzb_assn (last xs) (last ptrs) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (map Some (butlast xs)) (butlast ptrs))"
proof -
  have ptrs_ne: "ptrs \<noteq> []"
    using assms by auto
  have list_eq:
    "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs =
      (mpzb_assn (last xs) (last ptrs) \<and>*
        \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (map Some (butlast xs)) (butlast ptrs))"
    by (rule poly_list_assn_last[OF assms])
  show ?thesis
    unfolding list_eq
    using ptrs_ne
    by (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
      SOLVE_AUTO_DEFER_def)
qed

lemma poly_pop_coeff_monadic_arl_post_entails:
  "((case r of
      (x, ali) \<Rightarrow> raw_al_assn (butlast ptrs) ali \<and>* \<up>(x = last ptrs)) \<and>*
      mpzb_assn (last xs) (last ptrs) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (butlast xs)) (butlast ptrs))
    \<turnstile>
      (case r of
        (xptr, p') \<Rightarrow>
          mpzb_assn (last xs) xptr \<and>*
          gmp_poly_assn (butlast xs) p')"
  apply (cases r)
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply clarsimp
  apply (simp add: sep_conj_exists)
  apply (rule entails_exI[where x="butlast ptrs"])
  apply (rule poly_pop_coeff_monadic_eq_entails_return_order)
  done

lemma poly_pop_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw
  assumes "xs \<noteq> []"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs)
    (poly_pop_coeff_impl p)
    (\<lambda>(xptr, p'). mpzb_assn (last xs) xptr \<and>*
      gmp_poly_assn (butlast xs) p')"
proof -
  let ?slots =
    "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs"
  let ?rest =
    "mpzb_assn (last xs) (last ptrs) \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (butlast xs)) (butlast ptrs)"
  let ?mid =
    "\<lambda>r. ((case r of
      (x, ali) \<Rightarrow> raw_al_assn (butlast ptrs) ali \<and>* \<up>(x = last ptrs)) \<and>* ?rest)"

  have pre_ent: "raw_al_assn ptrs p \<and>* ?slots
    \<turnstile> (raw_al_assn ptrs p \<and>* \<up>\<^sub>d(ptrs \<noteq> [])) \<and>* ?rest"
    using assms by (rule poly_pop_coeff_monadic_pre_entails)

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
        (xptr, p') \<Rightarrow>
          mpzb_assn (last xs) xptr \<and>*
          gmp_poly_assn (butlast xs) p')"
    by (rule poly_pop_coeff_monadic_arl_post_entails)

  show ?thesis
    unfolding poly_pop_coeff_impl_def
    using post_ent hpre
    by (rule htriple_ent_post)
qed

lemma poly_pop_coeff_impl_rule:
  fixes p :: gmp_poly_raw
  assumes "xs \<noteq> []"
  shows "llvm_htriple
    (gmp_poly_assn xs p)
    (poly_pop_coeff_impl p)
    (\<lambda>(xptr, p'). mpzb_assn (last xs) xptr \<and>*
      gmp_poly_assn (butlast xs) p')"
proof -
  let ?raw =
    "EXS ptrs. raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs"

  have pre_ent: "gmp_poly_assn xs p \<turnstile> ?raw"
    unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
    by simp

  have hraw: "llvm_htriple
    ?raw
    (poly_pop_coeff_impl p)
    (\<lambda>(xptr, p'). mpzb_assn (last xs) xptr \<and>*
      gmp_poly_assn (butlast xs) p')"
    apply (rule dsc_htriple_ex_preI)
    subgoal for ptrs
      apply (rule htriple_pure_preI)
      apply (frule gmp_poly_raw_slots_lenD)
      apply (rule poly_pop_coeff_impl_ptrs_rule)
       apply (simp add: assms)
      apply simp
      done
    done

  show ?thesis
    using pre_ent hraw
    by (rule htriple_ent_pre)
qed

lemma poly_pop_coeff_impl_hnr[sepref_fr_rules]:
  "(poly_pop_coeff_impl, PR_CONST poly_pop_coeff_monadic) \<in>
    [\<lambda>xs. xs \<noteq> []]\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      mpzb_assn \<times>\<^sub>a gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_pop_coeff_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for xs p
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_pop_coeff_impl_rule)
     apply simp
    apply (clarsimp simp: entails_def sep_algebra_simps)
    done
  done

definition poly_free_slot_monadic ::
  "gmp_poly_slots \<Rightarrow> nat \<Rightarrow> gmp_poly_slots nres" where
"poly_free_slot_monadic slots i \<equiv> doN {
  ASSERT (i < length slots);
  ASSERT (slots ! i \<noteq> None);
  RETURN (slots[i := None])
}"

sepref_register "PR_CONST poly_free_slot_monadic"
  :: "gmp_poly_slots \<Rightarrow> nat \<Rightarrow> gmp_poly_slots nres"

definition [llvm_code, llvm_inline]:
  "poly_free_slot_impl p i \<equiv> doM {
    a \<leftarrow> arl_nth p i;
    mpzb_free a;
    Mreturn p
  }"

lemma poly_free_slot_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn x (ptrs ! i) \<and>* F)
    (poly_free_slot_impl p ii)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>* F)"
  using assms
  unfolding poly_free_slot_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

lemma poly_free_slot_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length slots"
    and "slots ! i = Some x"
    and "length ptrs = length slots"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs \<and>*
      \<upharpoonleft>snat.assn i ii)
    (poly_free_slot_impl p ii)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (slots[i := None]) ptrs)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_free_slot_impl_focused_rule[
      where ptrs=ptrs and i=i
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (slots[i := None]) ptrs"
        and x=x])
    using assms apply simp
   using assms
  apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
    gmp_poly_slots_focus_some)
  apply (clarsimp simp: entails_def sep_algebra_simps)
  done

lemma poly_free_slot_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length slots"
    and "slots ! i = Some x"
  shows "llvm_htriple
    (gmp_poly_slots_assn slots p \<and>* \<upharpoonleft>snat.assn i ii)
    (poly_free_slot_impl p ii)
    (\<lambda>p'. gmp_poly_slots_assn (slots[i := None]) p')"
  using assms
  unfolding gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_snat_len_generalD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_free_slot_impl_ptrs_rule[where x=x])
       using assms apply simp
      using assms apply simp
     apply assumption
    apply (clarsimp simp: entails_def)
    subgoal for r s
      apply (rule exI[where x=ptrs])
      apply assumption
      done
    done
  done

lemma poly_free_slot_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_free_slot_impl,
    uncurry (PR_CONST poly_free_slot_monadic)) \<in>
    [\<lambda>(slots, i). i < length slots \<and> slots ! i \<noteq> None]\<^sub>a
      gmp_poly_slots_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_slots_assn"
  apply sepref_to_hoare
  unfolding poly_free_slot_monadic_def
  apply (clarsimp simp: refine_pw_simps split: option.splits)
  subgoal for x i ii slots p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_free_slot_impl_rule)
       apply assumption
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps)
    done
  done

lemma dsc_list_assn_oelem_repl_None:
  "\<upharpoonleft>(list_assn (oelem_assn (mk_assn A))) (replicate (length xs) None) xs = \<box>"
  by (induction xs) (simp_all add: sep_algebra_simps)

lemma gmp_poly_slots_none_entails_emp:
  assumes "set slots \<subseteq> {None}"
  shows "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs \<turnstile> \<box>"
proof (cases "length slots = length ptrs")
  case True
  from assms have slots_eq: "slots = replicate (length slots) None"
    by (induction slots) auto
  have repl_eq:
    "replicate (length slots) None = replicate (length ptrs) None"
    using True by simp
  have empty_eq:
    "\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs = \<box>"
    apply (subst slots_eq)
    apply (subst repl_eq)
    apply (rule dsc_list_assn_oelem_repl_None)
    done
  show ?thesis
    by (simp only: empty_eq entails_refl)
next
  case False
  then show ?thesis
    by simp
qed

definition poly_free_empty_slots_monadic ::
  "gmp_poly_slots \<Rightarrow> unit nres" where
"poly_free_empty_slots_monadic slots \<equiv> doN {
  ASSERT (set slots \<subseteq> {None});
  RETURN ()
}"

sepref_register "PR_CONST poly_free_empty_slots_monadic"
  :: "gmp_poly_slots \<Rightarrow> unit nres"

definition [llvm_code, llvm_inline]:
  "poly_free_empty_slots_impl p \<equiv> arl_free p"

lemma poly_free_empty_slots_impl_rule:
  assumes "set slots \<subseteq> {None}"
  shows "llvm_htriple
    (gmp_poly_slots_assn slots p)
    (poly_free_empty_slots_impl p)
    (\<lambda>_. \<box>)"
  unfolding poly_free_empty_slots_impl_def
    gmp_poly_slots_assn_def
  apply (rule dsc_htriple_raw_ex_preI)
  subgoal for ptrs
    apply (rule htriple_ent_pre[
      where P'="raw_al_assn ptrs p"])
     apply (rule entails_trans[
       where Q="raw_al_assn ptrs p \<and>* \<box>"])
      apply (rule conj_entails_mono)
       apply (rule entails_refl)
      apply (rule gmp_poly_slots_none_entails_emp[OF assms])
     apply (simp add: sep_algebra_simps)
    apply (rule arl_free_rule)
    done
  done

lemma poly_free_empty_slots_impl_hnr[sepref_fr_rules]:
  "(poly_free_empty_slots_impl,
    PR_CONST poly_free_empty_slots_monadic) \<in>
    [\<lambda>slots. set slots \<subseteq> {None}]\<^sub>a
      gmp_poly_slots_assn\<^sup>d \<rightarrow> unit_assn"
  apply sepref_to_hoare
  unfolding poly_free_empty_slots_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule poly_free_empty_slots_impl_rule)
   apply assumption
  apply (simp add: entails_def sep_algebra_simps)
  done

definition poly_slots_free_monadic ::
  "gmp_poly_slots \<Rightarrow> unit nres" where
"poly_slots_free_monadic slots0 \<equiv> doN {
  ASSERT (None \<notin> set slots0);
  len \<leftarrow> (PR_CONST poly_slots_length_monadic) slots0;
  ASSERT (len = length slots0);
  slots \<leftarrow> for 0 len (\<lambda>i slots. doN {
    ASSERT (i < len);
    ASSERT (slots = replicate i None @ drop i slots0);
    ASSERT (length slots = len);
    ASSERT (slots ! i \<noteq> None);
    (PR_CONST poly_free_slot_monadic) slots i
  }) slots0;
  ASSERT (set slots \<subseteq> {None});
  (PR_CONST poly_free_empty_slots_monadic) slots
}"

lemma poly_slots_free_monadic_rule[refine_vcg]:
  assumes "None \<notin> set slots"
  shows "poly_slots_free_monadic slots \<le> SPEC (\<lambda>_. True)"
  using assms
  unfolding poly_slots_free_monadic_def poly_slots_length_monadic_def
    poly_free_slot_monadic_def poly_free_empty_slots_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[
    where I="\<lambda>i slots'. slots' = replicate i None @ drop i slots"])
  apply (auto simp: nth_append)
  apply (metis nth_mem option.exhaust)
  apply (simp add: list_update_append drop_upd_first replicate_append_same
    replicate_Suc_conv_snoc)
  done

sepref_register "PR_CONST poly_slots_free_monadic"
  :: "gmp_poly_slots \<Rightarrow> unit nres"

sepref_definition poly_slots_free_impl [llvm_inline] is
  "poly_slots_free_monadic" ::
  "[\<lambda>slots. None \<notin> set slots]\<^sub>a
    gmp_poly_slots_assn\<^sup>d \<rightarrow> unit_assn"
  unfolding poly_slots_free_monadic_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

definition poly_free_monadic :: "gmp_poly \<Rightarrow> unit nres" where
"poly_free_monadic xs \<equiv>
  (PR_CONST poly_slots_free_monadic) (map Some xs)"

lemma poly_free_monadic_rule[refine_vcg]:
  "poly_free_monadic xs \<le> SPEC (\<lambda>_. True)"
  unfolding poly_free_monadic_def PR_CONST_def
  by (refine_vcg; simp)

lemma poly_free_monadic_nofail[simp]:
  "nofail (poly_free_monadic xs)"
  using poly_free_monadic_rule[of xs]
  by (simp add: pw_le_iff refine_pw_simps)

text \<open>@{const poly_free_monadic} always has at least one result witness. Its body is built from
  \<open>RETURN\<close>/\<open>ASSERT\<close>/\<open>bind\<close>/\<open>for\<close>; a failing ASSERT gives \<open>FAIL\<close>, which contains every result
  (\<open>inres FAIL x = True\<close>), so no invariant reasoning is needed, and the only excluded case is
  \<open>RES {}\<close>, which none of these combinators introduces. The three \<open>cdlr_ex_inres_*\<close> combinator
  rules below make the proof a one-line \<open>intro\<close> after unfolding.\<close>

lemma cdlr_ex_inres_RETURN: "Ex (inres (RETURN x))"
  by (intro exI[of _ x]) simp

lemma cdlr_ex_inres_ASSERT: "Ex (inres (ASSERT \<Phi>))"
  by (cases \<Phi>) (auto intro: exI[of _ "()"])

lemma cdlr_ex_inres_bind:
  assumes m: "Ex (inres m)"
    and f: "\<And>x. Ex (inres (f x))"
  shows "Ex (inres (m \<bind> f))"
proof (cases "nofail (m \<bind> f)")
  case False
  then show ?thesis by (meson not_nofail_inres)
next
  case True
  hence nfm: "nofail m" by (simp add: refine_pw_simps)
  obtain x where x: "inres m x" using m by blast
  obtain y where y: "inres (f x) y" using f by blast
  have "inres (m \<bind> f) y"
    using nfm x y by (simp add: refine_pw_simps) blast
  thus ?thesis by blast
qed

lemma cdlr_ex_inres_nfoldli:
  assumes body: "\<And>x s. Ex (inres (f x s))"
  shows "Ex (inres (nfoldli l c f s))"
proof (induction l arbitrary: s)
  case Nil
  show ?case by (simp add: cdlr_ex_inres_RETURN)
next
  case (Cons x l)
  show ?case
  proof (cases "c s")
    case True
    thus ?thesis by (simp add: cdlr_ex_inres_bind[OF body Cons.IH])
  next
    case False
    thus ?thesis by (simp add: cdlr_ex_inres_RETURN)
  qed
qed

lemma poly_free_monadic_ex_inres: "Ex (inres (poly_free_monadic xs))"
  unfolding poly_free_monadic_def poly_slots_free_monadic_def
    poly_slots_length_monadic_def poly_free_slot_monadic_def
    poly_free_empty_slots_monadic_def for_def PR_CONST_def
  by (intro cdlr_ex_inres_bind cdlr_ex_inres_nfoldli
      cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN)

text \<open>Strengthens the above to full equality: since the result type is \<open>unit\<close>, ANY inres
  witness must be \<open>()\<close>, so nofail + at-least-one-witness pins down the value completely
  (\<open>pw_eq_iff\<close>). This makes the ubiquitous \<open>poly_free_monadic xs \<bind> g = g ()\<close>
  simplification available via plain \<open>simp\<close> everywhere it's needed.\<close>
lemma poly_free_monadic_eq_RETURN[simp]: "poly_free_monadic xs = RETURN ()"
  using poly_free_monadic_nofail[of xs] poly_free_monadic_ex_inres[of xs]
  by (auto simp: pw_eq_iff)

sepref_register "PR_CONST poly_free_monadic"
  :: "gmp_poly \<Rightarrow> unit nres"

definition [llvm_code, llvm_inline]:
  "poly_free_impl (p :: gmp_poly_raw) \<equiv>
    poly_slots_free_impl p"

lemma poly_invalid_map_some:
  "invalid_assn (\<lambda>xs. gmp_poly_slots_assn (map Some xs)) xs p =
    invalid_assn gmp_poly_slots_assn (map Some xs) p"
  by (simp add: invalid_assn_def)

lemma poly_free_impl_hnr[sepref_fr_rules]:
  "(poly_free_impl, PR_CONST poly_free_monadic) \<in>
    gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  unfolding poly_free_impl_def poly_free_monadic_def
    gmp_poly_assn_def PR_CONST_def
  apply (rule hfrefI)
  apply (simp add: keep_drop_sels poly_invalid_map_some)
  using poly_slots_free_impl.refine[
    unfolded hfref_def PR_CONST_def]
  apply (auto simp: keep_drop_sels)
  done

definition poly_from_sint_list_monadic :: "int list \<Rightarrow> gmp_poly nres" where
"poly_from_sint_list_monadic xs \<equiv> doN {
  len \<leftarrow> mop_list_length xs;
  ASSERT (len = length xs);
  ASSERT (len + 1 < max_snat LENGTH(gmp_poly_len));
  dst \<leftarrow> (PR_CONST poly_empty_sz_monadic) len;
  dst \<leftarrow> for 0 len (\<lambda>i dst. doN {
    x \<leftarrow> mop_list_get xs i;
    gx \<leftarrow> RETURN (mpz_from_int x);
    ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
    (PR_CONST poly_push_coeff_monadic) dst gx
  }) dst;
  RETURN dst
}"

sepref_register "PR_CONST poly_from_sint_list_monadic"
  :: "int list \<Rightarrow> gmp_poly nres"

sepref_definition poly_from_sint_list_impl is
  "poly_from_sint_list_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (al_assn' TYPE(gmp_poly_len) gmp_sint_assn)\<^sup>k \<rightarrow>
      gmp_poly_assn"
  unfolding poly_from_sint_list_monadic_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

definition poly_copy_coeff_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int nres" where
"poly_copy_coeff_monadic xs i \<equiv> doN {
  ASSERT (i < length xs);
  RETURN (xs ! i)
}"

sepref_register "PR_CONST poly_copy_coeff_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]: "poly_copy_coeff_impl p i \<equiv> doM {
  a \<leftarrow> arl_nth p i;
  mpzb_copy a
}"

lemma poly_copy_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn x (ptrs ! i) \<and>* F)
    (poly_copy_coeff_impl p ii)
    (\<lambda>ri. raw_al_assn ptrs p \<and>* (mpzb_assn x (ptrs ! i) \<and>* F) \<and>*
      mpzb_assn x ri)"
  using assms
  unfolding poly_copy_coeff_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

lemma poly_copy_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii)
    (poly_copy_coeff_impl p ii)
    (\<lambda>ri. raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      mpzb_assn (xs ! i) ri)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_copy_coeff_impl_focused_rule[
      where ptrs=ptrs and i=i
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        ((map Some xs)[i := None]) ptrs"
        and x="xs ! i"])
    using assms apply simp
   using assms
  apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps
    gmp_poly_slots_unfocus_coeff)
  done

lemma poly_copy_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii)
    (poly_copy_coeff_impl p ii)
    (\<lambda>ri. gmp_poly_assn xs p \<and>* mpzb_assn (xs ! i) ri)"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_snat_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_copy_coeff_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def)
    subgoal for r s
      apply (rule exI[where x=ptrs])
      apply assumption
      done
    done
  done

lemma poly_copy_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_copy_coeff_impl, uncurry (PR_CONST poly_copy_coeff_monadic))
  \<in> [\<lambda>(xs, i). i < length xs]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  apply sepref_to_hoare
  unfolding poly_copy_coeff_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_copy_coeff_impl_rule)
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps)
    done
  done

definition poly_set_coeff_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly nres" where
"poly_set_coeff_monadic xs i x \<equiv> doN {
  ASSERT (i < length xs);
  RETURN (xs[i := x])
}"

definition poly_take_coeff_monadic ::
  "gmp_poly_slots \<Rightarrow> nat \<Rightarrow> (int \<times> gmp_poly_slots) nres" where
"poly_take_coeff_monadic slots i \<equiv> doN {
  ASSERT (i < length slots);
  ASSERT (slots ! i \<noteq> None);
  RETURN (the (slots ! i), slots[i := None])
}"

definition [llvm_code, llvm_inline]:
  "poly_take_coeff_impl p i \<equiv> doM {
    a \<leftarrow> arl_nth p i;
    Mreturn (a, p)
  }"

lemma poly_take_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn x (ptrs ! i) \<and>* F)
    (poly_take_coeff_impl p ii)
    (\<lambda>(a, p'). mpzb_assn x a \<and>* raw_al_assn ptrs p' \<and>* F)"
  using assms
  unfolding poly_take_coeff_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

lemma poly_take_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length slots"
    and "slots ! i = Some x"
    and "length ptrs = length slots"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs \<and>*
      \<upharpoonleft>snat.assn i ii)
    (poly_take_coeff_impl p ii)
    (\<lambda>(a, p'). mpzb_assn x a \<and>* raw_al_assn ptrs p' \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (slots[i := None]) ptrs)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_take_coeff_impl_focused_rule[
      where ptrs=ptrs and i=i
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (slots[i := None]) ptrs"
        and x=x])
    using assms apply simp
   using assms
  apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
    gmp_poly_slots_focus_some)
  apply (clarsimp simp: entails_def sep_algebra_simps)
  done

lemma poly_take_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length slots"
    and "slots ! i = Some x"
  shows "llvm_htriple
    (gmp_poly_slots_assn slots p \<and>* \<upharpoonleft>snat.assn i ii)
    (poly_take_coeff_impl p ii)
    (\<lambda>(a, p'). mpzb_assn x a \<and>*
      gmp_poly_slots_assn (slots[i := None]) p')"
  using assms
  unfolding gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_snat_len_generalD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_take_coeff_impl_ptrs_rule[where x=x])
       using assms apply simp
      using assms apply simp
     apply assumption
    apply (clarsimp simp: entails_def)
    subgoal for r p' s
      apply (rule exI[where x=ptrs])
      apply assumption
      done
    done
  done

lemma poly_take_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_take_coeff_impl,
    uncurry (PR_CONST poly_take_coeff_monadic)) \<in>
    [\<lambda>(slots, i). i < length slots \<and> slots ! i \<noteq> None]\<^sub>a
      gmp_poly_slots_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      mpzb_assn \<times>\<^sub>a gmp_poly_slots_assn"
  apply sepref_to_hoare
  unfolding poly_take_coeff_monadic_def
  apply (clarsimp simp: refine_pw_simps split: option.splits)
  subgoal for x i ii slots p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_take_coeff_impl_rule)
       apply assumption
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps prod_assn_def)
    done
  done

definition poly_put_coeff_monadic ::
  "gmp_poly_slots \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly_slots nres" where
"poly_put_coeff_monadic slots i x \<equiv> doN {
  ASSERT (i < length slots);
  ASSERT (slots ! i = None);
  RETURN (slots[i := Some x])
}"

definition [llvm_code, llvm_inline]:
  "poly_put_coeff_impl p i x \<equiv> arl_upd p i x"

lemma poly_put_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length slots"
    and "slots ! i = None"
    and "length ptrs = length slots"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn x ptr)
    (poly_put_coeff_impl p ii ptr)
    (\<lambda>p'. raw_al_assn (ptrs[i := ptr]) p' \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (slots[i := Some x]) (ptrs[i := ptr]))"
  unfolding poly_put_coeff_impl_def
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule frame_rule[
      where F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) slots ptrs \<and>*
        mpzb_assn x ptr"])
    apply (rule arl_upd_rule[where al=ptrs and i=i])
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     SOLVE_AUTO_DEFER_def)
  apply (rule poly_put_coeff_monadic_post_entails[OF assms(1,2)])
  done

lemma poly_put_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length slots"
    and "slots ! i = None"
  shows "llvm_htriple
    (gmp_poly_slots_assn slots p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn x ptr)
    (poly_put_coeff_impl p ii ptr)
    (\<lambda>p'. gmp_poly_slots_assn (slots[i := Some x]) p')"
  using assms
  unfolding gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_snat_coeff_len_generalD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_put_coeff_impl_ptrs_rule)
       using assms apply simp
      using assms apply simp
     apply assumption
    apply (clarsimp simp: entails_def)
    subgoal for r s
      apply (rule exI[where x="ptrs[i := ptr]"])
      apply assumption
      done
    done
  done

lemma poly_put_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_put_coeff_impl,
    uncurry2 (PR_CONST poly_put_coeff_monadic)) \<in>
    [\<lambda>((slots, i), _). i < length slots \<and> slots ! i = None]\<^sub>a
      gmp_poly_slots_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>d \<rightarrow>
      gmp_poly_slots_assn"
  apply sepref_to_hoare
  unfolding poly_put_coeff_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for x ptr i ii slots p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_put_coeff_impl_rule[where x=x])
       apply assumption
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps)
    apply (auto dest!: dsc_pure_part_left_pureD)
    done
  done

definition [llvm_code, llvm_inline]:
  "poly_set_coeff_impl p i x \<equiv> doM {
    p \<leftarrow> poly_free_slot_impl p i;
    poly_put_coeff_impl p i x
  }"

lemma poly_set_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn x ptr)
    (poly_set_coeff_impl p ii ptr)
    (\<lambda>p'. gmp_poly_assn (xs[i := x]) p')"
  using assms
  unfolding poly_set_coeff_impl_def gmp_poly_assn_def
  apply (subst gmp_poly_slots_set_coeff_eq[OF assms, symmetric])
  apply (rule htriple_pure_preI)
  apply (frule pure_part_split_conj)
  apply (clarsimp dest!: dsc_snat_mpzb_pure_relD)
  apply (rule dsc_htriple_bindI[
    where Q="\<lambda>p'. gmp_poly_slots_assn ((map Some xs)[i := None]) p' \<and>*
      mpzb_assn x ptr"])
   apply (rule htriple_ent_post)
    prefer 2
    apply (rule htriple_ent_pre)
     prefer 2
     apply (rule frame_rule[where F="mpzb_assn x ptr"])
     apply (rule poly_free_slot_impl_rule[
       where x="xs ! i" and slots="map Some xs" and i=i])
      using assms apply simp
     using assms apply simp
    apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c)
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c)
  subgoal for p'
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre[
       where P'="gmp_poly_slots_assn ((map Some xs)[i := None]) p' \<and>*
         \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn x ptr"])
      prefer 2
      apply (rule poly_put_coeff_impl_rule[
        where x=x and slots="(map Some xs)[i := None]" and i=i])
       using assms apply simp
      apply simp
     apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps
      list_update_overwrite)
    done
  done

lemma poly_set_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_set_coeff_impl,
    uncurry2 (PR_CONST poly_set_coeff_monadic)) \<in>
    [\<lambda>((xs, i), _). i < length xs]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>d \<rightarrow>
      gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_set_coeff_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for x ptr i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_set_coeff_impl_rule[where x=x])
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps)
    apply (auto dest!: dsc_pure_part_left_pureD)
    done
  done

definition poly_add_coeff_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly nres" where
"poly_add_coeff_monadic xs i j \<equiv> doN {
  ASSERT (i < length xs);
  ASSERT (j < length xs);
  ASSERT (i \<noteq> j);
  RETURN (xs[i := xs ! i + xs ! j])
}"

sepref_register "PR_CONST poly_add_coeff_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly nres"

definition [llvm_code, llvm_inline]:
  "poly_add_coeff_impl p i j \<equiv> doM {
    target \<leftarrow> arl_nth p i;
    source \<leftarrow> arl_nth p j;
    mpzb_add_impl target source;
    Mreturn p
  }"

lemma poly_add_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw
    and ii jj :: "gmp_poly_len word"
  assumes "i < length ptrs"
    and "j < length ptrs"
    and "i \<noteq> j"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      \<upharpoonleft>snat.assn j jj \<and>* mpzb_assn xi (ptrs ! i) \<and>*
      mpzb_assn xj (ptrs ! j) \<and>* F)
    (poly_add_coeff_impl p ii jj)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      \<upharpoonleft>snat.assn j jj \<and>* mpzb_assn (xi + xj) (ptrs ! i) \<and>*
      mpzb_assn xj (ptrs ! j) \<and>* F)"
  using assms
  unfolding poly_add_coeff_impl_def
  supply [vcg_rules] =
    dsc_arl_nth_rule_bounded[OF assms(1)]
    dsc_arl_nth_rule_bounded[OF assms(2)]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_ac)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

lemma poly_add_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw
    and ii jj :: "gmp_poly_len word"
  assumes "i < length xs"
    and "j < length xs"
    and "i \<noteq> j"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* \<upharpoonleft>snat.assn j jj)
    (poly_add_coeff_impl p ii jj)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (xs[i := xs ! i + xs ! j])) ptrs)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_add_coeff_impl_focused_rule[
      where ptrs=ptrs and i=i and j=j
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (((map Some xs)[i := None])[j := None]) ptrs"
        and xi="xs ! i" and xj="xs ! j"])
      using assms apply simp_all
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_two_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps
    gmp_poly_slots_focus_two_coeff_update
    pred_lift_extract_simps pure_def snat.assn_is_rel snat_rel_def)
  done

lemma poly_add_coeff_impl_rule:
  fixes p :: gmp_poly_raw
    and ii jj :: "gmp_poly_len word"
  assumes "i < length xs"
    and "j < length xs"
    and "i \<noteq> j"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      \<upharpoonleft>snat.assn j jj)
    (poly_add_coeff_impl p ii jj)
    (\<lambda>p'. gmp_poly_assn (xs[i := xs ! i + xs ! j]) p')"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_two_snat_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_add_coeff_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def)
    subgoal for p' s
      apply (rule exI[where x=ptrs])
      apply assumption
      done
    done
  done

lemma poly_add_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_add_coeff_impl,
    uncurry2 (PR_CONST poly_add_coeff_monadic)) \<in>
    [\<lambda>((xs, i), j). i < length xs \<and> j < length xs \<and> i \<noteq> j]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_add_coeff_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for i ii j ji xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_add_coeff_impl_rule[where i=j and j=i])
        apply assumption
       apply assumption
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps)
    done
  done

definition poly_addmul_coeff_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly nres" where
"poly_addmul_coeff_monadic xs i c j \<equiv> doN {
  ASSERT (i < length xs);
  ASSERT (j < length xs);
  ASSERT (i \<noteq> j);
  RETURN (xs[i := xs ! i + c * xs ! j])
}"

sepref_register "PR_CONST poly_addmul_coeff_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly nres"

definition [llvm_code, llvm_inline]:
  "poly_addmul_coeff_impl p i c j \<equiv> doM {
    target \<leftarrow> arl_nth p i;
    source \<leftarrow> arl_nth p j;
    mpzb_addmul_impl target c source;
    Mreturn p
  }"

lemma poly_addmul_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw
    and ii jj :: "gmp_poly_len word"
  assumes "i < length ptrs"
    and "j < length ptrs"
    and "i \<noteq> j"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn c ci \<and>* \<upharpoonleft>snat.assn j jj \<and>*
      mpzb_assn xi (ptrs ! i) \<and>* mpzb_assn xj (ptrs ! j) \<and>* F)
    (poly_addmul_coeff_impl p ii ci jj)
    (\<lambda>p'. F \<and>* raw_al_assn ptrs p' \<and>*
      mpzb_assn xj (ptrs ! j) \<and>* mpzb_assn c ci \<and>*
      mpzb_assn (xi + c * xj) (ptrs ! i))"
  using assms
  unfolding poly_addmul_coeff_impl_def
  supply [vcg_rules] =
    dsc_arl_nth_rule_bounded[OF assms(1)]
    dsc_arl_nth_rule_bounded[OF assms(2)]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

lemma poly_addmul_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw
    and ii jj :: "gmp_poly_len word"
  assumes "i < length xs"
    and "j < length xs"
    and "i \<noteq> j"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn c ci \<and>*
      \<upharpoonleft>snat.assn j jj)
    (poly_addmul_coeff_impl p ii ci jj)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (xs[i := xs ! i + c * xs ! j])) ptrs \<and>*
      mpzb_assn c ci)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_addmul_coeff_impl_focused_rule[
      where ptrs=ptrs and i=i and j=j
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          (((map Some xs)[i := None])[j := None]) ptrs"
        and xi="xs ! i" and xj="xs ! j" and c=c])
      using assms apply simp_all
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_two_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
    gmp_poly_slots_focus_two_coeff_update
    pred_lift_extract_simps pure_def snat.assn_is_rel snat_rel_def)
  done

lemma poly_addmul_coeff_impl_rule:
  fixes p :: gmp_poly_raw
    and ii jj :: "gmp_poly_len word"
  assumes "i < length xs"
    and "j < length xs"
    and "i \<noteq> j"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn c ci \<and>* \<upharpoonleft>snat.assn j jj)
    (poly_addmul_coeff_impl p ii ci jj)
    (\<lambda>p'. gmp_poly_assn (xs[i := xs ! i + c * xs ! j]) p' \<and>*
      mpzb_assn c ci)"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_snat_coeff_snat_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_addmul_coeff_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def sep_algebra_simps)
    subgoal for p' s
      apply (rule exI[where x=ptrs])
      apply (simp add: sep_algebra_simps)
      done
    done
  done

lemma poly_addmul_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_addmul_coeff_impl,
    uncurry3 (PR_CONST poly_addmul_coeff_monadic)) \<in>
    [\<lambda>(((xs, i), _), j).
      i < length xs \<and> j < length xs \<and> i \<noteq> j]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_addmul_coeff_monadic_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for j ji c ci i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_addmul_coeff_impl_rule[
        where i=i and j=j and c=c])
        apply assumption
       apply assumption
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (frule dsc_pure_part_pure_assn_pureD)
    apply (elim conjE)
    apply (simp add: conj_entails_mono gmp_poly_assn_return_entails
        pure_true_conv sep_conj_aci(1))
  done
done


sepref_register "PR_CONST poly_set_coeff_monadic"
sepref_register "PR_CONST poly_take_coeff_monadic"
sepref_register "PR_CONST poly_put_coeff_monadic"

section \<open>Base-2 bit length: \<open>mpz_sizeinbase(\<cdot>, 2)\<close>\<close>

text \<open>Bit-length of a borrowed mpz: the number of base-2 digits, with a witnessable abstract
  specification of GMP's \<open>__gmpz_sizeinbase(op, 2)\<close>: the lower bound \<open>2^(r-1) \<le> \<bar>op\<bar>\<close>, the zero
  case and \<open>1 \<le> r\<close> unconditionally, and the upper bound \<open>\<bar>op\<bar> < 2^r\<close> guarded by
  \<open>size_t\<close>-representability of the bit length (\<open>\<bar>op\<bar> < 2 ^ (max_unat 64 - 1)\<close>), inherited from
  the specification rule @{thm [source] raw_mpz_sizeinbase2_rl} in \<open>GMP_Bindings\<close>. The HNR is
  proved by \<open>sepref_to_hoare\<close> and \<open>vcg'\<close> over that rule. The base is fixed at 2 and the mpz is
  borrowed. Extra headroom a caller's arithmetic needs on the result (e.g. computing \<open>r+1\<close>) is
  stated as an explicit hypothesis of that caller's correctness lemma rather than put into this
  specification.\<close>

definition mpz_bitlen2_monadic :: "int \<Rightarrow> nat nres" where
"mpz_bitlen2_monadic m \<equiv>
   SPEC (\<lambda>r. 1 \<le> r
             \<and> (m \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>m\<bar>)
             \<and> (m = 0 \<longrightarrow> r = 1)
             \<and> (\<bar>m\<bar> < 2 ^ (max_unat gmp_size_len - 1) \<longrightarrow> \<bar>m\<bar> < 2 ^ r))"

sepref_register "PR_CONST mpz_bitlen2_monadic" :: "int \<Rightarrow> nat nres"

definition [llvm_code, llvm_inline]: "mpz_bitlen2_impl m \<equiv> doM {
  mpzb_sizeinbase m (2::gmp_int_t)
}"

lemma mpz_bitlen2_impl_hnr[sepref_fr_rules]:
  "(mpz_bitlen2_impl, PR_CONST mpz_bitlen2_monadic) \<in>
    mpzb_assn\<^sup>k \<rightarrow>\<^sub>a gmp_size_assn"
  apply sepref_to_hoare
  unfolding mpz_bitlen2_monadic_def mpz_bitlen2_impl_def
    mpzb_sizeinbase_def PR_CONST_def
  supply [simp] = pure_def refine_pw_simps sint_rel_def sint.rel_def br_def
  supply [vcg_rules del] = raw_mpz_sizeinbase_rl
  supply [vcg_rules] = raw_mpz_sizeinbase2_rl
  apply vcg'
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)
  apply blast
  apply (fact Defer_Slot.remove_slot)
  done

text \<open>\<open>\<le> SPEC\<close> projections of the bit-length facts, for @{method refine_vcg}. The lower bound and
  zero case are unconditional; the upper bound is available under the \<open>size_t\<close>-representability
  guard on the input magnitude. Callers that need the upper bound have a stronger magnitude
  hypothesis, which implies the guard via \<open>bitlen2_snat_guard\<close> (below).\<close>
lemma bitlen2_snat_guard:
  fixes m :: int
  shows "\<bar>m\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)
     \<Longrightarrow> \<bar>m\<bar> < 2 ^ (max_unat gmp_size_len - 1)"
proof -
  assume a: "\<bar>m\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)"
  have "(max_snat LENGTH(gmp_poly_len) - 1) \<le> (max_unat gmp_size_len - 1)"
    by (simp add: max_snat_def max_unat_def)
  hence "(2::int) ^ (max_snat LENGTH(gmp_poly_len) - 1)
           \<le> 2 ^ (max_unat gmp_size_len - 1)"
    by (rule power_increasing) simp
  thus ?thesis using a by linarith
qed

lemma mpz_bitlen2_monadic_pow2_bound:
  assumes "\<bar>m\<bar> < 2 ^ (max_unat gmp_size_len - 1)"
  shows "mpz_bitlen2_monadic m
     \<le> SPEC (\<lambda>r. \<bar>m\<bar> < 2 ^ r)"
  using assms by (auto simp: mpz_bitlen2_monadic_def pw_le_iff refine_pw_simps)

lemma mpz_bitlen2_monadic_lower:
  "mpz_bitlen2_monadic m
     \<le> SPEC (\<lambda>r. m \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>m\<bar>)"
  by (auto simp: mpz_bitlen2_monadic_def pw_le_iff refine_pw_simps)

text \<open>\<^bold>\<open>The machine-word (SIGNED) bound is CONDITIONAL, by design\<close> (see the trust-boundary note
  on @{thm [source] raw_mpz_sizeinbase2_rl}). \<open>r < max_snat 64\<close> is NOT a GMP-contract fact --
  the abstract bit-length is unbounded -- so it is provided ONLY under the EXPLICIT practical
  hypothesis that the input magnitude fits a signed word's worth of bits
  (\<open>\<bar>m\<bar> < 2 ^ (max_snat 64 - 1)\<close>). A caller that needs \<open>r < max_snat\<close> (e.g. to
  \<open>op_unat_snat_conv\<close> the result) must discharge this hypothesis about ITS input, making the
  assumption visible in that caller's correctness lemma rather than hidden in the trusted axiom.
  Derivation: for \<open>m \<noteq> 0\<close>, \<open>2^(r-1) \<le> \<bar>m\<bar> < 2^(max_snat-1)\<close> gives \<open>r - 1 < max_snat - 1\<close>;
  for \<open>m = 0\<close>, \<open>r = 1\<close>.\<close>
lemma mpz_bitlen2_monadic_snat_bound:
  assumes "\<bar>m\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)"
  shows "mpz_bitlen2_monadic m
     \<le> SPEC (\<lambda>r. r < max_snat LENGTH(gmp_poly_len))"
proof -
  have ms: "Suc 0 < max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
  have "\<And>r::nat. (m \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>m\<bar>)
          \<Longrightarrow> (m = 0 \<longrightarrow> r = 1) \<Longrightarrow> r < max_snat LENGTH(gmp_poly_len)"
  proof -
    fix r :: nat
    assume lbc: "m \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>m\<bar>" and zc: "m = 0 \<longrightarrow> r = 1"
    show "r < max_snat LENGTH(gmp_poly_len)"
    proof (cases "m = 0")
      case True thus ?thesis using zc ms by simp
    next
      case False
      hence "(2::int) ^ (r - 1) \<le> \<bar>m\<bar>" using lbc by simp
      hence B: "(2::int) ^ (r - 1) < 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)"
        using assms by linarith
      have "r - 1 < max_snat LENGTH(gmp_poly_len) - 1"
        by (rule power_less_imp_less_exp[OF _ B]) simp
      thus ?thesis using ms by linarith
    qed
  qed
  thus ?thesis
    by (auto simp: mpz_bitlen2_monadic_def pw_le_iff refine_pw_simps)
qed

text \<open>Borrow-read a coefficient's bit-length, the sibling of @{const poly_coeff_sgn_monadic}
  (above): \<open>bitlen |xs!i|\<close> without a per-coefficient copy. @{const mpz_bitlen2_monadic}'s
  specification is stated on \<open>|m|\<close>, so no absolute value or copy is needed.\<close>
definition poly_coeff_bitlen2_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat nres" where
"poly_coeff_bitlen2_monadic xs i \<equiv> doN {
  ASSERT (i < length xs);
  (PR_CONST mpz_bitlen2_monadic) (xs ! i)
}"

sepref_register "PR_CONST poly_coeff_bitlen2_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat nres"

definition [llvm_code, llvm_inline]: "poly_coeff_bitlen2_impl p i \<equiv> doM {
  a \<leftarrow> arl_nth p i;
  mpz_bitlen2_impl a
}"

lemma poly_coeff_bitlen2_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn x (ptrs ! i) \<and>* F)
    (poly_coeff_bitlen2_impl p ii)
    (\<lambda>ri. raw_al_assn ptrs p \<and>* (mpzb_assn x (ptrs ! i) \<and>* F) \<and>*
      (EXS r. gmp_size_assn r ri \<and>* \<up>(1 \<le> r
              \<and> (x \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>x\<bar>) \<and> (x = 0 \<longrightarrow> r = 1)
              \<and> (\<bar>x\<bar> < 2 ^ (max_unat gmp_size_len - 1) \<longrightarrow> \<bar>x\<bar> < 2 ^ r))))"
  using assms
  unfolding poly_coeff_bitlen2_impl_def mpz_bitlen2_impl_def mpzb_sizeinbase_def
  supply [simp] = pure_def refine_pw_simps sint_rel_def sint.rel_def br_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  supply [vcg_rules del] = raw_mpz_sizeinbase_rl
  supply [vcg_rules] = raw_mpz_sizeinbase2_rl
  apply vcg'
   apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
     pred_lift_extract_simps sep_conj_c)
   apply blast
  apply (rule Defer_Slot.remove_slot)
  done

lemma poly_coeff_bitlen2_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs" and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii)
    (poly_coeff_bitlen2_impl p ii)
    (\<lambda>ri. raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      (EXS r. gmp_size_assn r ri \<and>* \<up>(1 \<le> r
              \<and> (xs ! i \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>xs ! i\<bar>) \<and> (xs ! i = 0 \<longrightarrow> r = 1)
              \<and> (\<bar>xs ! i\<bar> < 2 ^ (max_unat gmp_size_len - 1) \<longrightarrow> \<bar>xs ! i\<bar> < 2 ^ r))))"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_coeff_bitlen2_impl_focused_rule[
      where ptrs=ptrs and i=i
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        ((map Some xs)[i := None]) ptrs"
        and x="xs ! i"])
    using assms apply simp
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps
    gmp_poly_slots_unfocus_coeff)
  done

lemma poly_coeff_bitlen2_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii)
    (poly_coeff_bitlen2_impl p ii)
    (\<lambda>ri. gmp_poly_assn xs p \<and>*
      (EXS r. gmp_size_assn r ri \<and>* \<up>(1 \<le> r
              \<and> (xs ! i \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>xs ! i\<bar>) \<and> (xs ! i = 0 \<longrightarrow> r = 1)
              \<and> (\<bar>xs ! i\<bar> < 2 ^ (max_unat gmp_size_len - 1) \<longrightarrow> \<bar>xs ! i\<bar> < 2 ^ r))))"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_snat_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_coeff_bitlen2_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def sep_conj_exists)
    subgoal for r s xa
      apply (rule exI[where x=ptrs])
      apply (rule exI[where x=xa])
      apply (clarsimp simp: sep_algebra_simps pred_lift_extract_simps)
      done
    done
  done

lemma poly_coeff_bitlen2_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_coeff_bitlen2_impl, uncurry (PR_CONST poly_coeff_bitlen2_monadic))
  \<in> [\<lambda>(xs, i). i < length xs]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_size_assn"
  apply sepref_to_hoare
  unfolding poly_coeff_bitlen2_monadic_def mpz_bitlen2_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_coeff_bitlen2_impl_rule)
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps
      pred_lift_extract_simps pure_def)
    done
  done

end
