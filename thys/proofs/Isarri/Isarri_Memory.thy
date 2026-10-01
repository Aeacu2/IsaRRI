theory Isarri_Memory
  imports "IsaRRI.Public_Export"
begin

text \<open>\<^bold>\<open>Memory layer: an \<open>llvm_htriple\<close> for the exported C entry \<open>isarri\<close> itself\<close>
  (\<open>isarri_wrapper\<close>, \<open>Public_Export\<close>), composing the three solver HNRs with the hand-written
  \<open>[llvm_code]\<close> output-copy loops, the flag writes and the frees.

  The theorem is generic in each path's \<open>\<le> SPEC\<close> postcondition (\<open>\<Phi>A\<close>, \<open>\<Phi>B\<close>, \<open>\<Phi>C\<close>): this theory
  sees only the implementation layer, and \<open>Isarri_Correct\<close> instantiates the three postconditions
  from the isolation theorems of the three paths.

  \<^bold>\<open>What the memory model assumes of the caller\<close> (preconditions of the theorem, not runtime
  checks):
  \<^item> the coefficient buffer is the Isabelle-LLVM array-list \<open>(len, len, coeff_ptrs)\<close>, i.e. a block
    of exactly \<open>len\<close> pointers carrying the allocator's size tag (\<open>narray_assn\<close>), each pointing to
    its own allocated GMP value (\<open>mpzb_assn\<close>). The code never frees it; the tag is a modelling
    artefact of reusing \<open>gmp_poly_assn\<close>;
  \<^item> each output mpz array holds \<open>out_cap\<close> pointers to initialised, pairwise distinct \<open>mpz_t\<close> values
    (\<open>out_mpz_arr_assn\<close>, no allocator tag), each exponent array \<open>out_cap\<close> words, and every output
    cell is disjoint from every other and from the input (separating conjunction);
  \<^item> \<open>len\<close>, \<open>out_cap\<close>, \<open>nfloor\<close>, \<open>hcap\<close>, \<open>dlt\<close> are non-negative as signed 64-bit words.\<close>

text \<open>Caller-owned output storage. No malloc tag: the routine never frees these.\<close>

definition out_mpz_arr_assn :: "int list \<Rightarrow> mpz_t list \<Rightarrow> mpz_t ptr \<Rightarrow> assn" where
  "out_mpz_arr_assn vs ps p \<equiv>
     \<up>(length ps = length vs) \<and>*
     \<upharpoonleft>(ll_range {0..<int (length vs)}) (\<lambda>j. ps ! nat j) p \<and>*
     (\<Union>*j\<in>{0..<length vs}. mpz_assn (vs ! j) (ps ! j))"

definition out_word_arr_assn :: "'a::len word list \<Rightarrow> 'a word ptr \<Rightarrow> assn" where
  "out_word_arr_assn ws p \<equiv> \<upharpoonleft>(ll_range {0..<int (length ws)}) (\<lambda>j. ws ! nat j) p"

definition store_upd :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "store_upd n src dst = take n src @ drop n dst"

context
begin
interpretation llvm_prim_mem_setup .

lemma out_mpz_arr_ofs_rule:
  "llvm_htriple (out_mpz_arr_assn vs ps p \<and>* \<upharpoonleft>snat.assn n ni \<and>* \<up>\<^sub>d(n < length vs))
     (ll_ofs_ptr p ni)
     (\<lambda>r. \<up>(r = p +\<^sub>a int n) \<and>* out_mpz_arr_assn vs ps p \<and>* \<upharpoonleft>snat.assn n ni)"
  unfolding out_mpz_arr_assn_def snat.assn_def
  supply [simp] = cnv_snat_to_uint and [simp del] = nat_uint_eq
  by vcg

lemma out_mpz_arr_load_rule:
  "llvm_htriple (out_mpz_arr_assn vs ps p \<and>* \<up>\<^sub>d(n < length vs))
     (ll_load (p +\<^sub>a int n))
     (\<lambda>r. \<up>(r = ps ! n) \<and>* out_mpz_arr_assn vs ps p)"
  unfolding out_mpz_arr_assn_def
  by vcg

lemma out_mpz_arr_focus:
  assumes "n < length vs"
  shows "(\<Union>*j\<in>{0..<length vs}. mpz_assn (vs ! j) (ps ! j))
    = (mpz_assn (vs ! n) (ps ! n) \<and>* (\<Union>*j\<in>{0..<length vs} - {n}. mpz_assn (vs ! j) (ps ! j)))"
  using assms by (subst sep_set_img_remove[of n]) auto

lemma out_mpz_arr_unfocus:
  assumes "n < length vs"
  shows "(mpz_assn a (ps ! n) \<and>* (\<Union>*j\<in>{0..<length vs} - {n}. mpz_assn (vs ! j) (ps ! j)))
    = (\<Union>*j\<in>{0..<length vs}. mpz_assn (vs[n := a] ! j) (ps ! j))"
proof -
  have "(\<Union>*j\<in>{0..<length vs} - {n}. mpz_assn (vs ! j) (ps ! j))
      = (\<Union>*j\<in>{0..<length vs} - {n}. mpz_assn (vs[n := a] ! j) (ps ! j))"
    by (rule sep_set_img_cong) auto
  thus ?thesis using assms
    by (subst sep_set_img_remove[of n]) auto
qed

abbreviation src_slots_assn :: "int list \<Rightarrow> mpz_t list \<Rightarrow> assn" where
  "src_slots_assn L pl \<equiv> \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some L) pl"

lemma out_mpz_arr_set_rule:
  "llvm_htriple
     (out_mpz_arr_assn vs ps p \<and>* src_slots_assn L pl \<and>* \<up>\<^sub>d(n < length vs \<and> n < length L))
     (raw_mpz_set (ps ! n) (pl ! n))
     (\<lambda>_. out_mpz_arr_assn (vs[n := L ! n]) ps p \<and>* src_slots_assn L pl)"
proof (cases "n < length vs \<and> n < length L")
  case True
  note [vcg_rules] = mpz_set.vcg_rule[THEN conjunct2, rule_format]
  define Rest where "Rest = (\<Union>*j\<in>{0..<length vs} - {n}. mpz_assn (vs ! j) (ps ! j))"
  define SRest where "SRest = \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) ((map Some L)[n := None]) pl"
  have e1: "(\<Union>*j\<in>{0..<length vs}. mpz_assn (vs ! j) (ps ! j)) = (mpz_assn (vs ! n) (ps ! n) \<and>* Rest)"
    unfolding Rest_def using True by (rule_tac out_mpz_arr_focus) simp
  have e2: "(\<Union>*j\<in>{0..<length vs}. mpz_assn (vs[n := L ! n] ! j) (ps ! j)) = (mpz_assn (L ! n) (ps ! n) \<and>* Rest)"
    unfolding Rest_def using True by (rule_tac out_mpz_arr_unfocus[symmetric]) simp
  have e3: "src_slots_assn L pl = (mpz_assn (L ! n) (pl ! n) \<and>* mpzbr_assn (pl ! n) \<and>* SRest)"
    unfolding SRest_def using True
    by (subst gmp_poly_slots_focus_coeff[where i=n and xs=L and ptrs=pl]) (simp_all add: mpzb_assn_open)
  show ?thesis
    unfolding out_mpz_arr_assn_def length_list_update e1 e2 e3
    by vcg
next
  case False
  then show ?thesis
    by (rule_tac htriple_pure_preI) (auto dest!: pure_part_split_conj simp: dr_assn_pure_asm_prefix_def)
qed

lemma out_word_arr_ofs_rule:
  "llvm_htriple (out_word_arr_assn ws p \<and>* \<upharpoonleft>snat.assn n ni \<and>* \<up>\<^sub>d(n < length ws))
     (ll_ofs_ptr p ni)
     (\<lambda>r. \<up>(r = p +\<^sub>a int n) \<and>* out_word_arr_assn ws p \<and>* \<upharpoonleft>snat.assn n ni)"
  unfolding out_word_arr_assn_def snat.assn_def
  supply [simp] = cnv_snat_to_uint and [simp del] = nat_uint_eq
  by vcg

lemma out_word_arr_store_rule:
  "llvm_htriple (out_word_arr_assn ws p \<and>* \<up>\<^sub>d(n < length ws))
     (ll_store x (p +\<^sub>a int n))
     (\<lambda>_. out_word_arr_assn (ws[n := x]) p)"
proof -
  have E: "n < length ws \<Longrightarrow>
      \<upharpoonleft>(ll_range {0..<int (length ws)}) ((\<lambda>j. ws ! nat j)(int n := x)) p
      = \<upharpoonleft>(ll_range {0..<int (length ws)}) (\<lambda>j. ws[n := x] ! nat j) p"
    by (rule ll_range_cong) (auto simp: nth_list_update)
  show ?thesis
    unfolding out_word_arr_assn_def
    apply vcg
    apply (clarsimp simp: ENTAILS_def entails_def)
    apply (frule ll_range_base[OF pure_partI])
    apply (simp add: E)
    done
qed

lemma store_upd_len[simp]: "n \<le> length src \<Longrightarrow> n \<le> length dst \<Longrightarrow> length (store_upd n src dst) = length dst"
  unfolding store_upd_def by simp

lemma store_upd_step:
  "n < length src \<Longrightarrow> n < length dst \<Longrightarrow> (store_upd n src dst)[n := src ! n] = store_upd (Suc n) src dst"
  unfolding store_upd_def
  by (simp add: list_update_append take_Suc_conv_app_nth Cons_nth_drop_Suc[symmetric])

lemma store_upd_0[simp]: "store_upd 0 src dst = dst"
  unfolding store_upd_def by simp

lemma store_interval_vec_keep_raw_rule:
  fixes lnsi rnsi :: gmp_poly_raw and ksi :: "(64 word, 64) array_list"
  assumes lens: "length pl = length L" "length R = length L" "length pr = length R" "length Kw = length L"
    and caps: "length VL = cap" "length VR = cap" "length KW = cap"
  shows "llvm_htriple
    (\<upharpoonleft>ll_pto c0 cnt \<and>* \<upharpoonleft>arl_assn pl lnsi \<and>* src_slots_assn L pl \<and>*
     \<upharpoonleft>arl_assn pr rnsi \<and>* src_slots_assn R pr \<and>* \<upharpoonleft>arl_assn Kw ksi \<and>*
     out_mpz_arr_assn VL PL lna \<and>* out_mpz_arr_assn VR PR rnb \<and>* out_word_arr_assn KW kp \<and>*
     \<upharpoonleft>snat.assn cap capi)
    (store_interval_vec_keep cnt lna rnb kp capi (lnsi, rnsi, ksi))
    (\<lambda>_. EXS cw. \<upharpoonleft>ll_pto cw cnt \<and>* \<upharpoonleft>snat.assn (length L) cw \<and>*
     \<upharpoonleft>arl_assn pl lnsi \<and>* src_slots_assn L pl \<and>*
     \<upharpoonleft>arl_assn pr rnsi \<and>* src_slots_assn R pr \<and>* \<upharpoonleft>arl_assn Kw ksi \<and>*
     out_mpz_arr_assn (store_upd (min (length L) cap) L VL) PL lna \<and>*
     out_mpz_arr_assn (store_upd (min (length L) cap) R VR) PR rnb \<and>*
     out_word_arr_assn (store_upd (min (length L) cap) Kw KW) kp \<and>*
     \<upharpoonleft>snat.assn cap capi)"
  unfolding store_interval_vec_keep_def
  apply (rewrite annotate_llc_while[where
    I="\<lambda>i t. EXS n. \<upharpoonleft>snat.assn n i \<and>* \<up>\<^sub>d(n \<le> min (length L) cap) \<and>*
        \<up>\<^sub>!(t = min (length L) cap - n) \<and>*
        out_mpz_arr_assn (store_upd n L VL) PL lna \<and>*
        out_mpz_arr_assn (store_upd n R VR) PR rnb \<and>*
        out_word_arr_assn (store_upd n Kw KW) kp"
    and R="measure id"])
  supply [vcg_rules] = out_mpz_arr_ofs_rule out_mpz_arr_load_rule out_mpz_arr_set_rule
    out_word_arr_ofs_rule out_word_arr_store_rule
  apply vcg_monadify
  supply [simp] = store_upd_step lens caps
  apply vcg'
  done

definition out_half_pre ::
  "nat \<Rightarrow> 64 word ptr \<Rightarrow> mpz_t ptr \<Rightarrow> mpz_t list \<Rightarrow> mpz_t ptr \<Rightarrow> mpz_t list \<Rightarrow> 64 word ptr \<Rightarrow> assn" where
  "out_half_pre cap cnt lna PL rnb PR kp \<equiv> EXS (c0::64 word) VL VR (KW::64 word list).
     \<upharpoonleft>ll_pto c0 cnt \<and>* out_mpz_arr_assn VL PL lna \<and>* out_mpz_arr_assn VR PR rnb \<and>*
     out_word_arr_assn KW kp \<and>* \<up>(length VL = cap \<and> length VR = cap \<and> length KW = cap)"

definition out_half_post ::
  "nat \<Rightarrow> ((int \<times> int) \<times> nat) list \<Rightarrow> 64 word ptr \<Rightarrow> mpz_t ptr \<Rightarrow> mpz_t list \<Rightarrow> mpz_t ptr \<Rightarrow> mpz_t list
     \<Rightarrow> 64 word ptr \<Rightarrow> assn" where
  "out_half_post cap trs cnt lna PL rnb PR kp \<equiv> EXS (cw::64 word) VL VR (KW::64 word list).
     \<upharpoonleft>ll_pto cw cnt \<and>* out_mpz_arr_assn VL PL lna \<and>* out_mpz_arr_assn VR PR rnb \<and>*
     out_word_arr_assn KW kp \<and>*
     \<up>(unat cw = length trs \<and> length VL = cap \<and> length VR = cap \<and> length KW = cap \<and>
        (\<forall>j < min (length trs) cap. trs ! j = ((VL ! j, VR ! j), unat (KW ! j))))"

lemma htriple_raw_conj_preI:
  assumes "P \<Longrightarrow> llvm_htriple Q c R"
  shows "llvm_htriple (\<lambda>s. P \<and> Q s) c R"
proof (rule htripleI)
  fix st asf
  assume S: "STATE asf (\<lambda>s. P \<and> Q s) st"
  then have p: P and SQ: "STATE asf Q st" unfolding STATE_def by auto
  from htripleD[OF assms[OF p] SQ]
  show "wpa asf c (\<lambda>r st'. STATE asf (R r) st') st" .
qed

lemma snat_list_rel_unat:
  assumes "(ws, K) \<in> \<langle>snat_rel\<rangle>list_rel" "j < length K"
  shows "unat (ws ! j) = K ! j"
  using assms
  unfolding list_rel_def snat_rel_def snat.rel_def br_def
  by (clarsimp simp: list_all2_conv_all_nth snat_eq_unat_aux2)

lemma store_upd_nth_take: "j < n \<Longrightarrow> n \<le> length src \<Longrightarrow> store_upd n src dst ! j = src ! j"
  unfolding store_upd_def by (simp add: nth_append)

lemma store_keep_vec_rule:
  assumes inv: "dyadic_interval_vec_invar v"
  shows "llvm_htriple
    (gmp_dyadic_interval_vec_assn v vi \<and>* out_half_pre cap cnt lna PL rnb PR kp \<and>* \<upharpoonleft>snat.assn cap capi)
    (store_interval_vec_keep cnt lna rnb kp capi vi)
    (\<lambda>_. gmp_dyadic_interval_vec_assn v vi \<and>*
         out_half_post cap (dyadic_interval_vec_triples v) cnt lna PL rnb PR kp \<and>* \<upharpoonleft>snat.assn cap capi)"
proof -
  obtain L R K where v: "v = (L, R, K)" by (cases v)
  obtain a b c where vi: "vi = (a, b, c)" by (cases vi)
  show ?thesis
    unfolding v vi out_half_pre_def out_half_post_def gmp_poly_assn_def gmp_poly_slots_assn_def
      al_assn_def hr_comp_def
    apply (simp add: sep_algebra_simps)
    apply (intro dsc_htriple_raw_ex_preI htriple_raw_conj_preI)
    apply (rule htriple_pure_preI)
    subgoal premises p for pl pr Kw c0 VL VR KW
    proof -
      have lpl: "length pl = length L" and lpr: "length pr = length R"
        using p(5) by (auto dest!: pure_part_split_conj gmp_poly_slots_lenD)
      have lK: "length Kw = length K" using p(1) by (simp add: list_rel_imp_same_length)
      have lR: "length R = length L" "length K = length L"
        using inv unfolding v dyadic_interval_vec_invar_def by auto
      have lKw: "length Kw = length L" using lK lR by simp
      note raw = store_interval_vec_keep_raw_rule[OF lpl lR(1) lpr lKw p(2,3,4)]
      show ?thesis
        supply [vcg_rules] = raw
        apply vcg
        subgoal for asf sa cw
        proof -
          assume cap: "\<flat>\<^sub>psnat.assn cap capi" and cwr: "\<flat>\<^sub>psnat.assn (length L) cw"
          let ?m = "min (length L) cap"
          have ucw: "unat cw = length L"
            using dsc_snat_pure_relD[OF cwr] by (simp add: snat_rel_def snat.rel_def br_def snat_eq_unat_aux2)
          have trl: "length (dyadic_interval_vec_triples (L, R, K)) = length L"
            using lR by (simp add: dyadic_interval_vec_triples_def)
          have trn: "j < length L \<Longrightarrow> dyadic_interval_vec_triples (L, R, K) ! j = ((L ! j, R ! j), K ! j)" for j
            using lR by (simp add: dyadic_interval_vec_triples_def)
          have nth: "\<forall>j. j < length L \<and> j < cap \<longrightarrow>
              dyadic_interval_vec_triples (L, R, K) ! j =
              ((store_upd ?m L VL ! j, store_upd ?m R VR ! j), unat (store_upd ?m Kw KW ! j))"
            using lR lKw lpl p(1) by (auto simp: trn store_upd_nth_take snat_list_rel_unat)
          have lens: "length (store_upd ?m L VL) = cap" "length (store_upd ?m R VR) = cap"
              "length (store_upd ?m Kw KW) = cap"
            using p(2,3,4) lR lKw by auto
          show ?thesis
            using p(1) cap ucw trl nth lens
            apply (clarsimp simp: ENTAILS_def entails_def)
            apply (rule exI[where x=pl], rule exI[where x=pr], rule exI[where x=Kw])
            apply (intro conjI, assumption)
            apply (rule exI[where x=cw], intro conjI, simp)
            apply (rule exI[where x="store_upd ?m L VL"], intro conjI, assumption)
            apply (rule exI[where x="store_upd ?m R VR"], intro conjI, assumption)
            apply (rule exI[where x="store_upd ?m Kw KW"], intro conjI, assumption)
            apply simp
            using cap
            apply (simp add: snat.assn_def dr_assn_pure_asm_prefix_def sep_algebra_simps
              pred_lift_extract_simps sep_conj_ac)
            done
        qed
        done
    qed
    done
qed


lemma hnr_spec_htriple:
  assumes H: "hn_refine \<Gamma> c \<Gamma>' R CP m" and S: "m \<le> SPEC \<Phi>"
  shows "llvm_htriple \<Gamma> c (\<lambda>r. \<Gamma>' \<and>* (EXS x. R x r \<and>* \<up>(\<Phi> x)))"
proof -
  have nf: "nofail m" using S by (rule SPEC_nofail)
  show ?thesis
    apply (rule htriple_ent_post[OF _ hn_refineD[OF H nf]])
    using S
    apply (clarsimp simp: entails_def sep_algebra_simps pred_lift_extract_simps)
    subgoal for r s x using order_trans[of "RETURN x" m "SPEC \<Phi>"] by auto
    done
qed

abbreviation "vec_assn \<equiv> gmp_dyadic_interval_vec_assn"

lemma bool1_assn_eq: "bool1_assn = \<upharpoonleft>bool.assn"
  unfolding bool1_rel_def bool.assn_is_rel ..

lemma lowdeg_impl_rule:
  assumes S: "lowdeg_isolate_all_split_main xs \<le> SPEC \<Phi>"
  shows "llvm_htriple (gmp_poly_assn xs xsi) (lowdeg_isolate_all_split_main_impl xsi)
    (\<lambda>(r1, r2, r3). gmp_poly_assn xs xsi \<and>*
       (EXS P Q b. vec_assn P r1 \<and>* vec_assn Q r2 \<and>* \<upharpoonleft>bool.assn b r3 \<and>* \<up>(\<Phi> (P, Q, b))))"
  apply (rule htriple_ent_post[OF _ hnr_spec_htriple[OF
    lowdeg_isolate_all_split_main_impl_hnr[to_hnr, unfolded hn_ctxt_def APP_def PR_CONST_def] S]])
  apply (clarsimp split: prod.splits simp: bool1_assn_eq)
  done

lemma defl_impl_rule:
  assumes S: "defl_isolate_all_split_main xs \<le> SPEC \<Phi>"
  shows "llvm_htriple (gmp_poly_assn xs xsi) (defl_isolate_all_split_main_impl xsi)
    (\<lambda>(r1, r2, r3). gmp_poly_assn xs xsi \<and>*
       (EXS P Q b. vec_assn P r1 \<and>* vec_assn Q r2 \<and>* \<upharpoonleft>bool.assn b r3 \<and>* \<up>(\<Phi> (P, Q, b))))"
  apply (rule htriple_ent_post[OF _ hnr_spec_htriple[OF
    defl_isolate_all_split_main_impl_hnr[to_hnr, unfolded hn_ctxt_def APP_def PR_CONST_def] S]])
  apply (clarsimp split: prod.splits simp: bool1_assn_eq)
  done

lemma snat_assn_eq: "snat_assn = \<upharpoonleft>snat.assn"
  unfolding snat_rel_def snat.assn_is_rel ..

lemma pow_sub_impl_rule:
  assumes S: "pow_sub_entry_monadic nf hc dl xs \<le> SPEC \<Phi>"
    and pre: "0 < length xs" "length xs < max_snat LENGTH(64)"
  shows "llvm_htriple
    (\<upharpoonleft>snat.assn nf nfi \<and>* \<upharpoonleft>snat.assn hc hci \<and>* \<upharpoonleft>snat.assn dl dli \<and>* gmp_poly_assn xs xsi)
    (pow_sub_entry_impl nfi hci dli xsi)
    (\<lambda>(r1, r2, r3). \<upharpoonleft>snat.assn nf nfi \<and>* \<upharpoonleft>snat.assn hc hci \<and>* \<upharpoonleft>snat.assn dl dli \<and>* gmp_poly_assn xs xsi \<and>*
       (EXS V b1 b2. vec_assn V r1 \<and>* \<upharpoonleft>bool.assn b1 r2 \<and>* \<upharpoonleft>bool.assn b2 r3 \<and>* \<up>(\<Phi> (V, b1, b2))))"
proof -
  have H: "hn_refine
      (\<upharpoonleft>snat.assn nf nfi \<and>* \<upharpoonleft>snat.assn hc hci \<and>* \<upharpoonleft>snat.assn dl dli \<and>* gmp_poly_assn xs xsi)
      (pow_sub_entry_impl nfi hci dli xsi)
      (\<upharpoonleft>snat.assn nf nfi \<and>* \<upharpoonleft>snat.assn hc hci \<and>* \<upharpoonleft>snat.assn dl dli \<and>* gmp_poly_assn xs xsi)
      (vec_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn) (\<lambda>_. True) (pow_sub_entry_monadic nf hc dl xs)"
    using hfrefD[OF pow_sub_entry_impl_hnr, of "(((nf, hc), dl), xs)" "(((nfi, hci), dli), xsi)"] pre
    by (simp add: hn_ctxt_def snat_assn_eq sep_conj_ac)
  show ?thesis
    apply (rule htriple_ent_post[OF _ hnr_spec_htriple[OF H S]])
    apply (clarsimp split: prod.splits simp: bool1_assn_eq)
    done
qed

lemma vec_free_rule: "llvm_htriple (vec_assn v vi) (dyadic_interval_vec_free_impl vi) (\<lambda>_. \<box>)"
proof -
  have S: "dyadic_interval_vec_free_monadic v \<le> SPEC (\<lambda>_. True)"
    by (cases v) (simp add: dyadic_interval_vec_free_monadic_def poly_free_monadic_def mop_free_def)
  show ?thesis
    apply (rule htriple_ent_post[OF _ hnr_spec_htriple[OF
      dyadic_interval_vec_free_impl_hnr[to_hnr, unfolded hn_ctxt_def APP_def PR_CONST_def] S]])
    apply (auto simp: entails_def sep_algebra_simps invalid_assn_def pure_def)
    done
qed

lemma hybrid_store_eq:
  "hybrid_store_interval_vec a b c d e acc =
     doM { store_interval_vec_keep a b c d e acc; dyadic_interval_vec_free_impl acc }"
  unfolding hybrid_store_interval_vec_def store_interval_vec_keep_def
  by (cases acc) simp

lemma store_vec_rule:
  assumes inv: "dyadic_interval_vec_invar v"
  shows "llvm_htriple
    (vec_assn v vi \<and>* out_half_pre cap cnt lna PL rnb PR kp \<and>* \<upharpoonleft>snat.assn cap capi)
    (hybrid_store_interval_vec cnt lna rnb kp capi vi)
    (\<lambda>_. out_half_post cap (dyadic_interval_vec_triples v) cnt lna PL rnb PR kp \<and>* \<upharpoonleft>snat.assn cap capi)"
  unfolding hybrid_store_eq
  supply [vcg_rules] = store_keep_vec_rule[OF inv] vec_free_rule
  by vcg

lemma store_vec_rule':
  "llvm_htriple
    (vec_assn v vi \<and>* out_half_pre cap cnt lna PL rnb PR kp \<and>* \<upharpoonleft>snat.assn cap capi \<and>*
     \<up>\<^sub>d(dyadic_interval_vec_invar v))
    (hybrid_store_interval_vec cnt lna rnb kp capi vi)
    (\<lambda>_. out_half_post cap (dyadic_interval_vec_triples v) cnt lna PL rnb PR kp \<and>* \<upharpoonleft>snat.assn cap capi)"
  by (cases "dyadic_interval_vec_invar v")
     (auto intro: store_vec_rule simp: SOLVE_AUTO_DEFER_def sep_algebra_simps)

lemma store_keep_vec_rule':
  "llvm_htriple
    (vec_assn v vi \<and>* out_half_pre cap cnt lna PL rnb PR kp \<and>* \<upharpoonleft>snat.assn cap capi \<and>*
     \<up>\<^sub>d(dyadic_interval_vec_invar v))
    (store_interval_vec_keep cnt lna rnb kp capi vi)
    (\<lambda>_. vec_assn v vi \<and>*
         out_half_post cap (dyadic_interval_vec_triples v) cnt lna PL rnb PR kp \<and>* \<upharpoonleft>snat.assn cap capi)"
  by (cases "dyadic_interval_vec_invar v")
     (auto intro: store_keep_vec_rule simp: SOLVE_AUTO_DEFER_def sep_algebra_simps)

lemma store_vec_rule_split:
  "llvm_htriple
    (gmp_poly_assn L a \<and>* gmp_poly_assn R b \<and>* al_assn snat_assn K c \<and>*
     out_half_pre cap cnt lna PL rnb PR kp \<and>* \<upharpoonleft>snat.assn cap capi \<and>*
     \<up>\<^sub>d(dyadic_interval_vec_invar (L, R, K)))
    (hybrid_store_interval_vec cnt lna rnb kp capi (a, b, c))
    (\<lambda>_. out_half_post cap (dyadic_interval_vec_triples (L, R, K)) cnt lna PL rnb PR kp \<and>*
         \<upharpoonleft>snat.assn cap capi)"
  using store_vec_rule'[of "(L, R, K)" "(a, b, c)"] by (simp add: sep_conj_ac)

lemma store_keep_vec_rule_split:
  fixes c :: "(64 word, 64) array_list"
  shows "llvm_htriple
    (gmp_poly_assn L a \<and>* gmp_poly_assn R b \<and>* al_assn snat_assn K c \<and>*
     out_half_pre cap cnt lna PL rnb PR kp \<and>* \<upharpoonleft>snat.assn cap capi \<and>*
     \<up>\<^sub>d(dyadic_interval_vec_invar (L, R, K)))
    (store_interval_vec_keep cnt lna rnb kp capi (a, b, c))
    (\<lambda>_. gmp_poly_assn L a \<and>* gmp_poly_assn R b \<and>* al_assn snat_assn K c \<and>*
         out_half_post cap (dyadic_interval_vec_triples (L, R, K)) cnt lna PL rnb PR kp \<and>*
         \<upharpoonleft>snat.assn cap capi)"
  using store_keep_vec_rule'[of "(L, R, K)" "(a, b, c)"] by (simp add: sep_conj_ac)

lemma vec_free_rule_split:
  "llvm_htriple (gmp_poly_assn L a \<and>* gmp_poly_assn R b \<and>* al_assn snat_assn K c)
     (dyadic_interval_vec_free_impl (a, b, c)) (\<lambda>_. \<box>)"
  using vec_free_rule[of "(L, R, K)" "(a, b, c)"] by simp

definition bool_word :: "bool \<Rightarrow> 64 word" where
  "bool_word b = (if b then 1 else 0)"

definition wrapper_outcome ::
  "nat \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool \<Rightarrow> bool)
   \<Rightarrow> (gmp_dyadic_interval_vec \<times> bool \<times> bool \<Rightarrow> bool)
   \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool \<Rightarrow> bool)
   \<Rightarrow> ((int \<times> int) \<times> nat) list \<Rightarrow> ((int \<times> int) \<times> nat) list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> bool" where
  "wrapper_outcome n \<Phi>A \<Phi>B \<Phi>C trP trN zw okw \<longleftrightarrow>
     (n < 10 \<and> okw = 0 \<and> (\<exists>P Q z. \<Phi>A (P, Q, z) \<and> zw = bool_word z
        \<and> trP = dyadic_interval_vec_triples P \<and> trN = dyadic_interval_vec_triples Q))
   \<or> (\<not> n < 10 \<and> okw = 1 \<and> (\<exists>V z. \<Phi>B (V, z, True) \<and> zw = bool_word z
        \<and> trP = dyadic_interval_vec_triples V \<and> trN = dyadic_interval_vec_triples V))
   \<or> (\<not> n < 10 \<and> okw = 0 \<and> (\<exists>V z'. \<Phi>B (V, z', False))
       \<and> (\<exists>P Q z. \<Phi>C (P, Q, z) \<and> zw = bool_word z
        \<and> trP = dyadic_interval_vec_triples P \<and> trN = dyadic_interval_vec_triples Q))"

lemma llc_if_word_0_1[simp]:
  "llc_if (0::1 word) t e = e" "llc_if (1::1 word) t e = t"
  unfolding llc_if_def by simp_all

lemma llc_if_from_bool: "llc_if (from_bool b) t e = (if b then t else e)"
  unfolding llc_if_def by simp

lemma bool_assn_ne0[simp]: "\<flat>\<^sub>pbool.assn b bi \<Longrightarrow> (bi \<noteq> 0) = b"
  by (auto simp: bool.assn_def dr_assn_pure_asm_prefix_def bool.rel_def br_def)

lemma snat_flat_unat: "\<flat>\<^sub>psnat.assn n (w::64 word) \<Longrightarrow> unat w = n"
  by (drule dsc_snat_pure_relD) (auto simp: snat.rel_def br_def snat_eq_unat_aux2)

lemma snat_flat_0D[dest!]: "\<flat>\<^sub>psnat.assn 0 (w::64 word) \<Longrightarrow> w = 0"
  by (drule snat_flat_unat) (simp add: unat_eq_zero)

lemma snat_flat_1D[dest!]: "\<flat>\<^sub>psnat.assn 1 (w::64 word) \<Longrightarrow> w = 1"
  by (drule snat_flat_unat) (simp add: unat_eq_1)

lemma snat_flat_Suc0D[dest!]: "\<flat>\<^sub>psnat.assn (Suc 0) (w::64 word) \<Longrightarrow> w = 1"
  using snat_flat_1D by simp

lemma bool_flat_0D[dest!]: "\<flat>\<^sub>pbool.assn b (0::1 word) \<Longrightarrow> \<not> b"
  by (drule bool_assn_ne0) simp

lemma bool_flat_1D[dest!]: "\<flat>\<^sub>pbool.assn b (1::1 word) \<Longrightarrow> b"
  by (drule bool_assn_ne0) simp

lemma pow_sub_impl_rule_facts:
  assumes S: "pow_sub_entry_monadic nf hc dl xs \<le> SPEC \<Phi>"
    and pre: "0 < length xs" "length xs < max_snat LENGTH(64)"
    and nr: "\<flat>\<^sub>psnat.assn nf nfi" and hr: "\<flat>\<^sub>psnat.assn hc hci" and dr: "\<flat>\<^sub>psnat.assn dl dli"
  shows "llvm_htriple (gmp_poly_assn xs xsi)
    (pow_sub_entry_impl nfi hci dli xsi)
    (\<lambda>(r1, r2, r3). gmp_poly_assn xs xsi \<and>*
       (EXS V b1 b2. vec_assn V r1 \<and>* \<upharpoonleft>bool.assn b1 r2 \<and>* \<upharpoonleft>bool.assn b2 r3 \<and>* \<up>(\<Phi> (V, b1, b2))))"
proof -
  have E: "(\<upharpoonleft>snat.assn nf nfi \<and>* \<upharpoonleft>snat.assn hc hci \<and>* \<upharpoonleft>snat.assn dl dli \<and>* P) = P" for P
    using nr hr dr
    by (auto simp: dr_assn_pure_asm_prefix_def snat.assn_def sep_algebra_simps fun_eq_iff
      pure_part_pure_eq)
  show ?thesis
    using pow_sub_impl_rule[OF S pre, of nfi hci dli xsi] by (simp add: E case_prod_beta')
qed

lemma wrapper_outcome_B[intro]:
  "\<not> n < 10 \<Longrightarrow> \<Phi>B (V, z, True) \<Longrightarrow> zw = bool_word z \<Longrightarrow>
   wrapper_outcome n \<Phi>A \<Phi>B \<Phi>C (dyadic_interval_vec_triples V) (dyadic_interval_vec_triples V) zw 1"
  unfolding wrapper_outcome_def by blast

lemma wrapper_outcome_C[intro]:
  "\<not> n < 10 \<Longrightarrow> \<Phi>B (V, z', False) \<Longrightarrow> \<Phi>C (P, Q, z) \<Longrightarrow> zw = bool_word z \<Longrightarrow>
   wrapper_outcome n \<Phi>A \<Phi>B \<Phi>C (dyadic_interval_vec_triples P) (dyadic_interval_vec_triples Q) zw 0"
  unfolding wrapper_outcome_def by blast

lemma wrapper_outcome_A[intro]:
  "n < 10 \<Longrightarrow> \<Phi>A (P, Q, z) \<Longrightarrow> zw = bool_word z \<Longrightarrow>
   wrapper_outcome n \<Phi>A \<Phi>B \<Phi>C (dyadic_interval_vec_triples P) (dyadic_interval_vec_triples Q) zw 0"
  unfolding wrapper_outcome_def by blast

theorem isarri_wrapper_rule:
  fixes xs :: "int list" and leni :: "64 word"
  assumes lenb: "0 < length xs" "length xs < max_snat LENGTH(64)"
    and A: "length xs < 10 \<Longrightarrow> lowdeg_isolate_all_split_main xs \<le> SPEC \<Phi>A"
    and invA: "\<And>P Q b. \<Phi>A (P, Q, b) \<Longrightarrow> dyadic_interval_vec_invar P \<and> dyadic_interval_vec_invar Q"
    and B: "\<not> length xs < 10 \<Longrightarrow> pow_sub_entry_monadic nf hc dl xs \<le> SPEC \<Phi>B"
    and invB: "\<And>V b. \<Phi>B (V, b, True) \<Longrightarrow> dyadic_interval_vec_invar V"
    and C: "\<not> length xs < 10 \<Longrightarrow> defl_isolate_all_split_main xs \<le> SPEC \<Phi>C"
    and invC: "\<And>P Q b. \<Phi>C (P, Q, b) \<Longrightarrow> dyadic_interval_vec_invar P \<and> dyadic_interval_vec_invar Q"
  shows "llvm_htriple
    (gmp_poly_assn xs (leni, leni, cp) \<and>* \<upharpoonleft>snat.assn (length xs) leni \<and>*
     \<upharpoonleft>snat.assn nf nfi \<and>* \<upharpoonleft>snat.assn hc hci \<and>* \<upharpoonleft>snat.assn dl dli \<and>* \<upharpoonleft>snat.assn cap capi \<and>*
     out_half_pre cap pcnt plna PPL prnb PPR pk \<and>* out_half_pre cap ncnt nlna NPL nrnb NPR nk \<and>*
     (EXS w. \<upharpoonleft>ll_pto (w::64 word) xs0p) \<and>* (EXS w. \<upharpoonleft>ll_pto (w::64 word) okp))
    (isarri_wrapper pcnt plna prnb pk ncnt nlna nrnb nk xs0p okp capi nfi hci dli leni cp)
    (\<lambda>_. gmp_poly_assn xs (leni, leni, cp) \<and>* \<upharpoonleft>snat.assn (length xs) leni \<and>*
     \<upharpoonleft>snat.assn nf nfi \<and>* \<upharpoonleft>snat.assn hc hci \<and>* \<upharpoonleft>snat.assn dl dli \<and>* \<upharpoonleft>snat.assn cap capi \<and>*
     (EXS trP trN (zw::64 word) (okw::64 word).
        out_half_post cap trP pcnt plna PPL prnb PPR pk \<and>* out_half_post cap trN ncnt nlna NPL nrnb NPR nk \<and>*
        \<upharpoonleft>ll_pto zw xs0p \<and>* \<upharpoonleft>ll_pto okw okp \<and>*
        \<up>(wrapper_outcome (length xs) \<Phi>A \<Phi>B \<Phi>C trP trN zw okw)))"
proof (cases "length xs < 10")
  case True
  note invA1 = invA[THEN conjunct1] and invA2 = invA[THEN conjunct2]
  show ?thesis
    unfolding isarri_wrapper_def
    supply [vcg_rules] = store_vec_rule_split lowdeg_impl_rule[OF A[OF True]]
    supply [simp] = llc_if_from_bool bool_word_def True
    supply [intro] = invA1 invA2
    apply vcg_monadify
    apply vcg'
    apply (simp_all add: snats_def max_snat_def)
    done
next
  case False
  note invC1 = invC[THEN conjunct1] and invC2 = invC[THEN conjunct2]
  show ?thesis
    apply (rule htriple_pure_preI)
    subgoal premises pp
    proof -
      have nr: "\<flat>\<^sub>psnat.assn nf nfi" and hr: "\<flat>\<^sub>psnat.assn hc hci" and dr: "\<flat>\<^sub>psnat.assn dl dli"
        using pp by (auto simp: dr_assn_pure_asm_prefix_def snat.assn_def dest!: pure_part_split_conj)
      show ?thesis
        unfolding isarri_wrapper_def
        supply [vcg_rules] = store_vec_rule_split store_keep_vec_rule_split vec_free_rule_split
          pow_sub_impl_rule_facts[OF B[OF False] lenb nr hr dr] defl_impl_rule[OF C[OF False]]
        supply [simp] = llc_if_from_bool bool_word_def False
        supply [intro] = invB invC1 invC2
        apply vcg_monadify
        apply vcg'
        apply (simp_all add: snats_def max_snat_def)
        done
    qed
    done
qed

end

end
