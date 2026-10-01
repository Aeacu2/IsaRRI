theory Isarri_Correct
  imports
    Isarri_Memory
    IsaRRI.Isarri_Paths
begin

text \<open>\<^bold>\<open>The exported C entry \<open>isarri\<close> isolates every real root once.\<close>
  The memory-layer theorem @{thm [source] isarri_wrapper_rule} is generic in each
  path's \<open>\<le> SPEC\<close> postcondition; here the three postconditions are instantiated with the uniform
  per-half contract @{const iso_half} (soundness, strict completeness, root-uniqueness, positivity)
  of \<open>Isarri_Paths\<close>, and the count follows from @{thm [source] iso_half_count}.\<close>

abbreviation Preal :: "int list \<Rightarrow> real poly" where
  "Preal xs \<equiv> real_of_int_poly (Poly xs)"

definition split_iso :: "int list \<Rightarrow> gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool \<Rightarrow> bool" where
  "split_iso xs = (\<lambda>(accP, accQ, xs0).
      dyadic_interval_vec_invar accP \<and> dyadic_interval_vec_invar accQ
    \<and> iso_half (Preal xs) (defl_wins accP)
    \<and> iso_half (Preal (refl_list xs)) (defl_wins accQ)
    \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"

definition pow_sub_entry_iso :: "int list \<Rightarrow> gmp_dyadic_interval_vec \<times> bool \<times> bool \<Rightarrow> bool" where
  "pow_sub_entry_iso xs = (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> dyadic_interval_vec_invar out \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0)
           \<and> iso_half (Preal xs) (defl_wins out)
           \<and> iso_half (Preal (refl_list xs)) (defl_wins out))"

text \<open>What a caller can read off the output cells. \<open>trP\<close>/\<open>trN\<close> are the \<open>((num_l, num_r), k)\<close>
  triples of the positive half and of the negative half (the latter in reflected coordinates: a
  window \<open>(a, b)\<close> there stands for \<open>(-b, -a)\<close>).\<close>

definition wrapper_contract ::
  "int list \<Rightarrow> ((int \<times> int) \<times> nat) list \<Rightarrow> ((int \<times> int) \<times> nat) list \<Rightarrow> 64 word \<Rightarrow> bool" where
  "wrapper_contract xs trP trN zw \<longleftrightarrow>
      iso_half (Preal xs) (trip_wins trP)
    \<and> iso_half (Preal (refl_list xs)) (trip_wins trN)
    \<and> zw = bool_word (xs \<noteq> [] \<and> xs ! 0 = 0)"

lemma wrapper_outcome_contract:
  "wrapper_outcome n (split_iso xs) (pow_sub_entry_iso xs) (split_iso xs) trP trN zw okw
     \<Longrightarrow> wrapper_contract xs trP trN zw"
  unfolding wrapper_outcome_def wrapper_contract_def split_iso_def pow_sub_entry_iso_def
  by (auto simp: defl_wins_trip_wins)

section \<open>The count\<close>

lemma refl_poly_nz:
  assumes "xs \<noteq> []" "last xs \<noteq> 0"
  shows "Preal (refl_list xs) \<noteq> 0"
proof -
  have "Preal xs \<noteq> 0" by (rule real_poly_nz[OF assms])
  then show ?thesis
    using pcompose_eq_0[where q="[:0, -1:] :: real poly"] unfolding Poly_refl_list_eq_pcompose
    by force
qed

lemma card_neg_roots_refl:
  "card {x. 0 < x \<and> poly (Preal (refl_list xs)) x = 0} = card {x. x < 0 \<and> poly (Preal xs) x = 0}"
proof -
  have "{x. 0 < x \<and> poly (Preal (refl_list xs)) x = 0} = uminus ` {x. x < 0 \<and> poly (Preal xs) x = 0}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> {x. 0 < x \<and> poly (Preal (refl_list xs)) x = 0}"
    then have "- x \<in> {x. x < 0 \<and> poly (Preal xs) x = 0}"
      by (simp add: Poly_refl_list_eq_pcompose poly_pcompose)
    then show "x \<in> uminus ` {x. x < 0 \<and> poly (Preal xs) x = 0}" by (rule rev_image_eqI) simp
  next
    fix x assume "x \<in> uminus ` {x. x < 0 \<and> poly (Preal xs) x = 0}"
    then show "x \<in> {x. 0 < x \<and> poly (Preal (refl_list xs)) x = 0}"
      by (auto simp: Poly_refl_list_eq_pcompose poly_pcompose)
  qed
  then show ?thesis by (simp add: card_image)
qed

corollary wrapper_contract_count:
  assumes ne: "xs \<noteq> []" and nz: "last xs \<noteq> 0" and K: "wrapper_contract xs trP trN zw"
  shows "length trP = card {x. 0 < x \<and> poly (Preal xs) x = 0}"
    and "length trN = card {x. x < 0 \<and> poly (Preal xs) x = 0}"
proof -
  have P0: "Preal xs \<noteq> 0" by (rule real_poly_nz[OF ne nz])
  have "length (trip_wins trP) = card {x. 0 < x \<and> poly (Preal xs) x = 0}"
    using iso_half_count[OF P0] K unfolding wrapper_contract_def by blast
  then show "length trP = card {x. 0 < x \<and> poly (Preal xs) x = 0}"
    by (simp add: trip_wins_def)
  have "length (trip_wins trN) = card {x. 0 < x \<and> poly (Preal (refl_list xs)) x = 0}"
    using iso_half_count[OF refl_poly_nz[OF ne nz]] K unfolding wrapper_contract_def by blast
  then show "length trN = card {x. x < 0 \<and> poly (Preal xs) x = 0}"
    by (simp add: trip_wins_def card_neg_roots_refl)
qed

section \<open>The exported entry\<close>

text \<open>\<^bold>\<open>The precondition's squarefreeness is HOL's.\<close> @{const dsc_isolate_all_split_lin_pre} states
  \<open>square_free\<close> (Polynomial_Factorization: nonzero, no square of a positive-degree factor divides
  it); the power-substitution theorems take \<open>squarefree\<close> (HOL: every square divisor is a unit).
  Over a field the positive-degree polynomials are exactly the nonzero non-units, so the first gives
  the second, and the capstone needs no separate squarefreeness hypothesis.\<close>

lemma square_free_imp_squarefree:
  fixes p :: "'a::field poly"
  assumes "square_free p"
  shows "squarefree p"
  unfolding squarefree_def
proof (intro allI impI)
  fix x assume d2: "x\<^sup>2 dvd p"
  then have d: "x * x dvd p" by (simp add: power2_eq_square)
  have p0: "p \<noteq> 0" using assms by (simp add: square_free_def)
  then have x0: "x \<noteq> 0" using d by auto
  have "\<not> degree x > 0" using assms d unfolding square_free_def by blast
  then show "is_unit x" using x0 by (simp add: is_unit_iff_degree)
qed

text \<open>\<^bold>\<open>Below \<open>nfloor\<close> the substitution is not attempted.\<close> The entry's applicability test
  includes \<open>nfloor \<le> len\<close>, so on a shorter input it returns \<open>ok = False\<close> without solving the
  reduced polynomial, and the reduced polynomial's precondition is not needed.\<close>

lemma pow_sub_entry_monadic_below_nfloor:
  fixes xs :: "int list" and nfloor hcap dlt :: nat
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and hcb: "hcap < max_snat LENGTH(gmp_poly_len)"
    and short: "length xs < nfloor"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs \<le> SPEC (\<lambda>(out, xs0, ok). \<not> ok)"
proof -
  have lenxs: "length xs < max_snat LENGTH(gmp_poly_len)" using len1 by simp
  have hb: "pow_sub_h xs < max_snat LENGTH(gmp_poly_len)"
    using pow_sub_h_le_length[of xs] lenxs by simp
  have dbnd: "gcd (pow_sub_h xs) hcap < max_snat LENGTH(gmp_poly_len)"
    using pow_sub_gcd_le_max[of "pow_sub_h xs" hcap] hb hcb by simp
  have parbnd: "gcd d 2 < max_snat LENGTH(gmp_poly_len)" for d :: nat
  proof -
    have "gcd d 2 \<le> 2" by (rule pow_sub_gcd_two_le)
    thus ?thesis unfolding pow_sub_room_max_snat by linarith
  qed
  show ?thesis
    unfolding pow_sub_entry_monadic_def PR_CONST_def
      pow_sub_entry_applicable_mop_def pow_sub_entry_exp_mop_def
      pow_sub_entry_bail_mop_def poly_length_monadic_def
    apply (refine_vcg
           pow_sub_h_monadic_correct[OF lenxs, THEN order_trans]
           snat_gcd_monadic_correct[THEN order_trans]
           dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans])
    apply (all \<open>use ne lenxs len1 hb dbnd parbnd short in \<open>auto simp: Let_def\<close>\<close>)
    done
qed

theorem isarri_correct_paths:
  fixes xs :: "int list" and leni :: "64 word"
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(64)"
    and hcb: "hc < max_snat LENGTH(64)"
    and nz: "last xs \<noteq> 0"
    and preA: "length xs < 10 \<Longrightarrow> dsc_isolate_all_split_lin_pre xs"
    and preC: "\<not> length xs < 10 \<Longrightarrow> dsc_isolate_all_split_defl_pre xs"
    and qpre: "\<And>d. \<not> length xs < 10 \<Longrightarrow> nf \<le> length xs \<Longrightarrow> 2 \<le> d \<Longrightarrow> even d \<Longrightarrow>
          d = gcd (pow_sub_h xs) hc \<Longrightarrow> dsc_isolate_all_split_defl_pre (pow_sub_extract d xs)"
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
        \<up>(wrapper_contract xs trP trN zw)))"
proof -
  have lenb: "0 < length xs" "length xs < max_snat LENGTH(64)" using ne len1 by auto
  have sfP: "squarefree (Preal xs)"
    using preA preC
    by (cases "length xs < 10")
       (auto simp: dsc_isolate_all_split_lin_pre_def dsc_isolate_all_split_defl_pre_def
         intro: square_free_imp_squarefree)
  have A: "lowdeg_isolate_all_split_main xs \<le> SPEC (split_iso xs)" if "length xs < 10"
    unfolding split_iso_def by (rule lowdeg_isolate_all_split_main_iso[OF preA[OF that]])
  have B: "pow_sub_entry_monadic nf hc dl xs \<le> SPEC (pow_sub_entry_iso xs)" if nl: "\<not> length xs < 10"
  proof (cases "nf \<le> length xs")
    case True
    show ?thesis unfolding pow_sub_entry_iso_def
      by (rule pow_sub_entry_monadic_iso[OF ne len1 hcb nz sfP]) (use qpre[OF nl True] in blast)
  next
    case False
    then have short: "length xs < nf" by simp
    show ?thesis unfolding pow_sub_entry_iso_def
      by (rule weaken_SPEC[OF pow_sub_entry_monadic_below_nfloor[OF ne len1 hcb short]]) auto
  qed
  have C: "defl_isolate_all_split_main xs \<le> SPEC (split_iso xs)" if "\<not> length xs < 10"
    unfolding split_iso_def by (rule defl_isolate_all_split_main_iso[OF preC[OF that]])
  have invA: "\<And>P Q b. split_iso xs (P, Q, b) \<Longrightarrow> dyadic_interval_vec_invar P \<and> dyadic_interval_vec_invar Q"
    by (simp add: split_iso_def)
  have invB: "\<And>V b. pow_sub_entry_iso xs (V, b, True) \<Longrightarrow> dyadic_interval_vec_invar V"
    by (simp add: pow_sub_entry_iso_def)
  show ?thesis
    apply (rule htriple_ent_post[OF _ isarri_wrapper_rule[OF lenb A invA B invB C invA]])
    apply (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps
        intro: wrapper_outcome_contract)
    done
qed

text \<open>\<^bold>\<open>One caller-side precondition.\<close> The deflating path's precondition contains the degree
  \<open>\<le> 8\<close> path's (@{const dsc_isolate_all_split_lin_pre}), the nonzero leading coefficient and the length
  bound and \<open>square_free\<close> (which gives \<open>squarefree\<close>, @{thm [source] square_free_imp_squarefree}), so
  the three paths' obligations reduce to it, the \<open>hcap\<close> word bound, and the reduced polynomial's
  precondition. That last one is needed only when the substitution is attempted: at least ten
  coefficients (else the degree \<open>\<le> 8\<close> path runs), \<open>nfloor \<le> len\<close>, and an even \<open>d \<ge> 2\<close>
  (@{thm [source] pow_sub_entry_monadic_below_nfloor}).

  \<^bold>\<open>No exponential depth-budget clause\<close>: neither bundle contains @{const split_cap}'s
  \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 + 1 < 2\<^sup>6\<^sup>3\<close> clause. The loops' word budgets are linear in \<open>\<mu>\<close>, and so are the depth
  and guard-headroom clauses that remain.\<close>

corollary isarri_correct:
  fixes xs :: "int list" and leni :: "64 word"
  assumes pre: "dsc_isolate_all_split_defl_pre xs"
    and hcb: "hc < max_snat LENGTH(64)"
    and qpre: "\<And>d. \<not> length xs < 10 \<Longrightarrow> nf \<le> length xs \<Longrightarrow> 2 \<le> d \<Longrightarrow> even d \<Longrightarrow>
          d = gcd (pow_sub_h xs) hc \<Longrightarrow> dsc_isolate_all_split_defl_pre (pow_sub_extract d xs)"
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
        \<up>(wrapper_contract xs trP trN zw
           \<and> length trP = card {x. 0 < x \<and> poly (Preal xs) x = 0}
           \<and> length trN = card {x. x < 0 \<and> poly (Preal xs) x = 0})))"
proof -
  have sp: "dsc_isolate_all_split_lin_pre xs" and l3: "length xs + 3 < max_snat LENGTH(64)"
    using pre unfolding dsc_isolate_all_split_defl_pre_def by auto
  have l2: "2 \<le> length xs" and nz: "last xs \<noteq> 0"
    using sp unfolding dsc_isolate_all_split_lin_pre_def by auto
  have ne: "xs \<noteq> []" using l2 by auto
  have len1: "length xs + 1 < max_snat LENGTH(64)" using l3 by simp
  show ?thesis
    apply (rule htriple_ent_post[OF _ isarri_correct_paths[OF ne len1 hcb nz sp pre qpre]])
       apply (auto simp: entails_def sep_algebra_simps pred_lift_extract_simps
        dest: wrapper_contract_count[OF ne nz])
    done
qed

text \<open>The trust base of the capstone: no \<open>skip_proof\<close> oracle may appear here.\<close>
thm_oracles isarri_correct

end
