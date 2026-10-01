theory Kiou_Bound_Hybrid_Reflect
  imports "IsaRRI_Refine.Kiou_Bound_Bail_Reflect"
    "IsaRRI_Refine.Hybrid_Capstone"
begin

text \<open>The pipeline capstone for the hybrid solver. Imports are session-qualified.\<close>

text \<open>\<^bold>\<open>Correctness of @{const hybrid_isolate_all_split_main}\<close>, the hybrid split pipeline. Structurally
  \<open>Kiou_Bound_Bail_Reflect\<close> (the same two half solves, zero check and frame-scaling algebra), with the
  retained root \<open>rp\<close> threaded through.

  \<^bold>\<open>Why this is not an instance of the bail theory.\<close> The bail pipeline's frame scaling is stated at the
  fixed policy @{const pol_final}; the hybrid keystone delivers an \<open>\<exists>pol\<close> multiset instead, because the
  push-time ambiguous sentinel lets the hybrid solver's \<open>\<sigma>\<close>, and so its tree, diverge from the bail
  solver's. The frame-scaling lemmas are therefore used at a free policy.
  @{thm [source] newdsc_pol_bail_elems_of_rat_image} and
  @{thm [source] newdsc_pol_bail_terminates_squarefree} are policy-generic, and the \<open>of_rat\<close>-image section
  of \<open>Kiou_Bound_Bail_Reflect\<close> is imported.

  \<^bold>\<open>The \<open>rp\<close> thread.\<close> @{const hybrid_split_pos_solve_monadic} copies \<open>xs\<close> into the retained escalation
  root \<open>rp\<close> and initialises \<open>Pinit = split_init_pow2_l0_monadic kpos xs\<close>. The keystone's \<open>P_eq\<close> premise
  wants \<open>Pinit = carried_init_same_den 0 (2\<^sup>0) (2\<^sup>k\<^sup>p\<^sup>o\<^sup>s) rp\<close>, and
  @{thm [source] split_init_pow2_l0_eq_scale_poly_list} is that equation, so \<open>P_eq\<close> is discharged in the
  pipeline and is not a caller obligation.

  \<^bold>\<open>Not discharged here\<close>: \<open>rp_small\<close> and the two depth-quantified bounds \<open>k_depth_safe\<close>/\<open>g_room\<close>. They are
  obligations on \<open>length xs\<close>, carried by the precondition, and not checked at run time.\<close>

section \<open>The seed caps are THEOREMS at the pipeline, not preconditions\<close>

text \<open>\<^bold>\<open>Why this precondition bundle is shorter than @{const dsc_isolate_all_split_bail_pre}.\<close> The bail
  solver's \<open>cap\<close>/\<open>kcap\<close> bound its escalation ladder against \<open>max_snat\<close> absolutely, so its pipeline carries a
  \<open>k\<close>-quantified clause for them. The hybrid keystone bounds \<open>kcap\<close> against its own
  @{const hybrid_root_potential}, and the pipeline calls the solver at depth 0
  (\<open>hybrid_main_list_monadic e0 zl rpos 0 Pinit rp\<close>), where \<open>kcap\<close> is reflexive.

  \<^bold>\<open>\<open>mucap\<close>\<close>: the worklist-length invariant needs \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 + 1 < max_snat\<close>, which is already a clause of
  @{const dsc_isolate_all_split_pre} (spelled with \<open>rational_interval_mu\<close>, the same function by
  \<open>dyadic_iv_interval_mu_eq_rational\<close> below), so the obligation is inherited, not new.\<close>

lemma hybrid_seed_kcap:
  fixes \<delta> :: real
  shows "int 0 + int (2 ^ newton_pol_ecap + 2) * int (dyadic_iv_interval_mu \<delta> (0, 1))
         \<le> hybrid_root_potential \<delta> 0"
  by (simp add: hybrid_root_potential_def)

text \<open>\<^bold>\<open>The two \<open>\<mu>\<close> spellings are ONE function\<close> --- @{const dyadic_iv_interval_mu} and
  @{const rational_interval_mu} are both \<open>mu \<delta> (of_rat (fst I)) (of_rat (snd I))\<close>, verbatim.
  Stated because the pipeline's inherited \<open>\<mu>\<close> premise is in the \<open>rational_\<close> spelling and the
  keystone's \<open>mucap\<close> is in the \<open>dyadic_iv_\<close> one, and nothing else bridges them.\<close>
lemma dyadic_iv_interval_mu_eq_rational:
  "dyadic_iv_interval_mu \<delta> I = rational_interval_mu \<delta> I"
  by (simp add: dyadic_iv_interval_mu_def rational_interval_mu_def)

section \<open>\<open>newdsc_pol_bail_int\<close> sound/complete real-image at a FREE policy\<close>

text \<open>\<^bold>\<open>Instantiations.\<close> These two lemmas and the frame-scaling pair below are instances of the
  statements in \<open>Kiou_Bound_Bail_Reflect\<close>, which are stated at a free policy pair \<open>(pol, polr)\<close> with the
  int/real bridge's \<open>polrel\<close> side condition as a premise: the bail solver instantiates at
  @{thm [source] pol_final_real_rel}, the hybrid solver at @{thm [source] hybrid_polr_of_pol_rel}.\<close>
lemma newdsc_pol_bail_int_expol_sound_real_image':
  fixes P :: "int poly" and pol :: newton_pol
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0" and sf: "square_free P_real"
  shows "\<forall>I \<in> set (newdsc_pol_bail_int pol 0 1 e dk P).
    \<exists>J \<in> set (newdsc_pol_bail (hybrid_polr_of_pol pol) (degree P)
                (of_rat 0) (of_rat 1) e dk 0 P_real).
      I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
  unfolding P_real_def
  by (rule newdsc_pol_bail_int_polr_sound_real_image'[OF P0 p0 sf[unfolded P_real_def] zero_less_one])
     (rule hybrid_polr_of_pol_rel)

lemma newdsc_pol_bail_int_expol_complete_real_image':
  fixes P :: "int poly" and pol :: newton_pol
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0" and sf: "square_free P_real"
    and root: "poly P_real x = 0" and ax: "of_rat 0 < x" and xb: "x < of_rat 1"
  shows "\<exists>I \<in> set (newdsc_pol_bail_int pol 0 1 e dk P).
    \<exists>J \<in> set (newdsc_pol_bail (hybrid_polr_of_pol pol) (degree P)
                (of_rat 0) (of_rat 1) e dk 0 P_real).
      I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
  unfolding P_real_def
  by (rule newdsc_pol_bail_int_polr_complete_real_image'[OF P0 p0 sf[unfolded P_real_def]
        root[unfolded P_real_def] ax xb])
     (rule hybrid_polr_of_pol_rel)

section \<open>Frame-scaling half correctness at a FREE policy\<close>

text \<open>Verbatim @{thm [source] dsc_carried_bail_pos_half_sound} with \<open>pol_final\<close> generalized to
  a free \<open>pol\<close>, @{const pol_final_real} to @{term "hybrid_polr_of_pol pol"}, and
  @{thm [source] newdsc_pol_bail_pol_final_dom} to the policy-generic
  @{thm [source] newdsc_pol_bail_terminates_squarefree}. The scale-by-\<open>rpos\<close> algebra is shared
  and unchanged.\<close>
lemma dsc_carried_hybrid_pos_half_sound:
  fixes xs :: "int list" and rpos :: int and pol :: newton_pol
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and p0: "degree (Poly Pinit) \<noteq> 0"
    and sf: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (dyadic_iv_acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit))"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
    \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
  unfolding P_real_def
  by (rule dsc_carried_polr_pos_half_sound[OF P0 rpos_pos p0[unfolded Pinit_def]
        sf[unfolded Pinit_def] acc_eq[unfolded Pinit_def]])
     (rule hybrid_polr_of_pol_rel)

text \<open>\<^bold>\<open>The pinned soundness twin\<close>: the isolation holds of the emitted interval's own \<open>of_rat\<close> image
  rather than of an unconstrained existential witness. See
  @{thm [source] dsc_carried_polr_pos_half_sound_strong} for why the existential form is not an isolation
  statement about \<open>I\<close>.\<close>
lemma dsc_carried_hybrid_pos_half_sound_strong:
  fixes xs :: "int list" and rpos :: int and pol :: newton_pol
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and p0: "degree (Poly Pinit) \<noteq> 0"
    and sf: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (dyadic_iv_acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit))"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
    dsc_pair_ok P_real (of_rat (fst I), of_rat (snd I))"
  unfolding P_real_def
  by (rule dsc_carried_polr_pos_half_sound_strong[OF P0 rpos_pos p0[unfolded Pinit_def]
        sf[unfolded Pinit_def] acc_eq[unfolded Pinit_def]])
     (rule hybrid_polr_of_pol_rel)

text \<open>Completeness twin --- verbatim @{thm [source] dsc_carried_bail_pos_half_complete} under
  the same generalization.\<close>
lemma dsc_carried_hybrid_pos_half_complete:
  fixes xs :: "int list" and rpos :: int and x :: real and pol :: newton_pol
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and p0: "degree (Poly Pinit) \<noteq> 0"
    and sf: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (dyadic_iv_acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit))"
    and x_pos: "0 < x" and x_lt: "x < of_int rpos" and root: "poly P_real x = 0"
  shows "\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
    \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
  by (rule dsc_carried_polr_pos_half_complete[OF P0 rpos_pos p0[unfolded Pinit_def]
        sf[unfolded Pinit_def] acc_eq[unfolded Pinit_def] x_pos x_lt root[unfolded P_real_def]])
     (rule hybrid_polr_of_pol_rel)

text \<open>\<^bold>\<open>The pinned completeness twin\<close>: the root is covered by the emitted interval's own \<open>of_rat\<close> image
  rather than by an unconstrained existential witness. See
  @{thm [source] dsc_carried_polr_pos_half_complete_strong} for why the existential form is not a covering
  statement about \<open>I\<close>.\<close>
lemma dsc_carried_hybrid_pos_half_complete_strong:
  fixes xs :: "int list" and rpos :: int and x :: real and pol :: newton_pol
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and p0: "degree (Poly Pinit) \<noteq> 0"
    and sf: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (dyadic_iv_acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit))"
    and x_pos: "0 < x" and x_lt: "x < of_int rpos" and root: "poly P_real x = 0"
  shows "\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
    (of_rat (fst I) < x \<and> x < of_rat (snd I))
    \<or> (of_rat (fst I) = x \<and> of_rat (snd I) = x)"
  by (rule dsc_carried_polr_pos_half_complete_strong[OF P0 rpos_pos p0[unfolded Pinit_def]
        sf[unfolded Pinit_def] acc_eq[unfolded Pinit_def] x_pos x_lt root[unfolded P_real_def]])
     (rule hybrid_polr_of_pol_rel)

text \<open>The pinned \<open>\<rightarrow>\<close> existential step for the COVERING clause — the twin of
  @{thm [source] dsc_pair_ok_of_rat_witness_pair}, and needed for the same reason: every weakening
  corollary below has to put the old existential back, and \<open>I\<close>'s own \<open>of_rat\<close> image is the witness
  no automatic method guesses.\<close>
lemma cover_of_rat_witness_pair:
  fixes x :: real
  assumes "(of_rat (fst I) < x \<and> x < of_rat (snd I))
           \<or> (of_rat (fst I) = x \<and> of_rat (snd I) = x)"
  shows "\<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
  using assms
  by (rule_tac exI[where x = "(of_rat (fst I), of_rat (snd I))"])
     (auto simp: real_to_rat_pair_of_rat)

section \<open>The pipeline's hybrid-specific precondition\<close>

text \<open>Extends @{const dsc_isolate_all_split_pre} with the three things the hybrid keystone needs and the
  base bundle does not supply: the \<open>+3\<close> length headroom, the \<open>2\<^sup>4\<^sup>0\<close> root-length window, and the two
  depth-quantified bounds. There is no \<open>kcap\<close> clause, because at the pipeline's depth 0 it is a theorem
  (@{thm [source] hybrid_seed_kcap}), and no \<open>mucap\<close> clause, because that one is inherited from
  @{const dsc_isolate_all_split_pre}.

  The depth bounds are stated against \<open>\<kappa> = 258 \<cdot> \<mu>\<close>, which is @{const hybrid_root_potential} at depth 0,
  the shape the keystone's \<open>k_depth_safe\<close>/\<open>g_room\<close> carry, so the bridge below is a rewrite. The range is
  linear in \<open>\<mu>\<close>, and @{const dsc_isolate_all_split_pre} caps \<open>\<mu>\<close> at 61, so the resulting obligation is on
  \<open>length xs\<close> alone rather than a root-separation floor.\<close>
text \<open>\<^bold>\<open>The depth capacity, at one \<open>k\<close>\<close>, for the same reason as \<open>split_cap\<close>: a \<open>\<forall>k\<close> depth clause would make
  the bundle unsatisfiable and every theorem conditional on it vacuous. \<open>length (refl_list xs) = length xs\<close>,
  so one argument serves both halves.\<close>

definition hybrid_depth_cap :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"hybrid_depth_cap ys k \<longleftrightarrow>
  (let Yinit = scale_poly_list (2 ^ k) ys;
       \<delta> = delta_P (map_poly of_int (Poly Yinit) :: real poly) in
     (\<forall>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
              * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<longrightarrow>
        kD * (length ys - 1) < max_snat LENGTH(gmp_poly_len)) \<and>
     (\<forall>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
              * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<longrightarrow>
        (kD + 1) * length ys < 1099511627776))"

definition dsc_isolate_all_split_hybrid_pre :: "int list \<Rightarrow> bool" where
"dsc_isolate_all_split_hybrid_pre xs \<longleftrightarrow>
  dsc_isolate_all_split_pre xs \<and>
  length xs + 3 < max_snat LENGTH(gmp_poly_len) \<and>
  length xs < 1099511627776 \<and>
  kiou_bound_k_monadic xs \<le> SPEC (hybrid_depth_cap xs) \<and>
  kiou_bound_k_monadic (refl_list xs) \<le> SPEC (hybrid_depth_cap (refl_list xs))"

text \<open>\<^bold>\<open>The satisfiability witness\<close> for @{const hybrid_expol_int_pre}. Structurally
  @{thm [source] dsc_isolate_all_split_pos_bail_pre}: squarefreeness, non-zeroness and canonicity transfer
  under any dilation (@{thm [source] square_free_pcompose_linear}); \<open>P_eq\<close> is
  @{thm [source] split_init_pow2_l0_eq_scale_poly_list}; \<open>kcap\<close> comes from \<open>hybrid_seed_kcap\<close> and \<open>mucap\<close>
  from the inherited base bundle.\<close>
lemma dsc_isolate_all_split_pos_hybrid_pre:
  fixes xs :: "int list" and kpos :: nat
  assumes pre: "dsc_isolate_all_split_hybrid_pre xs"
    and kpos_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ kpos"
    \<comment> \<open>Both capacities arrive AT \<open>kpos\<close> as hypotheses, rather than being instantiated out of
       \<open>\<forall>k\<close> clauses. The caller has both from the merged \<open>SPEC\<close> of \<open>kiou_bound_k_monadic\<close>.\<close>
    and cap_at: "split_cap xs kpos"
    and depth_at: "hybrid_depth_cap xs kpos"
  shows "hybrid_expol_int_pre
      (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ kpos) xs)) :: real poly))
      (((((split_pipeline_e0, 0), 2 ^ kpos), 0), scale_poly_list (2 ^ kpos) xs), xs)"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    and lenb3: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    and xs_small: "length xs < 1099511627776"
    unfolding dsc_isolate_all_split_hybrid_pre_def by auto
  from pre' have len2: "2 \<le> length xs"
    and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and canonxs: "coeffs (Poly xs) = xs"
    unfolding dsc_isolate_all_split_pre_def by auto
  define Pinit where "Pinit = scale_poly_list (2 ^ kpos) xs"
  define d where "d = delta_P (map_poly of_int (Poly Pinit) :: real poly)"
  have cpos: "(2::int) ^ kpos \<noteq> 0" by simp
  have len_eq: "length Pinit = length xs"
    unfolding Pinit_def by (simp add: scale_poly_list_eq_map_upt)
  have sfPinit: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    unfolding Pinit_def
    using square_free_pcompose_linear[OF sfxs, of "2 ^ kpos"]
    by (simp add: Poly_scale_poly_list_eq_pcompose)
  have P0init: "Poly Pinit \<noteq> 0" using sfPinit unfolding square_free_def by simp
  have canonPinit: "coeffs (Poly Pinit) = Pinit"
    unfolding Pinit_def
    using coeffs_scale_poly_list[OF canonxs[symmetric], of "2 ^ kpos"] cpos
    by (simp add: scale_poly_list_correct[symmetric, of "2 ^ kpos" "Poly xs"] canonxs)
  have delta_pos: "d > 0" unfolding d_def using P0init delta_P_pos by simp
  have degne: "degree (Poly Pinit) \<noteq> 0"
  proof -
    have "length (coeffs (Poly Pinit)) = degree (Poly Pinit) + 1"
      using P0init by (rule length_coeffs)
    thus ?thesis using len2 len_eq canonPinit by simp
  qed
  have small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> d \<Longrightarrow> descartes_list_int a b Pinit \<le> 1"
    unfolding d_def
    by (rule rational_fast_descartes_list_int_delta_P_le1[OF P0init canonPinit degne sfPinit])
  have len2P: "Suc 0 < length Pinit" using len2 len_eq by simp
  have lenbP: "length Pinit + 2 < max_snat LENGTH(gmp_poly_len)" using lenb3 len_eq by simp
  have lrP: "(0::int) < 2 ^ kpos" by simp
  \<comment> \<open>\<open>P_eq\<close>: MACHINE-DISCHARGED, not a caller duty --- the same \<open>q0_eq\<close> step
     \<open>dsc_isolate_all_split_truncate_pos_half_step\<close> takes (Truncate Reflect;
     not imported here, so the citation is plain text).\<close>
  have P_eq: "Pinit = carried_init_same_den 0 (2 ^ 0) (2 ^ kpos) xs"
    unfolding Pinit_def by (simp add: split_init_pow2_l0_eq_scale_poly_list)
  \<comment> \<open>\<open>(cases xs) auto\<close>, not \<open>simp\<close>: \<open>simp\<close> normalises the goal to \<open>xs \<noteq> []\<close>, which it cannot
     then derive from \<open>2 \<le> length xs\<close> — the bail Reflect's \<open>P_len\<close> uses the same idiom.\<close>
  have rp_len: "0 < length xs" using len2 by (cases xs) auto
  have depth: "(\<forall>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu d (0, 1)) \<longrightarrow>
           kD * (length xs - 1) < max_snat LENGTH(gmp_poly_len)) \<and>
        (\<forall>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu d (0, 1)) \<longrightarrow>
           (kD + 1) * length xs < 1099511627776)"
    using depth_at unfolding hybrid_depth_cap_def Pinit_def d_def by (simp add: Let_def)
  \<comment> \<open>\<^bold>\<open>\<open>mucap\<close> is INHERITED, not new\<close>: the base bundle's own \<open>\<mu>\<close> clause, which arrives already
     instantiated at this \<open>k\<close> as \<open>cap_at\<close> and is re-spelled by
     @{thm [source] dyadic_iv_interval_mu_eq_rational}.\<close>
  have mucap: "int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) + 1
               < int (max_snat LENGTH(gmp_poly_len))"
    using cap_at
    unfolding split_cap_def Pinit_def d_def
    by (simp add: Let_def dyadic_iv_interval_mu_eq_rational)
  have kcap: "int 0 + int (2 ^ newton_pol_ecap + 2) * int (dyadic_iv_interval_mu d (0, 1))
              \<le> hybrid_root_potential d 0"
    by (rule hybrid_seed_kcap)
  show ?thesis
    unfolding hybrid_expol_int_pre_def prod.case Pinit_def[symmetric] d_def[symmetric]
    using delta_pos len2P small_fast sfPinit P0init canonPinit lenbP lrP
          mucap kcap P_eq rp_len xs_small depth
    by simp
qed

text \<open>Negative-half twin, at \<open>Qb = refl_list xs\<close>.\<close>
lemma dsc_isolate_all_split_neg_hybrid_pre:
  fixes xs :: "int list" and kneg :: nat
  defines "Qb \<equiv> refl_list xs"
  assumes pre: "dsc_isolate_all_split_hybrid_pre xs"
    and kneg_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ kneg"
    \<comment> \<open>Negative twin: both capacities at \<open>kneg\<close>, stated at \<open>refl_list xs\<close> — the
       list the negative half actually runs \<open>kiou_bound_k_monadic\<close> on.\<close>
    and cap_at: "split_cap (refl_list xs) kneg"
    and depth_at: "hybrid_depth_cap (refl_list xs) kneg"
  shows "hybrid_expol_int_pre
      (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ kneg) Qb)) :: real poly))
      (((((split_pipeline_e0, 0), 2 ^ kneg), 0), scale_poly_list (2 ^ kneg) Qb), Qb)"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    and lenb3: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    and xs_small: "length xs < 1099511627776"
    unfolding dsc_isolate_all_split_hybrid_pre_def by auto
  from pre' have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and canonxs: "coeffs (Poly xs) = xs"
    unfolding dsc_isolate_all_split_pre_def by auto
  have xsne: "xs \<noteq> []" using len2 by auto
  have sfQb: "square_free (map_poly of_int (Poly Qb) :: real poly)"
    unfolding Qb_def
    using square_free_pcompose_linear[OF sfxs, of "-1"]
    by (simp add: refl_list_eq_scale_poly_list_neg1 Poly_scale_poly_list_eq_pcompose)
  have Q0: "Poly Qb \<noteq> 0" using sfQb unfolding square_free_def by simp
  have lenQb: "length Qb = length xs" unfolding Qb_def by (simp add: refl_list_def)
  \<comment> \<open>There is NO \<open>canon_refl_list\<close>; canonicity of the reflected list is recovered the way
     @{thm [source] dsc_isolate_all_split_neg_bail_pre} does it --- from non-emptiness plus a
     nonzero LAST coefficient (\<open>lastnz\<close> is a conjunct of @{const dsc_isolate_all_split_pre},
     and @{thm [source] last_refl_list_nz} carries it through the reflection).\<close>
  have lastnzQb: "last Qb \<noteq> 0" unfolding Qb_def using last_refl_list_nz[OF xsne lastnz] by simp
  have Qb_ne: "Qb \<noteq> []" unfolding Qb_def using xsne by (simp add: refl_list_def)
  have canonQb: "coeffs (Poly Qb) = Qb"
    using coeffs_Poly_eq_self_of_last_nonzero[OF Qb_ne lastnzQb] .
  define Qinit where "Qinit = scale_poly_list (2 ^ kneg) Qb"
  define d where "d = delta_P (map_poly of_int (Poly Qinit) :: real poly)"
  have cpos: "(2::int) ^ kneg \<noteq> 0" by simp
  have len_eq: "length Qinit = length Qb"
    unfolding Qinit_def by (simp add: scale_poly_list_eq_map_upt)
  have sfQinit: "square_free (map_poly of_int (Poly Qinit) :: real poly)"
    unfolding Qinit_def
    using square_free_pcompose_linear[OF sfQb, of "2 ^ kneg"]
    by (simp add: Poly_scale_poly_list_eq_pcompose)
  have Q0init: "Poly Qinit \<noteq> 0" using sfQinit unfolding square_free_def by simp
  have canonQinit: "coeffs (Poly Qinit) = Qinit"
    unfolding Qinit_def
    using coeffs_scale_poly_list[OF canonQb[symmetric], of "2 ^ kneg"] cpos
    by (simp add: scale_poly_list_correct[symmetric, of "2 ^ kneg" "Poly Qb"] canonQb)
  have delta_pos: "d > 0" unfolding d_def using Q0init delta_P_pos by simp
  have degne: "degree (Poly Qinit) \<noteq> 0"
  proof -
    have "length (coeffs (Poly Qinit)) = degree (Poly Qinit) + 1"
      using Q0init by (rule length_coeffs)
    thus ?thesis using len2 len_eq lenQb canonQinit by simp
  qed
  have small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> d \<Longrightarrow> descartes_list_int a b Qinit \<le> 1"
    unfolding d_def
    by (rule rational_fast_descartes_list_int_delta_P_le1[OF Q0init canonQinit degne sfQinit])
  have len2Q: "Suc 0 < length Qinit" using len2 len_eq lenQb by simp
  have lenbQ: "length Qinit + 2 < max_snat LENGTH(gmp_poly_len)"
    using lenb3 len_eq lenQb by simp
  have lrQ: "(0::int) < 2 ^ kneg" by simp
  have Q_eq: "Qinit = carried_init_same_den 0 (2 ^ 0) (2 ^ kneg) Qb"
    unfolding Qinit_def by (simp add: split_init_pow2_l0_eq_scale_poly_list)
  have rp_len: "0 < length Qb" using len2 lenQb by (cases xs) auto
  have Qb_small: "length Qb < 1099511627776" using xs_small lenQb by simp
  have depth: "(\<forall>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu d (0, 1)) \<longrightarrow>
           kD * (length Qb - 1) < max_snat LENGTH(gmp_poly_len)) \<and>
        (\<forall>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu d (0, 1)) \<longrightarrow>
           (kD + 1) * length Qb < 1099511627776)"
    using depth_at unfolding hybrid_depth_cap_def Qinit_def Qb_def d_def by (simp add: Let_def)
  \<comment> \<open>\<^bold>\<open>\<open>mucap\<close> is INHERITED, not new\<close>: the base bundle's own \<open>\<mu>\<close> clause, which arrives already
     instantiated at this \<open>k\<close> as \<open>cap_at\<close>. Note it is stated at \<open>length (refl_list xs)\<close>, which
     \<open>lenQb\<close> equates to \<open>length xs\<close>.\<close>
  have mucap: "int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) + 1
               < int (max_snat LENGTH(gmp_poly_len))"
    using cap_at
    unfolding split_cap_def Qinit_def Qb_def d_def
    by (simp add: Let_def dyadic_iv_interval_mu_eq_rational)
  have kcap: "int 0 + int (2 ^ newton_pol_ecap + 2) * int (dyadic_iv_interval_mu d (0, 1))
              \<le> hybrid_root_potential d 0"
    by (rule hybrid_seed_kcap)
  show ?thesis
    unfolding hybrid_expol_int_pre_def prod.case Qinit_def[symmetric] d_def[symmetric]
    using delta_pos len2Q small_fast sfQinit Q0init canonQinit lenbQ lrQ
          mucap kcap Q_eq rp_len Qb_small depth
    by simp
qed

section \<open>Pipeline stage correctness + capstone\<close>

text \<open>The positive-half solve meets the sound+complete SPEC. Same shape as
  @{thm [source] bail_split_pos_solve_half}, with three hybrid differences: the extra
  \<open>rp \<leftarrow> poly_copy_monadic xs\<close> stage (\<open>rp = xs\<close>, so its spec is
  @{thm [source] poly_copy_correct}, not the scale-by-1 clone the ET/bail route used);
  the solver bound is the \<open>\<exists>pol\<close> @{thm [source] hybrid_main_list_correct}; and the frame
  scaling therefore runs at an OBTAINED policy.\<close>
lemma hybrid_split_pos_solve_half_strong:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_hybrid_pre xs"
  \<comment> \<open>\<open>dyadic_interval_vec_invar\<close> is the third conjunct: \<open>hybrid_expol_int_refine\<close> supplies it in the
     \<open>solver\<close> fact below. The power-substitution entry needs it, and it cannot be re-derived downstream,
     since nothing outside this proof sees the refinement.\<close>
  \<comment> \<open>\<open>length \<dots> + 1 < max_snat\<close> is the fourth conjunct, the bound on the number of emitted intervals.
     @{const hybrid_budget_invar} is an unguarded conjunct of @{const hybrid_state_invar}, so it still
     holds at the loop's exit.\<close>
  shows "hybrid_split_pos_solve_monadic xs
    \<le> SPEC (\<lambda>accP. dyadic_interval_vec_invar accP \<and>
      length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        dsc_pair_ok (map_poly of_int (Poly xs) :: real poly)
                    (of_rat (fst I), of_rat (snd I))) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          (of_rat (fst I) < x \<and> x < of_rat (snd I))
          \<or> (of_rat (fst I) = x \<and> of_rat (snd I) = x))))"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    unfolding dsc_isolate_all_split_hybrid_pre_def by simp
  from pre' have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    unfolding dsc_isolate_all_split_pre_def by auto
  have P0: "Poly xs \<noteq> 0" using sfxs unfolding square_free_def by simp
  \<comment> \<open>Both capacity clauses are stated about the producer, and the hybrid one is merged into the same
     \<open>SPEC\<close> as the base one: only one \<open>\<le> SPEC\<close> fact fires per producer call, so otherwise only one of them
     would reach the continuation. \<open>kiou_le_SPEC_conj\<close> makes the merge valid.\<close>
  have capY: "kiou_bound_k_monadic xs \<le> SPEC (split_cap xs)"
    using pre' unfolding dsc_isolate_all_split_pre_def by (simp add: Let_def)
  have capD: "kiou_bound_k_monadic xs \<le> SPEC (hybrid_depth_cap xs)"
    using pre unfolding dsc_isolate_all_split_hybrid_pre_def by (simp add: Let_def)
  have merged: "kiou_bound_k_monadic xs \<le> SPEC (\<lambda>k.
      ((\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ k) \<and>
       k * length xs < max_snat LENGTH(gmp_poly_len) \<and>
       k < max_snat LENGTH(gmp_poly_len) \<and> split_cap xs k)
      \<and> hybrid_depth_cap xs k)"
    by (rule kiou_le_SPEC_conj[OF kiou_bound_k_monadic_spec_capped[OF len2 lastnz hr capY] capD])
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  show ?thesis
    unfolding hybrid_split_pos_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg merged[THEN order_trans])
    subgoal using len2 lenb by (cases xs) auto
    subgoal using lenb by simp
    subgoal premises p using p by simp
    subgoal premises p using p by simp
    subgoal premises kp for kpos
    proof -
      from kp have kpos_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ kpos"
        and kpos_cap: "kpos * length xs < max_snat LENGTH(gmp_poly_len)"
        and kpos_lt: "kpos < max_snat LENGTH(gmp_poly_len)"
        and cap_at: "split_cap xs kpos"
        and depth_at: "hybrid_depth_cap xs kpos" by blast+
      define Pinit0 where "Pinit0 = scale_poly_list (2 ^ kpos) xs"
      have rp_eq: "poly_copy_monadic xs \<le> RETURN xs"
        by (rule poly_copy_correct[OF lenb])
      have Pinit_eq: "split_init_pow2_l0_monadic kpos xs \<le> RETURN Pinit0"
        using split_init_pow2_l0_monadic_correct[OF lenb kpos_cap]
        by (simp add: Pinit0_def split_init_pow2_l0_eq_scale_poly_list)
      have npre: "hybrid_expol_int_pre
          (delta_P (map_poly of_int (Poly Pinit0) :: real poly))
          (((((split_pipeline_e0, 0), 2 ^ kpos), 0), Pinit0), xs)"
        using dsc_isolate_all_split_pos_hybrid_pre[OF pre kpos_sound cap_at depth_at]
        unfolding Pinit0_def by simp
      have p0P: "degree (Poly Pinit0) \<noteq> 0"
      proof -
        have sfP: "square_free (map_poly of_int (Poly Pinit0) :: real poly)"
          using npre unfolding hybrid_expol_int_pre_def prod.case by blast
        have P0init: "Poly Pinit0 \<noteq> 0" using sfP unfolding square_free_def by simp
        have len2P: "Suc 0 < length Pinit0"
          using npre unfolding hybrid_expol_int_pre_def prod.case by blast
        have canonP: "coeffs (Poly Pinit0) = Pinit0"
          using npre unfolding hybrid_expol_int_pre_def prod.case by blast
        have "length (coeffs (Poly Pinit0)) = degree (Poly Pinit0) + 1"
          using P0init by (rule length_coeffs)
        thus ?thesis using len2P canonP by simp
      qed
      have sfP: "square_free (map_poly of_int (Poly Pinit0) :: real poly)"
        using npre unfolding hybrid_expol_int_pre_def prod.case by blast
      have len2P: "Suc 0 < length Pinit0"
        using npre unfolding hybrid_expol_int_pre_def prod.case by blast
      have lenbP: "length Pinit0 + 2 < max_snat LENGTH(gmp_poly_len)"
        using npre unfolding hybrid_expol_int_pre_def prod.case by blast
      have lrP: "(0::int) < 2 ^ kpos" by simp
      \<comment> \<open>\<^bold>\<open>The solver bound is taken from the keystone rather than from the composition-side
         refinement.\<close> @{const hybrid_expol_int_spec} is the composition specification and states only
         what the implementation's HNR consumes, so it omits the accumulator cap; strengthening it would
         change @{const hybrid_main_list_impl}'s \<open>hfref\<close>. @{thm [source] hybrid_main_list_correct_strong}
         is the same fact one layer up, about the same \<open>hybrid_main_list_monadic\<close>, and carries the cap.
         \<open>npre\<close> is @{const hybrid_expol_int_pre}, whose bundle is the keystone's hypotheses, so both routes
         take the same input.\<close>
      have solver: "hybrid_main_list_monadic split_pipeline_e0 0 (2 ^ kpos) 0 Pinit0 xs
          \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
              length (dyadic_interval_vec_triples acc) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
              (\<exists>pol. mset (dyadic_iv_acc_ivs 0 (2 ^ kpos) 0 (dyadic_interval_vec_triples acc))
                = mset (newdsc_pol_bail_int pol 0 1 split_pipeline_e0 0 (Poly Pinit0))))"
        by (rule hybrid_main_list_correct_strong[where
                   \<delta> = "delta_P (map_poly of_int (Poly Pinit0) :: real poly)"])
           (use npre[unfolded hybrid_expol_int_pre_def prod.case] in auto)
      show ?thesis
        apply (refine_vcg rp_eq[THEN order_trans]
            Pinit_eq[unfolded Pinit0_def, THEN order_trans]
            mpz_pow2_monadic_spec[OF kpos_lt, THEN order_trans]
            solver[unfolded Pinit0_def, THEN order_trans])
        \<comment> \<open>the post-copy ASSERT \<open>0 < length rp \<and> length rp + 1 < max_snat\<close> at \<open>rp = xs\<close>. \<open>(cases xs)\<close>, not
           bare \<open>simp\<close>: \<open>0 < length xs\<close> normalises to \<open>xs \<noteq> []\<close>, which \<open>simp\<close> will not then derive from
           \<open>2 \<le> length xs\<close>.\<close>
        subgoal using len2 lenb by (cases xs) auto
        subgoal using len2 lenb by (cases xs) auto
        subgoal using len2P lenbP unfolding Pinit0_def by simp
        subgoal using len2P lenbP unfolding Pinit0_def by simp
        \<comment> \<open>The \<open>dyadic_interval_vec_invar\<close> conjunct. It is the first conjunct of the SPEC, so it is the first
           of these subgoals; it comes from \<open>solver\<close>'s postcondition, which \<open>refine_vcg\<close> has put in
           \<open>prems\<close>.\<close>
        subgoal premises prems for x using prems by blast
        \<comment> \<open>the accumulator-cap conjunct, second in the SPEC and so second here, from the same source.\<close>
        subgoal premises prems for x using prems by blast
        subgoal premises prems for x
        proof -
          from prems obtain pol where acc_eq:
            "mset (dyadic_iv_acc_ivs 0 (2 ^ kpos) 0 (dyadic_interval_vec_triples x))
              = mset (newdsc_pol_bail_int pol 0 1 split_pipeline_e0 0
                        (Poly (scale_poly_list (2 ^ kpos) xs)))" by auto
          show ?thesis
            using dsc_carried_hybrid_pos_half_sound_strong[OF P0 lrP p0P[unfolded Pinit0_def]
                sfP[unfolded Pinit0_def] acc_eq]
            by simp
        qed
        subgoal premises prems for x xa
        proof -
          from prems obtain pol where acc_eq:
            "mset (dyadic_iv_acc_ivs 0 (2 ^ kpos) 0 (dyadic_interval_vec_triples x))
              = mset (newdsc_pol_bail_int pol 0 1 split_pipeline_e0 0
                        (Poly (scale_poly_list (2 ^ kpos) xs)))" by auto
          from prems have xa_pos: "0 < xa" and root: "ripoly (Poly xs) xa = 0" by auto
          have xa_lt: "xa < of_int ((2::int) ^ kpos)"
            using kpos_sound[rule_format, OF xa_pos] root by (simp add: of_int_power)
          show ?thesis
            using dsc_carried_hybrid_pos_half_complete_strong[OF P0 lrP p0P[unfolded Pinit0_def]
                sfP[unfolded Pinit0_def] acc_eq xa_pos xa_lt root]
            by simp
        qed
        done
    qed
    done
qed

text \<open>The original positive-half statement, kept so the downstream chain and its use sites
  are unaffected. A strict weakening of the pinned form: \<open>I\<close>'s own \<open>of_rat\<close> image witnesses
  the existential (@{thm [source] real_to_rat_pair_of_rat}).\<close>
lemma hybrid_split_pos_solve_half:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_hybrid_pre xs"
  shows "hybrid_split_pos_solve_monadic xs
    \<le> SPEC (\<lambda>accP. (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
  \<comment> \<open>Written with \<open>weaken_SPEC\<close> rather than \<open>order_trans\<close> and \<open>auto intro:\<close>. The existential's witness is
     \<open>(of_rat (fst I), of_rat (snd I))\<close>, and \<open>auto\<close> does not find it: applying the witness rule needs the
     bounded-\<open>\<forall>\<close> hypothesis instantiated at the pair \<open>auto\<close> has just destructured, with \<open>fst (ab, ba)\<close>
     reduced, two steps it does not chain.\<close>
proof (rule weaken_SPEC[OF hybrid_split_pos_solve_half_strong[OF pre]])
  fix accP :: gmp_dyadic_interval_vec
  \<comment> \<open>\<open>dyadic_interval_vec_invar\<close> and the accumulator cap are the first two conjuncts of the strong form,
     so they are assumed here too (a corollary that weakens the strong statement must assume all of its
     conjuncts) and then dropped. This \<open>assume\<close> restates the strong SPEC, so a conjunct added there must be
     added here; a mismatch is reported at the closing \<open>show\<close>, not at the \<open>assume\<close>.\<close>
  assume A: "dyadic_interval_vec_invar accP \<and>
      length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        dsc_pair_ok (map_poly of_int (Poly xs) :: real poly)
                    (of_rat (fst I), of_rat (snd I))) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          (of_rat (fst I) < x \<and> x < of_rat (snd I))
          \<or> (of_rat (fst I) = x \<and> of_rat (snd I) = x)))"
  have sound': "\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and>
              dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J"
  proof
    fix I assume "I \<in> set (dyadic_interval_vec_to_list accP)"
    then have "dsc_pair_ok (map_poly of_int (Poly xs) :: real poly)
                 (of_rat (fst I), of_rat (snd I))" using A by blast
    thus "\<exists>J. I = real_to_rat_pair J \<and>
              dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J"
      by (rule dsc_pair_ok_of_rat_witness_pair)
  qed
  \<comment> \<open>the completeness clause weakens the same way, through the covering twin of the witness rule, with
     \<open>I\<close>'s own \<open>of_rat\<close> image as the witness\<close>
  have complete': "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)"
  proof (intro allI impI)
    fix x :: real assume "0 < x" and "ripoly (Poly xs) x = 0"
    then obtain I where Iin: "I \<in> set (dyadic_interval_vec_to_list accP)"
      and c: "(of_rat (fst I) < x \<and> x < of_rat (snd I))
              \<or> (of_rat (fst I) = x \<and> of_rat (snd I) = x)" using A by blast
    show "\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
            \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
      using Iin cover_of_rat_witness_pair[OF c] by blast
  qed
  from sound' complete'
  show "(\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. I = real_to_rat_pair J \<and>
            dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))" by blast
qed

text \<open>NEGATIVE half. Structurally the positive half prefixed with the reflect front
  (\<open>Qb = refl_list xs\<close>), and here \<open>Qb\<close> serves as BOTH the reflected input and the retained
  escalation root --- the pipeline passes it in both roles
  (\<open>hybrid_main_list_monadic e0 zln rneg 0 Qinit Qb\<close>).\<close>
lemma hybrid_split_neg_solve_half:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_hybrid_pre xs"
  shows "hybrid_split_neg_solve_monadic xs
    \<le> SPEC (\<lambda>accQ. (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. I = real_to_rat_pair J \<and>
            dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    unfolding dsc_isolate_all_split_hybrid_pre_def by simp
  from pre' have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    unfolding dsc_isolate_all_split_pre_def by auto
  have xsne: "xs \<noteq> []" using len2 by auto
  have sfrefl: "square_free (map_poly of_int (Poly (refl_list xs)) :: real poly)"
    using square_free_pcompose_linear[OF sfxs, of "-1"]
    by (simp add: refl_list_eq_scale_poly_list_neg1 Poly_scale_poly_list_eq_pcompose)
  have Q0: "Poly (refl_list xs) \<noteq> 0" using sfrefl unfolding square_free_def by simp
  have lastnzQb: "last (refl_list xs) \<noteq> 0" using last_refl_list_nz[OF xsne lastnz] .
  have hrQb: "kiou_headroom (refl_list xs)" using kiou_headroom_refl_list[of xs] hr by simp
  have len2Qb: "2 \<le> length (refl_list xs)" using len2 by simp
  \<comment> \<open>Extracted, then MERGED with the hybrid depth clause so both reach the
     continuation through the single \<open>\<le> SPEC\<close> fact that fires for this producer.\<close>
  have capYQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (split_cap (refl_list xs))"
    using pre' unfolding dsc_isolate_all_split_pre_def by (auto simp: Let_def)
  have capDQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (hybrid_depth_cap (refl_list xs))"
    using pre unfolding dsc_isolate_all_split_hybrid_pre_def by (auto simp: Let_def)
  have mergedQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (\<lambda>k.
      ((\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ k) \<and>
       k * length (refl_list xs) < max_snat LENGTH(gmp_poly_len) \<and>
       k < max_snat LENGTH(gmp_poly_len) \<and> split_cap (refl_list xs) k)
      \<and> hybrid_depth_cap (refl_list xs) k)"
    by (rule kiou_le_SPEC_conj[OF kiou_bound_k_monadic_spec_capped[OF len2Qb lastnzQb hrQb capYQb]
          capDQb])
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have lenbQb: "length (refl_list xs) + 1 < max_snat LENGTH(gmp_poly_len)" using lenb by simp
  have copy_correct: "poly_copy_monadic xs \<le> RETURN xs"
    by (rule poly_copy_correct[OF lenb])
  have poly_reflect_correct: "poly_reflect_in_place_monadic xs \<le> RETURN (refl_list xs)"
    using poly_reflect_in_place_correct[OF lenb] by (simp add: refl_list_def)
  show ?thesis
    unfolding hybrid_split_neg_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg
        copy_correct[THEN order_trans]
        poly_reflect_correct[THEN order_trans]
        mergedQb[THEN order_trans])
    subgoal using len2Qb lenb lenbQb by (cases xs) auto
    subgoal using len2Qb lenb lenbQb by auto
    subgoal using len2Qb lenb lenbQb by auto
    subgoal premises p using p by simp
    subgoal premises p using p by simp
    subgoal premises kp for kneg
    proof -
      from kp have kneg_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ kneg"
        and kneg_cap: "kneg * length (refl_list xs) < max_snat LENGTH(gmp_poly_len)"
        and kneg_lt: "kneg < max_snat LENGTH(gmp_poly_len)"
        and cap_at: "split_cap (refl_list xs) kneg"
        and depth_at: "hybrid_depth_cap (refl_list xs) kneg" by blast+
      define Qinit0 where "Qinit0 = scale_poly_list (2 ^ kneg) (refl_list xs)"
      have Qinit_eq: "split_init_pow2_l0_monadic kneg (refl_list xs) \<le> RETURN Qinit0"
        using split_init_pow2_l0_monadic_correct[OF lenbQb kneg_cap]
        by (simp add: Qinit0_def split_init_pow2_l0_eq_scale_poly_list)
      have npre: "hybrid_expol_int_pre
          (delta_P (map_poly of_int (Poly Qinit0) :: real poly))
          (((((split_pipeline_e0, 0), 2 ^ kneg), 0), Qinit0), refl_list xs)"
        using dsc_isolate_all_split_neg_hybrid_pre[OF pre kneg_sound cap_at depth_at]
        unfolding Qinit0_def by simp
      have sfQ: "square_free (map_poly of_int (Poly Qinit0) :: real poly)"
        using npre unfolding hybrid_expol_int_pre_def prod.case by blast
      have Q0init: "Poly Qinit0 \<noteq> 0" using sfQ unfolding square_free_def by simp
      have len2Q: "Suc 0 < length Qinit0"
        using npre unfolding hybrid_expol_int_pre_def prod.case by blast
      have canonQ: "coeffs (Poly Qinit0) = Qinit0"
        using npre unfolding hybrid_expol_int_pre_def prod.case by blast
      have lenbQ: "length Qinit0 + 2 < max_snat LENGTH(gmp_poly_len)"
        using npre unfolding hybrid_expol_int_pre_def prod.case by blast
      have q0Q: "degree (Poly Qinit0) \<noteq> 0"
      proof -
        have "length (coeffs (Poly Qinit0)) = degree (Poly Qinit0) + 1"
          using Q0init by (rule length_coeffs)
        thus ?thesis using len2Q canonQ by simp
      qed
      have lrQ: "(0::int) < 2 ^ kneg" by simp
      have solver: "hybrid_main_list_monadic split_pipeline_e0 0 (2 ^ kneg) 0 Qinit0 (refl_list xs)
          \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
              (\<exists>pol. mset (dyadic_iv_acc_ivs 0 (2 ^ kneg) 0 (dyadic_interval_vec_triples acc))
                = mset (newdsc_pol_bail_int pol 0 1 split_pipeline_e0 0 (Poly Qinit0))))"
        using hybrid_expol_int_refine[where
                \<delta> = "delta_P (map_poly of_int (Poly Qinit0) :: real poly)"] npre
        by (auto simp: fref_def nres_rel_def hybrid_expol_int_spec_def)
      show ?thesis
        apply (refine_vcg Qinit_eq[unfolded Qinit0_def, THEN order_trans]
            mpz_pow2_monadic_spec[OF kneg_lt, THEN order_trans]
            solver[unfolded Qinit0_def, THEN order_trans])
        subgoal using len2Q lenbQ unfolding Qinit0_def by simp
        subgoal using len2Q lenbQ unfolding Qinit0_def by simp
        subgoal using len2Qb lenbQb by simp
        subgoal premises prems for x
        proof -
          from prems obtain pol where acc_eq:
            "mset (dyadic_iv_acc_ivs 0 (2 ^ kneg) 0 (dyadic_interval_vec_triples x))
              = mset (newdsc_pol_bail_int pol 0 1 split_pipeline_e0 0
                        (Poly (scale_poly_list (2 ^ kneg) (refl_list xs))))" by auto
          show ?thesis
            using dsc_carried_hybrid_pos_half_sound[OF Q0 lrQ q0Q[unfolded Qinit0_def]
                sfQ[unfolded Qinit0_def] acc_eq]
            by simp
        qed
        subgoal premises prems for x xa
        proof -
          from prems obtain pol where acc_eq:
            "mset (dyadic_iv_acc_ivs 0 (2 ^ kneg) 0 (dyadic_interval_vec_triples x))
              = mset (newdsc_pol_bail_int pol 0 1 split_pipeline_e0 0
                        (Poly (scale_poly_list (2 ^ kneg) (refl_list xs))))" by auto
          from prems have xa_pos: "0 < xa" and root: "ripoly (Poly (refl_list xs)) xa = 0" by auto
          have xa_lt: "xa < of_int ((2::int) ^ kneg)"
            using kneg_sound[rule_format, OF xa_pos] root by (simp add: of_int_power)
          show ?thesis
            using dsc_carried_hybrid_pos_half_complete[OF Q0 lrQ q0Q[unfolded Qinit0_def]
                sfQ[unfolded Qinit0_def] acc_eq xa_pos xa_lt root]
            by simp
        qed
        done
    qed
    done
qed

text \<open>\<^bold>\<open>The pipeline capstone for the hybrid solver\<close>: @{const hybrid_isolate_all_split_main} is sound
  and complete against \<open>xs\<close> in each half's own frame, and the exact-zero flag is correct. The second
  conjunct of each half rules out an empty result: it requires every real root of \<open>xs\<close> / \<open>refl_list xs\<close> in
  \<open>(0,\<infinity>)\<close> to be covered.

  \<^bold>\<open>The negative half\<close>: \<open>accQ\<close> is stated against \<open>refl_list xs\<close>, i.e. in reflected coordinates, which is
  the interface's convention: a caller negates and swaps both endpoints of a negative-half interval.\<close>
theorem hybrid_isolate_all_split_main_correct:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_hybrid_pre xs"
  shows "hybrid_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accQ, xs0).
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)) \<and>
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. I = real_to_rat_pair J \<and>
            dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)) \<and>
      xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    unfolding dsc_isolate_all_split_hybrid_pre_def by simp
  have len2: "2 \<le> length xs" using pre' unfolding dsc_isolate_all_split_pre_def by auto
  show ?thesis
    unfolding hybrid_isolate_all_split_main_def PR_CONST_def
    apply (refine_vcg
        hybrid_split_pos_solve_half[OF pre, THEN order_trans]
        hybrid_split_neg_solve_half[OF pre, THEN order_trans]
        dsc_isolate_all_split_zero_check_correct[OF pre', THEN order_trans])
    using len2 by auto
qed

text \<open>Explicit termination corollary --- every loop below this point is a well-founded
  \<open>RECT\<close>/\<open>WHILET\<close>, so \<open>\<le> SPEC\<close> genuinely excludes non-termination.\<close>
corollary hybrid_isolate_all_split_main_terminates:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_hybrid_pre xs"
  shows "nofail (hybrid_isolate_all_split_main xs)"
  using hybrid_isolate_all_split_main_correct[OF pre] by (rule SPEC_nofail)

text \<open>\<^bold>\<open>The pinned positive clause.\<close> The capstone above states its soundness as
  \<open>\<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok \<dots> J\<close>, which is not an isolation statement about the emitted
  interval \<open>I\<close>: @{const real_to_rat_pair} is not injective, so the existential witness is unconstrained on
  an irrational endpoint (see @{thm [source] dsc_carried_polr_pos_half_sound_strong}). The multiset
  equality against @{const dsc_int} does not depend on it, but the power-substitution back-map needs
  isolation on the emitted dyadic numerators.

  This variant states the positive half's soundness at \<open>I\<close>'s own \<open>of_rat\<close> image. Only the positive half is
  strengthened: the power-substitution entry frees the reduced solve's negative vector unused (each
  positive \<open>Q\<close>-root lifts to \<open>\<plusminus>y\<close> under the even exponent).\<close>
theorem hybrid_isolate_all_split_main_correct_pos_pinned:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_hybrid_pre xs"
  shows "hybrid_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accQ, xs0).
      dyadic_interval_vec_invar accP \<and>
      length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        dsc_pair_ok (map_poly of_int (Poly xs) :: real poly)
                    (of_rat (fst I), of_rat (snd I))) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          (of_rat (fst I) < x \<and> x < of_rat (snd I))
          \<or> (of_rat (fst I) = x \<and> of_rat (snd I) = x))) \<and>
      xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    unfolding dsc_isolate_all_split_hybrid_pre_def by simp
  have len2: "2 \<le> length xs" using pre' unfolding dsc_isolate_all_split_pre_def by auto
  show ?thesis
    unfolding hybrid_isolate_all_split_main_def PR_CONST_def
    apply (refine_vcg
        hybrid_split_pos_solve_half_strong[OF pre, THEN order_trans]
        hybrid_split_neg_solve_half[OF pre, THEN order_trans]
        dsc_isolate_all_split_zero_check_correct[OF pre', THEN order_trans])
    using len2 by auto
qed

end
