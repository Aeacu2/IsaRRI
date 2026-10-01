theory Hybrid_Capstone
  imports Hybrid_Keystone
begin

text \<open>\<^bold>\<open>The composition block\<close> for the hybrid solver: its Sepref implementation meets the
  \<open>\<exists>pol\<close> multiset specification. This is the implementation-side step (HNR composition), apart from
  the abstract refinement in \<open>Hybrid_Keystone\<close>.

  \<open>Kiou_Bound_Hybrid_Reflect\<close> uses \<open>hybrid_expol_int_refine\<close>, \<open>hybrid_expol_pol_sound\<close>,
  \<open>hybrid_expol_pol_complete\<close> and \<open>hybrid_expol_int_set_image\<close> from here. (They are cited as
  plain text rather than \<open>@{thm}\<close> antiquotations because they are proved below this header.)\<close>

section \<open>FCOMP --- the hybrid solver's implementation satisfies the \<open>\<exists>pol\<close> spec\<close>

text \<open>\<^bold>\<open>The implementation-side capstone.\<close> Structurally the same as the composition block of
  \<open>Bail_Loop_Refine\<close>, with two differences:

  \<^item> the specification's policy is existential, not @{const pol_final}. That costs nothing, because
    every abstract theorem it is consumed by leaves the policy free
    (@{thm [source] newdsc_pol_bail_terminates_squarefree},
    @{thm [source] newdsc_pol_bail_sound}, @{thm [source] newdsc_pol_bail_complete}), and
    @{const hybrid_polr_of_pol} with @{thm [source] hybrid_polr_of_pol_rel} build the real
    partner of the obtained rational witness, so the \<open>polrel\<close> side condition of the int/real
    bridge is a proved fact rather than a hypothesis.
  \<^item> the arity is \<open>uncurry5\<close>: the retained escalation root \<open>rp\<close> is a sixth argument.

  \<^bold>\<open>Not checked at run time\<close>: \<open>hybrid_expol_int_pre\<close> below. Its conjuncts \<open>P_eq\<close> (the retained
  \<open>rp\<close> is the root \<open>P\<close> was carried from), \<open>rp_small\<close>, and the two depth-quantified bounds
  \<open>k_depth_safe\<close>/\<open>g_room\<close> are obligations on the caller.\<close>

subsection \<open>The keystone's premises imply the impl's own HNR preconditions\<close>

text \<open>@{const hybrid_main_list_impl}'s \<open>hfref\<close> carries six word-capacity side conditions.
  None of them needs to be stated separately at the ABI: they are all consequences of the
  keystone's premises, by exactly the derivation @{thm [source] hybrid_main_list_correct}
  runs internally (\<open>lenrp\<close>/\<open>rp2\<close> from \<open>P_eq\<close>, then \<open>kfit\<close> from \<open>k_depth_safe\<close> at a
  degree-\<open>\<ge> 1\<close> root). Extracted here so the \<open>hfref_weaken_pre\<close> step below can shed them in
  one move --- bail had to STATE \<open>k + 1 < max_snat\<close> in its \<open>_pre\<close> because it has no \<open>rp\<close> and
  hence no \<open>k_depth_safe\<close> to derive it from.\<close>
lemma hybrid_expol_hnr_bounds:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and len2: "Suc 0 < length P"
    and lenb: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
    and P_eq: "P = carried_init_same_den l_num (2 ^ k) r_num rp"
    and k_depth_safe: "\<And>kD. int kD \<le> int k + int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<Longrightarrow>
        kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "0 < length P \<and>
         length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
         k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
         0 < length rp \<and>
         length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
         k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
proof -
  have potK: "hybrid_root_potential \<delta> k
              = int k + int (2 ^ newton_pol_ecap + 2)
                  * int (dyadic_iv_interval_mu \<delta> (0, 1))"
    by (simp add: hybrid_root_potential_def)
  have lenrp: "length rp = length P"
    using P_eq by (simp add: truncate_length_carried_init_same_den)
  have rp2: "2 \<le> length rp" using len2 lenrp by simp
  have bud2: "1 \<le> dyadic_iv_interval_mu \<delta> (0, 1)"
    by (rule dyadic_iv_interval_mu_ge_1[OF \<delta>_pos]) simp
  have pot_ge: "int k + 258 \<le> hybrid_root_potential \<delta> k"
  proof -
    have "(258::int) * 1 \<le> 258 * int (dyadic_iv_interval_mu \<delta> (0, 1))"
      using bud2 by (intro mult_left_mono) simp_all
    thus ?thesis by (simp add: hybrid_root_potential_def newton_pol_ecap_def)
  qed
  \<comment> \<open>\<^bold>\<open>Destructure \<open>length rp\<close> first.\<close> Left as \<open>length rp - 1\<close> the goal normalises to
     \<open>0 < kD \<longrightarrow> Suc 0 \<le> length rp - Suc 0\<close>, which \<open>simp\<close> does not close from \<open>2 \<le> length rp\<close>.\<close>
  have kfit: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k \<Longrightarrow>
                 kD < max_snat LENGTH(gmp_poly_len)"
  proof -
    fix kD assume h: "int kD \<le> hybrid_root_potential \<delta> k"
    have A: "kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
      using k_depth_safe[of kD] h potK by simp
    obtain m where rpm: "length rp = Suc m" and m1: "1 \<le> m"
      using rp2 by (cases "length rp") auto
    have B: "kD \<le> kD * (length rp - 1)"
      using rpm m1 mult_le_mono2[of 1 m kD] by simp
    show "kD < max_snat LENGTH(gmp_poly_len)" using B A by (rule le_less_trans)
  qed
  have k1: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    using kfit[of "k + 1"] pot_ge by simp
  have krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    using k_depth_safe[of k] pot_ge potK by simp
  show ?thesis using len2 lenb lenrp k1 krp by simp
qed

subsection \<open>The \<open>\<exists>pol\<close> multiset spec and its precondition bundle\<close>

text \<open>The abstract spec: the returned dyadic vector's @{const dyadic_iv_acc_ivs} reading is,
  as a MULTISET, what @{const newdsc_pol_bail_int} produces on \<open>[0,1]\<close> at SOME policy. The
  existential is the whole point --- the lazy implementation's push-time ambiguous sentinel makes
  its \<open>\<sigma>\<close>, hence its gate decisions, hence its tree, genuinely diverge from bail's concrete
  program, and \<open>\<exists>pol\<close> absorbs exactly that divergence.\<close>
definition hybrid_expol_int_spec ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"hybrid_expol_int_spec e0 l_num r_num k P rp \<equiv>
  SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
    (\<exists>pol. mset (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
      = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly P))))"

text \<open>The precondition bundle, parameterised by the subdivision granularity \<open>\<delta>\<close>: \<^bold>\<open>exactly\<close>
  @{thm [source] hybrid_main_list_correct}'s hypotheses, meta-quantification turned into
  object-level \<open>\<forall>\<close>, and nothing added --- the impl's own six word caps are derived from these
  by @{thm [source] hybrid_expol_hnr_bounds} rather than assumed.\<close>
definition hybrid_expol_int_pre ::
  "real \<Rightarrow> (((((nat \<times> int) \<times> int) \<times> nat) \<times> gmp_poly) \<times> gmp_poly) \<Rightarrow> bool" where
"hybrid_expol_int_pre \<delta> x \<longleftrightarrow>
  (case x of (((((e0, l_num), r_num), k), P), rp) \<Rightarrow>
    \<delta> > 0 \<and>
    Suc 0 < length P \<and>
    (\<forall>a b. a < b \<longrightarrow> of_rat b - of_rat a \<le> \<delta> \<longrightarrow> descartes_list_int a b P \<le> 1) \<and>
    square_free (map_poly of_int (Poly P) :: real poly) \<and>
    Poly P \<noteq> 0 \<and> coeffs (Poly P) = P \<and>
    length P + 2 < max_snat LENGTH(gmp_poly_len) \<and>
    l_num < r_num \<and>
    int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
      < int (max_snat LENGTH(gmp_poly_len)) \<and>
    int k + int (2 ^ newton_pol_ecap + 2) * int (dyadic_iv_interval_mu \<delta> (0, 1))
      \<le> hybrid_root_potential \<delta> k \<and>
    P = carried_init_same_den l_num (2 ^ k) r_num rp \<and>
    0 < length rp \<and>
    length rp < 1099511627776 \<and>
    (\<forall>kD. int kD \<le> int k + int (2 ^ newton_pol_ecap + 2)
             * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<longrightarrow>
       kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)) \<and>
    (\<forall>kD. int kD \<le> int k + int (2 ^ newton_pol_ecap + 2)
             * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<longrightarrow>
       (kD + 1) * length rp < 1099511627776))"

text \<open>The six impl-side word caps, read off the bundle.\<close>
lemma hybrid_expol_int_pre_bounds:
  fixes \<delta> :: real
  assumes pre: "hybrid_expol_int_pre \<delta> (((((e0, l_num), r_num), k), P), rp)"
  shows "0 < length P \<and>
         length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
         k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
         0 < length rp \<and>
         length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
         k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
proof -
  \<comment> \<open>\<^bold>\<open>Unfold the raw definition rather than \<open>simp add: \<dots>_def\<close>.\<close> The bundle contains
     \<open>P = carried_init_same_den \<dots> rp\<close>, so as a simp rule that conjunct rewrites \<open>length P\<close> to
     \<open>length rp\<close> in the goal while the conjunctive assumption stays unsplit, and
     \<open>Suc 0 < length P\<close> cannot be used. \<open>unfolding\<close> plus \<open>blast\<close> extracts each conjunct verbatim.\<close>
  from pre[unfolded hybrid_expol_int_pre_def prod.case]
  have \<delta>_pos: "\<delta> > 0"
    and len2: "Suc 0 < length P"
    and lenb: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
    and P_eq: "P = carried_init_same_den l_num (2 ^ k) r_num rp"
    and kds: "\<And>kD. int kD \<le> int k + int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<Longrightarrow>
        kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    by blast+
  show ?thesis by (rule hybrid_expol_hnr_bounds[OF \<delta>_pos len2 lenb P_eq kds])
qed

text \<open>The functional refinement, as the \<open>Id\<close>-fref \<open>FCOMP\<close> composes --- straight from the keystone.\<close>
lemma hybrid_expol_int_refine:
  "(uncurry5 hybrid_main_list_monadic, uncurry5 hybrid_expol_int_spec)
   \<in> [hybrid_expol_int_pre \<delta>]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI)
  unfolding hybrid_expol_int_pre_def hybrid_expol_int_spec_def
  apply clarsimp
  apply (rule hybrid_main_list_correct)
  apply auto
  done

text \<open>\<^bold>\<open>The capstone HNR theorem\<close>: the exported @{const hybrid_main_list_impl} --- borrowing
  the \<open>mpz_t\<close> endpoints, owning both pushed polynomials --- refines the \<open>\<exists>pol\<close>
  @{const newdsc_pol_bail_int} multiset spec. \<open>FCOMP\<close> of the impl's \<open>.refine\<close> with
  @{thm [source] hybrid_expol_int_refine}, then @{thm [source] hfref_weaken_pre} to shed the
  six normalized length/word preconditions via @{thm [source] hybrid_expol_int_pre_bounds}.\<close>
theorem hybrid_main_list_impl_refine_expol_int:
  "(uncurry5 hybrid_main_list_impl, uncurry5 hybrid_expol_int_spec)
   \<in> [hybrid_expol_int_pre \<delta>]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
proof -
  have h:
    "(uncurry5 hybrid_main_list_impl, uncurry5 hybrid_expol_int_spec)
     \<in> [\<lambda>(((((e0, l_num), r_num), k), P), rp).
          hybrid_expol_int_pre \<delta> (((((e0, l_num), r_num), k), P), rp) \<and>
          0 < length P \<and>
          length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
          k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
          0 < length rp \<and>
          length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
          k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d
        \<rightarrow> gmp_dyadic_interval_vec_assn"
    using hybrid_main_list_impl.refine[FCOMP hybrid_expol_int_refine[where \<delta>=\<delta>]]
    by (simp add: PR_CONST_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF _ h])
    apply (auto dest: hybrid_expol_int_pre_bounds)
    done
qed

text \<open>\<^bold>\<open>Termination\<close> --- immediate from the keystone's \<open>\<le> SPEC\<close> (\<open>nofail\<close>).\<close>
lemma hybrid_main_list_terminates:
  fixes \<delta> :: real
  assumes pre: "hybrid_expol_int_pre \<delta> (((((e0, l_num), r_num), k), P), rp)"
  shows "nofail (hybrid_main_list_monadic e0 l_num r_num k P rp)"
proof -
  have "hybrid_main_list_monadic e0 l_num r_num k P rp
        \<le> hybrid_expol_int_spec e0 l_num r_num k P rp"
    using hybrid_expol_int_refine[where \<delta> = \<delta>] pre
    by (auto simp: fref_def nres_rel_def pw_le_iff refine_pw_simps)
  thus ?thesis
    unfolding hybrid_expol_int_spec_def by (auto simp: pw_le_iff refine_pw_simps)
qed

subsection \<open>Soundness + completeness at the OBTAINED policy witness\<close>

text \<open>Both directions hold at \<^bold>\<open>every\<close> policy, so the keystone's existential witness costs
  nothing here. @{thm [source] newdsc_pol_bail_terminates_squarefree} is already policy-generic
  (its \<open>pol\<close> is free), which is why no \<open>_pol_final_dom\<close> analogue is needed --- the bail route
  went through @{thm [source] newdsc_pol_bail_pol_final_dom} only because it had a policy to
  fix.\<close>
theorem hybrid_expol_pol_sound:
  fixes P :: "int poly" and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "\<forall>I \<in> set (newdsc_pol_bail polr (degree P) a b e dk s (map_poly of_int P)).
           dsc_pair_ok (map_poly of_int P) I"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  have dom: "newdsc_pol_bail_dom (polr, degree P, a, b, e, dk, s, map_poly of_int P)"
    by (rule newdsc_pol_bail_terminates_squarefree[OF dne dle p0 sf ab])
  show ?thesis by (rule newdsc_pol_bail_sound[OF dom dle dne ab])
qed

theorem hybrid_expol_pol_complete:
  fixes P :: "int poly" and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "\<And>x. poly (map_poly of_int P :: real poly) x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol_bail polr (degree P) a b e dk s (map_poly of_int P)).
              fst I \<le> x \<and> x \<le> snd I)"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  have dom: "newdsc_pol_bail_dom (polr, degree P, a, b, e, dk, s, map_poly of_int P)"
    by (rule newdsc_pol_bail_terminates_squarefree[OF dne dle p0 sf ab])
  show "\<And>x. poly (map_poly of_int P :: real poly) x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol_bail polr (degree P) a b e dk s (map_poly of_int P)).
              fst I \<le> x \<and> x \<le> snd I)"
    by (rule newdsc_pol_bail_complete[OF dom dle dne])
qed

text \<open>The int/real image at the obtained witness. @{const hybrid_polr_of_pol} supplies the
  real partner and @{thm [source] hybrid_polr_of_pol_rel} discharges the bridge's \<open>polrel\<close>
  side condition outright --- the same constructive device the keystone's branch obligations
  use, reused here at the top of the chain. Only the SET image is needed, so the bridge's
  \<open>rev\<close> is irrelevant.\<close>
lemma hybrid_expol_int_set_image:
  fixes P :: "int poly" and pol :: newton_pol
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
  shows "set (newdsc_pol_bail_int pol 0 1 e0 k P)
       = real_to_rat_pair ` set (newdsc_pol_bail (hybrid_polr_of_pol pol) (degree P)
             (of_rat 0) (of_rat 1) e0 k 0 (map_poly of_int P))"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  have abr: "(of_rat (0::rat) :: real) < of_rat (1::rat)" by simp
  have ab: "(0::rat) < 1" by simp
  have dom: "newdsc_pol_bail_dom (hybrid_polr_of_pol pol, degree P,
      of_rat (0::rat), of_rat (1::rat), e0, k, 0, map_poly of_int P)"
    by (rule newdsc_pol_bail_terminates_squarefree[OF dne dle p0 sf abr])
  \<comment> \<open>\<^bold>\<open>Pin EVERY variable with \<open>where\<close> before \<open>OF\<close>\<close> --- the same idiom
     @{thm [source] hybrid_tree1_split_norel} carries, and for the same reason: against
     schematic \<open>?polr\<close>/\<open>?p\<close>/\<open>?P\<close> the higher-order \<open>polrel\<close> argument raises
     \<open>OF: multiple unifiers\<close>.\<close>
  have "rev (newdsc_pol_bail_int pol 0 1 e0 k P)
      = map real_to_rat_pair (newdsc_pol_bail (hybrid_polr_of_pol pol) (degree P)
          (of_rat 0) (of_rat 1) e0 k 0 (map_poly of_int P))"
    by (rule newdsc_pol_bail_int_eq_newdsc_pol_bail[where pol = pol
              and polr = "hybrid_polr_of_pol pol" and p = "degree P" and P = P
              and a = 0 and b = 1 and e = e0 and dk = k,
            OF dom refl P0 ab hybrid_polr_of_pol_rel])
  hence "set (rev (newdsc_pol_bail_int pol 0 1 e0 k P))
       = set (map real_to_rat_pair (newdsc_pol_bail (hybrid_polr_of_pol pol) (degree P)
             (of_rat 0) (of_rat 1) e0 k 0 (map_poly of_int P)))" by simp
  thus ?thesis by simp
qed

text \<open>The combined sound+complete spec, as a standalone \<open>SPEC\<close> so it can be \<open>FCOMP\<close>-composed
  through to the impl. \<^bold>\<open>Read the quantifier shape\<close> (memory
  \<open>verify-completeness-not-just-soundness\<close>): the \<open>\<exists>polr\<close> scopes over BOTH conjuncts, so one
  single policy witnesses soundness and completeness together --- which is exactly what the
  keystone delivers, and is strictly stronger than two independently-witnessed halves.\<close>
definition hybrid_expol_sound_complete_spec ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"hybrid_expol_sound_complete_spec e0 l_num r_num k P rp \<equiv>
  SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      (\<exists>polr.
        (\<forall>R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
          \<exists>J \<in> set (newdsc_pol_bail polr (degree (Poly P)) 0 1 e0 k 0
                       (map_poly of_int (Poly P) :: real poly)).
             R = real_to_rat_pair J \<and>
             dsc_pair_ok (map_poly of_int (Poly P) :: real poly) J) \<and>
        (\<forall>x. poly (map_poly of_int (Poly P) :: real poly) x = 0 \<longrightarrow> 0 < x \<longrightarrow> x < 1 \<longrightarrow>
          (\<exists>R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
            \<exists>J \<in> set (newdsc_pol_bail polr (degree (Poly P)) 0 1 e0 k 0
                         (map_poly of_int (Poly P) :: real poly)).
               R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))))"

text \<open>The exact-multiset spec implies the sound+complete spec: obtain the keystone's rational
  witness, take its real partner, then one \<open>set_mset_mset\<close> bridge and the two policy-generic
  directions above.\<close>
lemma hybrid_expol_int_spec_sound_complete:
  fixes \<delta> :: real
  assumes pre: "hybrid_expol_int_pre \<delta> (((((e0, l_num), r_num), k), P), rp)"
  shows "hybrid_expol_int_spec e0 l_num r_num k P rp
       \<le> hybrid_expol_sound_complete_spec e0 l_num r_num k P rp"
proof -
  let ?P_real = "map_poly of_int (Poly P) :: real poly"
  \<comment> \<open>raw unfold, for the reason spelled out at @{thm [source] hybrid_expol_int_pre_bounds}\<close>
  from pre[unfolded hybrid_expol_int_pre_def prod.case]
  have P0: "Poly P \<noteq> 0"
    and sf: "square_free ?P_real"
    and canon: "coeffs (Poly P) = P"
    and len2: "Suc 0 < length P"
    by blast+
  have dg: "degree (Poly P) \<noteq> 0"
    using canon len2 by (simp add: degree_eq_length_coeffs)
  show ?thesis
    unfolding hybrid_expol_int_spec_def hybrid_expol_sound_complete_spec_def
  proof (rule SPEC_rule)
    fix acc :: gmp_dyadic_interval_vec
    assume A: "dyadic_interval_vec_invar acc \<and>
      (\<exists>pol. mset (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly P)))"
    have inv: "dyadic_interval_vec_invar acc" using A by blast
    obtain pol where mseteq:
      "mset (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly P))" using A by blast
    let ?ns = "newdsc_pol_bail (hybrid_polr_of_pol pol) (degree (Poly P)) 0 1 e0 k 0 ?P_real"
    have seteq: "set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
               = set (newdsc_pol_bail_int pol 0 1 e0 k (Poly P))"
      using mseteq by (metis set_mset_mset)
    \<comment> \<open>the image lemma is stated at \<open>of_rat 0\<close>/\<open>of_rat 1\<close>; normalise it to the bare numerals
       the spec uses BEFORE any closing step, so nothing has to search across that gap
       (\<open>Bail_Loop_Refine\<close>'s 27-minute \<open>metis\<close> is exactly this mismatch).\<close>
    have img: "set (newdsc_pol_bail_int pol 0 1 e0 k (Poly P)) = real_to_rat_pair ` set ?ns"
      using hybrid_expol_int_set_image[OF P0 dg sf] by (simp add: of_rat_0 of_rat_1)
    have sound: "\<forall>J \<in> set ?ns. dsc_pair_ok ?P_real J"
      by (rule hybrid_expol_pol_sound[where P = "Poly P"
            and polr = "hybrid_polr_of_pol pol" and a = 0 and b = 1
            and e = e0 and dk = k and s = 0, OF P0 dg sf]) simp
    have complete: "\<And>x. poly ?P_real x = 0 \<Longrightarrow> 0 < x \<Longrightarrow> x < 1 \<Longrightarrow>
          \<exists>J \<in> set ?ns. fst J \<le> x \<and> x \<le> snd J"
      by (rule hybrid_expol_pol_complete[where P = "Poly P"
            and polr = "hybrid_polr_of_pol pol" and a = 0 and b = 1
            and e = e0 and dk = k and s = 0, OF P0 dg sf]) simp_all
    have half1: "\<forall>R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
        \<exists>J \<in> set ?ns. R = real_to_rat_pair J \<and> dsc_pair_ok ?P_real J"
    proof
      fix R
      assume Rmem: "R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))"
      from Rmem seteq img obtain J where
        Jmem: "J \<in> set ?ns" and Req: "R = real_to_rat_pair J" by auto
      show "\<exists>J \<in> set ?ns. R = real_to_rat_pair J \<and> dsc_pair_ok ?P_real J"
        using Jmem Req sound by blast
    qed
    have half2: "\<forall>x. poly ?P_real x = 0 \<longrightarrow> 0 < x \<longrightarrow> x < 1 \<longrightarrow>
        (\<exists>R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
          \<exists>J \<in> set ?ns. R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)"
    proof (intro allI impI)
      fix x :: real
      assume root: "poly ?P_real x = 0" and lo: "0 < x" and hi: "x < 1"
      obtain J where Jmem: "J \<in> set ?ns" and Jlo: "fst J \<le> x" and Jhi: "x \<le> snd J"
        using complete[OF root lo hi] by blast
      have Rmem: "real_to_rat_pair J
            \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))"
        using Jmem seteq img by auto
      show "\<exists>R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
              \<exists>J \<in> set ?ns. R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
        using Rmem Jmem Jlo Jhi by blast
    qed
    show "dyadic_interval_vec_invar acc \<and>
      (\<exists>polr.
        (\<forall>R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
          \<exists>J \<in> set (newdsc_pol_bail polr (degree (Poly P)) 0 1 e0 k 0 ?P_real).
             R = real_to_rat_pair J \<and> dsc_pair_ok ?P_real J) \<and>
        (\<forall>x. poly ?P_real x = 0 \<longrightarrow> 0 < x \<longrightarrow> x < 1 \<longrightarrow>
          (\<exists>R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
            \<exists>J \<in> set (newdsc_pol_bail polr (degree (Poly P)) 0 1 e0 k 0 ?P_real).
               R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
      using inv half1 half2 by blast
  qed
qed

text \<open>The functional refinement, as the \<open>Id\<close>-fref \<open>FCOMP\<close> composes.\<close>
lemma hybrid_expol_sound_complete_refine:
  "(uncurry5 hybrid_expol_int_spec, uncurry5 hybrid_expol_sound_complete_spec)
   \<in> [hybrid_expol_int_pre \<delta>]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI)
  apply clarsimp
  apply (rule hybrid_expol_int_spec_sound_complete)
  apply assumption
  done

text \<open>\<^bold>\<open>The user-facing capstone\<close>: under @{const hybrid_expol_int_pre}, the exported
  @{const hybrid_main_list_impl} returns a dyadic vector that is a SOUND and COMPLETE
  real-root cover of @{term "Poly P"} on \<open>(0,1)\<close>. \<open>FCOMP\<close> of
  @{thm [source] hybrid_main_list_impl_refine_expol_int} with
  @{thm [source] hybrid_expol_sound_complete_refine}.\<close>
theorem hybrid_main_list_impl_refine_expol_sound_complete:
  "(uncurry5 hybrid_main_list_impl, uncurry5 hybrid_expol_sound_complete_spec)
   \<in> [hybrid_expol_int_pre \<delta>]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
proof -
  have h:
    "(uncurry5 hybrid_main_list_impl, uncurry5 hybrid_expol_sound_complete_spec)
     \<in> [\<lambda>(((((e0, l_num), r_num), k), P), rp).
          hybrid_expol_int_pre \<delta> (((((e0, l_num), r_num), k), P), rp)]\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d
        \<rightarrow> gmp_dyadic_interval_vec_assn"
    using hybrid_main_list_impl_refine_expol_int[where \<delta>=\<delta>,
      FCOMP hybrid_expol_sound_complete_refine[where \<delta>=\<delta>]]
    by (simp add: PR_CONST_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF _ h])
    apply clarsimp
    done
qed


end
