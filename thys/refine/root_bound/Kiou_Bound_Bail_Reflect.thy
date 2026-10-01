theory Kiou_Bound_Bail_Reflect
  imports Kiou_Bound_Reflect
    "IsaRRI_Refine.Bail_Loop_Refine"
    "IsaRRI_LLVM.Split_Bail"
begin

text \<open>Correctness of the bail solver's split pipeline @{const bail_isolate_all_split_main}: the half
  solves consume the cascade-bail keystone (@{thm [source] bail_main_list_correct} via
  @{const blr_newdsc_int_pre}), and the abstract target is \<open>newdsc_pol_bail pol_final_real\<close>.

  The policy node view of @{const newdsc_pol_bail} is \<open>a b e dk v \<rightarrow> bool \<times> bool\<close>, and its split
  children carry no run length.\<close>

section \<open>\<open>newdsc_pol_bail\<close> elements are \<open>of_rat\<close> images (the analog of @{thm [source] dsc_elems_of_rat_image})\<close>

text \<open>Every element @{const newdsc_pol_bail} returns, given \<open>of_rat\<close>-image bounds, is itself a
  pair of \<open>of_rat\<close> images. Proven by \<open>pinduct\<close> over a FREE real polynomial (matching the spec's
  own recursion shape, so the \<open>psimps\<close> unfold is fast): the \<open>v=1\<close> leaf is \<open>(a,b)\<close>; an accepted
  Newton window is @{const snap_window}, whose endpoints are grid points
  (@{thm [source] snap_window_rat_eq} — the Newton iterate is irrational but the SNAPPED
  endpoints are \<open>a + k\<cdot>step\<close> for integer \<open>k\<close>); the bisection children and midpoint use
  \<open>(a+b)/2\<close>. No int-window bridge (that route is circular — it presupposes the very
  \<open>of_rat\<close>-ness being proven). Round-trips \<open>real_to_rat_pair\<close> through the pipeline's frame
  scaling, as the ET pipeline needs @{thm [source] dsc_elems_of_rat_image}.\<close>

lemma try_blocks_result_of_rat_bl:
  assumes "try_blocks p (of_rat ra) (of_rat rb) N P v = Some I" and "ra < rb" and "N > 0"
  shows "\<exists>rx ry. I = (of_rat rx, of_rat ry) \<and> rx < ry"
proof -
  let ?w = "(rb - ra) / of_nat N"
  have wpos: "?w > 0" using assms(2,3) by simp
  from assms(1) consider
      "I = (of_rat ra, of_rat ra + (of_rat rb - of_rat ra) / of_nat N)"
    | "I = (of_rat rb - (of_rat rb - of_rat ra) / of_nat N, of_rat rb)"
    unfolding try_blocks_def Let_def by (auto split: if_split_asm)
  thus ?thesis
  proof cases
    case 1
    have "I = (of_rat ra, of_rat (ra + ?w))"
      unfolding 1 by (simp add: of_rat_add of_rat_diff of_rat_divide of_rat_of_nat_eq)
    thus ?thesis using wpos by (auto intro: exI[of _ ra] exI[of _ "ra + ?w"])
  next
    case 2
    have "I = (of_rat (rb - ?w), of_rat rb)"
      unfolding 2 by (simp add: of_rat_diff of_rat_divide of_rat_of_nat_eq)
    thus ?thesis using wpos by (auto intro: exI[of _ "rb - ?w"] exI[of _ rb])
  qed
qed

\<comment> \<open>Every @{const try_window_bail} accept is an \<open>of_rat\<close> pair. Follows the case split of
   @{thm [source] try_window_bail_SomeD}; the ordering comes from the positive width
   \<open>try_window_bail_SomeD(3)\<close>. Both sources are \<open>snap_window\<close>. @{thm [source] try_blocks_result_of_rat_bl}
   (above) is a statement about @{const try_blocks}, which the plain Newton route uses.\<close>
lemma try_window_bail_result_of_rat:
  assumes TW: "try_window_bail gn p (of_rat ra) (of_rat rb) N P v = Some I"
      and ab: "ra < rb" and Npos: "N > 0"
  shows "\<exists>rx ry. I = (of_rat rx, of_rat ry) \<and> rx < ry"
proof -
  have abr: "(of_rat ra :: real) < of_rat rb" using ab by (simp add: of_rat_less)
  have img: "\<exists>rx ry. I = (of_rat rx, of_rat ry)"
  proof (cases gn)
    case gn: True
    show ?thesis
    proof (cases "newton_at v P (of_rat ra)")
      case L1: (Some lam1)
      from TW gn L1 have "I = snap_window (of_rat ra) (of_rat rb) N lam1"
        by (auto simp: try_window_bail_def Let_def split: if_split_asm)
      thus ?thesis by (auto simp: snap_window_rat_eq)
    next
      case L1none: None
      show ?thesis
      proof (cases "newton_at v P (of_rat rb)")
        case L2: (Some lam2)
        from TW gn L1none L2 have "I = snap_window (of_rat ra) (of_rat rb) N lam2"
          by (auto simp: try_window_bail_def Let_def split: if_split_asm)
        thus ?thesis by (auto simp: snap_window_rat_eq)
      next
        case None
        \<comment> \<open>both probes missed \<Rightarrow> bail bisects, so \<open>Some I\<close> is impossible (was: a blocks accept)\<close>
        with TW gn L1none show ?thesis
          by (auto simp: try_window_bail_def)
      qed
    qed
  next
    case False
    \<comment> \<open>Newton gate closed \<Rightarrow> \<open>None\<close> outright (was: the ungated blocks arm)\<close>
    with TW show ?thesis by (auto simp: try_window_bail_def)
  qed
  then obtain rx ry where I_img: "I = (of_rat rx, of_rat ry)" by blast
  have "snd I - fst I = (of_rat rb - of_rat ra) / of_nat N"
    using try_window_bail_SomeD(3)[OF TW abr Npos] by simp
  hence "(of_rat ry :: real) - of_rat rx > 0" using I_img abr Npos by simp
  hence "rx < ry" by (simp add: of_rat_less of_rat_diff)
  thus ?thesis using I_img by blast
qed


\<comment> \<open>\<open>try_newton_result_of_rat_bl\<close> was DELETED — the FOLDED @{const try_window_bail} subsumes
   both the Newton and block accepts, handled uniformly by \<open>try_window_bail_result_of_rat\<close> above.\<close>

text \<open>Every element @{const newdsc_pol_bail} returns, given \<open>of_rat\<close>-image bounds, is an \<open>of_rat\<close>
  pair. Reworked to @{const newdsc_pol_bail}'s ACTUAL folded recursion (a single
  @{const try_window_bail} \<open>Some\<close>/\<open>None\<close> case), mirroring @{thm [source] newdsc_pol_bail_sound}'s
  induction — IH order (1)=left, (2)=right, (3)=window.\<close>
lemma newdsc_pol_bail_elems_of_rat_image:
  assumes dom: "newdsc_pol_bail_dom (pol, p, a, b, e, dk, s, P)"
    and a: "a = of_rat ra" and b: "b = of_rat rb" and ab: "ra < rb"
  shows "\<forall>I \<in> set (newdsc_pol_bail pol p a b e dk s P). \<exists>rx ry. I = (of_rat rx, of_rat ry)"
  using dom a b ab
proof (induction pol p a b e dk s P arbitrary: ra rb rule: newdsc_pol_bail.pinduct)
  case (1 pol p a b e dk s P)
  let ?v = "Bernstein_changes p a b P"
  let ?gn = "snd (pol p a b e dk (s, ?v))"
  have aeq: "a = of_rat ra" and beq: "b = of_rat rb" and abr: "ra < rb"
    using "1.prems" by auto
  have ab_real: "a < b" using aeq beq abr by (simp add: of_rat_less)
  have Npos: "N_of e > 0" using N_of_ge_2[of e] by simp
  have nd_eq:
    "newdsc_pol_bail pol p a b e dk s P =
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a, b)]
        else
          (case try_window_bail (snd (pol p a b e dk (s, v)))
                  p a b (N_of e) P v of
             Some I \<Rightarrow> newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
           | None \<Rightarrow>
               (let m  = (a + b) / 2; e' = max 1 (e - 1);
                    s' = split_run_len_real p P a b s;
                    mid_root = (if poly P m = 0 then [(m, m)] else [])
                in mid_root @ newdsc_pol_bail pol p a m e' (dk + 1) s' P
                          @ newdsc_pol_bail pol p m b e' (dk + 1) s' P)))"
    using "1.hyps" newdsc_pol_bail.psimps by blast
  show ?case
  proof (cases "?v = 0")
    case True thus ?thesis by (simp add: nd_eq Let_def)
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case True thus ?thesis using nd_eq aeq beq by (auto simp: Let_def)
    next
      case v1: False
      note vg = v0 v1
      define rm where "rm = (ra + rb) / 2"
      have m_eq: "(a + b) / 2 = of_rat rm"
        unfolding rm_def aeq beq by (simp add: of_rat_add of_rat_divide)
      have am: "ra < rm" and mb: "rm < rb" using abr by (simp_all add: rm_def)
      show ?thesis
      proof (cases "try_window_bail ?gn p a b (N_of e) P ?v")
        case (Some I)
        obtain rx ry where Iimg: "I = (of_rat rx, of_rat ry)" and Iord: "rx < ry"
          using try_window_bail_result_of_rat[OF Some[unfolded aeq beq] abr Npos] by blast
        have child: "\<forall>I'\<in>set (newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                       \<exists>rx ry. I' = (of_rat rx, of_rat ry)"
          using "1.IH"(3) vg Some Iimg Iord by force
        show ?thesis using nd_eq vg Some child by (auto simp: Let_def)
      next
        case None
        have IHl: "\<forall>I'\<in>set (newdsc_pol_bail pol p a ((a + b) / 2) (max 1 (e - 1)) (dk + 1)
                            (split_run_len_real p P a b s) P).
                     \<exists>rx ry. I' = (of_rat rx, of_rat ry)"
          using "1.IH"(1) vg None aeq m_eq am by metis
        have IHr: "\<forall>I'\<in>set (newdsc_pol_bail pol p ((a + b) / 2) b (max 1 (e - 1)) (dk + 1)
                            (split_run_len_real p P a b s) P).
                     \<exists>rx ry. I' = (of_rat rx, of_rat ry)"
          using "1.IH"(2) vg None m_eq beq mb by metis
        show ?thesis using nd_eq vg None IHl IHr m_eq by (auto simp: Let_def)
      qed
    qed
  qed
qed

section \<open>\<open>newdsc_pol_bail_int\<close> sound/complete real-image + frame-scaling half correctness\<close>

text \<open>@{const dyadic_iv_node_iv_of} and @{const dyadic_iv_acc_ivs} (Newton keystone) are byte-identical to the
  ET @{const node_iv_of}/@{const acc_ivs}, so the ET frame-scaling algebra
  (@{thm [source] dyadic_interval_of_triple_eq_r0_times_node_iv_of}) transfers via a definitional
  bridge.\<close>
lemma dyadic_iv_node_iv_of_eq_bl: "dyadic_iv_node_iv_of l0 r0 k0 t = node_iv_of l0 r0 k0 t"
  by (simp add: dyadic_iv_node_iv_of_def node_iv_of_def dyadic_iv_node_iv_def node_iv_def)

lemma dyadic_iv_acc_ivs_eq_acc_ivs_bl: "dyadic_iv_acc_ivs l0 r0 k0 acc = acc_ivs l0 r0 k0 acc"
  by (simp add: dyadic_iv_acc_ivs_def acc_ivs_def dyadic_iv_node_iv_of_eq_bl)

text \<open>The @{const newdsc_pol_bail_int}-at-\<open>pol_final\<close> analogs of @{thm [source] dsc_int_sound_real_image'}
  / @{thm [source] dsc_int_complete_real_image'}: from the bridge
  @{thm [source] newdsc_pol_bail_int_eq_newdsc_pol_bail} (int result = \<open>real_to_rat_pair\<close> image of the real
  \<open>newdsc_pol_bail\<close>) composed with @{thm [source] newdsc_pol_bail_pol_final_sound} /
  @{thm [source] newdsc_pol_bail_pol_final_complete}.\<close>
text \<open>\<^bold>\<open>Stated at a free policy pair \<open>(pol, polr)\<close>.\<close> Nothing in the proofs is \<open>pol_final\<close>-specific: the
  three facts they use are policy-generic (@{thm [source] newdsc_pol_bail_terminates_squarefree},
  @{thm [source] newdsc_pol_bail_sound}, @{thm [source] newdsc_pol_bail_complete}), and the int/real
  bridge @{thm [source] newdsc_pol_bail_int_eq_newdsc_pol_bail} takes the policy relation as a premise.
  So the premise \<open>rel\<close> below is the bridge's side condition, passed through; the bail solver discharges
  it with @{thm [source] pol_final_real_rel} and the hybrid solver with \<open>hybrid_polr_of_pol_rel\<close>.
  The \<open>pol_final\<close> names are instantiations.\<close>
lemma newdsc_pol_bail_int_polr_sound_real_image':
  fixes P :: "int poly" and pol :: newton_pol and polr :: newton_pol_real
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0" and sf: "square_free P_real" and ab: "a < b"
    and rel: "\<And>a' b' e' dk' s' v.
        polr (degree P) (of_rat a') (of_rat b') e' dk' (s', int v) = pol (degree P) a' b' e' dk' (s', v)"
  shows "\<forall>I \<in> set (newdsc_pol_bail_int pol a b e dk P).
    \<exists>J \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real).
      I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
proof -
  have abr: "(of_rat a :: real) < of_rat b" using ab by (simp add: of_rat_less)
  have dne: "P_real \<noteq> 0" unfolding P_real_def using P0 by simp
  have dle: "degree P_real \<le> degree P" unfolding P_real_def by simp
  have dom: "newdsc_pol_bail_dom (polr, degree P, of_rat a, of_rat b, e, dk, 0, P_real)"
    unfolding P_real_def
    by (rule newdsc_pol_bail_terminates_squarefree[OF dne[unfolded P_real_def] dle[unfolded P_real_def]
          p0 sf[unfolded P_real_def] abr])
  have eqbridge: "rev (newdsc_pol_bail_int pol a b e dk P)
      = map real_to_rat_pair (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real)"
    unfolding P_real_def
    by (rule newdsc_pol_bail_int_eq_newdsc_pol_bail[OF dom[unfolded P_real_def] refl P0 ab]) (rule rel)
  have set_eq: "set (newdsc_pol_bail_int pol a b e dk P)
      = real_to_rat_pair ` set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real)"
    using eqbridge by (metis set_map set_rev)
  have sound: "\<forall>J \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real).
      dsc_pair_ok P_real J"
    by (rule newdsc_pol_bail_sound[OF dom dle dne abr])
  show ?thesis using set_eq sound by auto
qed

lemma newdsc_pol_bail_int_polr_complete_real_image'_strong:
  fixes P :: "int poly" and pol :: newton_pol and polr :: newton_pol_real
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0" and sf: "square_free P_real"
    and root: "poly P_real x = 0" and ax: "of_rat a < x" and xb: "x < of_rat b"
    and rel: "\<And>a' b' e' dk' s' v.
        polr (degree P) (of_rat a') (of_rat b') e' dk' (s', int v) = pol (degree P) a' b' e' dk' (s', v)"
  shows "\<exists>I \<in> set (newdsc_pol_bail_int pol a b e dk P).
    \<exists>J \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real).
      I = real_to_rat_pair J
      \<and> ((fst J < x \<and> x < snd J) \<or> (fst J = x \<and> snd J = x))"
proof -
  have ab: "a < b" using ax xb by (meson less_trans of_rat_less)
  have abr: "(of_rat a :: real) < of_rat b" using ab by (simp add: of_rat_less)
  have dne: "P_real \<noteq> 0" unfolding P_real_def using P0 by simp
  have dle: "degree P_real \<le> degree P" unfolding P_real_def by simp
  have dom: "newdsc_pol_bail_dom (polr, degree P, of_rat a, of_rat b, e, dk, 0, P_real)"
    unfolding P_real_def
    by (rule newdsc_pol_bail_terminates_squarefree[OF dne[unfolded P_real_def] dle[unfolded P_real_def]
          p0 sf[unfolded P_real_def] abr])
  have eqbridge: "rev (newdsc_pol_bail_int pol a b e dk P)
      = map real_to_rat_pair (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real)"
    unfolding P_real_def
    by (rule newdsc_pol_bail_int_eq_newdsc_pol_bail[OF dom[unfolded P_real_def] refl P0 ab]) (rule rel)
  have set_eq: "set (newdsc_pol_bail_int pol a b e dk P)
      = real_to_rat_pair ` set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real)"
    using eqbridge by (metis set_map set_rev)
  obtain J where J_in: "J \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real)"
    and J_cov: "(fst J < x \<and> x < snd J) \<or> (fst J = x \<and> snd J = x)"
    \<comment> \<open>\<open>where\<close>, never a positional \<open>of\<close>: the first free variable here is the POLICY, so a
       positional instantiation puts \<open>e :: nat\<close> in a \<open>newton_pol_real\<close> slot and the failure
       surfaces as a type clash at an unrelated line. The schematic is \<open>?pol\<close> (this is the
       policy-generic \<open>Bail_Spec\<close> fact, whose policy argument is real-valued but still named
       \<open>pol\<close>) --- \<open>where polr = \<dots>\<close> fails with \<open>No such variable in theorem\<close>.\<close>
    \<comment> \<open>Its premise list ends \<open>poly ?P ?x = 0\<close>, \<open>?a < ?x\<close>, \<open>?x < ?b\<close> --- NOT \<open>?a < ?b\<close>. Feeding
       \<open>abr\<close> as the fourth \<open>OF\<close> slot fails as \<open>OF: no unifiers\<close> pointing at the \<open>using\<close> line.\<close>
    using newdsc_pol_bail_complete_strong[where pol = polr and e = e and dk = dk and s = 0,
            OF dom dle dne root ax xb]
    by blast
  then have "real_to_rat_pair J \<in> set (newdsc_pol_bail_int pol a b e dk P)" using set_eq by blast
  thus ?thesis using J_in J_cov by blast
qed

text \<open>The ORIGINAL closed-covering statement, kept verbatim so every pre-existing use site is
  unaffected. Strict-or-degenerate implies it immediately.\<close>
lemma newdsc_pol_bail_int_polr_complete_real_image':
  fixes P :: "int poly" and pol :: newton_pol and polr :: newton_pol_real
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0" and sf: "square_free P_real"
    and root: "poly P_real x = 0" and ax: "of_rat a < x" and xb: "x < of_rat b"
    and rel: "\<And>a' b' e' dk' s' v.
        polr (degree P) (of_rat a') (of_rat b') e' dk' (s', int v) = pol (degree P) a' b' e' dk' (s', v)"
  shows "\<exists>I \<in> set (newdsc_pol_bail_int pol a b e dk P).
    \<exists>J \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real).
      I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
  \<comment> \<open>\<open>rel\<close> is META-quantified, so feeding it through \<open>OF\<close> gives \<open>OF: multiple unifiers\<close>;
     discharge it as a trailing subgoal instead, the shape the sibling delegating lemmas use\<close>
proof -
  have main: "\<exists>I \<in> set (newdsc_pol_bail_int pol a b e dk P).
      \<exists>J \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0
                  (map_poly of_int P :: real poly)).
        I = real_to_rat_pair J
        \<and> ((fst J < x \<and> x < snd J) \<or> (fst J = x \<and> snd J = x))"
    by (rule newdsc_pol_bail_int_polr_complete_real_image'_strong[OF P0 p0
              sf[unfolded P_real_def] root[unfolded P_real_def] ax xb])
       (rule rel)
  show ?thesis using main unfolding P_real_def by force
qed

lemma newdsc_pol_bail_int_pol_final_sound_real_image':
  fixes P :: "int poly"
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0" and sf: "square_free P_real" and ab: "a < b"
  shows "\<forall>I \<in> set (newdsc_pol_bail_int pol_final a b e dk P).
    \<exists>J \<in> set (newdsc_pol_bail pol_final_real (degree P) (of_rat a) (of_rat b) e dk 0 P_real).
      I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
  unfolding P_real_def
  by (rule newdsc_pol_bail_int_polr_sound_real_image'[OF P0 p0 sf[unfolded P_real_def] ab])
     (rule pol_final_real_rel)

lemma newdsc_pol_bail_int_pol_final_complete_real_image':
  fixes P :: "int poly"
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0" and sf: "square_free P_real"
    and root: "poly P_real x = 0" and ax: "of_rat a < x" and xb: "x < of_rat b"
  shows "\<exists>I \<in> set (newdsc_pol_bail_int pol_final a b e dk P).
    \<exists>J \<in> set (newdsc_pol_bail pol_final_real (degree P) (of_rat a) (of_rat b) e dk 0 P_real).
      I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
  unfolding P_real_def
  by (rule newdsc_pol_bail_int_polr_complete_real_image'[OF P0 p0 sf[unfolded P_real_def]
        root[unfolded P_real_def] ax xb])
     (rule pol_final_real_rel)

text \<open>Frame-scaling POSITIVE half soundness — clone of @{thm [source] dsc_carried_et_pos_half_sound}
  with @{const dsc_int}\<open>\<rightarrow>\<close>@{const newdsc_pol_bail_int} \<open>pol_final\<close>, @{const dsc}\<open>\<rightarrow>\<close>@{const newdsc_pol_bail}
  \<open>pol_final_real\<close>, @{thm [source] dsc_elems_of_rat_image}\<open>\<rightarrow>\<close>@{thm [source] newdsc_pol_bail_elems_of_rat_image};
  the scale-by-\<open>rpos\<close> algebra is SHARED verbatim.\<close>
text \<open>\<^bold>\<open>Why this is stated at \<open>(of_rat (fst I), of_rat (snd I))\<close> and not as
  \<open>\<exists>J. I = real_to_rat_pair J \<and> \<dots>\<close>.\<close>

  The existential form is not an isolation statement about \<open>I\<close>. @{const real_to_rat_pair} is
  \<open>(\<lambda>(x,y). (THE r. of_rat r = x, THE r. of_rat r = y))\<close>: on an irrational \<open>x\<close> no \<open>r\<close> satisfies the
  predicate, so the \<open>THE\<close> is an unspecified fixed value that may coincide with the rational the goal
  names. So \<open>I = real_to_rat_pair J\<close> does not tie \<open>J\<close> to \<open>I\<close>'s real image, and \<open>dsc_pair_ok P_real J\<close>
  does not transfer to the emitted interval. The multiset equality against @{const dsc_int} does not
  depend on this clause, but isolation on the emitted dyadic numerators does.

  The proof derives \<open>(of_rat (fst I), of_rat (snd I)) = ?J'\<close> in \<open>I_real\<close>, via
  @{thm [source] newdsc_pol_bail_elems_of_rat_image} (every element of the real recursion's output over
  \<open>of_rat\<close> bounds has \<open>of_rat\<close> endpoints), and \<open>dsc_pair_ok P_real ?J'\<close> in \<open>okP\<close>; the theorem exports
  that conjunction. The existential statement follows as the corollary below.\<close>
lemma dsc_carried_polr_pos_half_sound_strong:
  fixes xs :: "int list" and rpos :: int and pol :: newton_pol and polr :: newton_pol_real
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and p0: "degree (Poly Pinit) \<noteq> 0" and sf: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (dyadic_iv_acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit))"
    and rel: "\<And>p a' b' e' dk' s' v.
        polr p (of_rat a') (of_rat b') e' dk' (s', int v) = pol p a' b' e' dk' (s', v)"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
    dsc_pair_ok P_real (of_rat (fst I), of_rat (snd I))"
proof
  fix I assume "I \<in> set (dyadic_interval_vec_to_list acc)"
  then obtain t where t_in: "t \<in> set (dyadic_interval_vec_triples acc)"
    and I_eq: "I = dyadic_interval_of_triple t"
    unfolding dyadic_interval_vec_to_list_def by auto
  have niv_in: "node_iv_of 0 rpos 0 t \<in> set (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit))"
    using t_in acc_eq unfolding dyadic_iv_acc_ivs_eq_acc_ivs_bl acc_ivs_def
    by (metis (no_types, lifting) image_eqI mset_map mset_eq_setD set_map)
  have Pinit0: "Poly Pinit \<noteq> 0"
    unfolding Pinit_def using poly_scale_poly_list_nonzero[OF P0] rpos_pos by simp
  obtain J where J_in: "J \<in> set (newdsc_pol_bail polr (degree (Poly Pinit))
      (of_rat 0) (of_rat 1) e0 k 0 (map_poly of_int (Poly Pinit) :: real poly))"
    and IJ: "node_iv_of 0 rpos 0 t = real_to_rat_pair J"
    and okPinit: "dsc_pair_ok (map_poly of_int (Poly Pinit) :: real poly) J"
    using newdsc_pol_bail_int_polr_sound_real_image'[where pol = pol and polr = polr
            and e = e0 and dk = k, OF Pinit0 p0 sf zero_less_one rel] niv_in
    by fastforce
  have abr01: "(of_rat (0::rat) :: real) < of_rat 1" by (simp add: of_rat_less)
  have dneP: "(map_poly of_int (Poly Pinit) :: real poly) \<noteq> 0" using Pinit0 by simp
  have dleP: "degree (map_poly of_int (Poly Pinit) :: real poly) \<le> degree (Poly Pinit)" by simp
  have domN: "newdsc_pol_bail_dom (polr, degree (Poly Pinit), of_rat (0::rat), of_rat (1::rat),
      e0, k, 0, map_poly of_int (Poly Pinit) :: real poly)"
    by (rule newdsc_pol_bail_terminates_squarefree[OF dneP dleP p0 sf abr01])
  obtain rx ry where J_rat: "J = (of_rat rx, of_rat ry)"
    using newdsc_pol_bail_elems_of_rat_image[OF domN refl refl] J_in by auto
  have dit_eq: "I = (rat_of_int rpos * fst (node_iv_of 0 rpos 0 t),
                      rat_of_int rpos * snd (node_iv_of 0 rpos 0 t))"
    using I_eq dyadic_interval_of_triple_eq_r0_times_node_iv_of[OF rpos_pos] by simp
  have scale_eq: "(of_rat (rat_of_int rpos * fst (real_to_rat_pair J)),
                   of_rat (rat_of_int rpos * snd (real_to_rat_pair J)))
      = (of_rat (rat_of_int rpos) * fst J, of_rat (rat_of_int rpos) * snd J :: real)"
    using real_to_rat_pair_scale[OF J_rat, of "rat_of_int rpos"] .
  let ?J' = "(of_rat (rat_of_int rpos) * fst J, of_rat (rat_of_int rpos) * snd J :: real)"
  have I_real: "(of_rat (fst I), of_rat (snd I)) = ?J'"
    using dit_eq IJ scale_eq by simp
  have okP: "dsc_pair_ok P_real ?J'"
    using dsc_pair_ok_scale_poly_list[OF P0 rpos_pos, of J] okPinit
    unfolding P_real_def Pinit_def by (simp add: of_rat_of_int_eq)
  \<comment> \<open>the whole strengthening: \<open>okP\<close> holds of \<open>?J'\<close>, and \<open>I_real\<close> says \<open>?J'\<close> IS \<open>I\<close>'s \<open>of_rat\<close>
     image — so rewrite along it instead of re-weakening to an existential\<close>
  show "dsc_pair_ok P_real (of_rat (fst I), of_rat (snd I))" using okP I_real by simp
qed

text \<open>The step from the pinned form to the existential one, as its own rule. It is stated over the
  destructured components \<open>(a, b)\<close>, not over an \<open>I\<close>, because at every use site \<open>auto\<close> has already split
  the pair and the goal reads \<open>\<exists>a b. (ab, ba) = real_to_rat_pair (a, b) \<and> \<dots>\<close>. It is a rule rather than
  a simp hint because the witness \<open>(of_rat a, of_rat b)\<close> is not guessed automatically.\<close>
lemma dsc_pair_ok_of_rat_witness:
  fixes a b :: rat
  assumes "dsc_pair_ok P (of_rat a, of_rat b)"
  shows "\<exists>x y. (a, b) = real_to_rat_pair (x, y) \<and> dsc_pair_ok P (x, y)"
  \<comment> \<open>The conclusion uses two existentials, over \<open>x\<close> and \<open>y\<close>, not one over a pair \<open>J\<close>. At the use site
     \<open>auto\<close> has already split the pair existential, so the goal reads
     \<open>\<exists>a b. \<dots> = real_to_rat_pair (a, b) \<and> \<dots>\<close>, and a rule shaped \<open>\<exists>J. \<dots>\<close> is a different term that
     \<open>intro\<close> does not match.\<close>
  by (rule exI[where x = "of_rat a"], rule exI[where x = "of_rat b"])
     (simp add: assms real_to_rat_pair_of_rat)

text \<open>The same step in the UNSPLIT \<open>\<exists>J\<close> shape, for use sites that state the goal themselves (an
  explicit Isar \<open>show\<close>) rather than letting \<open>auto\<close> split the pair. Both shapes are kept because
  neither matches the other's goal — see the banner above.\<close>
lemma dsc_pair_ok_of_rat_witness_pair:
  assumes "dsc_pair_ok P (of_rat (fst I), of_rat (snd I))"
  shows "\<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P J"
  by (rule exI[where x = "(of_rat (fst I), of_rat (snd I))"])
     (simp add: assms real_to_rat_pair_of_rat)

text \<open>The ORIGINAL statement, kept verbatim so every pre-existing use site is unaffected. It is a
  strict weakening: \<open>I\<close>'s own \<open>of_rat\<close> image is a witness for the existential
  (@{thm [source] real_to_rat_pair_of_rat}).\<close>
lemma dsc_carried_polr_pos_half_sound:
  fixes xs :: "int list" and rpos :: int and pol :: newton_pol and polr :: newton_pol_real
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and p0: "degree (Poly Pinit) \<noteq> 0" and sf: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (dyadic_iv_acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit))"
    and rel: "\<And>p a' b' e' dk' s' v.
        polr p (of_rat a') (of_rat b') e' dk' (s', int v) = pol p a' b' e' dk' (s', v)"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
    \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
proof
  fix I assume Iin: "I \<in> set (dyadic_interval_vec_to_list acc)"
  have "dsc_pair_ok P_real (of_rat (fst I), of_rat (snd I))"
    using dsc_carried_polr_pos_half_sound_strong[OF P0 rpos_pos p0[unfolded Pinit_def]
            sf[unfolded Pinit_def] acc_eq[unfolded Pinit_def] rel] Iin
    unfolding P_real_def by blast
  moreover have "I = real_to_rat_pair (of_rat (fst I), of_rat (snd I))"
    by (simp add: real_to_rat_pair_of_rat)
  ultimately show "\<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P_real J" by blast
qed

text \<open>Bail's own instantiation, at \<open>pol_final\<close>. Same statement it always had.\<close>
lemma dsc_carried_bail_pos_half_sound:
  fixes xs :: "int list" and rpos :: int
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and p0: "degree (Poly Pinit) \<noteq> 0" and sf: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (dyadic_iv_acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly Pinit))"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
    \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
  unfolding P_real_def
  by (rule dsc_carried_polr_pos_half_sound[OF P0 rpos_pos p0[unfolded Pinit_def]
        sf[unfolded Pinit_def] acc_eq[unfolded Pinit_def]])
     (rule pol_final_real_rel)

text \<open>Frame-scaling POSITIVE half completeness — clone of
  @{thm [source] dsc_carried_et_pos_half_complete}, likewise stated at a FREE policy pair.\<close>

text \<open>\<^bold>\<open>The pinned completeness twin.\<close> The existential form
  \<open>\<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J\<close> does not say that the root \<open>x\<close> lies in the
  emitted interval \<open>I\<close>: @{const real_to_rat_pair} is not injective, so \<open>J\<close> is unconstrained on an
  irrational endpoint. A consumer that needs \<open>x\<close> inside \<open>I\<close>'s own \<open>of_rat\<close> image, such as the
  power-substitution back-map, which needs the reduced interval that contains each \<open>Q\<close>-root, cannot
  use it.

  The proof derives \<open>(of_rat (fst I), of_rat (snd I)) = ?J\<close> in \<open>I_real\<close> and
  \<open>fst ?J \<le> x \<and> x \<le> snd ?J\<close> in \<open>cov_x\<close>; taking components of \<open>I_real\<close> gives the pinned statement. The
  existential statement follows as the corollary below.\<close>
lemma dsc_carried_polr_pos_half_complete_strong:
  fixes xs :: "int list" and rpos :: int and x :: real
    and pol :: newton_pol and polr :: newton_pol_real
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and p0: "degree (Poly Pinit) \<noteq> 0" and sf: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (dyadic_iv_acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit))"
    and x_pos: "0 < x" and x_lt: "x < of_int rpos" and root: "poly P_real x = 0"
    and rel: "\<And>p a' b' e' dk' s' v.
        polr p (of_rat a') (of_rat b') e' dk' (s', int v) = pol p a' b' e' dk' (s', v)"
  shows "\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
    (of_rat (fst I) < x \<and> x < of_rat (snd I))
    \<or> (of_rat (fst I) = x \<and> of_rat (snd I) = x)"
proof -
  have Pinit0: "Poly Pinit \<noteq> 0"
    unfolding Pinit_def using poly_scale_poly_list_nonzero[OF P0] rpos_pos by simp
  define y where "y = x / of_int rpos"
  have y_pos: "0 < y" unfolding y_def using x_pos rpos_pos by simp
  have y_lt: "y < 1" unfolding y_def using x_lt rpos_pos by (simp add: pos_divide_less_eq)
  have rooty: "poly (map_poly of_int (Poly Pinit) :: real poly) y = 0"
  proof -
    have "(map_poly of_int (Poly Pinit) :: real poly) = P_real \<circ>\<^sub>p [:0, of_int rpos:]"
      unfolding Pinit_def P_real_def by (rule Poly_scale_poly_list_eq_pcompose)
    also have "poly \<dots> y = poly P_real (of_int rpos * y)" by (simp add: poly_pcompose mult.commute)
    also have "of_int rpos * y = x" unfolding y_def using rpos_pos by simp
    finally show ?thesis using root by simp
  qed
  have y_ax: "of_rat (0::rat) < y" using y_pos by simp
  have y_xb: "y < of_rat (1::rat)" using y_lt by simp
  have ex_step: "\<exists>I' \<in> set (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit)).
      \<exists>J' \<in> set (newdsc_pol_bail polr (degree (Poly Pinit)) (of_rat 0) (of_rat 1) e0 k 0
        (map_poly of_int (Poly Pinit) :: real poly)).
      I' = real_to_rat_pair J'
      \<and> ((fst J' < y \<and> y < snd J') \<or> (fst J' = y \<and> snd J' = y))"
    using newdsc_pol_bail_int_polr_complete_real_image'_strong[where pol = pol and polr = polr
            and e = e0 and dk = k, OF Pinit0 p0 sf rooty y_ax y_xb rel] by blast
  obtain I' J' where I'_in: "I' \<in> set (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit))"
    and J'_in: "J' \<in> set (newdsc_pol_bail polr (degree (Poly Pinit)) (of_rat 0) (of_rat 1) e0 k 0
        (map_poly of_int (Poly Pinit) :: real poly))"
    and I'J': "I' = real_to_rat_pair J'"
    and cov: "(fst J' < y \<and> y < snd J') \<or> (fst J' = y \<and> snd J' = y)"
    using ex_step by blast
  have "I' \<in> set (acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))"
    using I'_in acc_eq[unfolded dyadic_iv_acc_ivs_eq_acc_ivs_bl] by (metis mset_eq_setD)
  then obtain t where t_in: "t \<in> set (dyadic_interval_vec_triples acc)"
    and niv_eq: "node_iv_of 0 rpos 0 t = I'"
    unfolding acc_ivs_def by auto
  define I where "I = dyadic_interval_of_triple t"
  have I_in_list: "I \<in> set (dyadic_interval_vec_to_list acc)"
    using t_in unfolding dyadic_interval_vec_to_list_def I_def by auto
  have dit_eq: "I = (rat_of_int rpos * fst (node_iv_of 0 rpos 0 t),
                      rat_of_int rpos * snd (node_iv_of 0 rpos 0 t))"
    unfolding I_def using dyadic_interval_of_triple_eq_r0_times_node_iv_of[OF rpos_pos] .
  have abr01: "(of_rat (0::rat) :: real) < of_rat 1" by (simp add: of_rat_less)
  have dneP: "(map_poly of_int (Poly Pinit) :: real poly) \<noteq> 0" using Pinit0 by simp
  have dleP: "degree (map_poly of_int (Poly Pinit) :: real poly) \<le> degree (Poly Pinit)" by simp
  have domN: "newdsc_pol_bail_dom (polr, degree (Poly Pinit), of_rat (0::rat), of_rat (1::rat),
      e0, k, 0, map_poly of_int (Poly Pinit) :: real poly)"
    by (rule newdsc_pol_bail_terminates_squarefree[OF dneP dleP p0 sf abr01])
  obtain rx ry where J'_rat: "J' = (of_rat rx, of_rat ry)"
    using newdsc_pol_bail_elems_of_rat_image[OF domN refl refl] J'_in by fastforce
  have scale_eq: "(of_rat (rat_of_int rpos * fst (real_to_rat_pair J')),
                   of_rat (rat_of_int rpos * snd (real_to_rat_pair J')))
      = (of_rat (rat_of_int rpos) * fst J', of_rat (rat_of_int rpos) * snd J' :: real)"
    using real_to_rat_pair_scale[OF J'_rat, of "rat_of_int rpos"] .
  let ?J = "(of_rat (rat_of_int rpos) * fst J', of_rat (rat_of_int rpos) * snd J' :: real)"
  have I_real: "(of_rat (fst I), of_rat (snd I)) = ?J"
    using dit_eq niv_eq I'J' scale_eq by simp
  \<comment> \<open>scaling by a POSITIVE \<open>rpos\<close> preserves both disjuncts: strict stays strict, and an
     equality stays an equality\<close>
  have cov_x: "(fst ?J < x \<and> x < snd ?J) \<or> (fst ?J = x \<and> snd ?J = x)"
    using cov unfolding y_def using rpos_pos
    by (simp add: of_rat_mult field_simps mult.commute)
  \<comment> \<open>Take components of \<open>I_real\<close>. Going through \<open>I = real_to_rat_pair ?J\<close> would weaken the covering
     onto a witness that @{const real_to_rat_pair}'s non-injectivity leaves unconstrained.\<close>
  have covI: "(of_rat (fst I) < x \<and> x < of_rat (snd I))
              \<or> (of_rat (fst I) = x \<and> of_rat (snd I) = x)"
    using cov_x I_real by (metis fst_conv snd_conv)
  show ?thesis using I_in_list covI by blast
qed

text \<open>The ORIGINAL statement, kept verbatim so every pre-existing use site is unaffected. It is a
  strict weakening: \<open>I\<close>'s own \<open>of_rat\<close> image is a witness for the existential
  (@{thm [source] real_to_rat_pair_of_rat}).\<close>
lemma dsc_carried_polr_pos_half_complete:
  fixes xs :: "int list" and rpos :: int and x :: real
    and pol :: newton_pol and polr :: newton_pol_real
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and p0: "degree (Poly Pinit) \<noteq> 0" and sf: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (dyadic_iv_acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly Pinit))"
    and x_pos: "0 < x" and x_lt: "x < of_int rpos" and root: "poly P_real x = 0"
    and rel: "\<And>p a' b' e' dk' s' v.
        polr p (of_rat a') (of_rat b') e' dk' (s', int v) = pol p a' b' e' dk' (s', v)"
  shows "\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
    \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
proof -
  obtain I where Iin: "I \<in> set (dyadic_interval_vec_to_list acc)"
    and covI: "(of_rat (fst I) < x \<and> x < of_rat (snd I))
               \<or> (of_rat (fst I) = x \<and> of_rat (snd I) = x)"
    using dsc_carried_polr_pos_half_complete_strong[OF P0 rpos_pos p0[unfolded Pinit_def]
            sf[unfolded Pinit_def] acc_eq[unfolded Pinit_def]
            x_pos x_lt root[unfolded P_real_def] rel]
    by blast
  from covI have covI': "of_rat (fst I) \<le> x \<and> x \<le> of_rat (snd I)" by auto
  have "I = real_to_rat_pair (of_rat (fst I), of_rat (snd I))"
    by (simp add: real_to_rat_pair_of_rat)
  then show ?thesis using Iin covI' by (metis fst_conv snd_conv)
qed

text \<open>Bail's own instantiation, at \<open>pol_final\<close>. Same statement it always had.\<close>
lemma dsc_carried_bail_pos_half_complete:
  fixes xs :: "int list" and rpos :: int and x :: real
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and p0: "degree (Poly Pinit) \<noteq> 0" and sf: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (dyadic_iv_acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly Pinit))"
    and x_pos: "0 < x" and x_lt: "x < of_int rpos" and root: "poly P_real x = 0"
  shows "\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
    \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
  by (rule dsc_carried_polr_pos_half_complete[OF P0 rpos_pos p0[unfolded Pinit_def]
        sf[unfolded Pinit_def] acc_eq[unfolded Pinit_def] x_pos x_lt root[unfolded P_real_def]])
     (rule pol_final_real_rel)

section \<open>The pipeline's Newton-specific precondition\<close>

text \<open>Extends @{const dsc_isolate_all_split_pre} with the Newton route's STRONGER capacity
  requirement: the ET route's per-\<open>k\<close> cap is \<open>k + \<mu> + 1 < max_snat\<close> (linear in \<open>\<mu>\<close>); the Newton
  route's \<open>kcap\<close> (@{const blr_newdsc_int_pre}) is \<open>k + 258\<cdot>(2^(\<mu>+1)-2) < max_snat\<close> (EXPONENTIAL in
  \<open>\<mu>\<close>, from the window escalation ladder's \<open>2^ecap\<close> jump) — the ET bundle does NOT imply it, so a
  fresh \<open>k\<close>-quantified clause is needed. \<open>newton_pol_ecap = 8\<close> is a fixed constant (not \<open>xs\<close>-dependent),
  so it is inlined directly rather than threaded as a parameter.\<close>
definition dsc_isolate_all_split_bail_pre :: "int list \<Rightarrow> bool" where
"dsc_isolate_all_split_bail_pre xs \<longleftrightarrow>
  dsc_isolate_all_split_pre xs \<and>
  length xs + 3 < max_snat LENGTH(gmp_poly_len) \<and>
  (\<forall>k. (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ k) \<longrightarrow>
     (let Pinit = scale_poly_list (2 ^ k) xs;
          \<delta> = delta_P (map_poly of_int (Poly Pinit) :: real poly) in
        int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len)) \<and>
        int k + int (2 ^ newton_pol_ecap + 2)
          * (int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len)))) \<and>
  (\<forall>k. (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ k) \<longrightarrow>
     (let Qb = refl_list xs; Qinit = scale_poly_list (2 ^ k) Qb;
          \<delta> = delta_P (map_poly of_int (Poly Qinit) :: real poly) in
        int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len)) \<and>
        int k + int (2 ^ newton_pol_ecap + 2)
          * (int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len))))"

text \<open>Bridge: the pipeline's Newton precondition, instantiated at \<open>kpos\<close>, implies
  @{const blr_newdsc_int_pre} for the positive half's \<open>(2, 0, 2^kpos, 0, Pinit)\<close> call (\<open>e0\<close> is the
  constant @{const split_pipeline_e0}; it does not appear in @{const blr_newdsc_int_pre}'s body,
  since the vestigial \<open>ibud0\<close> conjunct that once used it was deleted — memory
  \<open>newton-ibud0-vacuous-hypothesis\<close>). Structurally identical to
  @{thm [source] bisection_isolate_all_split_pos_pre}: squarefreeness/nonzero-ness/canonicity
  transfer under any dilation (@{thm [source] square_free_pcompose_linear}); only the capacity
  facts differ (drawn from the NEW \<open>kcap\<close> clause above, not the ET \<open>cap\<close>).\<close>
lemma dsc_isolate_all_split_pos_bail_pre:
  fixes xs :: "int list" and kpos :: nat
  assumes pre: "dsc_isolate_all_split_bail_pre xs"
    and kpos_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ kpos"
  shows "blr_newdsc_int_pre
      (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ kpos) xs)) :: real poly))
      ((((split_pipeline_e0, 0), 2 ^ kpos), 0), scale_poly_list (2 ^ kpos) xs)"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    and lenb3: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    and kcapP: "\<forall>k. (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ k) \<longrightarrow>
      (let Pinit = scale_poly_list (2 ^ k) xs;
           \<delta> = delta_P (map_poly of_int (Poly Pinit) :: real poly) in
        int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len)) \<and>
        int k + int (2 ^ newton_pol_ecap + 2)
          * (int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len)))"
    unfolding dsc_isolate_all_split_bail_pre_def by auto
  from pre' have len2: "2 \<le> length xs" and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and canonxs: "coeffs (Poly xs) = xs"
    unfolding dsc_isolate_all_split_pre_def by auto
  define Pinit where "Pinit = scale_poly_list (2 ^ kpos) xs"
  define d where "d = delta_P (map_poly of_int (Poly Pinit) :: real poly)"
  have cpos: "(2::int) ^ kpos \<noteq> 0" by simp
  have len_eq: "length Pinit = length xs" unfolding Pinit_def by (simp add: scale_poly_list_eq_map_upt)
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
    have "length (coeffs (Poly Pinit)) = degree (Poly Pinit) + 1" using P0init by (rule length_coeffs)
    thus ?thesis using len2 len_eq canonPinit by simp
  qed
  have small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> d \<Longrightarrow> descartes_list_int a b Pinit \<le> 1"
    unfolding d_def
    by (rule rational_fast_descartes_list_int_delta_P_le1[OF P0init canonPinit degne sfPinit])
  have capkcap: "int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len)) \<and>
      int kpos + int (2 ^ newton_pol_ecap + 2)
        * (int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len))"
    using kcapP[rule_format, OF kpos_sound[rule_format]] unfolding Pinit_def d_def by (simp add: Let_def)
  have cap: "int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len))"
    using capkcap by simp
  have kcap: "int kpos + int (2 ^ newton_pol_ecap + 2)
      * (int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len))"
    using capkcap by simp
  have len2P: "Suc 0 < length Pinit" using len2 len_eq by simp
  have lenbP: "length Pinit + 2 < max_snat LENGTH(gmp_poly_len)" using lenb3 len_eq by simp
  show ?thesis
    unfolding blr_newdsc_int_pre_def Pinit_def[symmetric]
    using delta_pos len2P small_fast sfPinit P0init canonPinit lenbP cap kcap
    by (simp add: Let_def d_def[symmetric])
qed

text \<open>Negative-half twin, structurally identical to @{thm [source] bisection_isolate_all_split_neg_pre}.\<close>
lemma dsc_isolate_all_split_neg_bail_pre:
  fixes xs :: "int list" and kneg :: nat
  defines "Qb \<equiv> refl_list xs"
  assumes pre: "dsc_isolate_all_split_bail_pre xs"
    and kneg_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ kneg"
  shows "blr_newdsc_int_pre
      (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ kneg) Qb)) :: real poly))
      ((((split_pipeline_e0, 0), 2 ^ kneg), 0), scale_poly_list (2 ^ kneg) Qb)"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    and lenb3: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    and kcapQ: "\<forall>k. (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ k) \<longrightarrow>
      (let Qb' = refl_list xs; Qinit = scale_poly_list (2 ^ k) Qb';
           \<delta> = delta_P (map_poly of_int (Poly Qinit) :: real poly) in
        int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len)) \<and>
        int k + int (2 ^ newton_pol_ecap + 2)
          * (int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len)))"
    unfolding dsc_isolate_all_split_bail_pre_def by auto
  from pre' have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and canonxs: "coeffs (Poly xs) = xs"
    unfolding dsc_isolate_all_split_pre_def by auto
  have xsne: "xs \<noteq> []" using len2 by auto
  have sfrefl: "square_free (map_poly of_int (Poly (refl_list xs)) :: real poly)"
    using square_free_pcompose_linear[OF sfxs, of "-1"]
    by (simp add: refl_list_eq_scale_poly_list_neg1 Poly_scale_poly_list_eq_pcompose)
  have sfQb: "square_free (map_poly of_int (Poly Qb) :: real poly)"
    using sfrefl unfolding Qb_def by simp
  have lastnzQb: "last Qb \<noteq> 0" unfolding Qb_def using last_refl_list_nz[OF xsne lastnz] by simp
  have Qb_ne: "Qb \<noteq> []" unfolding Qb_def using xsne by (simp add: refl_list_def)
  have canonQb: "coeffs (Poly Qb) = Qb"
    using coeffs_Poly_eq_self_of_last_nonzero[OF Qb_ne lastnzQb] .
  have lenQb: "length Qb = length xs" unfolding Qb_def by (simp add: refl_list_def)
  define Qinit where "Qinit = scale_poly_list (2 ^ kneg) Qb"
  define d where "d = delta_P (map_poly of_int (Poly Qinit) :: real poly)"
  have cneg: "(2::int) ^ kneg \<noteq> 0" by simp
  have len_eq: "length Qinit = length Qb" unfolding Qinit_def by (simp add: scale_poly_list_eq_map_upt)
  have sfQinit: "square_free (map_poly of_int (Poly Qinit) :: real poly)"
    unfolding Qinit_def
    using square_free_pcompose_linear[OF sfQb, of "2 ^ kneg"]
    by (simp add: Poly_scale_poly_list_eq_pcompose)
  have Q0init: "Poly Qinit \<noteq> 0" using sfQinit unfolding square_free_def by simp
  have canonQinit: "coeffs (Poly Qinit) = Qinit"
    unfolding Qinit_def
    using coeffs_scale_poly_list[OF canonQb[symmetric], of "2 ^ kneg"] cneg
    by (simp add: scale_poly_list_correct[symmetric, of "2 ^ kneg" "Poly Qb"] canonQb)
  have delta_pos: "d > 0" unfolding d_def using Q0init delta_P_pos by simp
  have degne: "degree (Poly Qinit) \<noteq> 0"
  proof -
    have "length (coeffs (Poly Qinit)) = degree (Poly Qinit) + 1" using Q0init by (rule length_coeffs)
    thus ?thesis using len2 lenQb len_eq canonQinit by simp
  qed
  have small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> d \<Longrightarrow> descartes_list_int a b Qinit \<le> 1"
    unfolding d_def
    by (rule rational_fast_descartes_list_int_delta_P_le1[OF Q0init canonQinit degne sfQinit])
  have capkcap: "int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len)) \<and>
      int kneg + int (2 ^ newton_pol_ecap + 2)
        * (int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len))"
    using kcapQ[rule_format, OF kneg_sound[rule_format]]
    unfolding Qinit_def d_def Qb_def by (simp add: Let_def)
  have cap: "int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len))"
    using capkcap by simp
  have kcap: "int kneg + int (2 ^ newton_pol_ecap + 2)
      * (int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len))"
    using capkcap by simp
  have len2Q: "Suc 0 < length Qinit" using len2 lenQb len_eq by simp
  have lenbQ: "length Qinit + 2 < max_snat LENGTH(gmp_poly_len)" using lenb3 lenQb len_eq by simp
  show ?thesis
    unfolding blr_newdsc_int_pre_def Qinit_def[symmetric]
    using delta_pos len2Q small_fast sfQinit Q0init canonQinit lenbQ cap kcap
    by (simp add: Let_def d_def[symmetric])
qed

section \<open>Pipeline stage correctness + capstone\<close>

text \<open>The Newton positive-half solve meets the sound+complete SPEC. Fuses the ET
  @{thm [source] bisection_isolate_all_split_pos_half_step} (fixed-\<open>kpos\<close> body via the solver spec)
  with @{thm [source] bisection_isolate_all_split_pos_half} (the \<open>kiou\<close> existential front), since
  @{const bail_split_pos_solve_monadic} inlines the bound call. Solver spec =
  @{thm [source] bail_main_list_correct} (the keystone); frame scaling =
  @{thm [source] dsc_carried_bail_pos_half_sound}/@{thm [source] dsc_carried_bail_pos_half_complete}.\<close>
lemma bail_split_pos_solve_half:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_bail_pre xs"
  shows "bail_split_pos_solve_monadic xs
    \<le> SPEC (\<lambda>accP. (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    unfolding dsc_isolate_all_split_bail_pre_def by simp
  from pre' have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    unfolding dsc_isolate_all_split_pre_def by auto
  have P0: "Poly xs \<noteq> 0" using sfxs unfolding square_free_def by simp
  \<comment> \<open>The producer-side clause, extracted from the precondition rather than re-derived.\<close>
  have capY: "kiou_bound_k_monadic xs \<le> SPEC (split_cap xs)"
    using pre' unfolding dsc_isolate_all_split_pre_def by (simp add: Let_def)
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  show ?thesis
    unfolding bail_split_pos_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg kiou_bound_k_monadic_spec_capped[OF len2 lastnz hr capY, THEN order_trans])
    subgoal using len2 lenb by (cases xs) auto
    subgoal using lenb by simp
    \<comment> \<open>the post-kiou ASSERT \<open>kpos*len < max_snat\<close> and \<open>kpos < max_snat\<close> (two subgoals), from the kiou postcond\<close>
    subgoal premises p using p by simp
    subgoal premises p using p by simp
    \<comment> \<open>for a fixed kpos satisfying the root bound + caps: the body meets SPEC\<close>
    subgoal premises kp for kpos
    proof -
      from kp have kpos_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ kpos"
        and kpos_cap: "kpos * length xs < max_snat LENGTH(gmp_poly_len)"
        and kpos_lt: "kpos < max_snat LENGTH(gmp_poly_len)" by blast+
      define Pinit0 where "Pinit0 = scale_poly_list (2 ^ kpos) xs"
      have Pinit_eq: "split_init_pow2_l0_monadic kpos xs \<le> RETURN Pinit0"
        using split_init_pow2_l0_monadic_correct[OF lenb kpos_cap]
        by (simp add: Pinit0_def split_init_pow2_l0_eq_scale_poly_list)
      have npre: "blr_newdsc_int_pre
          (delta_P (map_poly of_int (Poly Pinit0) :: real poly))
          ((((split_pipeline_e0, 0), 2 ^ kpos), 0), Pinit0)"
        using dsc_isolate_all_split_pos_bail_pre[OF pre kpos_sound]
        unfolding Pinit0_def by simp
      define d where "d = delta_P (map_poly of_int (Poly Pinit0) :: real poly)"
      from npre have dpos: "d > 0" and len2P: "Suc 0 < length Pinit0"
        and sfP: "square_free (map_poly of_int (Poly Pinit0) :: real poly)"
        and P0init: "Poly Pinit0 \<noteq> 0" and canonP: "coeffs (Poly Pinit0) = Pinit0"
        and small_fastP: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> d \<Longrightarrow> descartes_list_int a b Pinit0 \<le> 1"
        and lenbP: "length Pinit0 + 2 < max_snat LENGTH(gmp_poly_len)"
        and lrP: "(0::int) < 2 ^ kpos"
        and capP2: "int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len))"
        and kcapP: "int 0 + int (2 ^ newton_pol_ecap + 2)
            * (int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len))"
        unfolding blr_newdsc_int_pre_def d_def by (auto simp: Let_def)
      have p0P: "degree (Poly Pinit0) \<noteq> 0"
      proof -
        have "length (coeffs (Poly Pinit0)) = degree (Poly Pinit0) + 1" using P0init by (rule length_coeffs)
        thus ?thesis using len2P canonP by simp
      qed
      have k1: "(0::nat) + 1 < max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
      have solver: "bail_main_list_monadic split_pipeline_e0 0 (2 ^ kpos) 0 Pinit0
          \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
              mset (dyadic_iv_acc_ivs 0 (2 ^ kpos) 0 (dyadic_interval_vec_triples acc))
                = mset (newdsc_pol_bail_int pol_final 0 1 split_pipeline_e0 0 (Poly Pinit0)))"
        using bail_main_list_correct[OF dpos len2P small_fastP sfP P0init canonP
            lenbP lrP capP2 kcapP, of split_pipeline_e0]
        by simp
      show ?thesis
        apply (refine_vcg Pinit_eq[unfolded Pinit0_def, THEN order_trans]
            mpz_pow2_monadic_spec[OF kpos_lt, THEN order_trans]
            solver[unfolded Pinit0_def, THEN order_trans])
        subgoal using len2P lenbP unfolding Pinit0_def by simp
        subgoal using len2P lenbP unfolding Pinit0_def by simp
        subgoal
          apply (rule dsc_carried_bail_pos_half_sound[OF P0 lrP p0P[unfolded Pinit0_def]
                sfP[unfolded Pinit0_def]])
          unfolding Pinit0_def by simp
        subgoal premises prems for x xa
        proof -
          from prems have acc_eq: "mset (dyadic_iv_acc_ivs 0 (2 ^ kpos) 0 (dyadic_interval_vec_triples x))
              = mset (newdsc_pol_bail_int pol_final 0 1 split_pipeline_e0 0 (Poly (scale_poly_list (2 ^ kpos) xs)))"
            and xa_pos: "0 < xa" and root: "ripoly (Poly xs) xa = 0" by auto
          have xa_lt: "xa < of_int ((2::int) ^ kpos)"
            using kpos_sound[rule_format, OF xa_pos] root by (simp add: of_int_power)
          show ?thesis
            using dsc_carried_bail_pos_half_complete[OF P0 lrP p0P[unfolded Pinit0_def]
                sfP[unfolded Pinit0_def] acc_eq xa_pos xa_lt root]
            by simp
        qed
        done
    qed
    done
qed

text \<open>The Newton NEGATIVE-half solve meets the sound+complete SPEC against \<open>refl_list xs\<close> (the
  negative roots of \<open>xs\<close> reflected into \<open>(0,\<infinity>)\<close>). Structurally the positive half prefixed
  with the ET-neg \<open>clone \<rightarrow> scale-by-(-1)\<close> front (\<open>Qb = refl_list xs\<close>) and the mid-body
  \<open>poly_free Qb\<close> (auto-discharged by \<open>refine_vcg\<close>, as in @{thm [source]
  bisection_isolate_all_split_neg_half_step}); the frame-scaling halves
  @{thm [source] dsc_carried_bail_pos_half_sound}/\<open>_complete\<close> are generic in \<open>xs\<close>, so they
  apply at \<open>refl_list xs\<close> directly.\<close>
lemma bail_split_neg_solve_half:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_bail_pre xs"
  shows "bail_split_neg_solve_monadic xs
    \<le> SPEC (\<lambda>accQ. (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. I = real_to_rat_pair J \<and>
            dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    unfolding dsc_isolate_all_split_bail_pre_def by simp
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
  \<comment> \<open>The precondition carries this clause at exactly this list, so it is an extraction
     rather than an instantiation of a \<open>\<forall>k\<close> clause re-stated at \<open>length (refl_list xs)\<close>.\<close>
  have capYQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (split_cap (refl_list xs))"
    using pre' unfolding dsc_isolate_all_split_pre_def by (auto simp: Let_def)
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have lenbQb: "length (refl_list xs) + 1 < max_snat LENGTH(gmp_poly_len)" using lenb by simp
  have poly_reflect_correct: "poly_reflect_in_place_monadic xs \<le> RETURN (refl_list xs)"
    using poly_reflect_in_place_correct[OF lenb] by (simp add: refl_list_def)
  show ?thesis
    unfolding bail_split_neg_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg
        poly_clone_monadic_correct[OF lenb, THEN order_trans]
        poly_reflect_correct[THEN order_trans]
        kiou_bound_k_monadic_spec_capped[OF len2Qb lastnzQb hrQb capYQb, THEN order_trans])
    \<comment> \<open>The unconditional \<open>poly_reflect_correct\<close> fact makes \<open>refine_vcg\<close> absorb the reflect-length
      ASSERT and split the conjunctive Kioustelidis ASSERT
      \<open>1 \<le> length (refl_list xs) \<and> length (refl_list xs) + 1 < max_snat\<close> into two subgoals. Six subgoals in
      total: clone length, the two Kioustelidis conjuncts, the two post-Kioustelidis conjuncts, and the
      final business logic.\<close>
    subgoal using len2Qb lenb lenbQb by (cases xs) auto
    subgoal using len2Qb lenb lenbQb by auto
    subgoal using len2Qb lenb lenbQb by auto
    \<comment> \<open>the post-kiou ASSERT \<open>kneg*len < max_snat\<close> and \<open>kneg < max_snat\<close> (two subgoals)\<close>
    subgoal premises p using p by simp
    subgoal premises p using p by simp
    \<comment> \<open>for a fixed kneg satisfying the root bound + caps: the body meets SPEC\<close>
    subgoal premises kp for kneg
    proof -
      from kp have kneg_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ kneg"
        and kneg_cap: "kneg * length (refl_list xs) < max_snat LENGTH(gmp_poly_len)"
        and kneg_lt: "kneg < max_snat LENGTH(gmp_poly_len)" by blast+
      define Qinit0 where "Qinit0 = scale_poly_list (2 ^ kneg) (refl_list xs)"
      have Qinit_eq: "split_init_pow2_l0_monadic kneg (refl_list xs) \<le> RETURN Qinit0"
        using split_init_pow2_l0_monadic_correct[OF lenbQb kneg_cap]
        by (simp add: Qinit0_def split_init_pow2_l0_eq_scale_poly_list)
      have npre: "blr_newdsc_int_pre
          (delta_P (map_poly of_int (Poly Qinit0) :: real poly))
          ((((split_pipeline_e0, 0), 2 ^ kneg), 0), Qinit0)"
        using dsc_isolate_all_split_neg_bail_pre[OF pre kneg_sound]
        unfolding Qinit0_def by simp
      define d where "d = delta_P (map_poly of_int (Poly Qinit0) :: real poly)"
      from npre have dpos: "d > 0" and len2Q: "Suc 0 < length Qinit0"
        and sfQ: "square_free (map_poly of_int (Poly Qinit0) :: real poly)"
        and Q0init: "Poly Qinit0 \<noteq> 0" and canonQ: "coeffs (Poly Qinit0) = Qinit0"
        and small_fastQ: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> d \<Longrightarrow> descartes_list_int a b Qinit0 \<le> 1"
        and lenbQ: "length Qinit0 + 2 < max_snat LENGTH(gmp_poly_len)"
        and lrQ: "(0::int) < 2 ^ kneg"
        and capQ2: "int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len))"
        and kcapQ: "int 0 + int (2 ^ newton_pol_ecap + 2)
            * (int (2 ^ Suc (dyadic_iv_interval_mu d (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len))"
        unfolding blr_newdsc_int_pre_def d_def by (auto simp: Let_def)
      have q0Q: "degree (Poly Qinit0) \<noteq> 0"
      proof -
        have "length (coeffs (Poly Qinit0)) = degree (Poly Qinit0) + 1" using Q0init by (rule length_coeffs)
        thus ?thesis using len2Q canonQ by simp
      qed
      have solver: "bail_main_list_monadic split_pipeline_e0 0 (2 ^ kneg) 0 Qinit0
          \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
              mset (dyadic_iv_acc_ivs 0 (2 ^ kneg) 0 (dyadic_interval_vec_triples acc))
                = mset (newdsc_pol_bail_int pol_final 0 1 split_pipeline_e0 0 (Poly Qinit0)))"
        using bail_main_list_correct[OF dpos len2Q small_fastQ sfQ Q0init canonQ
            lenbQ lrQ capQ2 kcapQ, of split_pipeline_e0]
        by simp
      show ?thesis
        apply (refine_vcg Qinit_eq[unfolded Qinit0_def, THEN order_trans]
            mpz_pow2_monadic_spec[OF kneg_lt, THEN order_trans]
            solver[unfolded Qinit0_def, THEN order_trans])
        subgoal using len2Q lenbQ unfolding Qinit0_def by simp
        subgoal using len2Q lenbQ unfolding Qinit0_def by simp
        subgoal
          apply (rule dsc_carried_bail_pos_half_sound[OF Q0 lrQ q0Q[unfolded Qinit0_def]
                sfQ[unfolded Qinit0_def]])
          unfolding Qinit0_def by simp
        subgoal premises prems for x xa
        proof -
          from prems have acc_eq: "mset (dyadic_iv_acc_ivs 0 (2 ^ kneg) 0 (dyadic_interval_vec_triples x))
              = mset (newdsc_pol_bail_int pol_final 0 1 split_pipeline_e0 0 (Poly (scale_poly_list (2 ^ kneg) (refl_list xs))))"
            and xa_pos: "0 < xa" and root: "ripoly (Poly (refl_list xs)) xa = 0" by auto
          have xa_lt: "xa < of_int ((2::int) ^ kneg)"
            using kneg_sound[rule_format, OF xa_pos] root by (simp add: of_int_power)
          show ?thesis
            using dsc_carried_bail_pos_half_complete[OF Q0 lrQ q0Q[unfolded Qinit0_def]
                sfQ[unfolded Qinit0_def] acc_eq xa_pos xa_lt root]
            by simp
        qed
        done
    qed
    done
qed

text \<open>The bail split pipeline is sound and complete against \<open>xs\<close> in each half's own frame, and the
  exact-zero flag is correct: the analogue of @{thm [source] bisection_isolate_all_split_main_correct}
  with the two bail solve stages in place of the bisection ones (the zero-check stage is shared).
  Because the pipeline calls the three named stage ops, the \<open>refine_vcg\<close> and \<open>order_trans\<close>
  composition applies directly. Completeness matters as well as soundness: the second conjunct of each
  half rules out an empty result by requiring every real root of \<open>xs\<close>/\<open>refl_list xs\<close> in \<open>(0,\<infinity>)\<close> to be
  covered (@{thm [source] bail_split_pos_solve_half}/\<open>bail_split_neg_solve_half\<close>).\<close>
theorem bail_isolate_all_split_main_correct:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_bail_pre xs"
  shows "bail_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accQ, xs0).
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)) \<and>
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)) \<and>
      xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  from pre have pre': "dsc_isolate_all_split_pre xs"
    unfolding dsc_isolate_all_split_bail_pre_def by simp
  have len2: "2 \<le> length xs" using pre' unfolding dsc_isolate_all_split_pre_def by auto
  show ?thesis
    unfolding bail_isolate_all_split_main_def PR_CONST_def
    apply (refine_vcg
        bail_split_pos_solve_half[OF pre, THEN order_trans]
        bail_split_neg_solve_half[OF pre, THEN order_trans]
        dsc_isolate_all_split_zero_check_correct[OF pre', THEN order_trans])
    using len2 by auto
qed

text \<open>Explicit termination corollary for the Newton pipeline (same reasoning as
  @{thm [source] bisection_isolate_all_split_main_terminates}: every loop is a well-founded
  \<open>RECT\<close>/\<open>WHILET\<close>, so \<open>\<le> SPEC\<close> genuinely excludes non-termination here).\<close>
corollary bail_isolate_all_split_main_terminates:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_bail_pre xs"
  shows "nofail (bail_isolate_all_split_main xs)"
  using bail_isolate_all_split_main_correct[OF pre] by (rule SPEC_nofail)

end