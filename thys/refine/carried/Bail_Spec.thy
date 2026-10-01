theory Bail_Spec
  imports Newton_Spec
begin

text \<open>The abstract layer of the cascade-bail Newton variant.

  \<^bold>\<open>Bail versus the plain @{const newdsc_pol}.\<close> The plain window choice tries Newton at location
  0, then Newton at location 1, then the two blocks, then bisects. Cascade bail: once a Newton probe
  is issued (its \<open>newton_at\<close> \<open>\<lambda>\<close> exists) and its snapped window is rejected (count \<open>\<noteq> v\<close>), skip the
  remaining tries and bisect.

  \<^bold>\<open>Why this is a small change to verify.\<close> Bail only ever routes to bisection where the plain
  function would try more windows. Skipping a window try can only make the tree bisect more, never
  accept a wrong interval, so soundness and completeness are the plain function's, with bail as one
  more route into the bisection sub-proof. The whole cascade is folded into one
  @{term try_window_bail} returning the accepted interval option, which gives
  @{term newdsc_pol_bail} a two-way body (accept \<Rightarrow> recurse, else \<Rightarrow> bisect).\<close>

section \<open>The bail-folded window try (real level)\<close>

text \<open>@{term "try_window_bail gn p a b N P v"}: the implementation's cascade
  (the twin of \<open>newton_window_choice_bail_monadic\<close>) as one pure function:
  \<^item> \<open>gn\<close> is the Newton gate;
  \<^item> location-0 probe \<open>newton_at v P a\<close>: if it exists, accept its snapped window iff count \<open>= v\<close>, else
    \<open>None\<close>, without falling through to location 1 (the bail);
  \<^item> only if location 0 missed (\<open>\<lambda>\<close> is \<open>None\<close>) is location 1 tried, with the same rule;
  \<^item> otherwise bisect (\<open>None\<close>).
  By contrast, @{const try_newton} still tries location 1 after location 0 rejects.

  This variant has no block windows, so \<open>newdsc_pol_bail\<close> reads only \<open>snd pol\<close>, and one
  \<open>pol_final = (gate, gate)\<close> serves both routes. @{const try_blocks} remains defined in \<open>NewDsc\<close> and
  used by @{const newdsc} and by the plain Newton route's \<open>try_blocks_g\<close>; the specification the
  multiset equality is stated against is unchanged.\<close>

definition try_window_bail ::
  "bool \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_window_bail gn p a b N P v =
     (if gn then
        (case newton_at v P a of
           Some lam1 \<Rightarrow>
             (let I1 = snap_window a b N lam1;
                  v1 = Bernstein_changes p (fst I1) (snd I1) P
              in if v1 = v then Some I1 else None)
         | None \<Rightarrow>
             (case newton_at v P b of
                Some lam2 \<Rightarrow>
                  (let I2 = snap_window a b N lam2;
                       v2 = Bernstein_changes p (fst I2) (snd I2) P
                   in if v2 = v then Some I2 else None)
              | None \<Rightarrow> None))
      else None)"

text \<open>\<^bold>\<open>Accept soundness.\<close> Every \<open>Some I\<close> branch is a \<open>snap_window\<close> (at location 0 or 1, bounded by
  @{thm [source] snap_window_inside} and \<open>snap_window_width\<close>), so an accepted window
  has the same geometry (contained in \<open>[a,b]\<close>, width \<open>(b-a)/N\<close>) as a plain @{const try_newton} accept.
  That is all the soundness, completeness and termination proofs need from the window step.\<close>
lemma try_window_bail_SomeD:
  assumes TW: "try_window_bail gn p a b N P v = Some I"
      and ab: "a < b"
      and Npos: "N > 0"
  defines "w \<equiv> b - a"
  shows "fst I \<ge> a" "snd I \<le> b" "snd I - fst I = w / of_nat N"
proof -
  have "fst I \<ge> a \<and> snd I \<le> b \<and> snd I - fst I = w / of_nat N"
  proof (cases gn)
    case gn: True
    show ?thesis
    proof (cases "newton_at v P a")
      case L1: (Some lam1)
      \<comment> \<open>loc0 issued: the only \<open>Some\<close> is its snap window\<close>
      from TW gn L1 have "Some I = Some (snap_window a b N lam1)"
        and "Bernstein_changes p (fst (snap_window a b N lam1)) (snd (snap_window a b N lam1)) P = v"
        by (auto simp: try_window_bail_def Let_def split: if_split_asm)
      then have I: "I = snap_window a b N lam1" by simp
      show ?thesis using snap_window_inside[OF ab Npos] snap_window_width[OF ab Npos]
        by (simp add: I w_def)
    next
      case L1none: None
      show ?thesis
      proof (cases "newton_at v P b")
        case L2: (Some lam2)
        from TW gn L1none L2 have I: "I = snap_window a b N lam2"
          by (auto simp: try_window_bail_def Let_def split: if_split_asm)
        show ?thesis using snap_window_inside[OF ab Npos] snap_window_width[OF ab Npos]
          by (simp add: I w_def)
      next
        case None
        \<comment> \<open>both probes missed: bail bisects, so \<open>Some I\<close> is impossible here (was: a blocks accept)\<close>
        with TW gn L1none show ?thesis
          by (auto simp: try_window_bail_def)
      qed
    qed
  next
    case False
    \<comment> \<open>Newton gate closed: \<open>None\<close> outright (was: the ungated blocks arm)\<close>
    with TW show ?thesis
      by (auto simp: try_window_bail_def)
  qed
  thus "fst I \<ge> a" "snd I \<le> b" "snd I - fst I = w / of_nat N" by simp_all
qed

lemma try_window_bail_Some_fst_lt_snd:
  assumes TW: "try_window_bail gn p a b N P v = Some I"
      and ab: "a < b" and Npos: "N > 0"
  shows "fst I < snd I"
proof -
  have "snd I - fst I = (b - a) / of_nat N" using try_window_bail_SomeD(3)[OF TW ab Npos] .
  moreover have "(b - a) / of_nat N > 0" using ab Npos by simp
  ultimately show ?thesis by linarith
qed

text \<open>\<^bold>\<open>Accept count.\<close> An accepted window's Bernstein count equals the node count \<open>v\<close>: every \<open>Some\<close>
  branch tests exactly this (\<open>v1 = v\<close> / \<open>v2 = v\<close> for the snapped windows). Together with
  @{thm [source] try_window_bail_SomeD}, this is everything the plain proofs used from
  @{thm [source] try_newton_SomeD} at the window step.\<close>
lemma try_window_bail_Some_count:
  assumes TW: "try_window_bail gn p a b N P v = Some I"
  shows "Bernstein_changes p (fst I) (snd I) P = v"
proof (cases gn)
  case gn: True
  show ?thesis
  proof (cases "newton_at v P a")
    case (Some lam1)
    with TW gn show ?thesis
      by (auto simp: try_window_bail_def Let_def split: if_split_asm)
  next
    case L1none: None
    show ?thesis
    proof (cases "newton_at v P b")
      case (Some lam2)
      with TW gn L1none show ?thesis
        by (auto simp: try_window_bail_def Let_def split: if_split_asm)
    next
      case None
      \<comment> \<open>both probes missed \<Rightarrow> \<open>None\<close>, contradicting \<open>= Some I\<close> (was: a blocks accept)\<close>
      with TW gn L1none show ?thesis
        by (auto simp: try_window_bail_def)
    qed
  qed
next
  case False
  \<comment> \<open>Newton gate closed \<Rightarrow> \<open>None\<close>, contradicting \<open>= Some I\<close> (was: the ungated blocks arm)\<close>
  with TW show ?thesis
    by (auto simp: try_window_bail_def)
qed

section \<open>The bail recursion (real level, e-form)\<close>

function (domintros) newdsc_pol_bail ::
  "newton_pol_real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real poly
     \<Rightarrow> (real \<times> real) list"
where
  "newdsc_pol_bail pol p a b e dk s P =
     (let v = Bernstein_changes p a b P in
      if v = 0 then []
      else if v = 1 then [(a, b)]
      else
        \<comment> \<open>Reads only \<open>snd pol\<close> (the Newton gate), which is why one \<open>pol_final = (gate, gate)\<close> serves
           this route and the plain Newton route (which reads \<open>fst\<close> for its blocks).\<close>
        (case try_window_bail (snd (pol p a b e dk (s, v))) p a b (N_of e) P v of
           Some I \<Rightarrow> newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
         | None \<Rightarrow>
             (let m  = (a + b) / 2;
                  e' = max 1 (e - 1);
                  s' = split_run_len_real p P a b s;
                  mid_root = (if poly P m = 0 then [(m, m)] else [])
              in mid_root @ newdsc_pol_bail pol p a m e' (dk + 1) s' P
                        @ newdsc_pol_bail pol p m b e' (dk + 1) s' P)))"
  by pat_completeness auto

text \<open>Termination — a verbatim structural clone of @{thm [source] newdsc_pol_domI_general}, with
  the plain \<open>newton_case\<close>/\<open>block_case\<close> pair collapsed into ONE \<open>window_case\<close> (the accepted interval
  from @{const try_window_bail} has the same width \<open>(b-a)/N_of e\<close>, so \<open>\<mu>\<close> decreases identically).\<close>
lemma newdsc_pol_bail_domI_general:
  fixes \<delta> :: real and p :: nat and P :: "real poly" and pol :: newton_pol_real
  assumes \<delta>_pos: "\<delta> > 0"
    and small: "\<And>a b. a < b \<Longrightarrow> b - a \<le> \<delta> \<Longrightarrow> Bernstein_changes p a b P \<le> 1"
  shows "\<And>a b e dk s. a < b \<Longrightarrow> newdsc_pol_bail_dom (pol, p, a, b, e, dk, s, P)"
proof -
  define \<mu> where "\<mu> = (\<lambda>a b. mu \<delta> a b)"
  let ?Prop =
    "\<lambda>n::nat. \<forall>a b e dk s. \<mu> a b < n \<longrightarrow> a < b \<longrightarrow> newdsc_pol_bail_dom (pol, p, a, b, e, dk, s, P)"
  have step: "\<And>n. (\<And>m. m < n \<Longrightarrow> ?Prop m) \<Longrightarrow> ?Prop n"
  proof -
    fix n
    assume IH: "\<And>m. m < n \<Longrightarrow> ?Prop m"
    show "?Prop n"
    proof (intro allI impI)
      fix a b :: real and e dk s :: nat
      assume mu_lt_n: "\<mu> a b < n" and ab: "a < b"
      show "newdsc_pol_bail_dom (pol, p, a, b, e, dk, s, P)"
      proof -
        let ?v = "Bernstein_changes p a b P"
        let ?gn = "snd (pol p a b e dk (s, ?v))"
        show ?thesis
        proof (cases "?v = 0 \<or> ?v = 1")
          case True
          then show ?thesis by (auto intro: newdsc_pol_bail.domintros)
        next
          case False
          have v_ge2: "2 \<le> ?v" using False Bernstein_changes_def by fastforce
          have \<delta>_lt_width: "\<delta> < b - a"
          proof (rule ccontr)
            assume "\<not> \<delta> < b - a"
            then have "b - a \<le> \<delta>" by linarith
            then have "Bernstein_changes p a b P \<le> 1" using ab small by presburger
            with v_ge2 show False by linarith
          qed
          have IH_at_mu: "?Prop (\<mu> a b)" using IH mu_lt_n by simp
          have Nof_pos: "N_of e > 0" using N_of_ge_2[of e] by simp

          have window_case:
            "\<forall>I. try_window_bail ?gn p a b (N_of e) P ?v = Some I \<longrightarrow>
                 newdsc_pol_bail_dom (pol, p, fst I, snd I, e + 1, dk + (2 ^ e + 2), s, P)"
          proof (intro allI impI)
            fix I
            assume TW: "try_window_bail ?gn p a b (N_of e) P ?v = Some I"
            have width_I: "snd I - fst I = (b - a) / of_nat (N_of e)"
              using try_window_bail_SomeD(3)[OF TW ab Nof_pos] by simp
            have mu_less: "\<mu> (fst I) (snd I) < \<mu> a b"
              using \<delta>_pos ab \<delta>_lt_width N_of_ge_2[of e] width_I
              by (simp add: \<mu>_def mu_subinterval_factor_strict)
            have fst_lt_snd: "fst I < snd I"
              using try_window_bail_Some_fst_lt_snd[OF TW ab Nof_pos] .
            show "newdsc_pol_bail_dom (pol, p, fst I, snd I, e + 1, dk + (2 ^ e + 2), s, P)"
              using IH_at_mu mu_less fst_lt_snd by blast
          qed

          define m where "m = (a + b) / 2"
          have am: "a < m" and mb: "m < b" using ab by (simp_all add: m_def)
          have mu_left_strict: "\<mu> a m < \<mu> a b"
            by (simp add: \<mu>_def \<delta>_pos \<delta>_lt_width ab m_def mu_halve_strict(1))
          have mu_right_strict: "\<mu> m b < \<mu> a b"
            by (simp add: \<mu>_def \<delta>_pos \<delta>_lt_width ab m_def mu_halve_strict(2))
          have IH_left: "\<And>e' dk' s'. newdsc_pol_bail_dom (pol, p, a, m, e', dk', s', P)"
            using IH_at_mu mu_left_strict am by blast
          have IH_right: "\<And>e' dk' s'. newdsc_pol_bail_dom (pol, p, m, b, e', dk', s', P)"
            using IH_at_mu mu_right_strict mb by blast
          show ?thesis
            by (rule newdsc_pol_bail.domintros)
               (use IH_left IH_right window_case in \<open>auto simp: m_def\<close>)
        qed
      qed
    qed
  qed
  have all_Prop: "\<And>n. ?Prop n" by (rule less_induct, rule step)
  show "\<And>a b e dk s. a < b \<Longrightarrow> newdsc_pol_bail_dom (pol, p, a, b, e, dk, s, P)"
    using all_Prop by blast
qed

section \<open>Soundness for all pol (\<open>dsc_pair_ok\<close>)\<close>

text \<open>Clone of @{thm [source] newdsc_pol_sound} with the 3-way (newton/block/bisect) window
  case collapsed to the bail 2-way (window/bisect): the plain \<open>IH_newton\<close>+\<open>IH_block\<close> merge into
  one \<open>IH_window\<close> (fed by @{thm [source] try_window_bail_Some_fst_lt_snd}, IH index 3), and the
  bisection sub-proof \<open>IH_LR\<close> is the plain one verbatim (IH indices 1/2), reached from the single
  \<open>None\<close> case instead of the plain \<open>try_newton=None \<and> try_blocks=None\<close>.\<close>
theorem newdsc_pol_bail_sound:
  assumes dom: "newdsc_pol_bail_dom (pol, p, a, b, e, dk, s, P)"
      and deg: "degree P \<le> p"
      and P0:  "P \<noteq> 0"
      and ab:  "a < b"
  shows "\<forall>I \<in> set (newdsc_pol_bail pol p a b e dk s P). dsc_pair_ok P I"
  using dom deg P0 ab
proof (induction pol p a b e dk s P rule: newdsc_pol_bail.pinduct)
  case (1 pol p a b e dk s P)
  have newdsc_eq:
    "newdsc_pol_bail pol p a b e dk s P =
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a, b)]
        else
          (case try_window_bail (snd (pol p a b e dk (s, v)))
                  p a b (N_of e) P v of
             Some I \<Rightarrow> newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
           | None \<Rightarrow>
               (let m  = (a + b) / 2;
                    e' = max 1 (e - 1);
                    s' = split_run_len_real p P a b s;
                    mid_root = (if poly P m = 0 then [(m, m)] else [])
                in mid_root @ newdsc_pol_bail pol p a m e' (dk + 1) s' P
                          @ newdsc_pol_bail pol p m b e' (dk + 1) s' P)))"
    using "1.hyps" newdsc_pol_bail.psimps by blast

  show ?case
  proof -
    from 1 have ab: "a < b" and P0': "P \<noteq> 0" and deg': "degree P \<le> p" by blast+
    let ?v = "Bernstein_changes p a b P"
    let ?gn = "snd (pol p a b e dk (s, ?v))"
    show ?thesis
    proof (cases "?v = 0")
      case True
      then show ?thesis by (simp add: newdsc_eq Let_def)
    next
      case v0_ne: False
      show ?thesis
      proof (cases "?v = 1")
        case v1: True
        have v1_exact: "roots_in P a b = 1"
          using Bernstein_changes_1_one_root[OF deg' P0' ab v1] .
        have dsc_ok_ab: "dsc_pair_ok P (a, b)"
          using v1_exact ab by (simp add: dsc_pair_ok_def roots_in_def)
        show ?thesis using v1 v0_ne dsc_ok_ab by (simp add: newdsc_eq Let_def)
      next
        case v_ge2: False
        then have v_ge2': "?v \<ge> 2"
          using v0_ne by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)
        have Nof_pos: "N_of e > 0" using N_of_ge_2[of e] by simp

        have IH_window:
          "\<And>I. try_window_bail ?gn p a b (N_of e) P ?v = Some I \<Longrightarrow>
                \<forall>J\<in>set (newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                   dsc_pair_ok P J"
        proof -
          fix I
          assume TW: "try_window_bail ?gn p a b (N_of e) P ?v = Some I"
          have fst_lt_snd: "fst I < snd I"
            using try_window_bail_Some_fst_lt_snd[OF TW ab Nof_pos] .
          show "\<forall>J\<in>set (newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                   dsc_pair_ok P J"
            using "1.IH"(3) TW deg' P0' fst_lt_snd v0_ne v_ge2 by blast
        qed

        have IH_LR:
          "\<And>m e' s'.
             \<lbrakk>try_window_bail ?gn p a b (N_of e) P ?v = None;
              m = (a + b) / 2; e' = max 1 (e - 1);
              s' = split_run_len_real p P a b s\<rbrakk> \<Longrightarrow>
             (\<forall>I\<in>set (newdsc_pol_bail pol p a m e' (dk + 1) s' P). dsc_pair_ok P I) \<and>
             (\<forall>I\<in>set (newdsc_pol_bail pol p m b e' (dk + 1) s' P). dsc_pair_ok P I)"
        proof -
          fix m e' s'
          assume TW0: "try_window_bail ?gn p a b (N_of e) P ?v = None"
             and m_def: "m = (a + b) / 2"
             and e'_def: "e' = max 1 (e - 1)"
             and s'_def: "s' = split_run_len_real p P a b s"
          have IH_left: "\<forall>I\<in>set (newdsc_pol_bail pol p a m e' (dk + 1) s' P). dsc_pair_ok P I"
            using "1.IH"(1) deg' v0_ne v_ge2 TW0 m_def e'_def s'_def P0' ab
            by (metis field_less_half_sum)
          have IH_right: "\<forall>I\<in>set (newdsc_pol_bail pol p m b e' (dk + 1) s' P). dsc_pair_ok P I"
            using "1.IH"(2) deg' v0_ne v_ge2 TW0 m_def e'_def s'_def P0' ab
            by (metis gt_half_sum one_add_one)
          show "(\<forall>I\<in>set (newdsc_pol_bail pol p a m e' (dk + 1) s' P). dsc_pair_ok P I) \<and>
                (\<forall>I\<in>set (newdsc_pol_bail pol p m b e' (dk + 1) s' P). dsc_pair_ok P I)"
            using IH_left IH_right by simp
        qed

        show ?thesis
        proof (cases "try_window_bail ?gn p a b (N_of e) P ?v")
          case (Some I)
          then have "\<forall>J\<in>set (newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                        dsc_pair_ok P J"
            using IH_window by blast
          thus ?thesis using Some v0_ne v_ge2 by (simp add: newdsc_eq Let_def)
        next
          case TW_None: None
          let ?m = "(a + b) / 2"
          let ?e' = "max 1 (e - 1)"
          let ?s' = "split_run_len_real p P a b s"
          from IH_LR[OF TW_None refl refl refl]
          have left_ok:  "\<forall>I\<in>set (newdsc_pol_bail pol p a ?m ?e' (dk + 1) ?s' P). dsc_pair_ok P I"
            and right_ok: "\<forall>I\<in>set (newdsc_pol_bail pol p ?m b ?e' (dk + 1) ?s' P). dsc_pair_ok P I"
            by auto
          have mid_ok:
            "\<forall>I\<in>set (if poly P ?m = 0 then [(?m, ?m)] else []). dsc_pair_ok P I"
          proof (cases "poly P ?m = 0")
            case True
            then have "set (if poly P ?m = 0 then [(?m, ?m)] else []) = {(?m, ?m)}" by auto
            moreover have "dsc_pair_ok P (?m, ?m)"
              using True by (simp add: dsc_pair_ok_def)
            ultimately show ?thesis by auto
          next
            case False then show ?thesis by (simp add: dsc_pair_ok_def)
          qed
          show ?thesis
            using newdsc_eq TW_None v0_ne v_ge2 left_ok right_ok mid_ok
            by (auto simp: Let_def)
        qed
      qed
    qed
  qed
qed

section \<open>Completeness for all pol (coverage)\<close>

text \<open>Clone of @{thm [source] newdsc_pol_complete}, collapsed to the bail 2-way. The load-bearing
  \<open>Some I\<close> case (the root \<open>x\<close> is strictly inside the accepted window) is the plain \<open>try_newton\<close>
  copy of \<open>pos_in_I\<close> VERBATIM — it is generic in \<open>I_props\<close>/\<open>v_I\<close>/\<open>split_props\<close>, which here come
  from @{thm [source] try_window_bail_SomeD}/@{thm [source] try_window_bail_Some_count}/@{thm
  [source] try_window_bail_Some_fst_lt_snd} instead of \<open>try_newton_SomeD\<close> + the inline
  \<open>try_newton_def\<close> extraction. The \<open>None\<close> case is the plain bisection disjunction verbatim.\<close>
theorem newdsc_pol_bail_complete_strong:
  assumes dom: "newdsc_pol_bail_dom (pol, p, a, b, e, dk, s, P)"
      and deg: "degree P \<le> p"
      and P0:  "P \<noteq> 0"
  shows "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol_bail pol p a b e dk s P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x))"
  using dom deg P0
proof (induction pol p a b e dk s P rule: newdsc_pol_bail.pinduct)
  case (1 pol p a b e dk s P)
  have newdsc_eq:
    "newdsc_pol_bail pol p a b e dk s P =
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a, b)]
        else
          (case try_window_bail (snd (pol p a b e dk (s, v)))
                  p a b (N_of e) P v of
             Some I \<Rightarrow> newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
           | None \<Rightarrow>
               (let m  = (a + b) / 2;
                    e' = max 1 (e - 1);
                    s' = split_run_len_real p P a b s;
                    mid_root = (if poly P m = 0 then [(m, m)] else [])
                in mid_root @ newdsc_pol_bail pol p a m e' (dk + 1) s' P
                          @ newdsc_pol_bail pol p m b e' (dk + 1) s' P)))"
    using "1.hyps" newdsc_pol_bail.psimps by blast

  show ?case
  proof -
    have H:
      "\<And>x::real. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (newdsc_pol_bail pol p a b e dk s P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x))"
    proof -
      fix x :: real
      assume root: "poly P x = 0" and ax: "a < x" and xb: "x < b"
      show "\<exists>I\<in>set (newdsc_pol_bail pol p a b e dk s P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)"
      proof (cases "a \<ge> b \<or> P = 0")
        case True
        from True ax xb have False using "1.prems" by argo
        then show ?thesis by blast
      next
        case False
        hence ab: "a < b" and P0': "P \<noteq> 0" by auto
        from 1 have deg': "degree P \<le> p" by blast
        let ?v = "Bernstein_changes p a b P"
        let ?gn = "snd (pol p a b e dk (s, ?v))"
        have Nof_pos: "N_of e > 0" using N_of_ge_2[of e] by simp

        have v_nonzero: "?v \<noteq> 0"
        proof
          assume "?v = 0"
          then have "roots_in P a b = 0"
            using Bernstein_changes_0_no_root[OF deg' P0' ab] by simp
          then have "poly P x \<noteq> 0"
            using ax xb Bernstein_changes_pos_of_root P0' \<open>?v = 0\<close> ab deg' by blast
          with root show False by simp
        qed

        show ?thesis
        proof (cases "?v = 1")
          case v1: True
          have mem: "(a,b) \<in> set (newdsc_pol_bail pol p a b e dk s P)"
            using newdsc_eq v1 v_nonzero by (simp add: Let_def)
          show ?thesis
          proof (intro bexI[of _ "(a,b)"])
            show "(fst (a,b) < x \<and> x < snd (a,b)) \<or> (fst (a,b) = x \<and> snd (a,b) = x)" using ax xb by simp
          next
            show "(a,b) \<in> set (newdsc_pol_bail pol p a b e dk s P)" using mem .
          qed
        next
          case v_ne1: False
          hence v_ge2: "?v \<ge> 2"
            using v_nonzero by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)

          have IH_window:
            "\<And>I x. \<lbrakk> try_window_bail ?gn p a b (N_of e) P ?v = Some I;
                       poly P x = 0; fst I < x; x < snd I \<rbrakk> \<Longrightarrow>
                   \<exists>J\<in>set (newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                      (fst J < x \<and> x < snd J) \<or> (fst J = x \<and> snd J = x)"
            using "1.IH"(3) deg' v_ne1 v_nonzero P0' by presburger

          have IH_LR:
            "\<And>m e' s' x.
               \<lbrakk> try_window_bail ?gn p a b (N_of e) P ?v = None;
                  m = (a + b) / 2; e' = max 1 (e - 1);
                  s' = split_run_len_real p P a b s;
                  poly P x = 0; a < x; x < b \<rbrakk> \<Longrightarrow>
               (\<exists>I\<in>set (newdsc_pol_bail pol p a m e' (dk + 1) s' P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)) \<or>
               (\<exists>I\<in>set (newdsc_pol_bail pol p m b e' (dk + 1) s' P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)) \<or>
               (x = m)"
          proof -
            fix m e' s' x
            assume TW0: "try_window_bail ?gn p a b (N_of e) P ?v = None"
               and m_def: "m = (a + b) / 2"
               and e'_def: "e' = max 1 (e - 1)"
               and s'_def: "s' = split_run_len_real p P a b s"
               and rootx: "poly P x = 0" and ax': "a < x" and xb': "x < b"
            have am: "a < m" and mb: "m < b" using ab by (simp_all add: m_def)
            show "(\<exists>I\<in>set (newdsc_pol_bail pol p a m e' (dk + 1) s' P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)) \<or>
                  (\<exists>I\<in>set (newdsc_pol_bail pol p m b e' (dk + 1) s' P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)) \<or> x = m"
            proof (cases "x < m")
              case True
              then have "a < x" "x < m" using ax' xb' am by auto
              then have "\<exists>I\<in>set (newdsc_pol_bail pol p a m e' (dk + 1) s' P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)"
                using "1.IH"(1) deg' v_ne1 v_nonzero TW0 m_def e'_def s'_def rootx P0' by blast
              then show ?thesis by blast
            next
              case False
              then consider "x = m" | "x > m" by linarith
              then show ?thesis
              proof cases
                case 1 then show ?thesis by blast
              next
                case 2
                then have "m < x" "x < b" using xb' mb by auto
                then have "\<exists>I\<in>set (newdsc_pol_bail pol p m b e' (dk + 1) s' P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)"
                  using "1.IH"(2) e'_def s'_def P0' TW0 ab deg' m_def rootx v_ne1 v_nonzero by blast
                then show ?thesis by blast
              qed
            qed
          qed

          show ?thesis
          proof (cases "try_window_bail ?gn p a b (N_of e) P ?v")
            case (Some I)
            then have TW: "try_window_bail ?gn p a b (N_of e) P ?v = Some I" by simp
            have pos_in_I: "fst I < x \<and> x < snd I"
            proof -
              define w where "w = b - a"
              have "w > 0" using ab w_def by simp
              have I_props: "fst I \<ge> a \<and> snd I \<le> b \<and> snd I - fst I = w / of_nat (N_of e)"
                using try_window_bail_SomeD[OF TW ab Nof_pos] w_def by simp
              have split_props: "fst I < snd I"
                using try_window_bail_Some_fst_lt_snd[OF TW ab Nof_pos] .
              have v_I: "Bernstein_changes p (fst I) (snd I) P = ?v"
                using try_window_bail_Some_count[OF TW] .
              have not_left: "\<not> (x < fst I)"
              proof
                assume "x < fst I"
                hence "a < x" "x < fst I" using ax by simp_all
                hence "Bernstein_changes p a (fst I) P \<ge> 1"
                  using Bernstein_changes_pos_of_root[OF deg' P0' _ root]
                  by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)
                have "Bernstein_changes p a b P \<ge>
                      Bernstein_changes p a (fst I) P + Bernstein_changes p (fst I) b P"
                  using Bernstein_changes_split[OF _ _ deg'] I_props \<open>a < x\<close> \<open>x < fst I\<close> split_props by simp
                moreover have "Bernstein_changes p (fst I) b P \<ge> Bernstein_changes p (fst I) (snd I) P"
                  using Bernstein_changes_split[OF split_props _ deg'] I_props
                  by (smt (verit) Bernstein_changes_def int_nat_eq)
                ultimately have "?v \<ge> 1 + ?v"
                  using v_I \<open>1 \<le> Bernstein_changes p a (fst I) P\<close> by linarith
                thus False by simp
              qed
              have not_right: "\<not> (x > snd I)"
              proof
                assume "x > snd I"
                hence "snd I < x" "x < b" using xb by simp_all
                hence "Bernstein_changes p (snd I) b P \<ge> 1"
                  using Bernstein_changes_pos_of_root[OF deg' P0' _ root]
                  by (metis Bernstein_changes_def I_props add_0 dual_order.order_iff_strict
                      int_one_le_iff_zero_less not_less_iff_gr_or_eq zle_iff_zadd)
                have "Bernstein_changes p a b P \<ge>
                      Bernstein_changes p a (snd I) P + Bernstein_changes p (snd I) b P"
                  using Bernstein_changes_split[OF _ _ deg'] I_props \<open>snd I < x\<close> \<open>x < b\<close> split_props by simp
                moreover have "Bernstein_changes p a (snd I) P \<ge> Bernstein_changes p (fst I) (snd I) P"
                  using Bernstein_changes_split[OF _ split_props deg'] I_props split_props
                  by (smt (verit, ccfv_SIG) Bernstein_changes_def int_nat_eq)
                ultimately have "?v \<ge> ?v + 1"
                  using v_I \<open>1 \<le> Bernstein_changes p (snd I) b P\<close> by linarith
                thus False by simp
              qed
              have "x \<noteq> fst I"
              proof
                assume "x = fst I"
                then have "poly P (fst I) = 0" using root by simp
                have "Bernstein_changes p a (fst I) P + Bernstein_changes p (fst I) b P + 1
                      \<le> Bernstein_changes p a b P"
                  using Bernstein_changes_split_root \<open>x = fst I\<close> ax deg' root xb P0' by blast
                moreover have "Bernstein_changes p (fst I) b P \<ge> ?v"
                proof -
                  have "Bernstein_changes p (fst I) b P =
                        Bernstein_changes p (fst I) (snd I) P + Bernstein_changes p (snd I) b P"
                    using Bernstein_changes_split[OF split_props _ deg'] I_props
                    by (smt (verit, ccfv_SIG) Bernstein_changes_def calculation of_nat_0_le_iff v_I)
                  show ?thesis using Bernstein_changes_split[OF split_props _ deg'] I_props v_I
                    by (metis Bernstein_changes_def
                        \<open>Bernstein_changes p (fst I) b P = Bernstein_changes p (fst I) (snd I) P + Bernstein_changes p (snd I) b P\<close>
                        zle_iff_zadd)
                qed
                ultimately have "0 + ?v + 1 \<le> ?v"
                  using Bernstein_changes_split[OF _ _ deg'] I_props
                  by (smt (verit, ccfv_threshold) Bernstein_changes_def of_nat_0_le_iff)
                thus False by simp
              qed
              have "x \<noteq> snd I"
              proof
                assume "x = snd I"
                then have "poly P (snd I) = 0" using root by simp
                have "Bernstein_changes p a (snd I) P + Bernstein_changes p (snd I) b P + 1
                      \<le> Bernstein_changes p a b P"
                  using Bernstein_changes_split_root \<open>x = snd I\<close> ax deg' xb \<open>poly P (snd I) = 0\<close> P0'
                  by blast
                moreover have "Bernstein_changes p a (snd I) P \<ge> ?v"
                  using Bernstein_changes_split[OF _ split_props deg'] I_props v_I
                  by (metis Bernstein_changes_def \<open>x = snd I\<close> add.commute
                      dual_order.order_iff_strict dual_order.trans zle_iff_zadd)
                ultimately have "?v + 0 + 1 \<le> ?v"
                  by (smt (verit, ccfv_SIG) Bernstein_changes_def int_nat_eq)
                thus False by simp
              qed
              show "fst I < x \<and> x < snd I"
                using not_left not_right \<open>x \<noteq> fst I\<close> \<open>x \<noteq> snd I\<close> linorder_less_linear by blast
            qed
            then have fstI_lt: "fst I < x" and x_lt_sndI: "x < snd I" by auto
            from IH_window[OF TW root fstI_lt x_lt_sndI]
            obtain J where J_in: "J \<in> set (newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P)"
                          and J_cov: "(fst J < x \<and> x < snd J) \<or> (fst J = x \<and> snd J = x)" by blast
            have "newdsc_pol_bail pol p a b e dk s P
                    = newdsc_pol_bail pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P"
              using newdsc_eq Some v_ne1 v_nonzero by (simp add: Let_def)
            then show ?thesis using J_in J_cov by auto
          next
            case TW_None: None
            define m where "m = (a + b) / 2"
            define e' where "e' = max 1 (e - 1)"
            define s' where "s' = split_run_len_real p P a b s"
            have split:
              "(\<exists>I\<in>set (newdsc_pol_bail pol p a m e' (dk + 1) s' P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)) \<or>
               (\<exists>I\<in>set (newdsc_pol_bail pol p m b e' (dk + 1) s' P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)) \<or> x = m"
              using IH_LR[OF TW_None m_def e'_def s'_def root ax xb] .
            have eq_lin:
              "newdsc_pol_bail pol p a b e dk s P =
                 (if poly P m = 0 then [(m, m)] else [])
                 @ newdsc_pol_bail pol p a m e' (dk + 1) s' P
                 @ newdsc_pol_bail pol p m b e' (dk + 1) s' P"
              using newdsc_eq TW_None v_ne1 v_nonzero
              by (simp add: Let_def m_def e'_def s'_def)
            from split show ?thesis
            proof (elim disjE)
              assume "\<exists>I\<in>set (newdsc_pol_bail pol p a m e' (dk + 1) s' P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)"
              then show ?thesis using eq_lin by auto
            next
              assume "\<exists>I\<in>set (newdsc_pol_bail pol p m b e' (dk + 1) s' P). (fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)"
              then show ?thesis using eq_lin by auto
            next
              assume mid: "x = m"
              then have "poly P m = 0" using root by blast
              then have memm: "(m, m) \<in> set (newdsc_pol_bail pol p a b e dk s P)" using eq_lin by simp
              show ?thesis
              proof (intro bexI[of _ "(m,m)"])
                show "(fst (m,m) < x \<and> x < snd (m,m)) \<or> (fst (m,m) = x \<and> snd (m,m) = x)" using mid by simp
              next
                show "(m,m) \<in> set (newdsc_pol_bail pol p a b e dk s P)" using memm .
              qed
            qed
          qed
        qed
      qed
    qed
    show ?thesis using "1.prems" H by blast
  qed
qed

text \<open>\<^bold>\<open>Why the conclusion above is strict-or-degenerate.\<close> The closed covering
  \<open>fst I \<le> x \<and> x \<le> snd I\<close>, kept below as a corollary, is too weak to be an isolation statement: a
  root lying exactly between two adjacent emitted intervals satisfies it for both while being
  isolated by neither. The power-substitution back-map needs the strict form, and every case of the
  induction establishes it:

  \<^item> \<open>v = 1\<close> emits \<open>(a, b)\<close>, and the hypotheses are \<open>a < x\<close>, \<open>x < b\<close>;
  \<^item> the Newton/bail accept case proves \<open>pos_in_I : fst I < x \<and> x < snd I\<close>: the three
    \<open>Bernstein_changes_split\<close> arguments above rule out \<open>x = fst I\<close> and \<open>x = snd I\<close>;
  \<^item> the bisect case's \<open>x = m\<close> branch exhibits the degenerate pair \<open>(m, m)\<close>, which the recursion emits
    for this reason (\<open>mid_root = (if poly P m = 0 then [(m,m)] else [])\<close>).\<close>

theorem newdsc_pol_bail_complete:
  assumes dom: "newdsc_pol_bail_dom (pol, p, a, b, e, dk, s, P)"
      and deg: "degree P \<le> p"
      and P0:  "P \<noteq> 0"
  shows "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol_bail pol p a b e dk s P). fst I \<le> x \<and> x \<le> snd I)"
proof -
  fix x :: real
  assume A: "poly P x = 0" and B: "a < x" and C: "x < b"
  from newdsc_pol_bail_complete_strong[OF dom deg P0 A B C]
  obtain I where Iin: "I \<in> set (newdsc_pol_bail pol p a b e dk s P)"
    and Icov: "(fst I < x \<and> x < snd I) \<or> (fst I = x \<and> snd I = x)" by blast
  from Icov have "fst I \<le> x \<and> x \<le> snd I" by auto
  with Iin show "\<exists>I \<in> set (newdsc_pol_bail pol p a b e dk s P). fst I \<le> x \<and> x \<le> snd I"
    by blast
qed

text \<open>Termination on squarefree input — clone of @{thm [source] newdsc_pol_terminates_squarefree},
  instantiating @{thm [source] newdsc_pol_bail_domI_general} with the squarefree smallness witness.\<close>
theorem newdsc_pol_bail_terminates_squarefree:
  fixes P :: "real poly"
  assumes P0:  "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0:  "p \<noteq> 0"
      and sf:  "square_free P"
  shows "\<And>a b e dk s. a < b \<Longrightarrow> newdsc_pol_bail_dom (pol, p, a, b, e, dk, s, P)"
proof -
  have \<delta>_pos: "delta_P P > 0" using P0 delta_P_pos by blast
  have small: "\<And>a b. a < b \<Longrightarrow> b - a \<le> delta_P P \<Longrightarrow> Bernstein_changes p a b P \<le> 1"
    using Bernstein_changes_small_interval_le_1 P0 deg p0 sf rsquarefree_lift by blast
  show "\<And>a b e dk s. a < b \<Longrightarrow> newdsc_pol_bail_dom (pol, p, a, b, e, dk, s, P)"
    using newdsc_pol_bail_domI_general[OF \<delta>_pos small] by blast
qed

section \<open>Int level: the bail-folded window try + worklist recursion\<close>

text \<open>The integer twin of @{const try_window_bail}: the same fold, with @{const newton_at} on the real
  embedding, @{const snap_window_rat} for the rational endpoints, and @{const descartes_list_int} for
  the count. Like the real-level function it has no block arm.\<close>

definition try_window_bail_int ::
  "bool \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> nat \<Rightarrow> (rat \<times> rat) option"
where
  "try_window_bail_int gn a b N P v =
     (let P_real = map_poly of_int P :: real poly in
      if gn then
        (case newton_at (int v) P_real (of_rat a) of
           Some lam1 \<Rightarrow>
             (let I1 = snap_window_rat a b N lam1;
                  v1 = descartes_list_int (fst I1) (snd I1) (coeffs P)
              in if v1 = v then Some I1 else None)
         | None \<Rightarrow>
             (case newton_at (int v) P_real (of_rat b) of
                Some lam2 \<Rightarrow>
                  (let I2 = snap_window_rat a b N lam2;
                       v2 = descartes_list_int (fst I2) (snd I2) (coeffs P)
                   in if v2 = v then Some I2 else None)
              | None \<Rightarrow> None))
      else None)"

text \<open>The int\<leftrightarrow>real correspondence, in \<open>map_option\<close> form (both None- and Some-directions at once).
  Proof technique is @{thm [source] try_newton_int_Some_iff}'s: unfold both defs, feed the
  per-snap count correspondence \<open>v_snap\<close> + @{thm [source] snap_window_rat_eq}, and the block-arm
  @{term map_option} correspondence \<open>blk\<close>, close by \<open>smt\<close> (\<open>newton_at\<close> is literally the same term
  on both sides).\<close>

lemma try_blocks_int_map_option:
  assumes ab: "a < b" and P0: "P \<noteq> 0" and Npos: "N > 0"
      and pdeg: "p = degree (map_poly of_int P :: real poly)"
  shows "try_blocks p (of_rat a) (of_rat b) N (map_poly of_int P :: real poly) (int v)
         = map_option (\<lambda>I. (of_rat (fst I), of_rat (snd I))) (try_blocks_int a b N P v)"
proof -
  let ?P_real = "map_poly of_int P :: real poly"
  let ?w = "(b - a) / of_nat N"
  have N_pos: "of_nat N > (0::rat)" using Npos by simp
  have w_pos: "?w > 0" using ab N_pos by simp
  have b1_ord: "a < a + ?w" using w_pos by simp
  have b2_ord: "b - ?w < b" using w_pos by simp
  \<comment> \<open>count correspondences on the two blocks (int \<open>descartes_list_int\<close> = real \<open>Bernstein_changes\<close>)\<close>
  have v1_eq: "int (descartes_list_int a (a + ?w) (coeffs P))
               = Bernstein_changes p (of_rat a) (of_rat (a + ?w)) ?P_real"
    using descartes_roots_test_sc_of_int[OF b1_ord P0]
          descartes_roots_test_sc_eq_Bernstein_changes pdeg by simp
  have v2_eq: "int (descartes_list_int (b - ?w) b (coeffs P))
               = Bernstein_changes p (of_rat (b - ?w)) (of_rat b) ?P_real"
    using descartes_roots_test_sc_of_int[OF b2_ord P0]
          descartes_roots_test_sc_eq_Bernstein_changes pdeg by simp
  \<comment> \<open>endpoint homomorphisms (real block endpoints = \<open>of_rat\<close> of the rat ones)\<close>
  have hom1: "(of_rat a :: real) + (of_rat b - of_rat a) / of_nat N = of_rat (a + ?w)"
    by (simp add: of_rat_add of_rat_diff of_rat_divide)
  have hom2: "(of_rat b :: real) - (of_rat b - of_rat a) / of_nat N = of_rat (b - ?w)"
    by (simp add: of_rat_diff of_rat_divide)
  show ?thesis
    unfolding try_blocks_def try_blocks_int_def Let_def
    using v1_eq v2_eq hom1 hom2 by simp
qed

lemma try_window_bail_int_eq:
  assumes ab: "a < b" and P0: "P \<noteq> 0" and Npos: "N > 0"
      and pdeg: "p = degree (map_poly of_int P :: real poly)"
  shows "try_window_bail gn p (of_rat a) (of_rat b) N (map_poly of_int P :: real poly) (int v)
         = map_option (\<lambda>I. (of_rat (fst I), of_rat (snd I))) (try_window_bail_int gn a b N P v)"
proof -
  let ?P_real = "map_poly of_int P :: real poly"
  have v_snap:
    "\<And>lam. (descartes_list_int (fst (snap_window_rat a b N lam))
                                (snd (snap_window_rat a b N lam)) (coeffs P) = v)
         \<longleftrightarrow> (Bernstein_changes p (of_rat (fst (snap_window_rat a b N lam)))
                                  (of_rat (snd (snap_window_rat a b N lam))) ?P_real = int v)"
  proof -
    fix lam
    let ?l = "fst (snap_window_rat a b N lam)" and ?r = "snd (snap_window_rat a b N lam)"
    have ord: "?l < ?r"
    proof -
      have ab_real: "(of_rat a :: real) < of_rat b" using ab by (simp add: of_rat_less)
      have "(of_rat ?r :: real) - of_rat ?l
              = snd (snap_window (of_rat a) (of_rat b) N lam) - fst (snap_window (of_rat a) (of_rat b) N lam)"
        by (simp add: snap_window_rat_eq)
      also have "\<dots> = (of_rat b - of_rat a :: real) / of_nat N"
        using snap_window_width[OF ab_real Npos] by simp
      also have "\<dots> > 0" using ab_real Npos by simp
      finally show "?l < ?r" by (metis diff_gt_0_iff_gt of_rat_less)
    qed
    have "int (descartes_list_int ?l ?r (coeffs P)) = descartes_roots_test_sc (of_rat ?l) (of_rat ?r) ?P_real"
      using descartes_roots_test_sc_of_int[OF ord P0] by simp
    also have "\<dots> = Bernstein_changes p (of_rat ?l) (of_rat ?r) ?P_real"
      using descartes_roots_test_sc_eq_Bernstein_changes pdeg by blast
    finally show "(descartes_list_int ?l ?r (coeffs P) = v)
                  \<longleftrightarrow> (Bernstein_changes p (of_rat ?l) (of_rat ?r) ?P_real = int v)" by linarith
  qed
  \<comment> \<open>Both cascades bottom out at \<open>None\<close>, which needs no correspondence lemma.
     @{thm [source] try_blocks_int_map_option} (above) is used by the plain Newton route.\<close>
  \<comment> \<open>the snap arm (used at both loc0 and loc1): both sides reduce to the same guarded \<open>Some\<close>\<close>
  have snap_arm:
    "\<And>lam. (if Bernstein_changes p (fst (snap_window (of_rat a) (of_rat b) N lam))
                                    (snd (snap_window (of_rat a) (of_rat b) N lam)) ?P_real = int v
            then Some (snap_window (of_rat a) (of_rat b) N lam) else None)
         = map_option (\<lambda>I. (of_rat (fst I), of_rat (snd I)))
             (if descartes_list_int (fst (snap_window_rat a b N lam))
                                     (snd (snap_window_rat a b N lam)) (coeffs P) = v
              then Some (snap_window_rat a b N lam) else None)"
  proof -
    fix lam
    have sw: "snap_window (of_rat a) (of_rat b) N lam
                = (of_rat (fst (snap_window_rat a b N lam)), of_rat (snd (snap_window_rat a b N lam)))"
      by (rule snap_window_rat_eq)
    show "(if Bernstein_changes p (fst (snap_window (of_rat a) (of_rat b) N lam))
                                   (snd (snap_window (of_rat a) (of_rat b) N lam)) ?P_real = int v
           then Some (snap_window (of_rat a) (of_rat b) N lam) else None)
        = map_option (\<lambda>I. (of_rat (fst I), of_rat (snd I)))
            (if descartes_list_int (fst (snap_window_rat a b N lam))
                                    (snd (snap_window_rat a b N lam)) (coeffs P) = v
             then Some (snap_window_rat a b N lam) else None)"
      using v_snap[of lam] by (simp add: sw)
  qed
  show ?thesis
  proof (cases gn)
    case False
    thus ?thesis
      by (simp add: try_window_bail_def try_window_bail_int_def Let_def)
  next
    case gn: True
    show ?thesis
    proof (cases "newton_at (int v) ?P_real (of_rat a)")
      case (Some lam1)
      thus ?thesis using gn snap_arm[of lam1]
        by (simp add: try_window_bail_def try_window_bail_int_def Let_def)
    next
      case L1none: None
      show ?thesis
      proof (cases "newton_at (int v) ?P_real (of_rat b)")
        case (Some lam2)
        thus ?thesis using gn L1none snap_arm[of lam2]
          by (simp add: try_window_bail_def try_window_bail_int_def Let_def)
      next
        case None
        thus ?thesis using gn L1none
          by (simp add: try_window_bail_def try_window_bail_int_def Let_def)
      qed
    qed
  qed
qed

text \<open>Corollaries of the correspondence in the exact shapes the simulation consumes: a
  \<open>Some\<close>-mapping and a \<open>None\<close>-implication, plus the \<open>fst < snd\<close> geometry of an int accept.\<close>
lemma try_window_bail_int_Some:
  assumes "a < b" "P \<noteq> 0" "N > 0" "p = degree (map_poly of_int P :: real poly)"
      and "try_window_bail_int gn a b N P v = Some I_rat"
  shows "try_window_bail gn p (of_rat a) (of_rat b) N (map_poly of_int P :: real poly) (int v)
           = Some (of_rat (fst I_rat), of_rat (snd I_rat))"
  using try_window_bail_int_eq[OF assms(1-4)] assms(5) by simp

lemma try_window_bail_int_None:
  assumes "a < b" "P \<noteq> 0" "N > 0" "p = degree (map_poly of_int P :: real poly)"
      and "try_window_bail_int gn a b N P v = None"
  shows "try_window_bail gn p (of_rat a) (of_rat b) N (map_poly of_int P :: real poly) (int v) = None"
  using try_window_bail_int_eq[OF assms(1-4)] assms(5) by simp

section \<open>Int worklist recursion (LIFO tailrec twin)\<close>

text \<open>Clone of @{const newdsc_pol_main_int} with the two try cases folded into one
  @{const try_window_bail_int}. Reuses @{const accept_child_int} / @{const bisect_children_int}
  verbatim (the child bookkeeping is window-decision-agnostic).\<close>

partial_function (tailrec) newdsc_pol_bail_main_int ::
  "newton_pol_node \<Rightarrow> int poly \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> (rat \<times> rat) list
     \<Rightarrow> (rat \<times> rat) list"
where
  [code]:
  "newdsc_pol_bail_main_int pol P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a, b, e, dk, s) # todo' \<Rightarrow>
          (let v = descartes_list_int a b (coeffs P) in
           if v = 0 then
             newdsc_pol_bail_main_int pol P todo' acc
           else if v = 1 then
             newdsc_pol_bail_main_int pol P todo' ((a, b) # acc)
           else
             (case try_window_bail_int (snd (pol a b e dk (s, v)))
                     a b (N_of e) P v of
                Some I \<Rightarrow>
                  newdsc_pol_bail_main_int pol P (accept_child_int I e dk s # todo') acc
              | None \<Rightarrow>
                  (let m  = (a + b) / 2;
                       acc' = (if poly (map_poly of_int P :: rat poly) m = 0
                               then (m, m) # acc else acc)
                   in newdsc_pol_bail_main_int pol P
                        (bisect_children_int P a b e dk s @ todo') acc'))))"

definition newdsc_pol_bail_int ::
  "newton_pol \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> (rat \<times> rat) list"
where
  "newdsc_pol_bail_int pol a b e dk P
     = newdsc_pol_bail_main_int (pol (degree P)) P [(a, b, e, dk, 0)] []"

section \<open>Int\<leftrightarrow>real simulation (worklist \<open>=\<close> tree)\<close>

text \<open>Clone of @{thm [source] newdsc_pol_main_int_sim_aux} with the 3-way (newton/block/bisect)
  window case collapsed to the bail 2-way (window/bisect): the plain two \<open>Some\<close> arms merge into
  one, fed by @{thm [source] try_window_bail_int_Some}; the plain \<open>None\<close>-\<open>None\<close>-bisect nest
  collapses to one \<open>None\<close> (via @{thm [source] try_window_bail_int_None}), whose bisection body is
  the plain one verbatim. IH indices: 1 = left, 2 = right, 3 = window.\<close>
lemma newdsc_pol_bail_main_int_sim_aux:
  assumes dom: "newdsc_pol_bail_dom (polr, p, a', b', e, dk, s, P')"
    and aeq: "a' = of_rat a" and beq: "b' = of_rat b"
    and Peq: "P' = map_poly of_int P" and pdeg: "p = degree P"
    and P0: "P \<noteq> 0" and ab: "a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr p (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = nodepol a2 b2 e2 dk2 (s2, v)"
  shows
    "newdsc_pol_bail_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
     newdsc_pol_bail_main_int nodepol P todo
       (map real_to_rat_pair (rev (newdsc_pol_bail polr p a' b' e dk s P')) @ acc)"
  using assms
proof (induction polr p a' b' e dk s P' arbitrary: a b todo acc rule: newdsc_pol_bail.pinduct)
  case (1 polr p a' b' e dk s P' a b todo acc)
  have aeq: "a' = of_rat a" and beq: "b' = of_rat b" and Peq: "P' = map_poly of_int P"
    and pdeg: "p = degree P" and P0: "P \<noteq> 0" and ab: "a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr p (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = nodepol a2 b2 e2 dk2 (s2, v)"
    using "1.prems" by blast+
  let ?P_real = "map_poly of_int P :: real poly"
  let ?v = "Bernstein_changes p (of_rat a) (of_rat b) ?P_real"

  have deg_p: "degree ?P_real = p" using pdeg by simp
  have v_eq: "int (descartes_list_int a b (coeffs P)) = ?v"
    using descartes_roots_test_sc_of_int[OF \<open>a < b\<close> \<open>P \<noteq> 0\<close>]
    by (simp add: descartes_roots_test_sc_eq_Bernstein_changes deg_p pdeg)
  have vnn: "?v = int (nat ?v)" using v_eq by linarith

  have pol_eq: "polr p (of_rat a) (of_rat b) e dk (s, ?v) = nodepol a b e dk (s, nat ?v)"
  proof -
    have "polr p (of_rat a) (of_rat b) e dk (s, ?v)
            = polr p (of_rat a) (of_rat b) e dk (s, int (nat ?v))" using vnn by simp
    also have "\<dots> = nodepol a b e dk (s, nat ?v)" using polrel by blast
    finally show ?thesis .
  qed
  \<comment> \<open>Only the Newton-gate correspondence \<open>gn_eq\<close> is consumed.\<close>
  have gn_eq: "snd (polr p (of_rat a) (of_rat b) e dk (s, ?v))
                 = snd (nodepol a b e dk (s, nat ?v))" using pol_eq by simp
  let ?gn = "snd (nodepol a b e dk (s, nat ?v))"

  have Npos: "N_of e > 0" using N_of_ge_2[of e] by simp
  have N2: "N_of e \<ge> 2" using N_of_ge_2 by simp
  have ab_real: "((of_rat a)::real) < of_rat b" using ab by (simp add: of_rat_less)

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have nd0: "newdsc_pol_bail polr p a' b' e dk s P' = []"
      using "1.hyps" aeq beq Peq v0 newdsc_pol_bail.psimps by fastforce
    show ?thesis
      using nd0 newdsc_pol_bail_main_int.simps Let_def v0 v_eq aeq beq Peq by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have nd1: "newdsc_pol_bail polr p a' b' e dk s P' = [(a', b')]"
        using "1.hyps" aeq beq Peq v1 v0 newdsc_pol_bail.psimps by fastforce
      show ?thesis
        using nd1 newdsc_pol_bail_main_int.simps Let_def v0 v1 v_eq aeq beq Peq by auto
    next
      case v1: False
      have v_nat_eq: "descartes_list_int a b (coeffs P) = nat ?v" using v_eq by linarith
      have v_neq_0: "descartes_list_int a b (coeffs P) \<noteq> 0" using v0 v_eq by auto
      have v_neq_1: "descartes_list_int a b (coeffs P) \<noteq> 1" using v1 v_eq by auto

      show ?thesis
      proof (cases "try_window_bail_int ?gn a b (N_of e) P (nat ?v)")
        case (Some I_rat)
          let ?I_real = "(real_of_rat (fst I_rat), real_of_rat (snd I_rat))"
          have TW_real: "try_window_bail ?gn p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = Some ?I_real"
            using try_window_bail_int_Some[OF ab P0 Npos deg_p[symmetric] Some] vnn by simp
          have TWg_real: "try_window_bail (snd (polr p (of_rat a) (of_rat b) e dk (s, ?v)))
                            p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = Some ?I_real"
            using TW_real gn_eq by simp

          have nd_window:
            "newdsc_pol_bail polr p a' b' e dk s P'
               = newdsc_pol_bail polr p (fst ?I_real) (snd ?I_real) (e + 1) (dk + (2 ^ e + 2)) s P'"
            using "1.hyps" aeq beq Peq v0 v1 TWg_real newdsc_pol_bail.psimps by fastforce

          have main_window:
            "newdsc_pol_bail_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
             newdsc_pol_bail_main_int nodepol P ((fst I_rat, snd I_rat, e + 1, dk + (2 ^ e + 2), s) # todo) acc"
            apply (subst newdsc_pol_bail_main_int.simps)
            using v_neq_0 v_neq_1 Some v_nat_eq
            by (auto simp add: Let_def accept_child_int_def)

          have "fst ?I_real < snd ?I_real"
            using try_window_bail_Some_fst_lt_snd[OF TW_real ab_real Npos] by simp
          hence rat_lt: "fst I_rat < snd I_rat" using of_rat_less by auto

          have stepI:
            "newdsc_pol_bail_main_int nodepol P ((fst I_rat, snd I_rat, e + 1, dk + (2 ^ e + 2), s) # todo) acc =
             newdsc_pol_bail_main_int nodepol P todo
               (map real_to_rat_pair (rev (newdsc_pol_bail polr p (fst ?I_real) (snd ?I_real) (e + 1) (dk + (2 ^ e + 2)) s P')) @ acc)"
            using "1.IH"(3) aeq beq Peq pdeg P0 rat_lt polrel TWg_real v0 v1 by force

          show ?thesis using main_window stepI nd_window aeq beq by simp
      next
        case TW0i: None
          have TW0_real: "try_window_bail ?gn p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = None"
            using try_window_bail_int_None[OF ab P0 Npos deg_p[symmetric] TW0i] vnn by simp
          have TWg0_real: "try_window_bail (snd (polr p (of_rat a) (of_rat b) e dk (s, ?v)))
                             p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = None"
            using TW0_real gn_eq by simp

          define m where "m = (a + b) / 2"
          define e' where "e' = max 1 (e - 1)"
          let ?m_real = "(of_rat a + of_rat b) / 2"
          have m_real_eq: "of_rat m = ?m_real" by (simp add: m_def of_rat_add of_rat_divide)
          let ?s'_rat  = "split_run_len_int P a b s"
          let ?s'_real = "split_run_len_real p ?P_real (of_rat a) (of_rat b) s"
          have s'_eq: "?s'_real = ?s'_rat"
            by (rule split_run_len_int_eq_real[OF P0 ab pdeg])
          let ?mid_rat = "(if poly (map_poly of_int P :: rat poly) m = 0 then [(m, m)] else [])"
          let ?mid_real = "(if poly ?P_real ?m_real = 0 then [(?m_real, ?m_real)] else [])"
          have mid_map: "map real_to_rat_pair ?mid_real = ?mid_rat"
            using poly_rat_eq_poly_real m_real_eq
            by (smt (verit, ccfv_threshold) list.map(1,2) real_to_rat_pair_of_rat)

          have nd_split:
            "newdsc_pol_bail polr p a' b' e dk s P' =
               ?mid_real @ newdsc_pol_bail polr p a' ?m_real e' (dk + 1) ?s'_real P'
                         @ newdsc_pol_bail polr p ?m_real b' e' (dk + 1) ?s'_real P'"
            using "1.hyps" aeq beq Peq newdsc_pol_bail.psimps Let_def v0 v1 TWg0_real
                  m_real_eq[symmetric] e'_def
            by (smt (verit, ccfv_SIG) option.case(1))

          have main_split:
            "newdsc_pol_bail_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
             newdsc_pol_bail_main_int nodepol P ((a, m, e', dk + 1, ?s'_rat) # (m, b, e', dk + 1, ?s'_rat) # todo) (?mid_rat @ acc)"
          proof -
            have tmp:
              "newdsc_pol_bail_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
               newdsc_pol_bail_main_int nodepol P ((a, m, e', dk + 1, ?s'_rat) # (m, b, e', dk + 1, ?s'_rat) # todo)
                 (if poly (map_poly of_int P :: rat poly) m = 0 then (m, m) # acc else acc)"
              apply (subst newdsc_pol_bail_main_int.simps)
              using v_neq_0 v_neq_1 TW0i m_def e'_def v_nat_eq
              by (simp add: Let_def bisect_children_int_def m_def e'_def)
            show ?thesis using tmp by auto
          qed

          have a_lt_m: "a < m" using ab m_def by auto
          have m_lt_b: "m < b" using ab m_def by auto

          have stepL:
            "newdsc_pol_bail_main_int nodepol P ((a, m, e', dk + 1, ?s'_rat) # (m, b, e', dk + 1, ?s'_rat) # todo) (?mid_rat @ acc) =
             newdsc_pol_bail_main_int nodepol P ((m, b, e', dk + 1, ?s'_rat) # todo)
               (map real_to_rat_pair (rev (newdsc_pol_bail polr p a' ?m_real e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc))"
          proof -
            have "newdsc_pol_bail_main_int nodepol P ((a, m, e', dk + 1, ?s'_rat) # (m, b, e', dk + 1, ?s'_rat) # todo) (?mid_rat @ acc) =
                  newdsc_pol_bail_main_int nodepol P ((m, b, e', dk + 1, ?s'_rat) # todo)
                    (map real_to_rat_pair (rev (newdsc_pol_bail polr p a' (of_rat m) e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc))"
              using "1.IH"(1) aeq beq Peq pdeg P0 a_lt_m polrel TWg0_real v0 v1 e'_def s'_eq m_real_eq by metis
            thus ?thesis using m_real_eq by metis
          qed

          have stepR:
            "newdsc_pol_bail_main_int nodepol P ((m, b, e', dk + 1, ?s'_rat) # todo)
               (map real_to_rat_pair (rev (newdsc_pol_bail polr p a' ?m_real e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc)) =
             newdsc_pol_bail_main_int nodepol P todo
               (map real_to_rat_pair (rev (newdsc_pol_bail polr p ?m_real b' e' (dk + 1) ?s'_real P'))
                 @ (map real_to_rat_pair (rev (newdsc_pol_bail polr p a' ?m_real e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc)))"
          proof -
            have "newdsc_pol_bail_main_int nodepol P ((m, b, e', dk + 1, ?s'_rat) # todo)
                    (map real_to_rat_pair (rev (newdsc_pol_bail polr p a' ?m_real e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc)) =
                  newdsc_pol_bail_main_int nodepol P todo
                    (map real_to_rat_pair (rev (newdsc_pol_bail polr p (of_rat m) b' e' (dk + 1) ?s'_real P'))
                      @ (map real_to_rat_pair (rev (newdsc_pol_bail polr p a' ?m_real e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc)))"
              using "1.IH"(2) aeq beq Peq pdeg P0 m_lt_b polrel TWg0_real v0 v1 e'_def s'_eq m_real_eq by metis
            thus ?thesis using m_real_eq by metis
          qed

          have LHS_rewrite:
            "newdsc_pol_bail_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
             newdsc_pol_bail_main_int nodepol P todo
               (map real_to_rat_pair (rev (newdsc_pol_bail polr p ?m_real b' e' (dk + 1) ?s'_real P')
                 @ rev (newdsc_pol_bail polr p a' ?m_real e' (dk + 1) ?s'_real P') @ ?mid_real) @ acc)"
            using main_split stepL stepR mid_map by simp

          have RHS_rewrite:
            "newdsc_pol_bail_main_int nodepol P todo
               (map real_to_rat_pair (rev (newdsc_pol_bail polr p a' b' e dk s P')) @ acc) =
             newdsc_pol_bail_main_int nodepol P todo
               (map real_to_rat_pair (rev (newdsc_pol_bail polr p ?m_real b' e' (dk + 1) ?s'_real P')
                 @ rev (newdsc_pol_bail polr p a' ?m_real e' (dk + 1) ?s'_real P') @ ?mid_real) @ acc)"
            using nd_split by simp

          show ?thesis using LHS_rewrite RHS_rewrite by simp
      qed
    qed
  qed
qed

text \<open>The load-bearing bridge (clone of @{thm [source] newdsc_pol_int_eq_newdsc_pol}): what the
  FCOMP capstone composes with the impl keystone to reach @{thm [source] newdsc_pol_bail_sound}/
  @{thm [source] newdsc_pol_bail_complete}.\<close>
lemma newdsc_pol_bail_int_eq_newdsc_pol_bail:
  assumes dom:  "newdsc_pol_bail_dom
                   (polr, p, of_rat a, of_rat b, e, dk, 0, map_poly of_int P :: real poly)"
    and pdeg:   "p = degree P"
    and P0:     "P \<noteq> 0"
    and ab:     "a < b"
    and polrel: "\<And>a' b' e' dk' s' v. polr p (of_rat a') (of_rat b') e' dk' (s', int v)
                    = pol (degree P) a' b' e' dk' (s', v)"
  shows "rev (newdsc_pol_bail_int pol a b e dk P)
           = map real_to_rat_pair
               (newdsc_pol_bail polr p (of_rat a) (of_rat b) e dk 0 (map_poly of_int P))"
proof -
  have tr: "newdsc_pol_bail_int pol a b e dk P
              = map real_to_rat_pair (rev (newdsc_pol_bail polr p (of_rat a) (of_rat b) e dk 0 (map_poly of_int P)))"
    unfolding newdsc_pol_bail_int_def
    using newdsc_pol_bail_main_int_sim_aux[OF dom refl refl refl pdeg P0 ab,
            where nodepol = "pol (degree P)", OF _, of "[]" "[]"] polrel pdeg
    by (simp add: newdsc_pol_bail_main_int.simps)
  thus ?thesis by (simp add: rev_map)
qed

end
