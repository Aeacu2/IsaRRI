theory NewDsc_Isolation_Strong
  imports IsaRRI_Spec.NewDsc IsaRRI_Refine.Isolation_Contract
begin

text \<open>\<^bold>\<open>NewDsc proven to be a root isolation.\<close> \<open>newdsc_sound\<close> and \<open>newdsc_complete\<close>
  (\<open>IsaRRI_Spec.NewDsc\<close>) give soundness and CLOSED-bound coverage, which admits a root on a window's
  endpoint and says nothing about a root lying in two windows. This theory proves the strict
  form: every root of the open search interval lies strictly inside a returned window or is a
  returned point window (\<open>newdsc_complete_strong\<close>), and the windows are pairwise disjoint and
  inside the search interval (\<open>newdsc_iv_disj_inside\<close>). \<open>newdsc_isolation\<close> bundles both with
  termination and soundness.

  The one new argument is \<open>nd_retained_root_strict\<close>: a window inside the parent whose count
  equals the parent's contains every root of the parent STRICTLY inside it. A root outside the
  window, or on an interior boundary of it, costs the parent an extra sign variation
  (\<open>Bernstein_changes_split\<close>, \<open>Bernstein_changes_split_root\<close>). The bisection branch is the
  argument of \<open>dsc_complete_strong\<close> / \<open>dsc_iv_disj_inside\<close>. Additive: no existing statement
  or proof changes.\<close>

lemma nd_bc_nonneg: "0 \<le> Bernstein_changes p a b P"
  by (simp add: Bernstein_changes_def)

lemma nd_bc_mono_right:
  assumes "u < u'" "u' \<le> b" "degree P \<le> p"
  shows "Bernstein_changes p u u' P \<le> Bernstein_changes p u b P"
proof (cases "u' = b")
  case False
  then have "u' < b" using assms by simp
  then show ?thesis
    using Bernstein_changes_split[OF assms(1) _ assms(3)] nd_bc_nonneg[of p u' b P] by fastforce
qed simp

lemma nd_bc_mono_left:
  assumes "a \<le> u" "u < u'" "degree P \<le> p"
  shows "Bernstein_changes p u u' P \<le> Bernstein_changes p a u' P"
proof (cases "a = u")
  case False
  then have "a < u" using assms by simp
  then show ?thesis
    using Bernstein_changes_split[OF _ assms(2) assms(3)] nd_bc_nonneg[of p a u P] by fastforce
qed simp

text \<open>The retained-window argument: a window inside the parent whose count equals the parent's
  contains every root of the parent strictly inside it.\<close>
lemma nd_retained_root_strict:
  assumes deg: "degree P \<le> p" and P0: "P \<noteq> 0"
      and au: "a \<le> u" and uu: "u < u'" and ub: "u' \<le> b"
      and eq: "Bernstein_changes p u u' P = Bernstein_changes p a b P"
      and root: "poly P x = 0" and ax: "a < x" and xb: "x < b"
  shows "u < x \<and> x < u'"
proof -
  have not_le: "\<not> x \<le> u"
  proof
    assume xu: "x \<le> u"
    then have a_u: "a < u" using ax by simp
    have ub': "u < b" using uu ub by simp
    have "Bernstein_changes p u u' P \<le> Bernstein_changes p u b P"
      by (rule nd_bc_mono_right[OF uu ub deg])
    moreover have "Bernstein_changes p u b P + 1 \<le> Bernstein_changes p a b P"
    proof (cases "x = u")
      case True
      show ?thesis
        using Bernstein_changes_split_root[OF a_u ub' _ deg P0] root True nd_bc_nonneg[of p a u P]
        by simp
    next
      case False
      then have "x < u" using xu by simp
      then have "Bernstein_changes p a u P \<noteq> 0"
        using Bernstein_changes_pos_of_root[OF deg P0 a_u root ax] by simp
      then show ?thesis
        using Bernstein_changes_split[OF a_u ub' deg] nd_bc_nonneg[of p a u P] by simp
    qed
    ultimately show False using eq by simp
  qed
  have not_ge: "\<not> u' \<le> x"
  proof
    assume ux: "u' \<le> x"
    then have u_b: "u' < b" using xb by simp
    have au': "a < u'" using au uu by simp
    have "Bernstein_changes p u u' P \<le> Bernstein_changes p a u' P"
      by (rule nd_bc_mono_left[OF au uu deg])
    moreover have "Bernstein_changes p a u' P + 1 \<le> Bernstein_changes p a b P"
    proof (cases "x = u'")
      case True
      show ?thesis
        using Bernstein_changes_split_root[OF au' u_b _ deg P0] root True nd_bc_nonneg[of p u' b P]
        by simp
    next
      case False
      then have "u' < x" using ux by simp
      then have "Bernstein_changes p u' b P \<noteq> 0"
        using Bernstein_changes_pos_of_root[OF deg P0 u_b root _ xb] by simp
      then show ?thesis
        using Bernstein_changes_split[OF au' u_b deg] nd_bc_nonneg[of p u' b P] by simp
    qed
    ultimately show False using eq by simp
  qed  show ?thesis using not_le not_ge by simp
qed

lemma nd_try_blocks_accepted:
  assumes TB: "try_blocks p a b N P v = Some I" and ab: "a < b" and N0: "0 < N"
  shows "a \<le> fst I \<and> fst I < snd I \<and> snd I \<le> b \<and> Bernstein_changes p (fst I) (snd I) P = v"
proof -
  have "Bernstein_changes p (fst I) (snd I) P = v"
    using TB unfolding try_blocks_def Let_def by (auto split: if_split_asm)
  moreover have "(b - a) / of_nat N > 0" using ab N0 by simp
  ultimately show ?thesis using try_blocks_SomeD[OF TB N0 ab] by simp
qed

lemma nd_try_newton_accepted:
  assumes TN: "try_newton p a b N P v = Some I" and ab: "a < b" and N0: "0 < N"
  shows "a \<le> fst I \<and> fst I < snd I \<and> snd I \<le> b \<and> Bernstein_changes p (fst I) (snd I) P = v"
proof -
  have "Bernstein_changes p (fst I) (snd I) P = v"
    using TN unfolding try_newton_def Let_def by (auto split: option.split_asm if_split_asm)
  moreover have "(b - a) / of_nat N > 0" using ab N0 by simp
  ultimately show ?thesis using try_newton_SomeD[OF TN ab N0] by simp
qed

lemma nd_Nq_pos: "0 < N \<Longrightarrow> 0 < Nq N"
  by (simp add: Nq_def)

lemma nd_Nlin_pos: "0 < Nlin N"
  using Nlin_ge_2[of N] by simp

lemma nd_newdsc_eqs:
  assumes dom: "newdsc_dom (p, a, b, N, P)"
  defines "v \<equiv> Bernstein_changes p a b P"
  shows "v = 0 \<Longrightarrow> newdsc p a b N P = []"
    and "v = 1 \<Longrightarrow> newdsc p a b N P = [(a, b)]"
    and "v \<noteq> 0 \<Longrightarrow> v \<noteq> 1 \<Longrightarrow> try_blocks p a b N P v = Some I \<Longrightarrow>
           newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
    and "v \<noteq> 0 \<Longrightarrow> v \<noteq> 1 \<Longrightarrow> try_blocks p a b N P v = None \<Longrightarrow>
           try_newton p a b N P v = Some I \<Longrightarrow>
           newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
    and "v \<noteq> 0 \<Longrightarrow> v \<noteq> 1 \<Longrightarrow> try_blocks p a b N P v = None \<Longrightarrow>
           try_newton p a b N P v = None \<Longrightarrow>
           newdsc p a b N P =
             (if poly P ((a + b) / 2) = 0 then [((a + b) / 2, (a + b) / 2)] else [])
             @ newdsc p a ((a + b) / 2) (Nlin N) P @ newdsc p ((a + b) / 2) b (Nlin N) P"
  using newdsc.psimps[OF dom] unfolding v_def by (simp_all add: Let_def)

text \<open>\<^bold>\<open>Strict completeness.\<close> Every root in the open search interval lies strictly inside some
  returned window or is a returned point window.\<close>
theorem newdsc_complete_strong:
  assumes dom: "newdsc_dom (p, a, b, N, P)" and deg: "degree P \<le> p" and P0: "P \<noteq> 0"
      and N0: "0 < N"
  shows "poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow> (\<exists>w \<in> set (newdsc p a b N P). iv_in x w)"
  using dom deg P0 N0
proof (induction p a b N P rule: newdsc.pinduct)
  case (1 p a b N P)
  let ?v = "Bernstein_changes p a b P"
  let ?m = "(a + b) / 2"
  note E = nd_newdsc_eqs[OF "1.hyps"]
  have root: "poly P x = 0" and ax: "a < x" and xb: "x < b"
   and deg: "degree P \<le> p" and P0: "P \<noteq> 0" and N0: "0 < N"
    using "1.prems" by auto
  have ab: "a < b" using ax xb by linarith
  have vnz: "?v \<noteq> 0"
    using Bernstein_changes_pos_of_root[OF deg P0 ab root ax xb] .
  show ?case
  proof (cases "?v = 1")
    case True
    then show ?thesis using E(2) ax xb unfolding iv_in_def by auto
  next
    case v1: False
    show ?thesis
    proof (cases "try_blocks p a b N P ?v")
      case (Some I)
      have acc: "a \<le> fst I \<and> fst I < snd I \<and> snd I \<le> b \<and> Bernstein_changes p (fst I) (snd I) P = ?v"
        using nd_try_blocks_accepted[OF Some ab N0] .
      have xI: "fst I < x \<and> x < snd I"
        using nd_retained_root_strict[OF deg P0 _ _ _ _ root ax xb] acc by blast
      obtain w where "w \<in> set (newdsc p (fst I) (snd I) (Nq N) P)" "iv_in x w"
        using "1.IH"(4)[OF refl vnz v1 Some root] xI deg P0 nd_Nq_pos[OF N0] by blast
      then show ?thesis using E(3)[OF vnz v1 Some] by auto
    next
      case TB: None
      show ?thesis
      proof (cases "try_newton p a b N P ?v")
        case (Some I)
        have acc: "a \<le> fst I \<and> fst I < snd I \<and> snd I \<le> b \<and> Bernstein_changes p (fst I) (snd I) P = ?v"
          using nd_try_newton_accepted[OF Some ab N0] .
        have xI: "fst I < x \<and> x < snd I"
          using nd_retained_root_strict[OF deg P0 _ _ _ _ root ax xb] acc by blast
        obtain w where "w \<in> set (newdsc p (fst I) (snd I) (Nq N) P)" "iv_in x w"
          using "1.IH"(3)[OF refl vnz v1 TB Some root] xI deg P0 nd_Nq_pos[OF N0] by blast
        then show ?thesis using E(4)[OF vnz v1 TB Some] by auto
      next
        case TN: None
        note Eb = E(5)[OF vnz v1 TB TN]
        consider "x = ?m" | "x < ?m" | "?m < x" by linarith
        then show ?thesis
        proof cases
          case 1
          have pm: "poly P ?m = 0" using root unfolding 1 .
          have mem: "(?m, ?m) \<in> set (newdsc p a b N P)" using pm Eb by simp
          have "iv_in x (?m, ?m)" using 1 by (simp add: iv_in_def)
          then show ?thesis using mem by blast
        next
          case 2          obtain w where "w \<in> set (newdsc p a ?m (Nlin N) P)" "iv_in x w"
            using "1.IH"(1)[OF refl vnz v1 TB TN refl refl refl root ax 2 deg P0 nd_Nlin_pos] by blast
          then show ?thesis using Eb by auto
        next
          case 3
          obtain w where "w \<in> set (newdsc p ?m b (Nlin N) P)" "iv_in x w"
            using "1.IH"(2)[OF refl vnz v1 TB TN refl refl refl root 3 xb deg P0 nd_Nlin_pos] by blast
          then show ?thesis using Eb by auto
        qed
      qed
    qed
  qed
qed
text \<open>\<^bold>\<open>Uniqueness.\<close> The returned windows are pairwise disjoint and lie inside the open search
  interval, so no point, and in particular no root, is contained in two of them.\<close>
theorem newdsc_iv_disj_inside:
  assumes dom: "newdsc_dom (p, a, b, N, P)" and N0: "0 < N"
  shows "a < b \<Longrightarrow> iv_disj_mset (mset (newdsc p a b N P))
                 \<and> (\<forall>w \<in> set (newdsc p a b N P). \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < b)"
  using dom N0
proof (induction p a b N P rule: newdsc.pinduct)
  case (1 p a b N P)
  let ?v = "Bernstein_changes p a b P"
  let ?m = "(a + b) / 2"
  note E = nd_newdsc_eqs[OF "1.hyps"]
  have ab: "a < b" and N0: "0 < N" using "1.prems" by auto
  have am: "a < ?m" and mb: "?m < b" using ab by auto
  have retained: "a \<le> fst I \<and> fst I < snd I \<and> snd I \<le> b \<Longrightarrow>
      iv_disj_mset (mset (newdsc p (fst I) (snd I) (Nq N) P))
      \<and> (\<forall>w \<in> set (newdsc p (fst I) (snd I) (Nq N) P). \<forall>x. iv_in x w \<longrightarrow> fst I < x \<and> x < snd I) \<Longrightarrow>
      iv_disj_mset (mset (newdsc p (fst I) (snd I) (Nq N) P))
      \<and> (\<forall>w \<in> set (newdsc p (fst I) (snd I) (Nq N) P). \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < b)" for I
    by fastforce
  show ?case
  proof (cases "?v = 0 \<or> ?v = 1")
    case True
    then show ?thesis
      using E(1,2) ab unfolding iv_disj_mset_def iv_in_def by auto
  next
    case False
    then have v0: "?v \<noteq> 0" and v1: "?v \<noteq> 1" by auto
    show ?thesis
    proof (cases "try_blocks p a b N P ?v")
      case (Some I)
      have acc: "a \<le> fst I \<and> fst I < snd I \<and> snd I \<le> b"
        using nd_try_blocks_accepted[OF Some ab N0] by blast
      have "iv_disj_mset (mset (newdsc p (fst I) (snd I) (Nq N) P))
            \<and> (\<forall>w \<in> set (newdsc p (fst I) (snd I) (Nq N) P). \<forall>x. iv_in x w \<longrightarrow> fst I < x \<and> x < snd I)"
        using "1.IH"(4)[OF refl v0 v1 Some] acc nd_Nq_pos[OF N0] by blast
      then show ?thesis using retained[OF acc] E(3)[OF v0 v1 Some] by simp
    next
      case TB: None
      show ?thesis
      proof (cases "try_newton p a b N P ?v")
        case (Some I)
        have acc: "a \<le> fst I \<and> fst I < snd I \<and> snd I \<le> b"
          using nd_try_newton_accepted[OF Some ab N0] by blast
        have "iv_disj_mset (mset (newdsc p (fst I) (snd I) (Nq N) P))
              \<and> (\<forall>w \<in> set (newdsc p (fst I) (snd I) (Nq N) P). \<forall>x. iv_in x w \<longrightarrow> fst I < x \<and> x < snd I)"
          using "1.IH"(3)[OF refl v0 v1 TB Some] acc nd_Nq_pos[OF N0] by blast
        then show ?thesis using retained[OF acc] E(4)[OF v0 v1 TB Some] by simp
      next
        case TN: None
        define Ml where "Ml = (if poly P ?m = 0 then [(?m, ?m)] else [])"
        define Lw where "Lw = newdsc p a ?m (Nlin N) P"
        define Rw where "Rw = newdsc p ?m b (Nlin N) P"
        have deq: "newdsc p a b N P = Ml @ Lw @ Rw"
          unfolding Ml_def Lw_def Rw_def using E(5)[OF v0 v1 TB TN] by simp
        have IL: "iv_disj_mset (mset Lw)" and inL: "\<forall>w \<in> set Lw. \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < ?m"
          unfolding Lw_def using "1.IH"(1)[OF refl v0 v1 TB TN refl refl refl am nd_Nlin_pos] by auto
        have IR: "iv_disj_mset (mset Rw)" and inR: "\<forall>w \<in> set Rw. \<forall>x. iv_in x w \<longrightarrow> ?m < x \<and> x < b"
          unfolding Rw_def using "1.IH"(2)[OF refl v0 v1 TB TN refl refl refl mb nd_Nlin_pos] by auto
        have inM: "\<forall>w \<in> set Ml. \<forall>x. iv_in x w \<longrightarrow> x = ?m"
          unfolding Ml_def iv_in_def by auto
        have IM: "iv_disj_mset (mset Ml)" unfolding Ml_def iv_disj_mset_def by auto
        have LR: "\<forall>w \<in># mset Lw. \<forall>w' \<in># mset Rw. iv_disj w w'"
          using inL inR unfolding iv_disj_def by fastforce
        have MLR: "\<forall>w \<in># mset Ml. \<forall>w' \<in># mset Lw + mset Rw. iv_disj w w'"
          using inM inL inR unfolding iv_disj_def by fastforce
        have d1: "iv_disj_mset (mset Lw + mset Rw)" by (rule iv_disj_mset_union[OF IL IR LR])
        have d2: "iv_disj_mset (mset Ml + (mset Lw + mset Rw))" by (rule iv_disj_mset_union[OF IM d1 MLR])
        have ins: "\<forall>w \<in> set (newdsc p a b N P). \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < b"
          unfolding deq using inL inR inM am mb by fastforce
        show ?thesis using d2 ins unfolding deq by (simp add: add.assoc)
      qed
    qed
  qed
qed

text \<open>\<^bold>\<open>NewDsc is a root isolation\<close> in the sense of the thesis's Definition 2.1, for squarefree
  input: it terminates, every window isolates a root, every root of the open search interval
  lies strictly inside a window or is a point window, and the windows are pairwise disjoint
  (so no root lies in two entries).\<close>
theorem newdsc_isolation:
  assumes P0: "P \<noteq> 0" and deg: "degree P \<le> p" and p0: "p \<noteq> 0" and sf: "square_free P"
      and ab: "a < b" and N2: "2 \<le> N"
  shows "newdsc_dom (p, a, b, N, P)"
    and "\<forall>w \<in> set (newdsc p a b N P). dsc_pair_ok P w"
    and "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow> (\<exists>w \<in> set (newdsc p a b N P). iv_in x w)"
    and "iv_disj_mset (mset (newdsc p a b N P))"
    and "\<forall>w \<in> set (newdsc p a b N P). \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < b"
proof -
  show dom: "newdsc_dom (p, a, b, N, P)"
    using newdsc_terminates_squarefree[OF P0 deg p0 sf ab N2] .
  have N0: "0 < N" using N2 by simp
  show "\<forall>w \<in> set (newdsc p a b N P). dsc_pair_ok P w"
    using newdsc_sound[OF dom deg P0 ab] .
  show "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow> (\<exists>w \<in> set (newdsc p a b N P). iv_in x w)"
    using newdsc_complete_strong[OF dom deg P0 N0] by blast
  show "iv_disj_mset (mset (newdsc p a b N P))"
   and "\<forall>w \<in> set (newdsc p a b N P). \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < b"
    using newdsc_iv_disj_inside[OF dom N0 ab] by auto
qed

end
