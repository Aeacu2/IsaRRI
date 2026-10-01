theory NewDsc
  imports
    Dsc_Misc
    Bernstein_Split  
begin

text \<open>The abstract NewDsc (Newton-accelerated Descartes) solver over \<open>real poly\<close>.
  Layer: FUNCTIONAL SPEC.
  Main exports: \<open>newdsc\<close> / \<open>newdsc_pol\<close> and their domain predicates — the target the carried Newton
  and cascade-bail verticals refine onto.\<close>

definition Nq :: "nat \<Rightarrow> nat" where
  "Nq N = N * N"

definition Nlin :: "nat \<Rightarrow> nat" where
  "Nlin N = max 4 (nat \<lfloor>sqrt (of_nat N)\<rfloor>)"

lemma Nq_ge_2:
  assumes "N \<ge> 2"
  shows "Nq N \<ge> 2"
  using assms
  by (metis Nq_def dual_order.trans le_square)

lemma Nlin_ge_2:
  shows "Nlin N \<ge> 2"
  by (simp add: Nlin_def)

lemma Nlin_ge_4:
  shows "Nlin N \<ge> 4"
  by (simp add: Nlin_def)

definition try_blocks ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_blocks p a b N P v =
     (let w = b - a;
          B1 = (a, a + w / of_nat N);
          B2 = (b - w / of_nat N, b);
          v1 = Bernstein_changes p (fst B1) (snd B1) P;
          v2 = Bernstein_changes p (fst B2) (snd B2) P
      in if v1 = v then Some B1 else if v2 = v then Some B2 else None)"

lemma try_blocks_SomeD:
  assumes TB: "try_blocks p a b N P v = Some I"
      and Npos: "N > 0"
      and ab: "a < b"
  defines "w \<equiv> b - a"
  shows "fst I \<ge> a" "snd I \<le> b" "snd I - fst I = w / of_nat N"
proof -
  have "w > 0" using ab w_def by simp
  hence width_pos: "w / of_nat N > 0" using Npos by simp
  
  have "N \<ge> 1" using Npos by simp
  hence "w / of_nat N \<le> w" using `w > 0` by (simp add: field_simps)

  show "fst I \<ge> a" "snd I \<le> b" "snd I - fst I = w / of_nat N"
    using TB width_pos `w / of_nat N \<le> w`
    unfolding try_blocks_def Let_def w_def[symmetric]
    apply (auto split: if_split_asm)
    apply (simp add: field_simps) 
    using w_def apply argo
    using w_def by argo
qed

definition newton_at :: "int \<Rightarrow> real poly \<Rightarrow> real \<Rightarrow> real option" where
  "newton_at v P t =
     (let fp = poly (pderiv P) t; f = poly P t
      in if fp = 0 then None else Some (t - of_int v * f / fp))"

definition snap_window :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (real \<times> real)" where
  "snap_window a b N lam =
     (let w    = b - a;
          s    = 4 * N;
          step = w / of_nat s;
          k0   = floor (of_nat s * ((lam - a) / w));
          k    = max 2 (min (int s - 2) k0);
          kn   = nat k
       in (a + of_nat (kn - 2) * step, a + of_nat (kn + 2) * step))"

lemma snap_window_width:
  fixes a b lam :: real and N :: nat
  assumes "a < b" "N > 0"
  shows "snd (snap_window a b N lam) - fst (snap_window a b N lam) 
         = (b - a) / of_nat N"
proof -
  let ?s = "4 * N"
  let ?w = "b - a"
  let ?step = "?w / of_nat ?s"

  define k0 where "k0 = floor (of_nat ?s * ((lam - a) / ?w))"
  define k where "k = max 2 (min (int ?s - 2) k0)"
  define kn where "kn = nat k"

  have "int ?s = of_nat ?s" by simp
  have s_pos: "?s > 0" using `N > 0` by simp
  have w_pos: "?w > 0" using `a < b` by simp

  have "k \<ge> 2" unfolding k_def by simp
  hence "kn \<ge> 2" unfolding kn_def using `k \<ge> 2` by simp
  hence kn_real: "of_nat (kn - 2) = (of_nat kn :: real) - 2" 
    using of_nat_diff by simp

  have "snd (snap_window a b N lam) - fst (snap_window a b N lam) 
        = (a + of_nat (kn + 2) * ?step) - (a + of_nat (kn - 2) * ?step)"
    unfolding snap_window_def Let_def k0_def k_def kn_def 
    using assms by simp
  also have "\<dots> = (of_nat (kn + 2) - of_nat (kn - 2)) * ?step"
    by (simp add: algebra_simps)
  also have "\<dots> = ((of_nat kn + 2) - (of_nat kn - 2)) * ?step"
    using kn_real by simp
  also have "\<dots> = 4 * ?step"
    by simp
  also have "\<dots> = 4 * (?w / of_nat (4 * N))"
    by simp
  also have "\<dots> = ?w / of_nat N"
    using `N > 0` by (simp add: field_simps)
  then show ?thesis
    using
      \<open>(real (kn + 2) - real (kn - 2)) * ((b - a) / real (4 * N)) = (real kn + 2 - (real kn - 2)) * ((b - a) / real (4 * N))\<close>
      \<open>(real kn + 2 - (real kn - 2)) * ((b - a) / real (4 * N)) = 4 * ((b - a) / real (4 * N))\<close>
      \<open>a + real (kn + 2) * ((b - a) / real (4 * N)) - (a + real (kn - 2) * ((b - a) / real (4 * N))) = (real (kn + 2) - real (kn - 2)) * ((b - a) / real (4 * N))\<close>
      \<open>snd (snap_window a b N lam) - fst (snap_window a b N lam) = a + real (kn + 2) * ((b - a) / real (4 * N)) - (a + real (kn - 2) * ((b - a) / real (4 * N)))\<close>
    by presburger
qed

lemma snap_window_inside:
  assumes "a < b" "N > 0"
  shows "fst (snap_window a b N lam) \<ge> a" "snd (snap_window a b N lam) \<le> b"
proof -
  let ?s = "4 * N"
  let ?w = "b - a"
  let ?step = "?w / of_nat ?s"
  
  define k0 where "k0 = floor (of_nat ?s * ((lam - a) / ?w))"
  define k where "k = max 2 (min (int ?s - 2) k0)"
  define kn where "kn = nat k"
  
  have s_pos: "?s > 0" using `N > 0` by simp
  have w_pos: "?w > 0" using `a < b` by simp
  have step_pos: "?step > 0" using w_pos s_pos by simp

  have "k \<ge> 2" unfolding k_def by simp
  hence "kn \<ge> 2" unfolding kn_def by simp
  hence "of_nat (kn - 2) \<ge> (0::real)" by simp
  hence "of_nat (kn - 2) * ?step \<ge> 0" using step_pos
    using mult_nonneg_nonneg order_less_imp_le by blast
  thus "fst (snap_window a b N lam) \<ge> a"
    unfolding snap_window_def Let_def k0_def k_def kn_def 
    using assms by simp

  have "k \<le> int ?s - 2" unfolding k_def using assms by linarith
  hence "kn \<le> ?s - 2" unfolding kn_def using `k \<ge> 2` by linarith
  hence "kn + 2 \<le> ?s"
    by (simp add: Nat.le_diff_conv2 Suc_leI assms(2))
  hence "of_nat (kn + 2) \<le> (of_nat ?s :: real)" by simp
  
  have "snd (snap_window a b N lam) = a + of_nat (kn + 2) * ?step"
    unfolding snap_window_def Let_def k0_def k_def kn_def using assms by simp
  also have "\<dots> \<le> a + of_nat ?s * ?step"
    using `of_nat (kn + 2) \<le> of_nat ?s` step_pos 
    by (meson add_left_mono mult_right_mono order_less_le)
  also have "\<dots> = a + of_nat ?s * (?w / of_nat ?s)"
    by simp
  also have "\<dots> = a + ?w"
    using s_pos by simp
  also have "\<dots> = b"
    by simp
  finally show "snd (snap_window a b N lam) \<le> b" 
    using \<open>a + (b - a) = b\<close> \<open>a + real (4 * N) * ((b - a) / real (4 * N)) = a + (b - a)\<close>
      \<open>a + real (kn + 2) * ((b - a) / real (4 * N)) \<le> a + real (4 * N) * ((b - a) / real (4 * N))\<close>
      \<open>snd (snap_window a b N lam) = a + real (kn + 2) * ((b - a) / real (4 * N))\<close>
    by presburger
qed


definition try_newton ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_newton p a b N P v =
     (let L1 = newton_at v P a; L2 = newton_at v P b in
      case L1 of
        Some lam1 \<Rightarrow>
          (let I1 = snap_window a b N lam1;
               v1 = Bernstein_changes p (fst I1) (snd I1) P
           in if v1 = v then Some I1
              else (case L2 of
                      Some lam2 \<Rightarrow>
                        (let I2 = snap_window a b N lam2;
                             v2 = Bernstein_changes p (fst I2) (snd I2) P
                         in if v2 = v then Some I2 else None)
                    | None \<Rightarrow> None))
      | None \<Rightarrow>
          (case L2 of
             Some lam2 \<Rightarrow>
               (let I2 = snap_window a b N lam2;
                    v2 = Bernstein_changes p (fst I2) (snd I2) P
                in if v2 = v then Some I2 else None)
           | None \<Rightarrow> None))"

lemma try_newton_SomeD:
  assumes TN: "try_newton p a b N P v = Some I"
      and ab: "a < b" 
      and Npos: "N > 0"
  defines "w \<equiv> b - a"
  shows "fst I \<ge> a" "snd I \<le> b" "snd I - fst I = w / of_nat N"
proof -
  from TN show "fst I \<ge> a" "snd I \<le> b" "snd I - fst I = w / of_nat N"
    unfolding try_newton_def Let_def
    apply (auto split: option.split_asm if_split_asm)
    using snap_window_inside[OF ab Npos] snap_window_width[OF ab Npos] w_def apply auto[3]
    using snap_window_inside[OF ab Npos] snap_window_width[OF ab Npos] w_def apply auto[3]
    using snap_window_inside[OF ab Npos] snap_window_width[OF ab Npos] w_def apply auto[3]
    using \<open>\<And>lam. snd (snap_window a b N lam) - fst (snap_window a b N lam) = (b - a) / real N\<close>
      w_def apply presburger
    using \<open>\<And>lam. snd (snap_window a b N lam) - fst (snap_window a b N lam) = (b - a) / real N\<close>
      w_def apply presburger
    using \<open>\<And>lam. snd (snap_window a b N lam) - fst (snap_window a b N lam) = (b - a) / real N\<close>
      w_def by blast
qed

lemma try_blocks_Some_fst_lt_snd:
  assumes TB: "try_blocks p a b N P v = Some I"
      and ab: "a < b"
      and N2: "N \<ge> 2"
  shows "fst I < snd I"
proof -
  have Npos: "N > 0" using N2 by simp
  from try_blocks_SomeD[OF TB Npos ab] have w:
    "snd I - fst I = (b - a) / of_nat N"
    by simp
  have "snd I - fst I > 0"
    using ab Npos w by simp
  then show ?thesis by simp
qed

lemma try_newton_Some_fst_lt_snd:
  assumes TN: "try_newton p a b N P v = Some I"
      and ab: "a < b"
      and N2: "N \<ge> 2"
  shows "fst I < snd I"
proof -
  have Npos: "N > 0" using N2 by simp
  from try_newton_SomeD[OF TN ab Npos] have w:
    "snd I - fst I = (b - a) / of_nat N"
    by simp
  have "snd I - fst I > 0"
    using ab Npos w by simp
  then show ?thesis by simp
qed

function (domintros) newdsc ::
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "newdsc p a b N P =
     (let v = Bernstein_changes p a b P in
      if v = 0 then []
      else if v = 1 then [(a, b)]
      else
        (case try_blocks p a b N P v of
           Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
         | None \<Rightarrow>
             (case try_newton p a b N P v of
                Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
              | None \<Rightarrow>
                  (let m  = (a + b) / 2;
                       N' = Nlin N;
                       mid_root = (if poly P m = 0 then [(m, m)] else [])
                   in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))"
  by pat_completeness auto

lemma newdsc_domI_general:
  fixes \<delta> :: real and p :: nat and P :: "real poly"
  assumes \<delta>_pos: "\<delta> > 0"
    and small: "\<And>a b. a < b \<Longrightarrow> b - a \<le> \<delta> \<Longrightarrow> Bernstein_changes p a b P \<le> 1"
  shows "\<And>a b N. a < b \<Longrightarrow> N \<ge> 2 \<Longrightarrow> newdsc_dom (p, a, b, N, P)"
proof -
  define \<mu> where "\<mu> = (\<lambda>a b. mu \<delta> a b)"
  let ?Prop =
    "\<lambda>n::nat. \<forall>a b N. \<mu> a b < n \<longrightarrow> a < b \<longrightarrow> N \<ge> 2 \<longrightarrow> newdsc_dom (p, a, b, N, P)"

  have step: "\<And>n. (\<And>m. m < n \<Longrightarrow> ?Prop m) \<Longrightarrow> ?Prop n"
  proof -
    fix n
    assume IH: "\<And>m. m < n \<Longrightarrow> ?Prop m"
    show "?Prop n"
    proof (intro allI impI)
      fix a b :: real and N :: nat
      assume mu_lt_n: "\<mu> a b < n"
        and ab: "a < b"
        and N2: "N \<ge> 2"
      show "newdsc_dom (p, a, b, N, P)"
      proof -
        let ?v = "Bernstein_changes p a b P"
        show ?thesis
        proof (cases "?v = 0 \<or> ?v = 1")
          case True
          then show ?thesis
            by (auto intro: newdsc.domintros)
        next
          case False
          have v_ge2: "2 \<le> ?v"
            using False Bernstein_changes_def
            by fastforce

          have \<delta>_lt_width: "\<delta> < b - a"
          proof (rule ccontr)
            assume "\<not> \<delta> < b - a"
            then have width_le_\<delta>: "b - a \<le> \<delta>"
              by linarith
            then have v_le1: "Bernstein_changes p a b P \<le> 1"
              using ab small
              by presburger
            from v_ge2 v_le1 show False
              by linarith
          qed

          have IH_at_mu: "?Prop (\<mu> a b)"
            using IH mu_lt_n
            by simp

          have block_case:
            "\<forall>I. try_blocks p a b N P ?v = Some I
                 \<longrightarrow> newdsc_dom (p, fst I, snd I, Nq N, P)"
          proof (intro allI impI)
            fix I
            assume TB: "try_blocks p a b N P ?v = Some I"
            have N_pos: "N > 0"
              using N2 by simp

            have width_I: "snd I - fst I = (b - a) / of_nat N"
              using try_blocks_SomeD[OF TB] ab
              using N_pos by blast

            have mu_less: "\<mu> (fst I) (snd I) < \<mu> a b"
              using \<delta>_pos ab \<delta>_lt_width N2 width_I
              by (simp add: \<mu>_def mu_subinterval_factor_strict)

            have fst_lt_snd: "fst I < snd I"
              by (metis N_pos ab diff_gt_0_iff_gt divide_pos_pos of_nat_0_less_iff width_I)

            have Nq_ge2': "Nq N \<ge> 2"
              using N2 Nq_ge_2 by simp

            show "newdsc_dom (p, fst I, snd I, Nq N, P)"
              using IH_at_mu mu_less fst_lt_snd Nq_ge2'
              by blast
          qed

          have newton_case:
            "\<forall>I. try_blocks p a b N P ?v = None \<longrightarrow>
                 try_newton p a b N P ?v = Some I \<longrightarrow>
                 newdsc_dom (p, fst I, snd I, Nq N, P)"
          proof (intro allI impI)
            fix I
            assume TB_none: "try_blocks p a b N P ?v = None"
            assume TN: "try_newton p a b N P ?v = Some I"
            have N_pos: "N > 0"
              using N2 by simp

            have width_I: "snd I - fst I = (b - a) / of_nat N"
              using try_newton_SomeD[OF TN ab N_pos]
              by (simp add: Let_def)

            have mu_less: "\<mu> (fst I) (snd I) < \<mu> a b"
              using \<delta>_pos ab \<delta>_lt_width N2 width_I
              by (simp add: \<mu>_def mu_subinterval_factor_strict)

            have fst_lt_snd: "fst I < snd I"
              using try_newton_SomeD[OF TN ab N_pos]
              by (metis N_pos ab diff_gt_0_iff_gt divide_pos_pos of_nat_0_less_iff)

            have Nq_ge2': "Nq N \<ge> 2"
              using N2 Nq_ge_2 by simp

            show "newdsc_dom (p, fst I, snd I, Nq N, P)"
              using IH_at_mu mu_less fst_lt_snd Nq_ge2'
              by blast
          qed

          define m where "m = (a + b) / 2"

          have am: "a < m" and mb: "m < b"
            using ab by (simp_all add: m_def)

          have mu_left_strict: "\<mu> a m < \<mu> a b"
            by (simp add: \<mu>_def \<delta>_pos \<delta>_lt_width ab m_def mu_halve_strict(1))

          have mu_right_strict: "\<mu> m b < \<mu> a b"
            by (simp add: \<mu>_def \<delta>_pos \<delta>_lt_width ab m_def mu_halve_strict(2))

          have IH_left: "\<forall>N'. N' \<ge> 2 \<longrightarrow> newdsc_dom (p, a, m, N', P)"
            using IH_at_mu mu_left_strict am
            by blast

          have IH_right: "\<forall>N'. N' \<ge> 2 \<longrightarrow> newdsc_dom (p, m, b, N', P)"
            using IH_at_mu mu_right_strict mb
            by blast

          have lin_case:
            "try_blocks p a b N P ?v = None \<and> try_newton p a b N P ?v = None \<Longrightarrow>
             newdsc_dom (p, a, m, Nlin N, P) \<and> newdsc_dom (p, m, b, Nlin N, P)"
          proof
            assume both_none:
              "try_blocks p a b N P ?v = None \<and> try_newton p a b N P ?v = None"
            have Nlin_ge2': "Nlin N \<ge> 2"
              by (rule Nlin_ge_2)
            from IH_left Nlin_ge2' show "newdsc_dom (p, a, m, Nlin N, P)"
              by blast
            from IH_right Nlin_ge2' show "newdsc_dom (p, m, b, Nlin N, P)"
              by blast
          qed

          show ?thesis
          proof (cases "try_blocks p a b N P ?v")
            case (Some I)
            then show ?thesis
              by (smt (verit) block_case fst_conv newdsc.domintros option.discI snd_conv)
          next
            case None
            then show ?thesis
            proof (cases "try_newton p a b N P ?v")
              case (Some I)
              then show ?thesis
                by (smt (verit) None fst_conv newdsc.domintros newton_case option.discI snd_conv)
            next
              case None
              then show ?thesis
                by (smt (verit) block_case fst_conv lin_case m_def newdsc.domintros snd_conv)
            qed
          qed
        qed
      qed
    qed
  qed

  have all_Prop: "\<And>n. ?Prop n"
    by (rule less_induct, rule step)

  show "\<And>a b N. a < b \<Longrightarrow> N \<ge> 2 \<Longrightarrow> newdsc_dom (p, a, b, N, P)"
    using all_Prop
    by blast
qed


theorem newdsc_terminates_squarefree:
  fixes P :: "real poly"
  assumes P0: "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0: "p \<noteq> 0"
      and sf: "square_free P"
  shows "\<And>a b N. a < b \<Longrightarrow> N \<ge> 2 \<Longrightarrow> newdsc_dom (p,a,b,N,P)"
proof -
  have \<delta>_pos: "delta_P P > 0"
    using P0 delta_P_pos by blast
  have small:
    "\<And>a b. a < b \<Longrightarrow> b - a \<le> delta_P P \<Longrightarrow> Bernstein_changes p a b P \<le> 1"
    using Bernstein_changes_small_interval_le_1 P0 deg p0 sf rsquarefree_lift by blast
  show "\<And>a b N. a < b \<Longrightarrow> N \<ge> 2 \<Longrightarrow> newdsc_dom (p,a,b,N,P)"
    using newdsc_domI_general[OF \<delta>_pos small] by blast
qed

theorem newdsc_sound:
  assumes dom: "newdsc_dom (p, a, b, N, P)"
      and deg: "degree P \<le> p"
      and P0:  "P \<noteq> 0"
      and ab:  "a < b"
  shows "\<forall>I \<in> set (newdsc p a b N P). dsc_pair_ok P I"
  using dom deg P0 ab
proof (induction p a b N P rule: newdsc.pinduct)
  case (1 p a b N P)

  have newdsc_eq:
    "newdsc p a b N P =
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a, b)]
        else
          (case try_blocks p a b N P v of
             Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
           | None \<Rightarrow>
               (case try_newton p a b N P v of
                  Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                | None \<Rightarrow>
                    (let m  = (a + b) / 2;
                         N' = Nlin N;
                         mid_root = (if poly P m = 0 then [(m, m)] else [])
                     in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))"
    using "1.hyps" newdsc.psimps
    by blast

  show ?case
  proof -
    from 1 have ab: "a < b" and P0': "P \<noteq> 0"
      apply blast
      by (simp add: "1.prems"(2))
    from 1 have deg': "degree P \<le> p"
      by blast

    let ?v = "Bernstein_changes p a b P"

    show ?thesis
    proof (cases "?v = 0")
      case True
      then show ?thesis
        by (simp add: newdsc_eq Let_def)
    next
      case v0_ne: False
      show ?thesis
      proof (cases "?v = 1")
        case v1: True
        have v1_exact: "roots_in P a b = 1"
          using Bernstein_changes_1_one_root[OF deg' P0' ab v1] .
        have dsc_ok_ab: "dsc_pair_ok P (a, b)"
          using v1_exact ab
          by (simp add: dsc_pair_ok_def roots_in_def)
        show ?thesis
          using v1 v0_ne dsc_ok_ab
          by (simp add: newdsc_eq Let_def)
      next
        case v_ge2: False
        then have v_ge2': "?v \<ge> 2"
          using v0_ne
          by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)
        have IH_block:
          "\<And>I. \<lbrakk>try_blocks p a b N P ?v = Some I\<rbrakk> \<Longrightarrow>
                \<forall>J\<in>set (newdsc p (fst I) (snd I) (Nq N) P). dsc_pair_ok P J"
        proof -
          fix I
          assume TB: "try_blocks p a b N P ?v = Some I"

          have Npos: "N > 0"
          proof (rule ccontr)
            assume "\<not> N > 0"
            hence N0: "N = 0" by simp
            have "try_blocks p a b N P ?v = None"
              unfolding try_blocks_def Let_def N0
              by (simp add: Bernstein_changes_point v0_ne)
            thus False using TB by simp
          qed

          have fst_lt_snd: "fst I < snd I"
          proof -
            define w where "w = b - a"
            have wpos: "w > 0" using ab w_def by simp
            have width_I: "snd I - fst I = w / of_nat N"
              using try_blocks_SomeD(3)[OF TB Npos ab] w_def by simp
            have "w / of_nat N > 0" using wpos Npos by simp
            thus ?thesis using width_I by linarith
          qed

          show "\<forall>J\<in>set (newdsc p (fst I) (snd I) (Nq N) P). dsc_pair_ok P J"
            using "1.IH"(4) TB deg' P0' fst_lt_snd v0_ne v_ge2
            by blast
        qed

        have IH_newton:
          "\<And>I. \<lbrakk>try_blocks p a b N P ?v = None;
                  try_newton p a b N P ?v = Some I\<rbrakk> \<Longrightarrow>
                \<forall>J\<in>set (newdsc p (fst I) (snd I) (Nq N) P). dsc_pair_ok P J"
        proof -
          fix I
          assume TB0: "try_blocks p a b N P ?v = None"
             and TN : "try_newton p a b N P ?v = Some I"

          have Npos: "N > 0"
          proof (rule ccontr)
            assume "\<not> N > 0"
            hence N0: "N = 0" by simp
            have "try_newton p a b N P ?v = None"
              unfolding try_newton_def Let_def N0
              by (auto split: option.split if_split_asm
                  simp: newton_at_def snap_window_def Bernstein_changes_point v0_ne)
            thus False using TN by simp
          qed

          have fst_lt_snd: "fst I < snd I"
          proof -
            define w where "w = b - a"
            have wpos: "w > 0" using ab w_def by simp
            have width_I: "snd I - fst I = w / of_nat N"
              using try_newton_SomeD(3)[OF TN ab Npos] w_def by simp
            have "w / of_nat N > 0" using wpos Npos by simp
            thus ?thesis using width_I by linarith
          qed

          show "\<forall>J\<in>set (newdsc p (fst I) (snd I) (Nq N) P). dsc_pair_ok P J"
            using "1.IH"(3) TB0 TN deg' P0' fst_lt_snd v0_ne v_ge2
            by blast
        qed

        have IH_LR:
          "\<And>m N'.
             \<lbrakk>try_blocks p a b N P ?v = None;
              try_newton p a b N P ?v = None;
              m = (a + b) / 2; N' = Nlin N\<rbrakk> \<Longrightarrow>
             (\<forall>I\<in>set (newdsc p a m N' P). dsc_pair_ok P I) \<and>
             (\<forall>I\<in>set (newdsc p m b N' P). dsc_pair_ok P I)"
        proof -
          fix m N'
          assume TB0: "try_blocks p a b N P ?v = None"
             and TN0: "try_newton p a b N P ?v = None"
             and m_def: "m = (a + b) / 2"
             and N'_def: "N' = Nlin N"
          have IH_left:
            "\<forall>I\<in>set (newdsc p a m N' P). dsc_pair_ok P I"
            using "1.IH" deg' v0_ne v_ge2' TB0 TN0 m_def N'_def v_ge2 P0' ab 
            by (metis field_less_half_sum)
          have IH_right:
            "\<forall>I\<in>set (newdsc p m b N' P). dsc_pair_ok P I"
            using "1.IH" deg' v0_ne v_ge2' TB0 TN0 m_def N'_def v_ge2 P0' ab 
            by (metis gt_half_sum one_add_one)
          show "(\<forall>I\<in>set (newdsc p a m N' P). dsc_pair_ok P I) \<and>
                (\<forall>I\<in>set (newdsc p m b N' P). dsc_pair_ok P I)"
            using IH_left IH_right by simp
        qed

        show ?thesis
        proof (cases "try_blocks p a b N P ?v")
          case (Some I)
          then have block_ok:
            "\<forall>J\<in>set (newdsc p (fst I) (snd I) (Nq N) P). dsc_pair_ok P J"
            using IH_block by blast
          thus ?thesis
            using Some v0_ne v_ge2
            by (simp add: newdsc_eq Let_def)
        next
          case TB_None: None
          show ?thesis
          proof (cases "try_newton p a b N P ?v")
            case (Some I)
            then have newton_ok:
              "\<forall>J\<in>set (newdsc p (fst I) (snd I) (Nq N) P). dsc_pair_ok P J"
              using IH_newton TB_None by blast
            thus ?thesis
              using TB_None Some v0_ne v_ge2
              by (simp add: newdsc_eq Let_def)
          next
            case TN_None: None
            let ?m  = "(a + b) / 2"
            let ?N' = "Nlin N"

            from IH_LR[OF TB_None TN_None refl refl]
            have left_ok:  "\<forall>I\<in>set (newdsc p a ?m ?N' P). dsc_pair_ok P I"
              and right_ok: "\<forall>I\<in>set (newdsc p ?m b ?N' P). dsc_pair_ok P I"
              by auto

            have mid_ok:
              "\<forall>I\<in>set (if poly P ?m = 0 then [(?m, ?m)] else []). dsc_pair_ok P I"
            proof (cases "poly P ?m = 0")
              case True
              then have "set (if poly P ?m = 0 then [(?m, ?m)] else []) = {(?m, ?m)}"
                by auto
              moreover have "dsc_pair_ok P (?m, ?m)"
                using True by (simp add: dsc_pair_ok_def)
              ultimately show ?thesis by auto
            next
              case False
              then show ?thesis by (simp add: dsc_pair_ok_def)
            qed

            show ?thesis
              by (smt (verit) "1.hyps" P0' TB_None TN_None UnE ab left_ok mid_ok
                  newdsc.psimps option.simps(4) right_ok set_append v0_ne v_ge2)
          qed
        qed
      qed
    qed
  qed
qed


theorem newdsc_complete:
  assumes dom: "newdsc_dom (p,a,b,N,P)"
      and deg: "degree P \<le> p"
      and P0:  "P \<noteq> 0"
      and N0:  "N > 0"
  shows "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (newdsc p a b N P). fst I \<le> x \<and> x \<le> snd I)"
using dom deg P0
proof (induction p a b N P rule: newdsc.pinduct)
  case (1 p a b N P)
  have newdsc_eq:
    "newdsc p a b N P =
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a,b)]
        else
          (case try_blocks p a b N P v of
             Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
           | None \<Rightarrow>
              (case try_newton p a b N P v of
                 Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
               | None \<Rightarrow>
                   (let m  = (a + b) / 2;
                        N' = Nlin N;
                        mid_root = (if poly P m = 0 then [(m, m)] else [])
                    in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))"
    using "1.hyps" newdsc.psimps by blast

  show ?case
  proof -
    have H:
      "\<And>x::real. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (newdsc p a b N P). fst I \<le> x \<and> x \<le> snd I)"
    proof -
      fix x :: real
      assume root: "poly P x = 0"
         and ax: "a < x"
         and xb: "x < b"
      show "\<exists>I\<in>set (newdsc p a b N P). fst I \<le> x \<and> x \<le> snd I"
      proof (cases "a \<ge> b \<or> P = 0")
        case True
        from True ax xb P0 have False
          using "1.prems"(5) by argo
        then show ?thesis by blast
      next
        case False
        hence ab: "a < b" and P0': "P \<noteq> 0"
          by auto
        from 1 have deg': "degree P \<le> p" by blast

        let ?v = "Bernstein_changes p a b P"

        have v_nonzero: "?v \<noteq> 0"
        proof
          assume "?v = 0"
          then have "roots_in P a b = 0"
            using Bernstein_changes_0_no_root[OF deg' P0' ab] by simp
          then have "poly P x \<noteq> 0"
            using ax xb Bernstein_changes_pos_of_root P0' \<open>Bernstein_changes p a b P = 0\<close> ab deg'
            by blast
          with root show False by simp
        qed

        show ?thesis
        proof (cases "?v = 1")
          case True
          then have v1: "?v = 1" by simp
          have cover: "fst (a,b) \<le> x \<and> x \<le> snd (a,b)"
            using ax xb by simp
          moreover have mem:
            "(a,b) \<in> set (if ?v = 0 then [] else if ?v = 1 then [(a,b)] else
                          (case try_blocks p a b N P ?v of
                             Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                           | None \<Rightarrow>
                               (case try_newton p a b N P ?v of
                                  Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                                | None \<Rightarrow>
                                    (let m = (a + b) / 2;
                                         N' = Nlin N;
                                         mid_root = (if poly P m = 0 then [(m,m)] else [])
                                     in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))"
            using v1 v_nonzero by simp
          ultimately show ?thesis
            by (simp add: "1.hyps" False newdsc.psimps v1)
        next
          case v_ne1: False
          hence v_ge2: "?v \<ge> 2"
            using v_nonzero
            by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)

          have IH_block:
            "\<And>I x. \<lbrakk> try_blocks p a b N P ?v = Some I;
                       poly P x = 0; fst I < x; x < snd I \<rbrakk> \<Longrightarrow>
                   \<exists>J\<in>set (newdsc p (fst I) (snd I) (Nq N) P). fst J \<le> x \<and> x \<le> snd J"
            using "1.IH" deg' v_ne1 v_nonzero P0' by presburger

          have IH_newton:
            "\<And>I x. \<lbrakk> try_blocks p a b N P ?v = None;
                       try_newton p a b N P ?v = Some I;
                       poly P x = 0; fst I < x; x < snd I \<rbrakk> \<Longrightarrow>
                   \<exists>J\<in>set (newdsc p (fst I) (snd I) (Nq N) P). fst J \<le> x \<and> x \<le> snd J"
            using "1.IH" deg' v_ne1 v_nonzero P0' by presburger

          have IH_LR:
            "\<And>m N' x.
               \<lbrakk> try_blocks p a b N P ?v = None;
                  try_newton p a b N P ?v = None;
                  m = (a + b) / 2; N' = Nlin N;
                  poly P x = 0; a < x; x < b \<rbrakk> \<Longrightarrow>
               (\<exists>I\<in>set (newdsc p a m N' P). fst I \<le> x \<and> x \<le> snd I) \<or>
               (\<exists>I\<in>set (newdsc p m b N' P). fst I \<le> x \<and> x \<le> snd I) \<or>
               (x = m)"
          proof -
            fix m N' x
            assume TB0: "try_blocks p a b N P ?v = None"
               and TN0: "try_newton p a b N P ?v = None"
               and m_def: "m = (a + b) / 2"
               and N'_def: "N' = Nlin N"
               and rootx: "poly P x = 0" and ax': "a < x" and xb': "x < b"
            have am: "a < m" and mb: "m < b"
              using ab by (simp_all add: m_def)
            have split: "x < m \<or> x = m \<or> x > m"
              using ax' xb' am mb by linarith
            show "(\<exists>I\<in>set (newdsc p a m N' P). fst I \<le> x \<and> x \<le> snd I) \<or>
                  (\<exists>I\<in>set (newdsc p m b N' P). fst I \<le> x \<and> x \<le> snd I) \<or> x = m"
            proof (cases "x < m")
              case True
              then have "a < x" and "x < m" using ax' xb' am by auto
              then have Ex_left:
                "\<exists>I\<in>set (newdsc p a m N' P). fst I \<le> x \<and> x \<le> snd I"
                using "1.IH" deg' v_ne1 v_nonzero TB0 TN0 m_def N'_def rootx P0' by blast
              then show ?thesis by blast
            next
              case False
              then consider "x = m" | "x > m" by linarith
              then show ?thesis
              proof cases
                case 1
                then show ?thesis by blast
              next
                case 2
                then have "m < x" and "x < b" using xb' mb by auto
                then have Ex_right:
                  "\<exists>I\<in>set (newdsc p m b N' P). fst I \<le> x \<and> x \<le> snd I"
                  using "1.IH"(2) N'_def P0' TB0 TN0 ab deg' m_def rootx v_ne1 v_nonzero
                  by auto
                then show ?thesis by blast
              qed
            qed
          qed
          show ?thesis
          proof (cases "try_blocks p a b N P ?v")
            case (Some I)
            then have TB: "try_blocks p a b N P ?v = Some I" by simp
            have pos_in_I: "fst I < x \<and> x < snd I"
            proof -
              define w where "w = b - a"
              have "w > 0" using ab w_def by simp
              define B1 where "B1 = (a, a + w / of_nat N)"
              define B2 where "B2 = (b - w / of_nat N, b)"
              have "N > 0"
              proof (rule ccontr)
                assume "\<not> N > 0"
                hence "N = 0" by simp
                hence zero_width: "w / of_nat N = 0" using w_def by simp

                have "B1 = (a, a)" "B2 = (b, b)"
                  using zero_width unfolding B1_def B2_def by auto

                have v1_0: "Bernstein_changes p (fst B1) (snd B1) P = 0"
                  by (simp add: Bernstein_changes_point \<open>B1 = (a, a)\<close>)

                have v2_0: "Bernstein_changes p (fst B2) (snd B2) P = 0"
                  by (simp add: Bernstein_changes_point \<open>B2 = (b, b)\<close>)

                have "try_blocks p a b N P ?v = None"
                  unfolding try_blocks_def Let_def w_def[symmetric] B1_def[symmetric] B2_def[symmetric]
                  using \<open>N = 0\<close> v1_0 v2_0 v_ne1 v_nonzero
                  by auto

                thus False using TB by simp
              qed

              have I_props: "fst I \<ge> a \<and> snd I \<le> b \<and> snd I - fst I = w / of_nat N"
                using TB \<open>0 < N\<close> ab try_blocks_SomeD(1,2,3) w_def by presburger
              then have fst_le_snd: "fst I < snd I"
                using \<open>0 < N\<close> \<open>0 < w\<close> diff_gt_0_iff_gt by fastforce
              have v_I: "Bernstein_changes p (fst I) (snd I) P = ?v"
                using TB unfolding try_blocks_def Let_def by (auto split: if_split_asm)

              have "x \<noteq> snd I"
              proof
                assume "x = snd I"
                then have "poly P (snd I) = 0" using root by simp

                have "Bernstein_changes p a (snd I) P + Bernstein_changes p (snd I) b P + 1
                        \<le> Bernstein_changes p a b P"
                  using Bernstein_changes_split_root
                  using \<open>poly P (snd I) = 0\<close> \<open>x = snd I\<close> ax deg' xb
                  using P0' by blast

                moreover have "Bernstein_changes p a (snd I) P = ?v"
                  by (smt (verit, del_insts) TB fst_conv option.inject option.simps(3) snd_conv
                      try_blocks_def)
                ultimately have "?v + 0 + 1 \<le> ?v"
                  by (smt (verit) Bernstein_changes_def int_nat_eq)
                thus False by simp
              qed
              have "x \<noteq> fst I"
              proof
                assume "x = fst I"
                then have "poly P (fst I) = 0" using root by simp

                have "Bernstein_changes p a (fst I) P + Bernstein_changes p (fst I) b P + 1
                        \<le> Bernstein_changes p a b P"
                  using Bernstein_changes_split_root
                  using \<open>x = fst I\<close> ax deg' root xb
                  using P0' by blast

                moreover have "Bernstein_changes p (fst I) b P = ?v"
                  by (smt (verit, ccfv_threshold) I_props TB fst_conv option.distinct(1) option.inject
                      try_blocks_def w_def)
                ultimately have "?v + 0 + 1 \<le> ?v"
                  by (smt (verit) Bernstein_changes_def int_nat_eq)
                thus False by simp
              qed

              have not_left: "\<not> x < fst I"
              proof
                assume "x < fst I"
                hence "a < x" "x < fst I" using ax by simp_all
                hence "Bernstein_changes p a (fst I) P > 0"
                  using Bernstein_changes_pos_of_root[OF deg' P0' _ root]
                  by (metis Bernstein_changes_def I_props(1) dual_order.order_iff_strict int_nat_eq
                      order_less_asym')
                hence "Bernstein_changes p a (fst I) P \<ge> 1" by simp

                have "Bernstein_changes p a b P \<ge>
                      Bernstein_changes p a (fst I) P + Bernstein_changes p (fst I) b P"
                  using Bernstein_changes_split[of a "fst I" b] ab I_props `a < x` `x < fst I` deg' fst_le_snd by auto
                moreover have "Bernstein_changes p (fst I) b P \<ge>
                               Bernstein_changes p (fst I) (snd I) P"
                  using Bernstein_changes_split[of "fst I" "snd I" b] I_props fst_le_snd
                  by (smt (verit, del_insts) Bernstein_changes_def deg' int_nat_eq)
                then have "?v \<ge> 1 + ?v"
                  using v_I \<open>1 \<le> Bernstein_changes p a (fst I) P\<close> calculation by auto
                thus False by simp
              qed

              have not_right: "\<not> x > snd I"
              proof
                assume "x > snd I"
                hence "snd I < x" "x < b" using xb by simp_all
                hence "Bernstein_changes p (snd I) b P \<ge> 1"
                  using Bernstein_changes_pos_of_root[OF deg' P0' _ root]
                  by (metis Bernstein_changes_def I_props Orderings.order_eq_iff int_nat_eq
                      int_one_le_iff_zero_less not_le_imp_less not_less_iff_gr_or_eq)

                have "Bernstein_changes p a b P \<ge>
                      Bernstein_changes p a (snd I) P + Bernstein_changes p (snd I) b P"
                  using Bernstein_changes_split[of a "snd I" b] ab I_props \<open>snd I < x\<close> deg' fst_le_snd xb by force
                moreover have "Bernstein_changes p a (snd I) P \<ge>
                               Bernstein_changes p (fst I) (snd I) P"
                  using Bernstein_changes_split[of a "fst I" "snd I"] I_props fst_le_snd
                  by (smt (verit, best) TB fst_conv option.inject option.simps(3) try_blocks_def
                      w_def)
                ultimately have "?v \<ge> ?v + 1"
                  using v_I \<open>1 \<le> Bernstein_changes p (snd I) b P\<close> by linarith
                thus False by simp
              qed

              show "fst I < x \<and> x < snd I"
                using not_left not_right \<open>x \<noteq> fst I\<close> \<open>x \<noteq> snd I\<close> linorder_less_linear by blast
            qed
            then have fstI_lt: "fst I < x" and x_lt_sndI: "x < snd I"
              by auto

            from IH_block[OF TB root fstI_lt x_lt_sndI]
            obtain J where J_in: "J \<in> set (newdsc p (fst I) (snd I) (Nq N) P)"
                          and J_cov: "fst J \<le> x \<and> x \<le> snd J"
              by blast

            have J_in_top: "J \<in> set (newdsc p a b N P)"
            proof -
              have "newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
                using newdsc_eq False v_ne1 v_nonzero TB
                by (simp add: Let_def)
              thus ?thesis using J_in by simp
            qed

            show ?thesis
              using J_in_top J_cov by blast
          next
            case TB_None: None
            show ?thesis
            proof (cases "try_newton p a b N P ?v")
              case (Some I)
              then have TN: "try_newton p a b N P ?v = Some I" by simp

              have pos_in_I: "fst I < x \<and> x < snd I"
              proof -
                define w where "w = b - a"
                have "w > 0" using ab w_def by simp

                have "N > 0"
                proof (rule ccontr)
                  assume "\<not> N > 0"
                  hence "N = 0" by simp
                  have "try_newton p a b N P ?v = None"
                    unfolding try_newton_def Let_def snap_window_def
                    using \<open>N=0\<close> v_ge2 Bernstein_changes_point
                    by (auto split: option.split)
                  thus False using TN by simp
                qed

                have I_props: "fst I \<ge> a \<and> snd I \<le> b \<and> snd I - fst I = w / of_nat N"
                  using try_newton_SomeD[OF TN ab \<open>N > 0\<close>] w_def by simp

                have split_props: "fst I < snd I"
                  using I_props \<open>N > 0\<close> \<open>w > 0\<close>
                  by (metis diff_gt_0_iff_gt of_nat_0_less_iff zero_less_divide_iff)
                have v_I: "Bernstein_changes p (fst I) (snd I) P = ?v"
                  using TN unfolding try_newton_def Let_def
                  by (auto split: option.split_asm if_split_asm)

                have not_left: "\<not> (x < fst I)"
                proof
                  assume "x < fst I"
                  hence "a < x" "x < fst I" using ax by simp_all
                  hence "Bernstein_changes p a (fst I) P \<ge> 1"
                    using Bernstein_changes_pos_of_root[OF deg' P0' _ root]
                    by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)

                  have "Bernstein_changes p a b P \<ge>
                        Bernstein_changes p a (fst I) P + Bernstein_changes p (fst I) b P"
                    using Bernstein_changes_split[OF _ _ deg'] I_props `a < x` `x < fst I` split_props by simp

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
                    using Bernstein_changes_split[OF _ _ deg'] I_props `snd I < x` `x < b` split_props by simp

                  have "Bernstein_changes p a (snd I) P \<ge> Bernstein_changes p (fst I) (snd I) P"
                    using Bernstein_changes_split[OF _ split_props deg'] I_props split_props
                    by (smt (verit, ccfv_SIG) Bernstein_changes_def int_nat_eq)

                  have "?v \<ge> ?v + 1"
                    using v_I
                    using \<open>1 \<le> Bernstein_changes p (snd I) b P\<close>
                      \<open>Bernstein_changes p (fst I) (snd I) P \<le> Bernstein_changes p a (snd I) P\<close>
                      \<open>Bernstein_changes p a (snd I) P + Bernstein_changes p (snd I) b P \<le> Bernstein_changes p a b P\<close>
                    by linarith
                  thus False by simp
                qed

                have "x \<noteq> fst I"
                proof
                  assume "x = fst I"
                  then have "poly P (fst I) = 0" using root by simp

                  have "Bernstein_changes p a (fst I) P + Bernstein_changes p (fst I) b P + 1
                        \<le> Bernstein_changes p a b P"
                    using Bernstein_changes_split_root
                    using \<open>x = fst I\<close> ax deg' root xb  using P0' by blast

                  moreover have "Bernstein_changes p (fst I) b P \<ge> ?v"
                  proof -
                    have "Bernstein_changes p (fst I) b P =
                          Bernstein_changes p (fst I) (snd I) P + Bernstein_changes p (snd I) b P"
                      using Bernstein_changes_split[OF split_props _ deg'] I_props
                      by (smt (verit, ccfv_SIG) Bernstein_changes_def calculation of_nat_0_le_iff
                          v_I)
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
                    using Bernstein_changes_split_root
                    using \<open>x = snd I\<close> ax deg' xb
                    using \<open>poly P (snd I) = 0\<close> using P0' by blast

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
              then have fstI_lt: "fst I < x" and x_lt_sndI: "x < snd I"
                by auto

              from IH_newton[OF TB_None TN root fstI_lt x_lt_sndI]
              obtain J where J_in: "J \<in> set (newdsc p (fst I) (snd I) (Nq N) P)"
                            and J_cov: "fst J \<le> x \<and> x \<le> snd J"
                by blast

              have J_in_top: "J \<in> set (newdsc p a b N P)"
              proof -
                have "newdsc p a b N P =
                        (case try_blocks p a b N P ?v of
                           Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                         | None \<Rightarrow>
                             (case try_newton p a b N P ?v of
                                Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                              | None \<Rightarrow>
                                  (let m = (a + b) / 2;
                                       N' = Nlin N;
                                       mid_root = (if poly P m = 0 then [(m, m)] else [])
                                   in mid_root @ newdsc p a m N' P @ newdsc p m b N' P)))"
                  using newdsc_eq False v_ne1 v_nonzero
                  by (simp add: Let_def)
                moreover from TB_None TN have
                  "... = newdsc p (fst I) (snd I) (Nq N) P"
                  by simp
                ultimately show ?thesis
                  using J_in by simp
              qed

              show ?thesis
                using J_in_top J_cov by blast
            next
              case TN_None: None

              define m where "m = (a + b) / 2"
              define N' where "N' = Nlin N"

              have split:
                "(\<exists>I\<in>set (newdsc p a m N' P). fst I \<le> x \<and> x \<le> snd I) \<or>
                 (\<exists>I\<in>set (newdsc p m b N' P). fst I \<le> x \<and> x \<le> snd I) \<or>
                 x = m"
                using IH_LR[OF TB_None TN_None m_def N'_def root ax xb] .

              from split show ?thesis
              proof
                assume Ex_left:
                  "\<exists>I\<in>set (newdsc p a m N' P). fst I \<le> x \<and> x \<le> snd I"
                then obtain I where I_in: "I \<in> set (newdsc p a m N' P)"
                                 and I_cov: "fst I \<le> x \<and> x \<le> snd I"
                  by blast

                have mem_top:
                  "I \<in> set (newdsc p a b N P)"
                proof -
                  have "newdsc p a b N P =
                          (case try_blocks p a b N P ?v of
                             Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                           | None \<Rightarrow>
                               (case try_newton p a b N P ?v of
                                  Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                                | None \<Rightarrow>
                                    (let m = (a + b) / 2;
                                         N' = Nlin N;
                                         mid_root = (if poly P m = 0 then [(m,m)] else [])
                                     in mid_root @ newdsc p a m N' P @ newdsc p m b N' P)))"
                    using newdsc_eq False v_ne1 v_nonzero
                    by (simp add: Let_def)
                  moreover from TB_None TN_None have
                    "... =
                       (let m = (a + b) / 2;
                            N' = Nlin N;
                            mid_root = (if poly P m = 0 then [(m,m)] else [])
                        in mid_root @ newdsc p a m N' P @ newdsc p m b N' P)"
                    by simp
                  ultimately show ?thesis
                    using I_in
                    by (simp add: m_def N'_def Let_def)
                qed

                show ?thesis
                  using mem_top I_cov by blast
              next
                assume Ex_right_or_mid:
                  "(\<exists>I\<in>set (newdsc p m b N' P). fst I \<le> x \<and> x \<le> snd I) \<or> x = m"
                then show ?thesis
                proof
                  assume Ex_right:
                    "\<exists>I\<in>set (newdsc p m b N' P). fst I \<le> x \<and> x \<le> snd I"
                  then obtain I where I_in: "I \<in> set (newdsc p m b N' P)"
                                   and I_cov: "fst I \<le> x \<and> x \<le> snd I"
                    by blast

                  have mem_top:
                    "I \<in> set (newdsc p a b N P)"
                  proof -
                    have "newdsc p a b N P =
                            (case try_blocks p a b N P ?v of
                               Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                             | None \<Rightarrow>
                                 (case try_newton p a b N P ?v of
                                    Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                                  | None \<Rightarrow>
                                      (let m = (a + b) / 2;
                                           N' = Nlin N;
                                           mid_root = (if poly P m = 0 then [(m,m)] else [])
                                       in mid_root @ newdsc p a m N' P @ newdsc p m b N' P)))"
                      using newdsc_eq False v_ne1 v_nonzero
                      by (simp add: Let_def)
                    moreover from TB_None TN_None have
                      "... =
                         (let m = (a + b) / 2;
                              N' = Nlin N;
                              mid_root = (if poly P m = 0 then [(m,m)] else [])
                          in mid_root @ newdsc p a m N' P @ newdsc p m b N' P)"
                      by simp
                    ultimately show ?thesis
                      using I_in
                      by (simp add: m_def N'_def Let_def)
                  qed

                  show ?thesis
                    using mem_top I_cov by blast
                next
                  assume mid: "x = m"
                  then have mid_root: "poly P m = 0"
                    using root m_def by blast

                  have mid_ok:
                    "\<exists>I\<in>set (if poly P m = 0 then [(m,m)] else []). fst I \<le> x \<and> x \<le> snd I"
                  proof
                    show "(m,m) \<in> set (if poly P m = 0 then [(m,m)] else [])"
                      using mid_root by simp
                    moreover have "fst (m,m) \<le> x \<and> x \<le> snd (m,m)"
                      using mid by simp
                    ultimately show "fst (m,m) \<le> x \<and> x \<le> snd (m,m)" by simp
                  qed

                  then obtain I where I_mid_in:
                    "I \<in> set (if poly P m = 0 then [(m,m)] else [])"
                    and I_mid_cov: "fst I \<le> x \<and> x \<le> snd I"
                    by blast

                  have mem_top:
                    "I \<in> set (newdsc p a b N P)"
                  proof -
                    have "newdsc p a b N P =
                            (case try_blocks p a b N P ?v of
                               Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                             | None \<Rightarrow>
                                 (case try_newton p a b N P ?v of
                                    Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
                                  | None \<Rightarrow>
                                      (let m = (a + b) / 2;
                                           N' = Nlin N;
                                           mid_root = (if poly P m = 0 then [(m,m)] else [])
                                       in mid_root @ newdsc p a m N' P @ newdsc p m b N' P)))"
                      using newdsc_eq False v_ne1 v_nonzero
                      by (simp add: Let_def)
                    moreover from TB_None TN_None have
                      "... =
                         (let m = (a + b) / 2;
                              N' = Nlin N;
                              mid_root = (if poly P m = 0 then [(m,m)] else [])
                          in mid_root @ newdsc p a m N' P @ newdsc p m b N' P)"
                      by simp
                    ultimately show ?thesis
                      using I_mid_in
                      by (simp add: m_def N'_def Let_def)
                  qed

                  show ?thesis
                    using mem_top I_mid_cov by blast
                qed
              qed
            qed
          qed
        qed
      qed
    qed
    show ?thesis
      using "1.prems"(1,2,3) H by blast
  qed
qed

lemma newdsc_psimps_if:
  fixes P :: "real poly"
  assumes P0: "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0:  "p \<noteq> 0"
      and sf: "square_free P"
      and ab:  "a < b"
      and N2:  "N \<ge> 2"
  shows
    "newdsc p a b N P =
      (let v = Bernstein_changes p a b P in
       if v = 0 then []
       else if v = 1 then [(a, b)]
       else
         (case try_blocks p a b N P v of
            Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
          | None \<Rightarrow>
              (case try_newton p a b N P v of
                 Some I \<Rightarrow> newdsc p (fst I) (snd I) (Nq N) P
               | None \<Rightarrow>
                   (let m  = (a + b) / 2;
                        N' = Nlin N;
                        mid_root = (if poly P m = 0 then [(m, m)] else [])
                    in mid_root @ newdsc p a m N' P @ newdsc p m b N' P))))"
proof -
  have dom: "newdsc_dom (p, a, b, N, P)"
    using newdsc_terminates_squarefree ab N2 P0 deg p0 sf
    by blast
  show ?thesis
    using newdsc.psimps[OF dom] P0 ab
    by argo
qed

end