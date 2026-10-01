theory Dsc_Exec
  imports Dsc
          Dsc_Bern
          NewDsc
begin

text \<open>Executable form of the abstract solvers — the tail-recursive worklist drivers
  \<open>dsc\<close>/\<open>newdsc\<close> are shown equivalent to.
  Layer: FUNCTIONAL SPEC.
  Main exports: \<open>dsc_main_exec\<close>, \<open>newdsc_main_exec\<close> and their equivalence theorems.\<close>

partial_function (tailrec) dsc_main_exec ::
  "real poly \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "dsc_main_exec P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b) # todo' \<Rightarrow>
          (let v = descartes_roots_test_sc a b P in
           if v = 0 then
             dsc_main_exec P todo' acc
           else if v = 1 then
             dsc_main_exec P todo' ((a,b) # acc)
           else
             (let m = (a + b) / 2;
                  acc' = (if poly P m = 0 then (m,m) # acc else acc)
              in dsc_main_exec P ((a,m) # (m,b) # todo') acc')))"

definition dsc_exec :: "real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "dsc_exec a b P = (dsc_main_exec P [(a,b)] [])"

lemma dsc_main_exec_sim:
  assumes dom:  "dsc_dom (p,a,b,P)"
      and pdeg: "p = degree P"
  shows
    "dsc_main_exec P ((a,b) # todo) acc =
     dsc_main_exec P todo (rev (dsc p a b P) @ acc)"
  using dom pdeg
proof (induction p a b P arbitrary: todo acc rule: dsc.pinduct)
  case (1 p a b P todo acc)
  let ?v = "Bernstein_changes p a b P"

  have v_eq: "descartes_roots_test_sc a b P = ?v"
    using "1.prems"
    by (simp add: descartes_roots_test_sc_eq_Bernstein_changes)

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have dsc0: "dsc p a b P = []"
      by (simp add: "1.hyps" dsc.psimps v0)
    show ?thesis
      using dsc0 dsc_main_exec.simps v0 v_eq by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have dsc1: "dsc p a b P = [(a,b)]"
        by (simp add: "1.hyps" dsc.psimps v1)
      show ?thesis
        using dsc_main_exec.simps Let_def v0 v1 v_eq dsc1 by auto
    next
      case v1: False
      define m where "m = (a + b) / 2"
      let ?mid = "(if poly P m = 0 then [(m,m)] else [])"

      have dsc_split:
        "dsc p a b P = ?mid @ dsc p a m P @ dsc p m b P"
        by (smt (verit, ccfv_SIG) "1.hyps" dsc.psimps m_def v0 v1)

      have mid_acc_eq:
        "(if poly P m = 0 then (m,m) # acc else acc) = ?mid @ acc"
        by (cases "poly P m = 0"; simp)

      have main_split:
        "dsc_main_exec P ((a,b) # todo) acc =
         dsc_main_exec P ((a,m) # (m,b) # todo) (?mid @ acc)"
      proof -
        have tmp:
          "dsc_main_exec P ((a,b) # todo) acc =
           dsc_main_exec P ((a,m) # (m,b) # todo)
             (if poly P m = 0 then (m,m) # acc else acc)"
          by (smt (verit) dsc_main_exec.simps int_ops(2) list.simps(5) m_def of_nat_eq_0_iff old.prod.case v0 v1
              v_eq)
        show ?thesis
          using tmp
          by (simp add: mid_acc_eq)
      qed

      have stepL:
        "dsc_main_exec P ((a,m) # (m,b) # todo) (?mid @ acc) =
         dsc_main_exec P ((m,b) # todo) (rev (dsc p a m P) @ (?mid @ acc))"
        using "1.IH"(1)[of ?v m "((m,b)#todo)" "?mid @ acc"]
        v0 v1 m_def v_eq "1.prems" by blast

      have stepR:
        "dsc_main_exec P ((m,b) # todo) (rev (dsc p a m P) @ (?mid @ acc)) =
         dsc_main_exec P todo
           (rev (dsc p m b P) @ (rev (dsc p a m P) @ (?mid @ acc)))"
        using "1.IH"(2)[of ?v m todo "rev (dsc p a m P) @ (?mid @ acc)"]
        v0 v1 m_def v_eq "1.prems" by blast

      have LHS_rewrite:
        "dsc_main_exec P ((a,b) # todo) acc =
         dsc_main_exec P todo
           (rev (dsc p m b P) @ rev (dsc p a m P) @ ?mid @ acc)"
        using main_split stepL stepR
        by simp

      have RHS_rewrite:
        "dsc_main_exec P todo (rev (dsc p a b P) @ acc) =
         dsc_main_exec P todo
           (rev (dsc p m b P) @ rev (dsc p a m P) @ ?mid @ acc)"
        using dsc_split
        by simp

      show ?thesis
        using LHS_rewrite RHS_rewrite
        by simp
    qed
  qed
qed

lemma dsc_exec_eq_dsc:
  assumes dom:  "dsc_dom (p,a,b,P)"
      and pdeg: "p = degree P"
  shows "rev (dsc_exec a b P) = dsc p a b P"
proof -
  have tr: "dsc_exec a b P = rev (dsc p a b P)"
    unfolding dsc_exec_def
    using dsc_main_exec_sim[OF dom pdeg, of "[]::(real\<times>real) list" "[]"]
    by (simp add: dsc_main_exec.simps)
  thus ?thesis by simp
qed


definition try_blocks_sc ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_blocks_sc a b N P v =
     (let w = b - a;
          B1 = (a, a + w / of_nat N);
          B2 = (b - w / of_nat N, b);
          v1 = descartes_roots_test_sc (fst B1) (snd B1) P;
          v2 = descartes_roots_test_sc (fst B2) (snd B2) P
      in if v1 = v then Some B1 else if v2 = v then Some B2 else None)"

lemma try_block_sc_eq:
  assumes "p = degree P"
  shows "try_blocks_sc a b N P v = try_blocks p a b N P v"
  using assms descartes_roots_test_sc_eq_Bernstein_changes try_blocks_def
    try_blocks_sc_def by presburger

definition try_newton_sc ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_newton_sc a b N P v =
     (let L1 = newton_at v P a; L2 = newton_at v P b in
      case L1 of
        Some lam1 \<Rightarrow>
          (let I1 = snap_window a b N lam1;
               v1 = descartes_roots_test_sc (fst I1) (snd I1) P
           in if v1 = v then Some I1
              else (case L2 of
                      Some lam2 \<Rightarrow>
                        (let I2 = snap_window a b N lam2;
                             v2 = descartes_roots_test_sc (fst I2) (snd I2) P
                         in if v2 = v then Some I2 else None)
                    | None \<Rightarrow> None))
      | None \<Rightarrow>
          (case L2 of
             Some lam2 \<Rightarrow>
               (let I2 = snap_window a b N lam2;
                    v2 = descartes_roots_test_sc (fst I2) (snd I2)  P
                in if v2 = v then Some I2 else None)
           | None \<Rightarrow> None))"

lemma try_newton_sc_eq:
  assumes "p = degree P"
  shows "try_newton_sc a b N P v = try_newton p a b N P v"
  using assms descartes_roots_test_sc_eq_Bernstein_changes try_newton_def try_newton_sc_def
  by presburger

partial_function (tailrec) newdsc_main_exec ::
  "real poly \<Rightarrow> (real \<times> real \<times> nat) list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "newdsc_main_exec P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b,N) # todo' \<Rightarrow>
          (let v = descartes_roots_test_sc a b P in
           if v = 0 then
             newdsc_main_exec P todo' acc
           else if v = 1 then
             newdsc_main_exec P todo' ((a,b) # acc)
           else
             (case try_blocks_sc a b N P v of
                Some I \<Rightarrow>
                  newdsc_main_exec P ((fst I, snd I, Nq N) # todo') acc
              | None \<Rightarrow>
                  (case try_newton_sc a b N P v of
                     Some I \<Rightarrow>
                       newdsc_main_exec P ((fst I, snd I, Nq N) # todo') acc
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            N' = Nlin N;
                            acc' = (if poly P m = 0 then (m,m) # acc else acc)
                        in newdsc_main_exec P ((a,m,N') # (m,b,N') # todo') acc')))))"

definition newdsc_exec ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "newdsc_exec a b N P = newdsc_main_exec P [(a,b,N)] []"

lemma newdsc_main_exec_sim:
  assumes dom:  "newdsc_dom (p,a,b,N,P)"
      and pdeg: "p = degree P"
  shows
    "newdsc_main_exec P ((a,b,N) # todo) acc =
     newdsc_main_exec P todo (rev (newdsc p a b N P) @ acc)"
  using dom pdeg
proof (induction p a b N P arbitrary: todo acc rule: newdsc.pinduct)
  case (1 p a b N P todo acc)
  let ?v = "Bernstein_changes p a b P"

  have deg_p: "degree P = p"
    using "1.prems" by (simp add: eq_commute)

  have v_eq: "descartes_roots_test_sc a b P = ?v"
    using deg_p by (simp add: descartes_roots_test_sc_eq_Bernstein_changes)

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have nd0: "newdsc p a b N P = []"
      by (simp add: "1.hyps" newdsc.psimps v0)
    show ?thesis
      using nd0 newdsc_main_exec.simps Let_def v0 v_eq by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have nd1: "newdsc p a b N P = [(a,b)]"
        by (simp add: "1.hyps" newdsc.psimps v1)
      show ?thesis
        using nd1 newdsc_main_exec.simps Let_def v0 v1 v_eq by auto
    next
      case v1: False

      show ?thesis
      proof (cases "try_blocks p a b N P ?v")
        case (Some I)
        have nd_block:
          "newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
          by (simp add: "1.hyps" newdsc.psimps v0 v1 Some)

        have main_block:
          "newdsc_main_exec P ((a,b,N) # todo) acc =
           newdsc_main_exec P ((fst I, snd I, Nq N) # todo) acc"
          using Some newdsc_main_exec.simps Let_def v0 v1 v_eq
                try_block_sc_eq "1.prems" 
          by simp

        have stepI:
          "newdsc_main_exec P ((fst I, snd I, Nq N) # todo) acc =
           newdsc_main_exec P todo (rev (newdsc p (fst I) (snd I) (Nq N) P) @ acc)"
          using "1.IH" v0 v1 Some deg_p by presburger

        show ?thesis
          using main_block stepI nd_block
          by simp
      next
        case TB0: None
        show ?thesis
        proof (cases "try_newton p a b N P ?v")
          case (Some I)
          have nd_newton:
            "newdsc p a b N P = newdsc p (fst I) (snd I) (Nq N) P"
            by (simp add: "1.hyps" newdsc.psimps v0 v1 TB0 Some)

          have main_newton:
            "newdsc_main_exec P ((a,b,N) # todo) acc =
             newdsc_main_exec P ((fst I, snd I, Nq N) # todo) acc"
            using TB0 Some newdsc_main_exec.simps Let_def v0 v1 v_eq
                  try_block_sc_eq try_newton_sc_eq deg_p 
            by force

          have stepI:
            "newdsc_main_exec P ((fst I, snd I, Nq N) # todo) acc =
             newdsc_main_exec P todo (rev (newdsc p (fst I) (snd I) (Nq N) P) @ acc)"
            using "1.IH"(3) v0 v1 TB0 Some deg_p by force

          show ?thesis
            using main_newton stepI nd_newton
            by simp
        next
          case TN0: None
          define m  where "m  = (a + b) / 2"
          define N' where "N' = Nlin N"
          let ?mid = "(if poly P m = 0 then [(m,m)] else [])"

          have nd_split:
            "newdsc p a b N P = ?mid @ newdsc p a m N' P @ newdsc p m b N' P"
            by (simp add: "1.hyps" newdsc.psimps Let_def v0 v1 TB0 TN0 m_def N'_def)

          have mid_acc_eq:
            "(if poly P m = 0 then (m,m) # acc else acc) = ?mid @ acc"
            by (cases "poly P m = 0"; simp)

          have main_split:
            "newdsc_main_exec P ((a,b,N) # todo) acc =
             newdsc_main_exec P ((a,m,N') # (m,b,N') # todo) (?mid @ acc)"
          proof -
            have tmp:
              "newdsc_main_exec P ((a,b,N) # todo) acc =
               newdsc_main_exec P ((a,m,N') # (m,b,N') # todo)
                 (if poly P m = 0 then (m,m) # acc else acc)"
              by (smt (verit) TB0 TN0 newdsc_main_exec.simps Let_def v0 v1 v_eq m_def N'_def
                    try_block_sc_eq try_newton_sc_eq deg_p list.case(2) option.case(1) prod.simps(2))
            show ?thesis
              using tmp by (simp add: mid_acc_eq)
          qed

          have stepL:
            "newdsc_main_exec P ((a,m,N') # (m,b,N') # todo) (?mid @ acc) =
             newdsc_main_exec P ((m,b,N') # todo)
               (rev (newdsc p a m N' P) @ (?mid @ acc))"
            using "1.IH"(1) v0 v1 TB0 TN0 m_def N'_def deg_p 
            by blast

          have stepR:
            "newdsc_main_exec P ((m,b,N') # todo)
               (rev (newdsc p a m N' P) @ (?mid @ acc)) =
             newdsc_main_exec P todo
               (rev (newdsc p m b N' P) @ (rev (newdsc p a m N' P) @ (?mid @ acc)))"
            using "1.IH"(2) v0 v1 TB0 TN0 m_def N'_def deg_p by blast

          have LHS_rewrite:
            "newdsc_main_exec P ((a,b,N) # todo) acc =
             newdsc_main_exec P todo
               (rev (newdsc p m b N' P) @ rev (newdsc p a m N' P) @ ?mid @ acc)"
            using main_split stepL stepR
            by simp

          have RHS_rewrite:
            "newdsc_main_exec P todo (rev (newdsc p a b N P) @ acc) =
             newdsc_main_exec P todo
               (rev (newdsc p m b N' P) @ rev (newdsc p a m N' P) @ ?mid @ acc)"
            using nd_split
            by simp

          show ?thesis
            using LHS_rewrite RHS_rewrite
            by simp
        qed
      qed
    qed
  qed
qed

lemma newdsc_exec_eq_newdsc:
  assumes dom:  "newdsc_dom (p,a,b,N,P)"
      and pdeg: "p = degree P"
  shows "rev (newdsc_exec a b N P) = newdsc p a b N P"
proof -
  have tr: "newdsc_exec a b N P = rev (newdsc p a b N P)"
    unfolding newdsc_exec_def
    using newdsc_main_exec_sim[OF dom pdeg, of "[]::(real\<times>real\<times>nat) list" "[]::(real\<times>real) list"]
    by (simp add: newdsc_main_exec.simps)
  show ?thesis
    using tr by simp
qed


definition N_of :: "nat \<Rightarrow> nat" where
  "N_of e = 2 ^ (2 ^ e)"

lemma N_of_Nq:
  "Nq (N_of e) = N_of (e + 1)"
  unfolding N_of_def Nq_def
  by (simp add: power_add[symmetric])

lemma N_of_Nlin:
  "Nlin (N_of e) = N_of (max 1 (e - 1))"
proof (cases e)
  case 0
  have eq1: "N_of 0 = 2" 
    unfolding N_of_def by simp
  have eq2: "N_of (max 1 (0 - 1)) = 4" 
    unfolding N_of_def by simp
  have "sqrt (4::real) = sqrt (2\<^sup>2)" 
    by simp
  also have "\<dots> = 2" 
    by simp
  finally have "sqrt 4 = 2" .
  have "(2::real) < 4" 
    by simp
  hence "sqrt 2 < sqrt 4" 
    by (metis \<open>2 < 4\<close> real_sqrt_less_iff)
  hence "sqrt 2 < 2" 
    using `sqrt 4 = 2` by simp
  hence "\<lfloor>sqrt 2\<rfloor> \<le> 1" 
    by linarith
  hence "nat \<lfloor>sqrt 2\<rfloor> \<le> 1" 
    by linarith
  hence "max 4 (nat \<lfloor>sqrt 2\<rfloor>) = 4" 
    by simp
  thus ?thesis 
    unfolding Nlin_def eq1 eq2 
    by (metis \<open>max 4 (nat \<lfloor>sqrt 2\<rfloor>) = 4\<close> "0" eq2 of_nat_eq_numeral_iff eq1)
next
  case (Suc k)
  have "(2::nat) ^ (2 ^ Suc k) = (2::nat) ^ (2 * 2 ^ k)"
    by simp
  also have "\<dots> = ((2::nat) ^ (2 ^ k))\<^sup>2"
    by (simp add: power_even_eq)
  finally have "N_of (Suc k) = (N_of k)\<^sup>2"
    unfolding N_of_def by simp
  hence "real (N_of (Suc k)) = (real (N_of k))\<^sup>2"
    by simp
  hence "sqrt (real (N_of (Suc k))) = real (N_of k)"
    by simp
  hence "nat \<lfloor>sqrt (real (N_of (Suc k)))\<rfloor> = N_of k"
    by simp
  moreover have "max 4 (N_of k) = N_of (max 1 k)"
  proof (cases k)
    case 0
    then show ?thesis 
      unfolding N_of_def by simp
  next
    case (Suc k')
    have "2 \<le> (2::nat) ^ k" 
      using Suc by simp
    hence "4 \<le> (2::nat) ^ (2 ^ k)"
      using power_increasing[of 2 "2 ^ k" "2::nat"] by simp
    hence "4 \<le> N_of k" 
      unfolding N_of_def by simp
    thus ?thesis 
      using Suc by (simp add: max_def)
  qed
  ultimately show ?thesis
    unfolding Nlin_def using Suc by simp
qed

partial_function (tailrec) newdsc_main_exec_e ::
  "real poly \<Rightarrow> (real \<times> real \<times> nat) list \<Rightarrow> (real \<times> real) list \<Rightarrow> (real \<times> real) list"
where
  [code]:
  "newdsc_main_exec_e P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a,b,e) # todo' \<Rightarrow>
          (let v = descartes_roots_test_sc a b P in
           if v = 0 then
             newdsc_main_exec_e P todo' acc
           else if v = 1 then
             newdsc_main_exec_e P todo' ((a,b) # acc)
           else
             (case try_blocks_sc a b (N_of e) P v of
                Some I \<Rightarrow>
                  newdsc_main_exec_e P ((fst I, snd I, e + 1) # todo') acc
              | None \<Rightarrow>
                  (case try_newton_sc a b (N_of e) P v of
                     Some I \<Rightarrow>
                       newdsc_main_exec_e P ((fst I, snd I, e + 1) # todo') acc
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            e' = max 1 (e - 1);
                            acc' = (if poly P m = 0 then (m,m) # acc else acc)
                        in newdsc_main_exec_e P ((a,m,e') # (m,b,e') # todo') acc')))))"

definition newdsc_exec_e ::
  "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> (real \<times> real) list"
where
  "newdsc_exec_e a b e P = newdsc_main_exec_e P [(a,b,e)] []"

lemma newdsc_main_exec_e_sim:
  assumes dom:  "newdsc_dom (p,a,b,N_of e,P)"
      and pdeg: "p = degree P"
  shows
    "newdsc_main_exec_e P ((a,b,e) # todo) acc =
     newdsc_main_exec_e P todo (rev (newdsc p a b (N_of e) P) @ acc)"
  using dom pdeg
proof (induction p a b "N_of e" P arbitrary: e todo acc rule: newdsc.pinduct)
  case (1 p a b P e todo acc)
  let ?v = "Bernstein_changes p a b P"

  have deg_p: "degree P = p"
    using "1.prems" by (simp add: eq_commute)

  have v_eq: "descartes_roots_test_sc a b P = ?v"
    using deg_p by (simp add: descartes_roots_test_sc_eq_Bernstein_changes)

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have nd0: "newdsc p a b (N_of e) P = []"
      by (simp add: "1.hyps" newdsc.psimps v0)
    show ?thesis
      using nd0 newdsc_main_exec_e.simps Let_def v0 v_eq by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have nd1: "newdsc p a b (N_of e) P = [(a,b)]"
        by (simp add: "1.hyps" newdsc.psimps v1)
      show ?thesis
        using nd1 newdsc_main_exec_e.simps Let_def v0 v1 v_eq by auto
    next
      case v1: False

      show ?thesis
      proof (cases "try_blocks p a b (N_of e) P ?v")
        case (Some I)
        have nd_block:
          "newdsc p a b (N_of e) P = newdsc p (fst I) (snd I) (N_of (e + 1)) P"
          using "1.hyps" newdsc.psimps v0 v1 Some N_of_Nq[symmetric] by simp

        have main_block:
          "newdsc_main_exec_e P ((a,b,e) # todo) acc =
           newdsc_main_exec_e P ((fst I, snd I, e + 1) # todo) acc"
          using Some newdsc_main_exec_e.simps Let_def v0 v1 v_eq
                try_block_sc_eq "1.prems" by simp

        have stepI:
          "newdsc_main_exec_e P ((fst I, snd I, e + 1) # todo) acc =
           newdsc_main_exec_e P todo (rev (newdsc p (fst I) (snd I) (N_of (e + 1)) P) @ acc)"
          using v0 v1 Some deg_p N_of_Nq "1"(5) by blast

        show ?thesis
          using main_block stepI nd_block by simp
      next
        case TB0: None
        show ?thesis
        proof (cases "try_newton p a b (N_of e) P ?v")
          case (Some I)
          have nd_newton:
            "newdsc p a b (N_of e) P = newdsc p (fst I) (snd I) (N_of (e + 1)) P"
            using "1.hyps" newdsc.psimps v0 v1 TB0 Some N_of_Nq[symmetric] by simp

          have main_newton:
            "newdsc_main_exec_e P ((a,b,e) # todo) acc =
             newdsc_main_exec_e P ((fst I, snd I, e + 1) # todo) acc"
            using TB0 Some newdsc_main_exec_e.simps Let_def v0 v1 v_eq
                  try_block_sc_eq try_newton_sc_eq deg_p by force

          have stepI:
            "newdsc_main_exec_e P ((fst I, snd I, e + 1) # todo) acc =
             newdsc_main_exec_e P todo (rev (newdsc p (fst I) (snd I) (N_of (e + 1)) P) @ acc)"
            using "1"(4) v0 v1 TB0 Some deg_p N_of_Nq by metis

          show ?thesis
            using main_newton stepI nd_newton by simp
        next
          case TN0: None
          define m  where "m  = (a + b) / 2"
          define e' where "e' = max 1 (e - 1)"

          let ?mid = "(if poly P m = 0 then [(m,m)] else [])"

          have nd_split:
            "newdsc p a b (N_of e) P = ?mid @ newdsc p a m (N_of e') P @ newdsc p m b (N_of e') P"
            using N_of_Nlin[symmetric] e'_def
            by (simp add: "1.hyps" newdsc.psimps Let_def v0 v1 TB0 TN0 m_def N_of_Nlin)

          have mid_acc_eq:
             "(if poly P m = 0 then (m,m) # acc else acc) = ?mid @ acc"
            by (cases "poly P m = 0"; simp)

          have main_split:
            "newdsc_main_exec_e P ((a,b,e) # todo) acc =
             newdsc_main_exec_e P ((a,m,e') # (m,b,e') # todo) (?mid @ acc)"
          proof -
            have tmp:
              "newdsc_main_exec_e P ((a,b,e) # todo) acc =
                newdsc_main_exec_e P ((a,m,e') # (m,b,e') # todo)
                 (if poly P m = 0 then (m,m) # acc else acc)"
              by (smt (verit) TB0 TN0 newdsc_main_exec_e.simps Let_def v0 v1 v_eq m_def e'_def
                    try_block_sc_eq try_newton_sc_eq deg_p list.case(2) option.case(1) prod.simps(2))
            show ?thesis
              using tmp by (simp add: mid_acc_eq)
          qed

          have stepL:
            "newdsc_main_exec_e P ((a,m,e') # (m,b,e') # todo) (?mid @ acc) =
             newdsc_main_exec_e P ((m,b,e') # todo)
               (rev (newdsc p a m (N_of e') P) @ (?mid @ acc))"
            using "1"(2) v0 v1 TB0 TN0 m_def e'_def deg_p N_of_Nlin by metis

          have stepR:
            "newdsc_main_exec_e P ((m,b,e') # todo)
               (rev (newdsc p a m (N_of e') P) @ (?mid @ acc)) =
             newdsc_main_exec_e P todo
               (rev (newdsc p m b (N_of e') P) @ (rev (newdsc p a m (N_of e') P) @ (?mid @ acc)))"
            using "1"(3) v0 v1 TB0 TN0 m_def e'_def deg_p N_of_Nlin by metis

          have LHS_rewrite:
            "newdsc_main_exec_e P ((a,b,e) # todo) acc =
             newdsc_main_exec_e P todo
               (rev (newdsc p m b (N_of e') P) @ rev (newdsc p a m (N_of e') P) @ ?mid @ acc)"
            using main_split stepL stepR
            by simp

          have RHS_rewrite:
            "newdsc_main_exec_e P todo (rev (newdsc p a b (N_of e) P) @ acc) =
             newdsc_main_exec_e P todo
               (rev (newdsc p m b (N_of e') P) @ rev (newdsc p a m (N_of e') P) @ ?mid @ acc)"
            using nd_split
            by simp

          show ?thesis
             using LHS_rewrite RHS_rewrite
            by simp
        qed
      qed
    qed
  qed
qed

lemma newdsc_exec_e_eq_newdsc:
  assumes dom:  "newdsc_dom (p,a,b,N_of e,P)"
      and pdeg: "p = degree P"
  shows "rev (newdsc_exec_e a b e P) = newdsc p a b (N_of e) P"
proof -
  have tr: "newdsc_exec_e a b e P = rev (newdsc p a b (N_of e) P)"
    unfolding newdsc_exec_e_def
    using newdsc_main_exec_e_sim[OF dom pdeg, of "[]::(real\<times>real\<times>nat) list" "[]::(real\<times>real) list"]
    by (simp add: newdsc_main_exec_e.simps)
  show ?thesis
    using tr by simp
qed

end