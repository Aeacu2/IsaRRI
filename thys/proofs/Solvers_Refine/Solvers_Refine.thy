theory Solvers_Refine
  imports
    IsaRRI_LLVM.Bisection_Refine
    IsaRRI_LLVM.Rational_Refine
begin

text \<open>GAP-2 step 2: the functional carried worklist refines the endpoint worklist.
  Layer: NRES REFINEMENT.
  Main exports: the \<open>carried_step\<close>/\<open>carried_node\<close> abstract model and its equivalence
  onto \<open>rational_queue_step_int\<close>.\<close>

section \<open>GAP 2 step 2: the functional carried worklist refines the endpoint worklist\<close>

text \<open>A pure functional model of the carried main loop: the worklist carries, with each
  interval @{text "(a,b)"}, the carried polynomial @{term Q} that represents it
  (@{const carried_repr}). The dispatch mirrors @{const rational_queue_step_int} exactly,
  but takes the Descartes count from @{term Q} (via @{const carried_descartes_count}) and
  forms the children with the carried transforms instead of recomputing.\<close>

definition carried_step ::
  "gmp_poly \<Rightarrow> ((rat \<times> rat) \<times> gmp_poly) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow>
    (((rat \<times> rat) \<times> gmp_poly) list \<times> (rat \<times> rat) list)" where
"carried_step P todo acc =
  (case todo of
    [] \<Rightarrow> ([], acc)
  | ((a, b), Q) # rest \<Rightarrow>
      (let v = carried_descartes_count Q in
       if v = 0 then (rest, acc)
       else if v = 1 then (rest, acc @ [(a, b)])
       else
         (let m = (a + b) / 2 in
          (rest @ [((a, m), carried_left Q), ((m, b), carried_right Q)],
           acc @
             (if poly (map_poly rat_of_int (Poly P)) m = 0
              then [(m, m)] else [])))))"

text \<open>Step correspondence: under @{const carried_repr} for the head interval, one carried step
  produces the same accumulator and the same interval worklist (projected with @{term fst}) as
  one endpoint step. Needs only B3 (the count bridge).\<close>
lemma carried_step_corresp:
  assumes "carried_repr P a b Q"
  shows "(map fst (fst (carried_step P (((a, b), Q) # rest) acc)),
          snd (carried_step P (((a, b), Q) # rest) acc))
       = rational_queue_step_int P ((a, b) # map fst rest) acc"
proof -
  have "carried_descartes_count Q = descartes_list_int a b P"
    using assms by (rule carried_repr_count)
  thus ?thesis
    by (simp add: carried_step_def rational_queue_step_int_def Let_def)
qed

text \<open>Preservation: a bisection step keeps @{const carried_repr} on both children (B1+B2).
  The odd-width-numerator side-condition holds for every interval reached from the root by
  bisection (see @{thm carried_repr_left}); carried here as a hypothesis.\<close>
lemma carried_step_preserves_repr:
  assumes "carried_repr P a b Q" and "0 < length P" and "a < b"
    and "odd (fst (quotient_of ((b - a) * of_int (snd (quotient_of a)))))"
  shows "carried_repr P a ((a + b) / 2) (carried_left Q)"
    and "carried_repr P ((a + b) / 2) b (carried_right Q)"
   apply (rule carried_repr_left[OF assms(1) assms(4)])
  apply (rule carried_repr_right[OF assms(1) assms(2) assms(3) assms(4)])
  done

lemma quotient_of_denom_dvd:
  assumes "z = of_int p / of_int q" and "0 < q"
  shows "snd (quotient_of z) dvd q"
proof -
  have "z = Rat.Fract p q" using assms by (simp add: Fract_of_int_quotient)
  hence "quotient_of z = Rat.normalize (p, q)" by (simp add: quotient_of_Fract)
  hence eq: "snd (quotient_of z) = q div gcd p q"
    using assms(2) by (simp add: Rat.normalize_def Let_def)
  have "q div gcd p q dvd gcd p q * (q div gcd p q)" by (rule dvd_triv_right)
  hence "q div gcd p q dvd q" by simp
  thus ?thesis using eq by simp
qed

text \<open>The odd-width-numerator side-condition of B1/B2 holds for every unit dyadic interval
  @{text "[l/2^k, (l+1)/2^k]"}: the width numerator is in fact exactly @{text 1}. Uses the bridge
  helper @{thm quotient_of_denom_dvd} (the denominator of @{text "l/2^k"} divides @{text "2^k"}).\<close>
lemma fst_quotient_of_dyadic_width:
  fixes l :: int and k :: nat
  defines "a \<equiv> (of_int l / 2 ^ k :: rat)"
  shows "fst (quotient_of ((of_int (l + 1) / 2 ^ k - a)
            * of_int (snd (quotient_of a)))) = 1"
proof -
  have width: "(of_int (l + 1) / 2 ^ k :: rat) - a = 1 / 2 ^ k"
    by (simp add: a_def field_simps)
  have dvd: "snd (quotient_of a) dvd (2 ^ k :: int)"
    by (rule quotient_of_denom_dvd[where p = l and q = "2 ^ k"]) (simp_all add: a_def)
  have pos: "0 < snd (quotient_of a)" by (rule quotient_of_denom_pos')
  let ?da = "snd (quotient_of a)"
  have "(1 / 2 ^ k :: rat) * of_int ?da = Rat.Fract ?da (2 ^ k)"
    by (simp add: Fract_of_int_quotient)
  hence "quotient_of ((1 / 2 ^ k :: rat) * of_int ?da) = Rat.normalize (?da, 2 ^ k)"
    by (simp add: quotient_of_Fract)
  also have "Rat.normalize (?da, 2 ^ k) = (1, 2 ^ k div ?da)"
  proof -
    have "gcd ?da (2 ^ k) = ?da"
    proof (rule zdvd_antisym_nonneg)
      show "0 \<le> gcd ?da (2 ^ k)" by simp
      show "0 \<le> ?da" using pos by simp
      show "gcd ?da (2 ^ k) dvd ?da" by (rule gcd_dvd1)
      show "?da dvd gcd ?da (2 ^ k)" by (rule gcd_greatest[OF dvd_refl dvd])
    qed
    thus ?thesis using pos by (simp add: Rat.normalize_def Let_def)
  qed
  finally show ?thesis using width by simp
qed

text \<open>The unit-dyadic invariant: every node interval is @{text "[l/2^k, (l+1)/2^k]"}. The root
  @{text "[0,1]"} satisfies it and bisection preserves it; it implies @{text "a<b"} and the
  B1/B2 odd-nw side-condition (via @{thm fst_quotient_of_dyadic_width}).\<close>
definition unit_dyadic :: "rat \<times> rat \<Rightarrow> bool" where
"unit_dyadic ab \<longleftrightarrow> (\<exists>l k. fst ab = of_int l / 2 ^ k \<and> snd ab = of_int (l + 1) / 2 ^ k)"

lemma unit_dyadic_less:
  assumes "unit_dyadic (a, b)" shows "a < b"
proof -
  from assms obtain l k where "a = of_int l / 2 ^ k" "b = of_int (l + 1) / 2 ^ k"
    by (auto simp: unit_dyadic_def)
  thus ?thesis by (simp add: divide_strict_right_mono)
qed

lemma unit_dyadic_odd_nw:
  assumes "unit_dyadic (a, b)"
  shows "odd (fst (quotient_of ((b - a) * of_int (snd (quotient_of a)))))"
proof -
  from assms obtain l k where "a = of_int l / 2 ^ k" "b = of_int (l + 1) / 2 ^ k"
    by (auto simp: unit_dyadic_def)
  thus ?thesis using fst_quotient_of_dyadic_width[of l k] by simp
qed

lemma unit_dyadic_bisect_left:
  assumes "unit_dyadic (a, b)" shows "unit_dyadic (a, (a + b) / 2)"
proof -
  from assms obtain l k where lk: "a = of_int l / 2 ^ k" "b = of_int (l + 1) / 2 ^ k"
    by (auto simp: unit_dyadic_def)
  show ?thesis unfolding unit_dyadic_def
  proof (intro exI conjI)
    show "fst (a, (a + b) / 2) = of_int (2 * l) / 2 ^ (k + 1)"
      using lk by (simp add: field_simps)
    show "snd (a, (a + b) / 2) = of_int (2 * l + 1) / 2 ^ (k + 1)"
      using lk by (simp add: field_simps)
  qed
qed

lemma unit_dyadic_bisect_right:
  assumes "unit_dyadic (a, b)" shows "unit_dyadic ((a + b) / 2, b)"
proof -
  from assms obtain l k where lk: "a = of_int l / 2 ^ k" "b = of_int (l + 1) / 2 ^ k"
    by (auto simp: unit_dyadic_def)
  show ?thesis unfolding unit_dyadic_def
  proof (intro exI conjI)
    show "fst ((a + b) / 2, b) = of_int (2 * l + 1) / 2 ^ (k + 1)"
      using lk by (simp add: field_simps)
    show "snd ((a + b) / 2, b) = of_int (2 * l + 1 + 1) / 2 ^ (k + 1)"
      using lk by (simp add: field_simps)
  qed
qed

text \<open>The worklist node invariant (carried_repr + unit_dyadic for every entry) is preserved by
  @{const carried_step}: the children get carried_repr from B1/B2 (side-conditions discharged by
  @{thm unit_dyadic_less}/@{thm unit_dyadic_odd_nw}) and unit_dyadic from the bisection lemmas.\<close>
definition carried_node :: "gmp_poly \<Rightarrow> (rat \<times> rat) \<times> gmp_poly \<Rightarrow> bool" where
"carried_node P e \<longleftrightarrow> carried_repr P (fst (fst e)) (snd (fst e)) (snd e) \<and> unit_dyadic (fst e)"

lemma carried_step_preserves_node:
  assumes lenP: "0 < length P"
    and inv: "\<forall>e \<in> set todo. carried_node P e"
  shows "\<forall>e \<in> set (fst (carried_step P todo acc)). carried_node P e"
proof (cases todo)
  case Nil thus ?thesis by (simp add: carried_step_def)
next
  case (Cons h rest)
  obtain a b Q where h: "h = ((a, b), Q)" by (cases h) auto
  have head: "carried_repr P a b Q" "unit_dyadic (a, b)"
    using inv Cons h by (auto simp: carried_node_def)
  have rest_inv: "\<forall>e \<in> set rest. carried_node P e" using inv Cons by auto
  have ab: "a < b" using head(2) by (rule unit_dyadic_less)
  have onw: "odd (fst (quotient_of ((b - a) * of_int (snd (quotient_of a)))))"
    using head(2) by (rule unit_dyadic_odd_nw)
  show ?thesis
  proof (cases "carried_descartes_count Q = 0")
    case True thus ?thesis using rest_inv Cons h by (simp add: carried_step_def)
  next
    case v0: False
    show ?thesis
    proof (cases "carried_descartes_count Q = 1")
      case True thus ?thesis using rest_inv Cons h by (simp add: carried_step_def)
    next
      case v1: False
      have cl: "carried_node P ((a, (a + b) / 2), carried_left Q)"
        unfolding carried_node_def using head(2)
        by (simp add: carried_step_preserves_repr(1)[OF head(1) lenP ab onw]
            unit_dyadic_bisect_left)
      have cr: "carried_node P (((a + b) / 2, b), carried_right Q)"
        unfolding carried_node_def using head(2)
        by (simp add: carried_step_preserves_repr(2)[OF head(1) lenP ab onw]
            unit_dyadic_bisect_right)
      have fst_eq: "fst (carried_step P todo acc)
          = rest @ [((a, (a + b) / 2), carried_left Q),
                    (((a + b) / 2, b), carried_right Q)]"
        using v0 v1 Cons h by (simp add: carried_step_def Let_def)
      show ?thesis unfolding fst_eq using rest_inv cl cr by auto
    qed
  qed
qed

text \<open>The functional carried worklist driver: iterate @{const carried_step} until the todo is
  empty, returning the accumulator. Mirrors @{const rational_queue_main_int} but carrying the
  polynomials.\<close>
partial_function (tailrec) carried_main ::
  "gmp_poly \<Rightarrow> ((rat \<times> rat) \<times> gmp_poly) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list" where
"carried_main P todo acc =
  (case todo of [] \<Rightarrow> acc
   | _ \<Rightarrow> (let (todo', acc') = carried_step P todo acc in carried_main P todo' acc'))"

text \<open>The lift: the functional carried driver computes the same accumulator as the endpoint
  worklist (projected to intervals), under the node invariant. Proven by the endpoint domain
  @{thm rational_queue_fun_int.pinduct}, using @{thm carried_step_corresp} (steps match),
  @{thm carried_step_preserves_node} (invariant preserved), and B3 (the count).\<close>
lemma carried_main_eq_fun_int:
  "rational_queue_fun_int_dom (P, ivs, acc) \<Longrightarrow>
    \<forall>todo. 0 < length P \<and> map fst todo = ivs \<and> (\<forall>e\<in>set todo. carried_node P e) \<longrightarrow>
      carried_main P todo acc = rational_queue_fun_int P ivs acc"
proof (induction P ivs acc rule: rational_queue_fun_int.pinduct)
  case (1 P ivs acc)
  show ?case
  proof (intro allI impI, elim conjE)
    fix todo assume lenP: "0 < length P" and mt: "map fst todo = ivs"
      and ni: "\<forall>e\<in>set todo. carried_node P e"
    show "carried_main P todo acc = rational_queue_fun_int P ivs acc"
    proof (cases todo)
      case Nil
      hence "ivs = []" using mt by simp
      thus ?thesis using Nil "1.hyps"
        by (simp add: carried_main.simps rational_queue_fun_int.psimps)
    next
      case (Cons hh crest)
      obtain a b Q where hh: "hh = ((a, b), Q)" by (cases hh) auto
      have ivs_eq: "ivs = (a, b) # map fst crest" using mt Cons hh by simp
      have head: "carried_repr P a b Q" using ni Cons hh by (auto simp: carried_node_def)
      have count: "carried_descartes_count Q = descartes_list_int a b P"
        using head by (rule carried_repr_count)
      have ni_rest: "\<forall>e\<in>set crest. carried_node P e" using ni Cons by auto
      have dom_cons: "rational_queue_fun_int_dom (P, (a, b) # map fst crest, acc)"
        using "1.hyps"(1) ivs_eq by simp
      have cm: "carried_main P todo acc
          = carried_main P (fst (carried_step P todo acc)) (snd (carried_step P todo acc))"
        using Cons by (subst carried_main.simps) (simp add: split_def Let_def)
      let ?m = "(a + b) / 2"
      let ?accm = "acc @ (if poly (map_poly rat_of_int (Poly P)) ?m = 0 then [(?m, ?m)] else [])"
      note ihinst = "1.IH"[of "(a, b)" "map fst crest" a b "descartes_list_int a b P"]
      show ?thesis
      proof (cases "descartes_list_int a b P = 0")
        case v0: True
        have step: "carried_step P todo acc = (crest, acc)"
          using Cons hh count v0 by (simp add: carried_step_def)
        have ih: "\<forall>td. 0 < length P \<and> map fst td = map fst crest \<and> (\<forall>e\<in>set td. carried_node P e) \<longrightarrow>
            carried_main P td acc = rational_queue_fun_int P (map fst crest) acc"
          using ihinst(1) ivs_eq v0 by blast
        have fih: "carried_main P crest acc = rational_queue_fun_int P (map fst crest) acc"
          using ih lenP ni_rest by blast
        have fu: "rational_queue_fun_int P ivs acc = rational_queue_fun_int P (map fst crest) acc"
          using dom_cons v0 ivs_eq
          by (subst rational_queue_fun_int.psimps) (auto split: list.splits prod.splits)
        show ?thesis using cm step fih fu by simp
      next
        case v0: False
        show ?thesis
        proof (cases "descartes_list_int a b P = 1")
          case v1: True
          have step: "carried_step P todo acc = (crest, acc @ [(a, b)])"
            using Cons hh count v0 v1 by (simp add: carried_step_def)
          have ih: "\<forall>td. 0 < length P \<and> map fst td = map fst crest \<and> (\<forall>e\<in>set td. carried_node P e) \<longrightarrow>
              carried_main P td (acc @ [(a, b)]) = rational_queue_fun_int P (map fst crest) (acc @ [(a, b)])"
            using ihinst(2) ivs_eq v0 v1 by blast
          have fih: "carried_main P crest (acc @ [(a, b)]) = rational_queue_fun_int P (map fst crest) (acc @ [(a, b)])"
            using ih lenP ni_rest by blast
          have fu: "rational_queue_fun_int P ivs acc
              = rational_queue_fun_int P (map fst crest) (acc @ [(a, b)])"
            using dom_cons v0 v1 ivs_eq
            by (subst rational_queue_fun_int.psimps) (auto split: list.splits prod.splits)
          show ?thesis using cm step fih fu by simp
        next
          case v1: False
          let ?todo' = "crest @ [((a, ?m), carried_left Q), ((?m, b), carried_right Q)]"
          have step: "carried_step P todo acc = (?todo', ?accm)"
            using Cons hh count v0 v1 by (simp add: carried_step_def Let_def)
          have mt': "map fst ?todo' = map fst crest @ [(a, ?m), (?m, b)]" by simp
          have ni': "\<forall>e\<in>set ?todo'. carried_node P e"
          proof -
            have "\<forall>e\<in>set (fst (carried_step P todo acc)). carried_node P e"
              using lenP ni by (rule carried_step_preserves_node)
            thus ?thesis using step by simp
          qed
          have ih: "\<forall>td. 0 < length P \<and> map fst td = map fst crest @ [(a, ?m), (?m, b)] \<and> (\<forall>e\<in>set td. carried_node P e) \<longrightarrow>
              carried_main P td ?accm = rational_queue_fun_int P (map fst crest @ [(a, ?m), (?m, b)]) ?accm"
            using "1.IH"(3)[of "(a, b)" "map fst crest" a b "descartes_list_int a b P" ?m]
              ivs_eq v0 v1 by blast
          have fih: "carried_main P ?todo' ?accm
              = rational_queue_fun_int P (map fst crest @ [(a, ?m), (?m, b)]) ?accm"
            using ih lenP mt' ni' by blast
          have fu: "rational_queue_fun_int P ivs acc
              = rational_queue_fun_int P (map fst crest @ [(a, ?m), (?m, b)]) ?accm"
            using dom_cons v0 v1 ivs_eq
            by (subst rational_queue_fun_int.psimps)
              (auto simp: Let_def split: list.splits prod.splits)
          show ?thesis using cm step fih fu by simp
        qed
      qed
    qed
  qed
qed

lemma carried_main_eq:
  assumes "rational_queue_fun_int_dom (P, map fst todo, acc)" and "0 < length P"
    and "\<forall>e\<in>set todo. carried_node P e"
  shows "carried_main P todo acc = rational_queue_main_int P (map fst todo) acc"
proof -
  have "carried_main P todo acc = rational_queue_fun_int P (map fst todo) acc"
    using carried_main_eq_fun_int[OF assms(1)] assms(2,3) by blast
  thus ?thesis using rational_queue_main_int_eq_fun_int[OF assms(1)] by simp
qed

text \<open>Capstone: the functional carried driver started from a single unit-dyadic root node
  @{term "((a, b), Q)"} (with @{term "carried_repr P a b Q"}) computes exactly the isolating
  intervals @{const dsc_int} of @{term "Poly P"} on @{term "[a, b]"} (as multisets). Chains the
  lift with the endpoint @{thm rational_queue_main_int_mset_dsc_int}.\<close>
corollary carried_main_mset_dsc_int:
  fixes \<delta> :: real
  assumes "\<delta> > 0"
    and "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and "dsc_dom (degree (Poly P), of_rat a, of_rat b, map_poly of_int (Poly P) :: real poly)"
    and "Poly P \<noteq> 0" and "coeffs (Poly P) = P" and "a < b"
    and "0 < length P" and "carried_repr P a b Q" and "unit_dyadic (a, b)"
  shows "mset (carried_main P [((a, b), Q)] []) = mset (dsc_int a b (Poly P))"
proof -
  have dom: "rational_queue_fun_int_dom (P, map fst [((a, b), Q)], [])"
    by (rule rational_queue_fun_int_domI[OF assms(1) _ assms(2)]) (simp add: assms(6))
  have ni: "\<forall>e\<in>set [((a, b), Q)]. carried_node P e"
    using assms(8,9) by (simp add: carried_node_def)
  have "carried_main P [((a, b), Q)] [] = rational_queue_main_int P [(a, b)] []"
    using carried_main_eq[OF dom assms(7) ni] by simp
  thus ?thesis
    using rational_queue_main_int_mset_dsc_int[OF assms(1) assms(2) assms(3)
      assms(4) assms(5) assms(6)] by simp
qed

end
