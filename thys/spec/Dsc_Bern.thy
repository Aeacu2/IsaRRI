theory Dsc_Bern
  imports Three_Circles.Bernstein
    Budan_Fourier.Descartes_Roots_Test
    List_Changes
begin

text \<open>The Bernstein-coefficient bridge: Descartes' rule in the Bernstein basis.
  Layer: FUNCTIONAL SPEC.
  Main exports: \<open>reciprocal_shift_rescale_eq_fcompose\<close> and the \<open>Bernstein_changes\<close> transport facts.\<close>

lemma reciprocal_shift_rescale_eq_fcompose:
  fixes P :: "real poly" and a b :: real
  defines "p \<equiv> degree P"
  defines "R \<equiv> P \<circ>\<^sub>p [:b,1:] \<circ>\<^sub>p [:0, a-b:]"
  shows "(reciprocal_poly p R) \<circ>\<^sub>p [:1,1:] = fcompose P [:a,b:] [:1,1:]"
proof -
  let ?L = "(reciprocal_poly p R) \<circ>\<^sub>p [:1,1:]"
  let ?M = "fcompose P [:a,b:] [:1,1:]"
  let ?D = "?L - ?M"

  have eval_eq: "\<And>x. x \<noteq> -1 \<Longrightarrow> poly ?L x = poly ?M x"
    proof -
      fix x :: real
      assume hx: "x \<noteq> -1"

      let ?den = "poly [:1,1:] x"   
      have hden: "?den \<noteq> 0"
        using hx by simp
    
      have L_eval0: "poly ?L x = poly (reciprocal_poly p R) ?den"
        by (simp add: poly_pcompose)
    
      have L_eval1: "poly (reciprocal_poly p R) ?den = ?den^p * poly R (inverse ?den)"
        using poly_reciprocal hden
        by (smt (verit, del_insts) One_nat_def R_def degree_pCons_eq_if degree_pcompose diff_is_0_eq diff_zero
            le_eq_less_or_eq mult.right_neutral mult_zero_right not_less p_def)
    
      have R_at_inv: "poly R (inverse ?den) = poly P (b + (a - b) * inverse ?den)"
        unfolding R_def
        by (simp add: poly_pcompose algebra_simps)
    
      have frac_id: "b + (a - b) * inverse ?den = (a + b*x) / ?den"
      proof -
        have den_simp: "?den = 1 + x" by simp
        have hden': "1 + x \<noteq> 0"
          using hx by simp
        show ?thesis
          unfolding den_simp
          using hden'
          by (simp add: field_simps)
      qed
    
      have L_eval:
        "poly ?L x = ?den^p * poly P ((a + b*x) / ?den)"
        using L_eval0 L_eval1 R_at_inv frac_id
        by simp

      have M_eval0:
        "poly ?M x =
           poly P (poly [:a,b:] x / poly [:1,1:] x) * (poly [:1,1:] x) ^ degree P"
        using poly_fcompose[OF hden]
        by simp
    
      have M_eval:
        "poly ?M x = poly P ((a + b*x) / ?den) * ?den^p"
        unfolding p_def
        using M_eval0
        by (simp add: algebra_simps)

      show "poly ?L x = poly ?M x"
        using L_eval M_eval
        by simp
    qed

  have sub_roots: "range (of_nat :: nat \<Rightarrow> real) \<subseteq> {x. poly ?D x = 0}"
  proof
    fix x :: real
    assume "x \<in> range (of_nat :: nat \<Rightarrow> real)"
    then obtain n :: nat where x_def: "x = of_nat n" by blast
    have xne: "x \<noteq> -1"
      by (simp add: x_def)
    show "x \<in> {x. poly ?D x = 0}"
      using eval_eq[OF xne] unfolding x_def by simp
  qed

  have inf_sub: "infinite (range (of_nat :: nat \<Rightarrow> real))"
    by (rule range_inj_infinite) simp

  have inf_roots: "infinite {x. poly ?D x = 0}"
    using inf_sub sub_roots finite_subset by blast

  have D0: "?D = 0"
    using inf_roots poly_roots_finite[of ?D] by blast

  from D0 show ?thesis by simp
qed

lemma changes_Bernstein_coeffs_eq_changes_coeffs:
  fixes P :: "real poly" and a b :: real
  defines "p \<equiv> degree P"
  defines "R \<equiv> P \<circ>\<^sub>p [:a,1:] \<circ>\<^sub>p [:0, b-a:]"
  shows "changes (Bernstein_coeffs p a b P)
       = changes (coeffs ((reciprocal_poly p R) \<circ>\<^sub>p [:1,1:]))"
proof -
  have coeffs_id:
    "Bernstein_coeffs p a b P = Bernstein_coeffs_01 p R"
    unfolding Bernstein_coeffs_def Bernstein_coeffs_01_def R_def
    by (simp add: pcompose_assoc)

  have degR_le: "degree R \<le> p"
    unfolding R_def p_def
    by (metis (no_types, lifting) One_nat_def degree_pCons_eq_if degree_pcompose le_eq_less_or_eq
        mult.right_neutral mult_zero_right zero_le)
    
  have B01_is_changes:
    "Bernstein_changes_01 p R = changes (Bernstein_coeffs_01 p R)"
    unfolding Bernstein_changes_01_def
    using changes_nonneg[of "Bernstein_coeffs_01 p R"] by simp

  have "changes (Bernstein_coeffs_01 p R)
      = changes (coeffs ((reciprocal_poly p R) \<circ>\<^sub>p [:1,1:]))"
    using Bernstein_changes_01_eq_changes[OF degR_le]
    unfolding B01_is_changes
    by simp

  thus ?thesis
    using coeffs_id by simp
qed

lemma descartes_roots_test_eq_Bernstein_changes:
  fixes P :: "real poly" and a b :: real
  defines "p \<equiv> degree P"
  shows "descartes_roots_test b a P = Bernstein_changes p a b P"
  by (simp add: Bernstein_changes_def changes_Bernstein_coeffs_eq_changes_coeffs
      descartes_roots_test_def p_def reciprocal_shift_rescale_eq_fcompose)

lemma degree_fcompose_linear_le:
  fixes p :: "'a::field poly" and q1 q2 :: "'a poly"
  assumes dq1: "degree q1 \<le> 1" and dq2: "degree q2 \<le> 1"
  shows   "degree (fcompose p q1 q2) \<le> degree p"
proof (induction p)
  case 0
  then show ?case by simp
next
  case (pCons a p)
  let ?P = "pCons a p"
  have IH: "degree (fcompose p q1 q2) \<le> degree p" using pCons by simp

  have deg_q2pow: "degree (q2 ^ degree ?P) \<le> degree ?P"
    by (metis degree_power_le dq2 le_antisym less_one linorder_not_le mult_1 mult_zero_left
        zero_le)

  have deg_term1:
    "degree (smult a (q2 ^ degree ?P)) \<le> degree ?P"
    by (meson deg_q2pow degree_smult_le dual_order.trans)

  have deg_term2:
    "degree (q1 * fcompose p q1 q2) \<le> degree ?P"
  proof (cases "p = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have dp: "degree ?P = Suc (degree p)"
      using False by simp
    have "degree (q1 * fcompose p q1 q2)
          \<le> degree q1 + degree (fcompose p q1 q2)"
      by (simp add: degree_mult_le)
    also have "\<dots> \<le> 1 + degree p"
      using dq1 IH by linarith
    also have "\<dots> = degree ?P"
      using dp by simp
    finally show ?thesis .
  qed

  have "fcompose ?P q1 q2
        = smult a (q2^(degree ?P)) + q1 * fcompose p q1 q2"
    by (simp add: fcompose_pCons)
  then have "degree (fcompose ?P q1 q2)
             \<le> max (degree (smult a (q2^(degree ?P))))
                   (degree (q1 * fcompose p q1 q2))"
    by (simp add: degree_add_le)
  also have "\<dots> \<le> degree ?P"
    using deg_term1 deg_term2 by simp
  finally show ?case by simp
qed

lemma coeff_one_plus_X_pow_top:
  fixes n :: nat
  shows "coeff (([:(1::'a::field), 1:] )^n) n = 1"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?q = "([:(1::'a), 1:])"
  have deg_le: "degree (?q^n) \<le> n"
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc m)
    have "degree (?q^(Suc m)) = degree (?q^m * ?q)" by simp
    also have "... \<le> degree (?q^m) + degree ?q"
      using degree_mult_le by blast
    also have "... \<le> m + 1"
      using Suc.IH by simp
    finally show ?case by simp
  qed

  have coeff_suc0: "coeff (?q^n) (Suc n) = 0"
    using deg_le by (simp add: coeff_eq_0)

  have "coeff (?q^(Suc n)) (Suc n) = coeff (?q^n * ?q) (Suc n)"
    by simp
  also have "... = (\<Sum>i\<le>Suc n. coeff (?q^n) i * coeff ?q (Suc n - i))"
    using coeff_mult by blast
  also have "... =
      coeff (?q^n) n * coeff ?q 1 + coeff (?q^n) (Suc n) * coeff ?q 0"
  proof -
    have q0: "coeff ?q 0 = (1::'a)" by simp
    have q1: "coeff ?q 1 = (1::'a)" by simp
    have qk: "\<And>k. 2 \<le> k \<Longrightarrow> coeff ?q k = 0"
      by (simp add: coeff_eq_0)

    let ?f = "\<lambda>i. coeff (?q^n) i * coeff ?q (Suc n - i)"
    have fin: "finite {..Suc n}" by simp
    have decomp: "{..Suc n} = ({n, Suc n} \<union> ({..Suc n} - {n, Suc n}))" by auto
    have disj: "{n, Suc n} \<inter> ({..Suc n} - {n, Suc n}) = {}" by auto

    have split:
      "(\<Sum>i\<le>Suc n. ?f i)
       = (\<Sum>i\<in>{n, Suc n}. ?f i) + (\<Sum>i\<in>({..Suc n} - {n, Suc n}). ?f i)"
      using fin decomp disj
      by (metis (mono_tags, lifting) finite_Un sum.union_disjoint)

    have rest0: "(\<Sum>i\<in>({..Suc n} - {n, Suc n}). ?f i) = 0"
    proof -
      have "\<And>i. i \<in> ({..Suc n} - {n, Suc n}) \<Longrightarrow> ?f i = 0"
      proof -
        fix i assume hi: "i \<in> ({..Suc n} - {n, Suc n})"
        then have ile: "i \<le> Suc n" by auto
        from hi have ineq: "i \<noteq> n" "i \<noteq> Suc n" by auto
        from ile ineq have "2 \<le> Suc n - i" by linarith
        then have "coeff ?q (Suc n - i) = 0" using qk by blast
        thus "?f i = 0" by simp
      qed
      thus ?thesis by (simp add: sum.neutral)
    qed

    have "(\<Sum>i\<le>Suc n. ?f i) = (\<Sum>i\<in>{n, Suc n}. ?f i)"
      using split rest0 by simp
    also have "... = ?f n + ?f (Suc n)" by simp
    finally show ?thesis
      by (simp add: q0 q1)
  qed
  also have "... = coeff (?q^n) n"
    by (simp add: coeff_suc0)
  also have "... = 1"
    using Suc.IH by simp
  finally show ?case .
qed

lemma coeff_linear_mult_top:
  fixes F :: "'a::field poly" and a b :: 'a and n :: nat
  assumes degF: "degree F \<le> n"
  shows "coeff ([:a,b:] * F) (Suc n) = b * coeff F n"
proof -
  have "coeff ([:a,b:] * F) (Suc n)
        = (\<Sum>i\<le>Suc n. coeff [:a,b:] i * coeff F (Suc n - i))"
    using coeff_mult by blast
  also have "... =
      coeff [:a,b:] 0 * coeff F (Suc n) + coeff [:a,b:] 1 * coeff F n"
  proof -
    have lin2: "\<And>k. 2 \<le> k \<Longrightarrow> coeff [:a,b:] k = 0"
      by (simp add: coeff_eq_0)

    let ?f = "\<lambda>i. coeff [:a,b:] i * coeff F (Suc n - i)"
    have fin: "finite {..Suc n}" by simp
    have decomp: "{..Suc n} = ({0,1} \<union> ({..Suc n} - {0,1}))" by auto
    have disj: "{0,1} \<inter> ({..Suc n} - {0,1}) = {}" by auto

    have split:
      "(\<Sum>i\<le>Suc n. ?f i)
       = (\<Sum>i\<in>{0,1}. ?f i) + (\<Sum>i\<in>({..Suc n} - {0,1}). ?f i)"
      using fin decomp disj
      by (metis (no_types, lifting) sum_Un_eq)

    have rest0: "(\<Sum>i\<in>({..Suc n} - {0,1}). ?f i) = 0"
    proof -
      have "\<And>i. i \<in> ({..Suc n} - {0,1}) \<Longrightarrow> ?f i = 0"
      proof -
        fix i assume hi: "i \<in> ({..Suc n} - {0,1})"
        then have "2 \<le> i" by auto
        hence "coeff [:a,b:] i = 0" using lin2 by blast
        thus "?f i = 0" by simp
      qed
      thus ?thesis by (simp add: sum.neutral)
    qed

    have "(\<Sum>i\<le>Suc n. ?f i) = (\<Sum>i\<in>{0,1}. ?f i)"
      using split rest0 by simp
    also have "... = ?f 0 + ?f 1" by simp
    finally show ?thesis by simp
  qed
  also have "coeff F (Suc n) = 0"
    using degF by (simp add: coeff_eq_0)
  finally show ?thesis by simp
qed


lemma coeff_fcompose_ab_top:
  fixes p :: "'a::field poly" and a b :: 'a
  shows "coeff (fcompose p [:a,b:] [:1,1:]) (degree p) = poly p b"
proof (induction p)
  case 0
  show ?case
  proof -
    have "coeff (fcompose (0::'a poly) [:a,b:] [:1,1:]) (degree (0::'a poly))
          = coeff (0::'a poly) (degree (0::'a poly))"
      by simp
    also have "... = coeff (0::'a poly) 0"
      by simp
    also have "... = 0"
      by simp
    finally have LHS:
      "coeff (fcompose (0::'a poly) [:a,b:] [:1,1:]) (degree (0::'a poly)) = 0" .

    have RHS: "poly (0::'a poly) b = 0"
      by simp

    show ?thesis
      using LHS RHS by simp
  qed
next
  case (pCons c p)
  show ?case
  proof (cases "p = 0")
    case True
    have "pCons c p = [:c:]" using True by simp
    thus ?thesis
      by simp
  next
    case False
    let ?q1 = "[:a,b:]"
    let ?q2 = "[:(1::'a),1:]"
    let ?Fp = "fcompose p ?q1 ?q2"
    let ?P  = "pCons c p"
    let ?dp = "degree p"
    let ?dP = "degree ?P"
  
    have dP: "?dP = Suc ?dp"
      using False by simp

    have degFp_le: "degree ?Fp \<le> ?dp"
    proof (induction p)
      case 0
      then show ?case by simp
    next
      case (pCons u r)
      show ?case
      proof (cases "r = 0")
        case True
        then show ?thesis by simp
      next
        case False
        let ?R = "pCons u r"
        have dr: "degree ?R = Suc (degree r)" using False by simp
  
        have "fcompose ?R ?q1 ?q2
              = smult u (?q2 ^ degree ?R) + ?q1 * fcompose r ?q1 ?q2"
          by (simp add: fcompose_pCons)
        then have "degree (fcompose ?R ?q1 ?q2)
                   \<le> max (degree (smult u (?q2 ^ degree ?R)))
                         (degree (?q1 * fcompose r ?q1 ?q2))"
          by (simp add: degree_add_le)
        also have "degree (smult u (?q2 ^ degree ?R)) \<le> degree ?R"
        proof -
          have "degree (?q2 ^ degree ?R) \<le> degree ?R"
          proof -
            have dq2: "degree ?q2 = 1" by simp
            have "degree (?q2 ^ degree ?R) \<le> degree ?R * degree ?q2"
            proof (induction "degree ?R")
              case 0
              then show ?case by simp
            next
              case (Suc n)
              have "degree (?q2 ^ Suc n) = degree (?q2^n * ?q2)" by simp
              also have "... \<le> degree (?q2^n) + degree ?q2"
                using degree_mult_le by blast
              also have "... \<le> n * degree ?q2 + degree ?q2"
                by (simp add: degree_linear_power)
              also have "... = (Suc n) * degree ?q2" by simp
              finally show ?case
                using Suc.hyps(2) by argo
            qed
            thus ?thesis using dq2 
              by simp
          qed
          thus ?thesis
            by auto
        qed
        also have "degree (?q1 * fcompose r ?q1 ?q2) \<le> degree ?R"
        proof -
          have dq1: "degree ?q1 \<le> 1" by simp
          have "degree (?q1 * fcompose r ?q1 ?q2)
                \<le> degree ?q1 + degree (fcompose r ?q1 ?q2)"
            using degree_mult_le by blast
          also have "... \<le> 1 + degree r"
            using dq1 pCons.IH by linarith
          also have "... = degree ?R"
            using dr by simp
          finally show ?thesis .
        qed
        show ?thesis 
          using calculation degree_smult_le dual_order.trans
          using \<open>degree ([:a, b:] * fcompose r [:a, b:] [:1, 1:]) \<le> degree (pCons u r)\<close>
          by fastforce
      qed
    qed
  
    have top_pow: "coeff (?q2 ^ ?dP) ?dP = 1"
      using coeff_one_plus_X_pow_top[of ?dP] by simp
  
    have top_mult: "coeff (?q1 * ?Fp) ?dP = b * coeff ?Fp ?dp"
      by (metis One_nat_def coeff_linear_mult_top dP degree_fcompose_linear_le degree_pCons_eq_if
          degree_pCons_le)
    have step:
      "fcompose ?P ?q1 ?q2 = smult c (?q2 ^ ?dP) + ?q1 * ?Fp"
      by (simp add: fcompose_pCons)
  
    have "coeff (fcompose ?P ?q1 ?q2) ?dP
          = coeff (smult c (?q2 ^ ?dP) + ?q1 * ?Fp) ?dP"
      using step by simp
    also have "... =
        coeff (smult c (?q2 ^ ?dP)) ?dP + coeff (?q1 * ?Fp) ?dP"
      by simp
    also have "... = c * coeff (?q2 ^ ?dP) ?dP + coeff (?q1 * ?Fp) ?dP"
      by simp
    also have "... = c * 1 + b * coeff ?Fp ?dp"
      using top_pow top_mult by simp
    also have "... = c + b * poly p b"
      using pCons.IH 
      by simp
    also have "... = poly (pCons c p) b"
      by (simp add: algebra_simps)
    finally show ?thesis
      using dP by simp
  qed
qed

lemma fcompose_swap_reciprocal:
  fixes p :: "real poly" and a b :: real
  shows "fcompose p [:b,a:] [:1,1:]
       = reciprocal_poly (degree p) (fcompose p [:a,b:] [:1,1:])"
proof -
  let ?d = "degree p"
  let ?F = "fcompose p [:a,b:] [:1,1:]"
  let ?G = "fcompose p [:b,a:] [:1,1:]"

  have degF: "degree ?F \<le> ?d"
    by (rule degree_fcompose_linear_le) simp_all

  show ?thesis
  proof (rule poly_eq_by_eval)
    fix x :: real
    show "poly ?G x = poly (reciprocal_poly ?d ?F) x"
    proof (cases "x = 0")
      case True

      have rhs0: "poly (reciprocal_poly ?d ?F) 0 = coeff ?F ?d"
        using degF
        by (simp add: poly_0_coeff_0 coeff_reciprocal)

      have top: "coeff ?F ?d = poly p b"
        using coeff_fcompose_ab_top[of p a b] by simp

      have lhs0: "poly ?G 0 = poly p b"
        by (simp add: poly_fcompose)  
      show ?thesis
        using True lhs0 rhs0 top by simp
    next
      case False
      have x0: "x \<noteq> 0" using False .

      have rhs_rec:
        "poly (reciprocal_poly ?d ?F) x = x^?d * poly ?F (inverse x)"
        using poly_reciprocal[OF degF x0] by simp

      show ?thesis
      proof (cases "x = -1")
        case True

        have lhs_m1:
          "poly ?G x = (poly [:b,a:] x) ^ ?d * lead_coeff p"
          using True by (simp add: poly_fcompose_0_denominator)

        have rhs_m1:
          "poly (reciprocal_poly ?d ?F) x
           = x^?d * ((poly [:a,b:] (inverse x))^?d * lead_coeff p)"
        proof -
          have "poly (reciprocal_poly ?d ?F) x = x^?d * poly ?F (inverse x)"
            using rhs_rec by simp
          also have "poly ?F (inverse x) = (poly [:a,b:] (inverse x))^?d * lead_coeff p"
            using True by (simp add: poly_fcompose_0_denominator)
          finally show ?thesis .
        qed

        have inv_m1: "inverse x = -1"
          using True by simp

        have poly_lin1: "poly [:b,a:] x = b - a"
          using True by simp
        have poly_lin2: "poly [:a,b:] (inverse x) = a - b"
          using True inv_m1 by simp

        have pow_id:
          "x^?d * (a - b)^?d = (b - a)^?d"
        proof -
          have ab: "a - b = - (b - a)" by simp
          have "x^?d * (a - b)^?d = (-1)^?d * (-(b-a))^?d"
            using True ab by simp
          also have "... = (-1)^?d * ((-1) * (b-a))^?d"
            by simp
          also have "... = (-1)^?d * ((-1)^?d * (b-a)^?d)"
            using pow_mult_same by presburger
          also have "... = ((-1)^?d * (-1)^?d) * (b-a)^?d"
            by (simp add: algebra_simps)
          also have "... = (-1)^(?d + ?d) * (b-a)^?d"
            by (simp add: power_add)
          also have "... = (-1)^(2*?d) * (b-a)^?d"
            by simp
          also have "... = 1 * (b-a)^?d"
            by simp
          finally show ?thesis by simp
        qed

        show ?thesis
          using lhs_m1 rhs_m1 True inv_m1 poly_lin1 poly_lin2 pow_id
          by (simp add: algebra_simps)
      next
        case False
        have xm1: "x \<noteq> -1" using False .
        have denx: "poly [:1,1:] x \<noteq> 0"
          using xm1 by simp

        have deninv: "poly [:1,1:] (inverse x) \<noteq> 0"
        proof
          assume "poly [:1,1:] (inverse x) = 0"
          then have "inverse x = -1" by simp
          then have "x = -1" using x0 
            by (simp add: divide_eq_minus_1_iff inverse_eq_divide)
          with xm1 show False by contradiction
        qed

        have lhs:
          "poly ?G x
           = poly p (poly [:b,a:] x / poly [:1,1:] x) * (poly [:1,1:] x)^?d"
          using denx by (simp add: poly_fcompose)

        have F_inv:
          "poly ?F (inverse x)
           = poly p (poly [:a,b:] (inverse x) / poly [:1,1:] (inverse x))
             * (poly [:1,1:] (inverse x))^?d"
          using deninv by (simp add: poly_fcompose)

        have frac_id:
          "poly [:b,a:] x / poly [:1,1:] x
           = poly [:a,b:] (inverse x) / poly [:1,1:] (inverse x)"
        proof -
          have hx0: "x \<noteq> 0" using x0 .
          have hx1: "poly [:1,1:] x \<noteq> 0"
            using xm1 by simp 
          have hix1: "poly [:1,1:] (inverse x) \<noteq> 0"
          proof
            assume h : "poly [:1,1:] (inverse x) = 0"
            hence "1 + inverse x = 0" by simp
            hence "inverse x = -1" by simp
            hence "x = -1" using hx0 deninv h by blast
            with xm1 show False by simp
          qed
        
          have
            "(poly [:b,a:] x) / (poly [:1,1:] x)
             = (poly [:a,b:] (inverse x)) / (poly [:1,1:] (inverse x))"
          proof -
            have
              "(b + a * x) / (1 + x) = (a + b * inverse x) / (1 + inverse x)"
              using hx0 xm1
            proof -
              have hx1': "1 + x \<noteq> 0" using xm1 by simp
              have hix1': "1 + inverse x \<noteq> 0"
              proof
                assume "1 + inverse x = 0"
                then have "inverse x = -1" by simp
                then have "x = -1" using hx0
                  by (simp add: divide_eq_minus_1_iff inverse_eq_divide)
                with xm1 show False by simp
              qed
        
              have eq1: "(b + a * x) / (1 + x) = (a * x + b) / (x + 1)"
                by (simp add: algebra_simps)
            
              have eq2: "(a + b * inverse x) / (1 + inverse x) = (a * x + b) / (x + 1)"
            proof -
              have cross:
                "(a + b * inverse x) * (x + 1) = (a * x + b) * (1 + inverse x)"
                using hx0
                by (simp add: algebra_simps)

              have step1:
                "(a + b * inverse x) = ((a * x + b) / (x + 1)) * (1 + inverse x)"
              proof -
                have "(a + b * inverse x) * (x + 1) / (x + 1)
                      = (a * x + b) * (1 + inverse x) / (x + 1)"
                  using cross by simp
                then have "(a + b * inverse x) = (a * x + b) * (1 + inverse x) / (x + 1)"
                  using hx1' by simp
                also have "... = ((a * x + b) / (x + 1)) * (1 + inverse x)"
                  by (simp add: algebra_simps)
                finally show ?thesis .
              qed

              have "(a + b * inverse x) / (1 + inverse x) = (a * x + b) / (x + 1)"
                using step1 hix1' by simp
              thus ?thesis .
            qed

            
              show ?thesis
                using eq1 eq2 by simp      
            qed
            thus ?thesis
              by (simp add: mult.commute)
          qed
          thus ?thesis .
        qed


        have scale_id:
          "x^?d * (poly [:1,1:] (inverse x))^?d = (poly [:1,1:] x)^?d"
          using x0 xm1
          by (simp add: field_simps)

        have rhs:
          "poly (reciprocal_poly ?d ?F) x
           = x^?d
             * (poly p (poly [:a,b:] (inverse x) / poly [:1,1:] (inverse x))
                * (poly [:1,1:] (inverse x))^?d)"
          using rhs_rec F_inv by simp

        show ?thesis
          unfolding lhs rhs
          using frac_id scale_id
          by (simp add: algebra_simps)
      qed
    qed
  qed
qed

lemma changes_coeffs_Poly_eq_changes:
  fixes xs :: "real list"
  shows "changes (coeffs (Poly xs)) = changes xs"
  by (metis changes_eq_sign_changes sign_changes_coeff_sign_changes)

lemma changes_coeffs_reciprocal:
  fixes P :: "real poly" and p :: nat
  assumes hP: "degree P \<le> p"
  shows "changes (coeffs (reciprocal_poly p P)) = changes (coeffs P)"
proof (cases "P = 0")
  case True
  then show ?thesis
    by (simp add: reciprocal_0)
next
  case False
  let ?xs = "coeffs P"

  have len_xs: "length ?xs = degree P + 1"
    using False by (simp add: length_coeffs)

  let ?k = "p - degree P"

  have rec_as_Poly:
    "reciprocal_poly p P = Poly (rev (?xs @ replicate ?k 0))"
    by (simp add: reciprocal_poly_def)

  have "changes (coeffs (reciprocal_poly p P))
        = changes (coeffs (Poly (rev (?xs @ replicate ?k 0))))"
    by (simp add: rec_as_Poly)
  also have "... = changes (rev (?xs @ replicate ?k 0))"
    using changes_coeffs_Poly_eq_changes by blast
  also have "... = changes (replicate ?k 0 @ rev ?xs)"
    by simp
  have k_alt: "?k = (p + 1) - length ?xs"
    using hP len_xs by simp
  finally show ?thesis
    by (simp add: changes_rev_about)
qed

lemma descartes_roots_test_swap:
  fixes p :: "real poly" and a b :: real
  shows "descartes_roots_test a b p = descartes_roots_test b a p"
proof -
  let ?F = "fcompose p [:a,b:] [:1,1:]"
  have degF: "degree ?F \<le> degree p"
    by (rule degree_fcompose_linear_le) simp_all

  have ch:
    "changes (coeffs (fcompose p [:b,a:] [:1,1:]))
     = changes (coeffs (fcompose p [:a,b:] [:1,1:]))"
  proof -
    have "changes (coeffs (fcompose p [:b,a:] [:1,1:]))
          = changes (coeffs (reciprocal_poly (degree p) ?F))"
      using fcompose_swap_reciprocal by metis
    also have "... = changes (coeffs ?F)"
      using changes_coeffs_reciprocal[OF degF] by simp
    finally show ?thesis by simp
  qed

  show ?thesis
    unfolding descartes_roots_test_def
    using ch by simp
qed

definition descartes_roots_test_sc::"real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> nat" where
  "descartes_roots_test_sc a b P = sign_changes (coeffs (fcompose P [:a,b:] [:1,1:]))"

lemma descartes_roots_test_sc_eq : "descartes_roots_test a b P = descartes_roots_test_sc a b P"
  using changes_eq_sign_changes
  by (metis descartes_roots_test_def descartes_roots_test_sc_def nat_int)

lemma descartes_roots_test_sc_eq_Bernstein_changes: 
  fixes P :: "real poly" and a b :: real
  defines "p \<equiv> degree P"
  shows "descartes_roots_test_sc a b P = Bernstein_changes p a b P"
  using descartes_roots_test_sc_eq descartes_roots_test_eq_Bernstein_changes p_def 
  by (metis descartes_roots_test_swap)


end