theory Dsc_Taylor
  imports Dsc_Exec Dsc_Rat
begin

text \<open>Taylor shift, scaling and reciprocal transforms on coefficient lists.
  Layer: FUNCTIONAL SPEC.
  Main exports: \<open>taylor_shift\<close>, \<open>taylor_shift_list\<close>, \<open>scale_poly_list\<close>, \<open>sign_changes_fold\<close> — the list
  primitives every GMP kernel implements.\<close>

definition taylor_shift :: "'a::comm_ring_1 \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "taylor_shift c p = pcompose p [:c, 1:]"

definition scale_poly :: "'a::comm_ring_1 \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "scale_poly c p = Poly (map (\<lambda>(i, a). a * c^i) (List.enumerate 0 (coeffs p)))"

definition reverse_poly :: "'a::zero poly \<Rightarrow> 'a poly" where
  "reverse_poly p = Poly (rev (coeffs p))"

lemma Poly_foldr: "Poly xs = foldr pCons xs 0"
  by (induction xs) simp_all

lemma scale_poly_code [code]:
  "scale_poly c p = foldr pCons (map (\<lambda>(i, a). a * c^i) (List.enumerate 0 (coeffs p))) 0"
  unfolding scale_poly_def Poly_foldr by simp

lemma reverse_poly_code [code]:
  "reverse_poly p = foldr pCons (rev (coeffs p)) 0"
  unfolding reverse_poly_def Poly_foldr by simp

definition fast_descartes_transform :: "'a::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "fast_descartes_transform a b p =
    taylor_shift 1 (reverse_poly (scale_poly (b - a) (taylor_shift a p)))"

definition fast_descartes_roots_test :: "'a::linordered_idom \<Rightarrow> 'a \<Rightarrow> 'a poly \<Rightarrow> nat" where
  "fast_descartes_roots_test a b p = Descartes_Sign_Rule.sign_changes (coeffs (fast_descartes_transform a b p))"

lemma coeff_pcompose_linear:
  fixes p :: "'a::comm_ring_1 poly"
  shows "coeff (pcompose p [:0, c:]) n = coeff p n * c ^ n"
proof (induction p arbitrary: n rule: pCons_induct)
  case 0
  then show ?case by simp
next
  case (pCons a p)
  show ?case
  proof (cases n)
    case 0
    have "pcompose (pCons a p) [:0, c:] = [:a:] + [:0, c:] * pcompose p [:0, c:]"
      by simp
    then have "coeff (pcompose (pCons a p) [:0, c:]) 0 = coeff ([:a:] + [:0, c:] * pcompose p [:0, c:]) 0"
      by simp
    also have "\<dots> = coeff [:a:] 0 + coeff ([:0, c:] * pcompose p [:0, c:]) 0"
      by simp
    also have "coeff ([:0, c:] * pcompose p [:0, c:]) 0 = coeff [:0, c:] 0 * coeff (pcompose p [:0, c:]) 0"
      by (simp add: coeff_mult_0)
    also have "coeff [:0, c:] 0 = 0"
      by simp
    finally have LHS: "coeff (pcompose (pCons a p) [:0, c:]) 0 = a"
      by simp
    have RHS: "coeff (pCons a p) 0 * c ^ 0 = a"
      by simp
    then show ?thesis
      using LHS RHS "0" by presburger
  next
    case (Suc m)
    have "pcompose (pCons a p) [:0, c:] = [:a:] + [:0, c:] * pcompose p [:0, c:]"
      by simp
    also have "\<dots> = [:a:] + pCons 0 (Polynomial.smult c (pcompose p [:0, c:]))"
      by simp
    finally have "coeff (pcompose (pCons a p) [:0, c:]) (Suc m) = 
                  coeff (pCons a (Polynomial.smult c (pcompose p [:0, c:]))) (Suc m)"
      by simp
    also have "\<dots> = c * coeff (pcompose p [:0, c:]) m"
      by simp
    also have "\<dots> = c * (coeff p m * c ^ m)"
      using pCons.IH by simp
    also have "\<dots> = coeff p m * c ^ Suc m"
      by simp
    finally show ?thesis using Suc by simp
  qed
qed

lemma coeff_scale_poly:
  "coeff (scale_poly c p) n = coeff p n * c ^ n"
proof -
  have "coeff (scale_poly c p) n = nth_default 0 (map (\<lambda>(i, a). a * c ^ i) (List.enumerate 0 (coeffs p))) n"
    by (simp add: scale_poly_def coeff_Poly)
  also have "\<dots> = (if n < length (coeffs p) then (coeffs p ! n) * c ^ n else 0)"
    by (simp add: enumerate_eq_zip nth_default_def nth_map2_dsc)
  also have "\<dots> = (if n < length (coeffs p) then coeffs p ! n else 0) * c ^ n"
    by auto
  also have "\<dots> = nth_default 0 (coeffs p) n * c ^ n"
    by (simp add: nth_default_def)
  also have "nth_default 0 (coeffs p) n = coeff (Poly (coeffs p)) n"
    by (simp add: nth_default_coeffs_eq)
  also have "\<dots> = coeff p n"
    by simp
  finally show ?thesis 
    by simp
qed

lemma scale_poly_eq_pcompose:
  "scale_poly c p = pcompose p [:0, c:]"
proof (rule poly_eqI)
  fix n
  show "coeff (scale_poly c p) n = coeff (pcompose p [:0, c:]) n"
    using coeff_scale_poly coeff_pcompose_linear
    by (metis Groups.mult_ac(2)
        Polynomial.coeff_pcompose_linear)
qed

lemma scale_taylor_compose:
  "scale_poly d (taylor_shift c p) = pcompose p [:c, d:]"
  unfolding scale_poly_def taylor_shift_def
  using pcompose_pCons scale_poly_eq_pcompose Missing_Polynomial.pCons_0_as_mult
      mult_cancel_left2 pcompose_1 pcompose_assoc pcompose_idR
  by (metis (no_types, lifting) ext more_arith_simps(6)
      scale_poly_def)

lemma coeff_reverse_poly:
  "coeff (reverse_poly p) i = (if i \<le> degree p then coeff p (degree p - i) else 0)"
proof (cases "p = 0")
  case True
  then show ?thesis by (simp add: reverse_poly_def)
next
  case False
  have len: "length (coeffs p) = degree p + 1"
    using False by (simp add: degree_eq_length_coeffs)
    
  show ?thesis
  proof (cases "i \<le> degree p")
    case True_i: True
    hence i_lt: "i < length (coeffs p)" 
      using len by simp
      
    have "coeff (reverse_poly p) i = nth_default 0 (rev (coeffs p)) i"
      unfolding reverse_poly_def by (simp add: coeff_Poly)
      
    also have "\<dots> = rev (coeffs p) ! i"
      by (simp add: nth_default_def i_lt)
      
    also have "\<dots> = coeffs p ! (length (coeffs p) - 1 - i)"
      by (simp add: rev_nth i_lt)
      
    also have "\<dots> = coeffs p ! (degree p - i)"
      using len by simp
      
    also have "\<dots> = nth_default 0 (coeffs p) (degree p - i)"
      using True_i len by (auto simp add: nth_default_def)
      
    also have "\<dots> = coeff p (degree p - i)"
      by (simp add: coeff_Poly [symmetric])
      
    finally show ?thesis 
      using True_i by simp
  next
    case False_i: False
    hence i_ge: "i \<ge> length (coeffs p)" 
      using len by simp
      
    have "coeff (reverse_poly p) i = nth_default 0 (rev (coeffs p)) i"
      unfolding reverse_poly_def by (simp add: coeff_Poly)
      
    also have "\<dots> = 0"
      by (simp add: i_ge nth_default_beyond)
      
    finally show ?thesis 
      using False_i by simp
  qed
qed

lemma taylor_reverse_fcompose:
  "taylor_shift 1 (reverse_poly (p:: rat poly)) = fcompose p [:1:] [:1, 1:]"
proof (cases "p = 0")
  case True
  then show ?thesis by (simp add: taylor_shift_def reverse_poly_def fcompose_def)
next
  case False
  have "\<forall>x. poly (taylor_shift 1 (reverse_poly p)) x = poly (fcompose p [:1:] [:1, 1:]) x"
  proof
    fix x :: rat

    have f_eval: "poly (fcompose p [:1:] [:1, 1:]) x = (\<Sum>i\<le>degree p. coeff p i * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree p - i))"
    proof (induction p rule: pCons_induct)
      case 0
      show ?case by (simp add: fcompose_def)
    next
      case (pCons a p)
      show ?case
      proof (cases "p = 0")
        case True
        then show ?thesis by simp
      next
        case False
        have "poly (fcompose (pCons a p) [:1:] [:1, 1:]) x = 
              poly ([:a:] * [:1, 1:] ^ degree (pCons a p) + [:1:] * fcompose p [:1:] [:1, 1:]) x"
          by (simp add: fcompose_pCons)
        also have "... = a * poly [:1, 1:] x ^ degree (pCons a p) + poly [:1:] x * poly (fcompose p [:1:] [:1, 1:]) x"
          by simp
        also have "... = a * poly [:1, 1:] x ^ degree (pCons a p) + 
                   poly [:1:] x * (\<Sum>i\<le>degree p. coeff p i * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree p - i))"
          using pCons.IH by simp
        also have "... = a * poly [:1, 1:] x ^ degree (pCons a p) + 
                          (\<Sum>i\<le>degree p. coeff p i * poly [:1:] x ^ (i + 1) * poly [:1, 1:] x ^ (degree p - i))"
          by (simp add: sum_distrib_left mult.assoc)
        also have "... = coeff (pCons a p) 0 * poly [:1:] x ^ 0 * poly [:1, 1:] x ^ (degree (pCons a p) - 0) + 
                          (\<Sum>i=0..degree p. coeff p i * poly [:1:] x ^ (i + 1) * poly [:1, 1:] x ^ (degree p - i))"
          using atLeast0AtMost by fastforce
        also have "... = a * poly [:1, 1:] x ^ degree (pCons a p) + 
                          (\<Sum>i=1..Suc (degree p). coeff p (i - 1) * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree p - (i - 1)))"
        proof -
          have "(\<Sum>i\<le>degree p. coeff p i * poly [:1:] x ^ (i + 1) * poly [:1, 1:] x ^ (degree p - i)) = 
                (\<Sum>i\<in>Suc ` {0..degree p}. coeff p (i - 1) * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree p - (i - 1)))"
            using inj_on_def
            by (metis (lifting) Groups.add_ac(2)[of "1"]
                \<open>a * poly [:1, 1:] x ^ degree (pCons a p) + (\<Sum>i\<le>degree p. coeff p i * poly [:1:] x ^ (i + 1) * poly [:1, 1:] x ^ (degree p - i)) = coeff (pCons a p) 0 * poly [:1:] x ^ 0 * poly [:1, 1:] x ^ (degree (pCons a p) - 0) + (\<Sum>i = 0..degree p. coeff p i * poly [:1:] x ^ (i + 1) * poly [:1, 1:] x ^ (degree p - i))\<close>
                add_diff_cancel_left'[of "1"]
                add_diff_cancel_left'[of "a * poly [:1, 1:] x ^ degree (pCons a p)"
                  "\<Sum>uub = 0..degree p. coeff p uub * poly [:1:] x ^ (uub + 1) * poly [:1, 1:] x ^ (degree p - uub)"]
                  add_diff_cancel_left'[of "a * poly [:1, 1:] x ^ degree (pCons a p)"
                    "\<Sum>uub\<le>degree p. coeff p uub * poly [:1:] x ^ (uub + 1) * poly [:1, 1:] x ^ (degree p - uub)"]
                    coeff_pCons_0[of a p] diff_zero[of "degree (pCons a p)"]
                    mult_cancel_left1[of a "1"] plus_1_eq_Suc power_0[of "poly [:1:] x"]
                    sum.reindex_cong[of Suc "{0..degree p}" "Suc ` {0..degree p}"
                      "\<lambda>uub. coeff p (uub - 1) * poly [:1:] x ^ uub * poly [:1, 1:] x ^ (degree p - (uub - 1))"
                      "\<lambda>uub. coeff p uub * poly [:1:] x ^ (uub + 1) * poly [:1, 1:] x ^ (degree p - uub)"])
          also have "... = (\<Sum>i=1..Suc (degree p). coeff p (i - 1) * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree p - (i - 1)))"
            by simp
          finally show ?thesis 
            using False degree_pCons_eq
              \<open>a * poly [:1, 1:] x ^ degree (pCons a p) + (\<Sum>i\<le>degree p. coeff p i * poly [:1:] x ^ (i + 1) * poly [:1, 1:] x ^ (degree p - i)) = coeff (pCons a p) 0 * poly [:1:] x ^ 0 * poly [:1, 1:] x ^ (degree (pCons a p) - 0) + (\<Sum>i = 0..degree p. coeff p i * poly [:1:] x ^ (i + 1) * poly [:1, 1:] x ^ (degree p - i))\<close>
            by presburger
        qed
        also have "... = coeff (pCons a p) 0 * poly [:1:] x ^ 0 * poly [:1, 1:] x ^ (degree (pCons a p) - 0) + 
                          (\<Sum>i=1..degree (pCons a p). coeff (pCons a p) i * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree (pCons a p) - i))"
        proof -
          have deg_eq: "degree (pCons a p) = Suc (degree p)" 
            using False by (simp add: degree_pCons_eq)
          
          have term1: "a * poly [:1, 1:] x ^ degree (pCons a p) = 
                       coeff (pCons a p) 0 * poly [:1:] x ^ 0 * poly [:1, 1:] x ^ (degree (pCons a p) - 0)"
            by simp

          have term2: "(\<Sum>i=1..Suc (degree p). coeff p (i - 1) * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree p - (i - 1))) = 
                       (\<Sum>i=1..Suc (degree p). coeff (pCons a p) i * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree (pCons a p) - i))"
          proof (rule sum.cong)
            show "{1..Suc (degree p)} = {1..Suc (degree p)}" by simp
          next
            fix i assume "i \<in> {1..Suc (degree p)}"
            then have "i > 0" by simp
            then obtain j where j_def: "i = Suc j" by (cases i) auto
            show "coeff p (i - 1) * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree p - (i - 1)) = 
                  coeff (pCons a p) i * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree (pCons a p) - i)"
              unfolding j_def deg_eq by simp
          qed
          show ?thesis
            using term1 term2 deg_eq by simp
        qed
        also have "... = (\<Sum>i\<le>degree (pCons a p). coeff (pCons a p) i * poly [:1:] x ^ i * poly [:1, 1:] x ^ (degree (pCons a p) - i))"
        proof -
          have "degree (pCons a p) = Suc (degree p)" using False by (simp add: degree_pCons_eq)
          thus ?thesis 
            by (metis (lifting) One_nat_def atLeast0AtMost bot_nat_0.extremum
                sum.atLeast_Suc_atMost)
        qed
        finally show ?thesis .
      qed
    qed

    have t_eval: "poly (taylor_shift 1 (reverse_poly p)) x = (\<Sum>i\<le>degree p. coeff p (degree p - i) * (x + 1) ^ i)"
    proof -
      have "reverse_poly p = (\<Sum>i\<le>degree (reverse_poly p). Polynomial.monom (coeff (reverse_poly p) i) i)"
        using poly_as_sum_of_monoms by metis
      then have "poly (reverse_poly p) (x + 1) = poly (\<Sum>i\<le>degree (reverse_poly p). Polynomial.monom (coeff (reverse_poly p) i) i) (x + 1)"
        by simp
      also have "\<dots> = (\<Sum>i\<le>degree (reverse_poly p). coeff (reverse_poly p) i * (x + 1) ^ i)"
        by (simp add: poly_altdef poly_as_sum_of_monoms)
      also have "\<dots> = (\<Sum>i\<le>degree p. coeff (reverse_poly p) i * (x + 1) ^ i)"
      proof (rule sum.mono_neutral_left)
        show "finite {..degree p}" by simp
        have "\<forall>i > degree p. coeff (reverse_poly p) i = 0"
          by (simp add: coeff_reverse_poly)
        then have "degree (reverse_poly p) \<le> degree p"
          by (intro degree_le) simp
        then show "{..degree (reverse_poly p)} \<subseteq> {..degree p}" by auto
        show "\<forall>i\<in>{..degree p} - {..degree (reverse_poly p)}. coeff (reverse_poly p) i * (x + 1) ^ i = 0"
          by (metis Diff_iff atMost_iff le_degree mult_not_zero)
      qed
      also have "\<dots> = (\<Sum>i\<le>degree p. coeff p (degree p - i) * (x + 1) ^ i)"
        by (simp add: coeff_reverse_poly)
      finally show ?thesis 
        by (simp add: add.commute poly_pcompose
            taylor_shift_def)
    qed

    have reindex: "(\<Sum>i\<le>degree p. coeff p (degree p - i) * (x + 1) ^ i) = 
                   (\<Sum>i\<le>degree p. coeff p i * (x + 1) ^ (degree p - i))"
    proof -
      have "bij_betw (\<lambda>i. degree p - i) {..degree p} {..degree p}"
      proof (rule bij_betw_imageI)
        show "inj_on (\<lambda>i. degree p - i) {..degree p}" by (rule inj_onI) simp
        show "(\<lambda>i. degree p - i) ` {..degree p} = {..degree p}" 
          using image_diff_atMost by metis
      qed
      from sum.reindex_bij_betw[OF this, of "\<lambda>i. coeff p i * (x + 1) ^ (degree p - i)"]
      have "(\<Sum>i\<le>degree p. coeff p (degree p - i) * (x + 1) ^ (degree p - (degree p - i))) = 
            (\<Sum>i\<le>degree p. coeff p i * (x + 1) ^ (degree p - i))" .
      moreover have "(\<Sum>i\<le>degree p. coeff p (degree p - i) * (x + 1) ^ (degree p - (degree p - i))) = 
                     (\<Sum>i\<le>degree p. coeff p (degree p - i) * (x + 1) ^ i)"
        by (rule sum.cong) simp_all
      ultimately show ?thesis by simp
    qed 
    
    show "poly (taylor_shift 1 (reverse_poly p)) x = poly (fcompose p [:1:] [:1, 1:]) x"
      using f_eval t_eval reindex by (simp add: add.commute)
  qed
  then show ?thesis
    by fast
qed

lemma scale_taylor_is_pcompose:
  "scale_poly (b - a) (taylor_shift a p) = pcompose p [:a, b - a:]"
proof -
  have "\<forall>x. poly (scale_poly (b - a) (taylor_shift a p)) x = poly (pcompose p [:a, b - a:]) x"
    by (metis scale_taylor_compose)
  then show ?thesis
    using scale_taylor_compose by blast
qed

lemma degree_pcompose_linear:
  fixes a b :: "'a::idom" and p :: "'a poly"
  assumes "a \<noteq> b"
  shows "degree (pcompose p [:a, b - a:]) = degree p"
proof -
  have "degree (pcompose p [:a, b - a:]) = degree p \<and> (p \<noteq> 0 \<longrightarrow> pcompose p [:a, b - a:] \<noteq> 0)"
  proof (induction p rule: pCons_induct)
    case 0
    then show ?case by simp
  next
    case (pCons c p)
    have lin_neq_0: "[:a, b - a:] \<noteq> 0"
      using \<open>a \<noteq> b\<close> by auto
    have deg_lin: "degree [:a, b - a:] = 1"
      using \<open>a \<noteq> b\<close> by simp

    show ?case
    proof (cases "p = 0")
      case True
      then show ?thesis by auto
    next
      case False
      with pCons.IH have IH_deg: "degree (pcompose p [:a, b - a:]) = degree p" 
                     and IH_neq: "pcompose p [:a, b - a:] \<noteq> 0"
        by auto

      have comp_unfold: "pcompose (pCons c p) [:a, b - a:] = [:c:] + [:a, b - a:] * pcompose p [:a, b - a:]"
        by simp

      have deg_mult: "degree ([:a, b - a:] * pcompose p [:a, b - a:]) = 1 + degree p"
        using lin_neq_0 IH_neq IH_deg degree_mult_eq 
        by (metis deg_lin)
      
      have "degree [:c:] < degree ([:a, b - a:] * pcompose p [:a, b - a:])"
        using deg_mult by simp
      then have deg_eq: "degree ([:c:] + [:a, b - a:] * pcompose p [:a, b - a:]) = degree ([:a, b - a:] * pcompose p [:a, b - a:])"
        by (rule degree_add_eq_right)
      
      have final_deg: "degree (pcompose (pCons c p) [:a, b - a:]) = degree (pCons c p)"
        using comp_unfold deg_eq deg_mult False by (simp add: degree_pCons_eq)
        
      have final_neq: "pcompose (pCons c p) [:a, b - a:] \<noteq> 0"
      proof
        assume "pcompose (pCons c p) [:a, b - a:] = 0"
        then have "degree (pcompose (pCons c p) [:a, b - a:]) = 0" by simp
        with final_deg False show False by (simp add: degree_pCons_eq)
      qed
      
      show ?thesis using final_deg final_neq by simp
    qed
  qed
  then show ?thesis ..
qed

lemma reciprocal_shift_rescale_eq_fcompose_rat:
  fixes P :: "rat poly" and a b :: rat
  defines "p \<equiv> degree P"
  defines "R \<equiv> P \<circ>\<^sub>p [:b,1:] \<circ>\<^sub>p [:0, a-b:]"
  shows "(reciprocal_poly p R) \<circ>\<^sub>p [:1,1:] = fcompose P [:a,b:] [:1,1:]"
proof -
  let ?L = "(reciprocal_poly p R) \<circ>\<^sub>p [:1,1:]"
  let ?M = "fcompose P [:a,b:] [:1,1:]"
  let ?D = "?L - ?M"

  have eval_eq: "\<And>x. x \<noteq> -1 \<Longrightarrow> poly ?L x = poly ?M x"
    proof -
      fix x :: rat
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

  have sub_roots: "range (of_nat :: nat \<Rightarrow> rat) \<subseteq> {x. poly ?D x = 0}"
  proof
    fix x :: rat
    assume "x \<in> range (of_nat :: nat \<Rightarrow> rat)"
    then obtain n :: nat where x_def: "x = of_nat n" by blast
    have xne: "x \<noteq> -1"
      by (simp add: x_def)
    show "x \<in> {x. poly ?D x = 0}"
      using eval_eq[OF xne] unfolding x_def by simp
  qed

  have inf_sub: "infinite (range (of_nat :: nat \<Rightarrow> rat))"
    by (rule range_inj_infinite) (simp add: inj_on_def)

  have inf_roots: "infinite {x. poly ?D x = 0}"
    using inf_sub sub_roots finite_subset by blast

  have D0: "?D = 0"
    using inf_roots poly_roots_finite[of ?D] by blast

  from D0 show ?thesis by simp
qed

lemma fcompose_pcompose_descartes:
  fixes a b and p :: "rat poly"
  assumes "a \<noteq> b"
  shows "fcompose (pcompose p [:a, b - a:]) [:1:] [:1, 1:] = fcompose p [:b, a:] [:1, 1:]"
proof -
  have deg_eq: "degree (pcompose p [:a, b - a:]) = degree p"
    using \<open>a \<noteq> b\<close> by (rule degree_pcompose_linear)

  have "\<forall>x. poly (fcompose (pcompose p [:a, b - a:]) [:1:] [:1, 1:]) x = 
            poly (fcompose p [:b, a:] [:1, 1:]) x"
  proof
    fix x :: rat
    show "poly (fcompose (pcompose p [:a, b - a:]) [:1:] [:1, 1:]) x = 
          poly (fcompose p [:b, a:] [:1, 1:]) x"
      using deg_eq pcompose_idR
          reciprocal_shift_rescale_eq_fcompose_rat scale_poly_eq_pcompose
          scale_taylor_is_pcompose taylor_shift_def
      by (metis arith_simps(57) pCons_0_0)
  qed
  
  then show ?thesis
    by blast
qed

lemma fast_descartes_transform_eq:
  fixes a b :: "rat" and p :: "rat poly"
  assumes "a \<noteq> b"
  shows "fast_descartes_transform a b p = fcompose p [:b, a:] [:1, 1:]"
proof -
  have "fast_descartes_transform a b p = taylor_shift 1 (reverse_poly (scale_poly (b - a) (taylor_shift a p)))"
    unfolding fast_descartes_transform_def by order
  also have "... = taylor_shift 1 (reverse_poly (pcompose p [:a, b - a:]))"
    by (simp add: scale_taylor_is_pcompose)
  also have "... = fcompose (pcompose p [:a, b - a:]) [:1:] [:1, 1:]"
    by (simp add: taylor_reverse_fcompose)
  also have "... = fcompose p [:b, a:] [:1, 1:]"
    using \<open>a \<noteq> b\<close> fcompose_pcompose_descartes
    by presburger
  finally show ?thesis .
qed

lemma fast_descartes:
  fixes a b :: "rat" and p :: "rat poly"
  assumes "a \<noteq> b"
  shows "fast_descartes_roots_test a b p  = descartes_roots_test_sc_rat a b p"
  using assms descartes_roots_test_sc_def descartes_roots_test_sc_eq
    descartes_roots_test_swap fast_descartes_roots_test_def
    fast_descartes_transform_eq descartes_roots_test_sc_rat_def
    descartes_roots_test_sc_rat_refine by metis

section \<open>Sign_alg\<close>

fun sign_step :: "'a::linordered_idom \<Rightarrow> 'a \<times> nat \<Rightarrow> 'a \<times> nat" where
  "sign_step x (last_s, n) =
    (if x = 0 then (last_s, n)
     else if last_s = 0 then (sgn x, 0)
     else if sgn x \<noteq> last_s then (sgn x, n + 1)
     else (last_s, n))"

definition sign_changes_fold :: "'a::linordered_idom list \<Rightarrow> nat" where
  "sign_changes_fold xs = snd (fold sign_step xs (0, 0))"

lemma sign_step_sgn:
  "sign_step x (s, n) = sign_step (sgn x) (s, n)"
  by (simp add: sgn_0_0)

lemma fold_sign_step_map_filter:
  "fold sign_step xs (s, n) = fold sign_step (filter (\<lambda>x. x \<noteq> 0) (map sgn xs)) (s, n)"
proof (induction xs arbitrary: s n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "sign_step x (s, n) = sign_step (sgn x) (s, n)"
    using sign_step_sgn by blast
  then show ?case
    using Cons.IH by (cases "x = 0") auto
qed

lemma fold_sign_step_ys:
  "\<forall>x\<in>set ys. x \<noteq> 0 \<and> sgn x = x \<Longrightarrow>
   fold sign_step ys (s, n) =
    (if ys = [] then (s, n)
     else (last ys,
       if s = 0 then length (remdups_adj ys) - 1
       else n + length (remdups_adj (s # ys)) - 1))"
proof (induction ys arbitrary: s n)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case
    by fastforce
qed

lemma sign_changes_eq_fold:
  "Descartes_Sign_Rule.sign_changes xs = sign_changes_fold xs"
proof -
  let ?ys = "filter (\<lambda>x. x \<noteq> 0) (map sgn xs)"
  have "\<forall>x\<in>set ?ys. x \<noteq> 0 \<and> sgn x = x"
    by auto
  then have "fold sign_step ?ys (0, 0) =
    (if ?ys = [] then (0, 0)
     else (last ?ys, length (remdups_adj ?ys) - 1))"
    using fold_sign_step_ys[of "?ys" 0 0] by argo
  then have "snd (fold sign_step ?ys (0, 0)) = length (remdups_adj ?ys) - 1"
    by auto
  also have "... = Descartes_Sign_Rule.sign_changes xs"
    unfolding Descartes_Sign_Rule.sign_changes_def by simp
  finally show ?thesis
    unfolding sign_changes_fold_def
    using fold_sign_step_map_filter[of xs 0 0] by simp
qed

section \<open>Scale_alg\<close>

fun scale_poly_list_aux :: "'a::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "scale_poly_list_aux c acc [] = []"
| "scale_poly_list_aux c acc (x # xs) = (x * acc) # scale_poly_list_aux c (acc * c) xs"

definition scale_poly_list :: "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "scale_poly_list c xs = scale_poly_list_aux c 1 xs"

lemma scale_poly_list_aux_enumerate:
  "scale_poly_list_aux c (acc * c ^ n) xs = map (\<lambda>(i, a). a * acc * c ^ i) (List.enumerate n xs)"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "acc * c ^ n * c = acc * c ^ Suc n"
    by (simp add: algebra_simps)
  then show ?case
    using Cons.IH[of "Suc n"] by (simp add: algebra_simps)
qed

lemma scale_poly_list_eq_map:
  "scale_poly_list c xs = map (\<lambda>(i, a). a * c ^ i) (List.enumerate 0 xs)"
proof -
  have "scale_poly_list c xs = scale_poly_list_aux c (1 * c ^ 0) xs"
    unfolding scale_poly_list_def by simp
  also have "\<dots> = map (\<lambda>(i, a). a * 1 * c ^ i) (List.enumerate 0 xs)"
    using scale_poly_list_aux_enumerate[of c 1 0 xs] by simp
  also have "\<dots> = map (\<lambda>(i, a). a * c ^ i) (List.enumerate 0 xs)"
    by simp
  finally show ?thesis .
qed

lemma scale_poly_list_correct:
  "scale_poly c p = Poly (scale_poly_list c (coeffs p))"
  unfolding scale_poly_def scale_poly_list_eq_map by simp

section \<open>Reverse_alg\<close>

fun rev_acc :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_acc [] acc = acc"
| "rev_acc (x # xs) acc = rev_acc xs (x # acc)"

definition reverse_poly_list :: "'a list \<Rightarrow> 'a list" where
  "reverse_poly_list xs = rev_acc xs []"

fun rev_swap_step :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_swap_step i j xs =
     (if i < j then
        rev_swap_step (i + 1) (j - 1) (xs[i := xs ! j, j := xs ! i])
      else xs)"

definition reverse_array_fun :: "'a list \<Rightarrow> 'a list" where
  "reverse_array_fun xs = (if xs = [] then [] else rev_swap_step 0 (length xs - 1) xs)"

lemma rev_acc_eq:
  "rev_acc xs acc = rev xs @ acc"
proof (induction xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
    using Cons.IH[of "a # acc"] by simp
qed

lemma reverse_poly_list_eq_rev:
  "reverse_poly_list xs = rev xs"
  unfolding reverse_poly_list_def using rev_acc_eq[of xs "[]"] by simp

lemma reverse_poly_list_correct:
  "reverse_poly p = Poly (reverse_poly_list (coeffs p))"
  unfolding reverse_poly_def reverse_poly_list_eq_rev by simp

lemma rev_swap_step_correct:
  assumes "i + j + 1 = length xs" and "i \<le> j + 1"
  shows "rev_swap_step i j xs = take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs"
using assms
proof (induction i j xs rule: rev_swap_step.induct)
  case (1 i j xs)
  show ?case
  proof (cases "i < j")
    case True
    have len_update: "length (xs[i := xs ! j, j := xs ! i]) = length xs"
      by simp
    have "rev_swap_step i j xs = rev_swap_step (i + 1) (j - 1) (xs[i := xs ! j, j := xs ! i])"
      by (metis True rev_swap_step.elims)
    also have "\<dots> = take (i + 1) (xs[i := xs ! j, j := xs ! i]) @
                   rev (take (Suc (j - 1) - (i + 1)) (drop (i + 1) (xs[i := xs ! j, j := xs ! i]))) @
                   drop (Suc (j - 1)) (xs[i := xs ! j, j := xs ! i])"
      using "1.IH"[OF True] "1.prems" True len_update by auto
    also have "\<dots> = take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs"
    proof (rule nth_equalityI)
      show "length (take (i + 1) (xs[i := xs ! j, j := xs ! i]) @
             rev (take (Suc (j - 1) - (i + 1)) (drop (i + 1) (xs[i := xs ! j, j := xs ! i]))) @
             drop (Suc (j - 1)) (xs[i := xs ! j, j := xs ! i])) =
            length (take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs)"
        using "1.prems" True by simp
    next
      fix k
      assume "k < length (take (i + 1) (xs[i := xs ! j, j := xs ! i]) @
             rev (take (Suc (j - 1) - (i + 1)) (drop (i + 1) (xs[i := xs ! j, j := xs ! i]))) @
             drop (Suc (j - 1)) (xs[i := xs ! j, j := xs ! i]))"
      then have k_len: "k < length xs"
        using "1.prems" True by simp
      
      show "(take (i + 1) (xs[i := xs ! j, j := xs ! i]) @
             rev (take (Suc (j - 1) - (i + 1)) (drop (i + 1) (xs[i := xs ! j, j := xs ! i]))) @
             drop (Suc (j - 1)) (xs[i := xs ! j, j := xs ! i])) ! k =
            (take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs) ! k"
      proof (cases "k < i")
        case True
        then show ?thesis 
          using "1.prems" True k_len 
          by (metis calculation len_update less_add_Suc1 less_eq_Suc_le
              less_le_not_le not_less_eq nth_append_take_is_nth_conv
              nth_list_update_neq rev_swap_step.simps
              semiring_norm(174))
      next
        case False
        show ?thesis
        proof (cases "k = i")
          case True
          have lhs_eval: "(take (i + 1) (xs[i := xs ! j, j := xs ! i]) @
                 rev (take (Suc (j - 1) - (i + 1)) (drop (i + 1) (xs[i := xs ! j, j := xs ! i]))) @
                 drop (Suc (j - 1)) (xs[i := xs ! j, j := xs ! i])) ! k = xs ! j"
            using True `i < j` "1.prems" k_len by (simp add: nth_append nth_list_update min_def)
          have rhs_eval: "(take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs) ! k = xs ! j"
            using True `i < j` "1.prems" k_len nth_append rev_nth min_def
            by (smt (verit) Groups.add_ac(2) Suc_diff_Suc add.right_neutral
                add_diff_cancel_left' diff_Suc_Suc len_update length_drop
                length_rev less_add_Suc1 less_le_not_le not_less_eq nth_take
                plus_1_eq_Suc rev_drop rev_take)
          show ?thesis
            using lhs_eval rhs_eval by simp
        next
          case False
          show ?thesis
          proof (cases "k < j")
            case True
            have "i < k" using `\<not> k < i` `k \<noteq> i` by simp
            have lhs_eval: "(take (i + 1) (xs[i := xs ! j, j := xs ! i]) @
                   rev (take (Suc (j - 1) - (i + 1)) (drop (i + 1) (xs[i := xs ! j, j := xs ! i]))) @
                   drop (Suc (j - 1)) (xs[i := xs ! j, j := xs ! i])) ! k = xs ! (i + j - k)"
              using `i < k` True `i < j` "1.prems" k_len nth_append rev_nth nth_list_update min_def 
                    rev_drop rev_take len_update length_drop length_rev nth_take
                    nth_append rev_nth nth_take nth_drop length_take length_drop length_list_update nth_list_update_neq add_diff_cancel_left' diff_diff_left less_diff_conv less_add_Suc1
              by (smt (verit) Groups.add_ac(2) Suc_diff_Suc append_take_drop_id
                  diff_Suc_Suc diff_is_0_eq nat_less_le not_less_eq
                  ordered_cancel_comm_monoid_diff_class.add_diff_inverse
                  plus_1_eq_Suc)
            have rhs_eval: "(take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs) ! k = xs ! (i + j - k)"
              using `i < k` True `i < j` "1.prems" k_len nth_append rev_nth min_def
              rev_drop rev_take len_update length_drop length_rev nth_take
               nth_append rev_nth nth_take nth_drop length_take length_drop length_list_update nth_list_update_neq add_diff_cancel_left' diff_diff_left less_diff_conv less_add_Suc1
              by (smt (verit) Groups.add_ac(2) Suc_diff_Suc append_take_drop_id
                  diff_Suc_Suc diff_is_0_eq nat_less_le not_less_eq
                  ordered_cancel_comm_monoid_diff_class.add_diff_inverse
                  plus_1_eq_Suc)
            show ?thesis
              using lhs_eval rhs_eval by simp
          next
            case False
            show ?thesis
            proof (cases "k = j")
              case True
              have lhs_eval: "(take (i + 1) (xs[i := xs ! j, j := xs ! i]) @
                     rev (take (Suc (j - 1) - (i + 1)) (drop (i + 1) (xs[i := xs ! j, j := xs ! i]))) @
                     drop (Suc (j - 1)) (xs[i := xs ! j, j := xs ! i])) ! k = xs ! i"
                using True `i < j` "1.prems" k_len nth_append nth_list_update rev_nth min_def
                       rev_drop rev_take len_update length_drop length_rev nth_take
                by (smt (verit) Cons_nth_drop_Suc ab_semigroup_add_class.add_ac(1)
                    add_diff_cancel_left add_eq_if
                    cancel_comm_monoid_add_class.diff_cancel diff_add_inverse2
                    length_list_update length_take min_minus nth_append_length
                    plus_nat.simps(2))        
              have rhs_eval: "(take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs) ! k = xs ! i"
                using True `i < j` "1.prems" k_len nth_append rev_nth min_def
                      rev_drop rev_take len_update length_drop length_rev nth_take
                       nth_append rev_nth nth_take nth_drop length_take length_drop length_list_update nth_list_update_neq add_diff_cancel_left' diff_diff_left less_diff_conv less_add_Suc1
                      by (smt (verit) Groups.add_ac(2) Suc_diff_Suc append_take_drop_id
                          diff_Suc_Suc diff_is_0_eq nat_less_le not_less_eq
                          ordered_cancel_comm_monoid_diff_class.add_diff_inverse
                          plus_1_eq_Suc)
              show ?thesis
                using lhs_eval rhs_eval by simp
            next
              case False
              have "j < k" using `\<not> k < j` `k \<noteq> j` by simp
              have lhs_eval: "(take (i + 1) (xs[i := xs ! j, j := xs ! i]) @
                     rev (take (Suc (j - 1) - (i + 1)) (drop (i + 1) (xs[i := xs ! j, j := xs ! i]))) @
                     drop (Suc (j - 1)) (xs[i := xs ! j, j := xs ! i])) ! k = xs ! k"
                using `j < k` `i < j` "1.prems" k_len nth_append nth_list_update min_def
                      rev_drop rev_take len_update length_drop length_rev nth_take
                by (smt (verit) Groups.add_ac(2) Suc_eq_plus1 add.right_neutral
                    add_eq_if append_take_drop_id diff_diff_left diff_is_0_eq
                    diff_le_self length_take less_eq_Suc_le less_le_not_le
                    not_less_eq nth_list_update_neq
                    ordered_cancel_comm_monoid_diff_class.add_diff_inverse)  
              have rhs_eval: "(take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs) ! k = xs ! k"
                using `j < k` "1.prems" k_len 
                 rev_drop rev_take len_update length_drop length_rev nth_take
                by (smt (verit) Groups.add_ac(2) Suc_diff_Suc add_diff_cancel_left'
                    append_take_drop_id diff_diff_left diff_is_0_eq nat_less_le
                    not_less_eq nth_append
                    ordered_cancel_comm_monoid_diff_class.add_diff_inverse
                    plus_1_eq_Suc)
              show ?thesis
                using lhs_eval rhs_eval by simp
            qed
          qed
        qed
      qed
    qed
    finally show ?thesis .
  next
    case False
    have "rev_swap_step i j xs = xs"
      using False by (simp add: rev_swap_step.simps)
    also have "xs  = take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs"
    proof (rule nth_equalityI)
      show "length xs = length (take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs)"
        using "1.prems" False by simp
    next 
      fix k
      assume "k < length xs"
      have "i = j \<or> i = j + 1"
        using False "1.prems" by linarith
      then show "xs ! k = (take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs) ! k"
      proof
        assume eq: "i = j"
        have i_len: "i < length xs"
          using "1.prems" eq by linarith
        have drop_eq: "drop i xs = (xs ! i) # drop (Suc i) xs"
          using i_len by (simp add: Cons_nth_drop_Suc)
        have "take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs = take i xs @ [xs ! i] @ drop (Suc i) xs"
          using eq drop_eq by simp
        also have "\<dots> = take i xs @ drop i xs"
          using drop_eq[symmetric] by simp
        also have "\<dots> = xs"
          by simp
        finally have "take i xs @ rev (take (Suc j - i) (drop i xs)) @ drop (Suc j) xs = xs" .
        then show ?thesis
          by simp
      next
        assume "i = j + 1"
        then show ?thesis
          using `k < length xs` "1.prems" False by (simp add: nth_append rev_nth min_def)
      qed
    qed
    finally show ?thesis .
  qed
qed

lemma reverse_array_fun_eq_rev:
  "reverse_array_fun xs = rev xs"
proof (cases "xs = []")
  case True
  then show ?thesis
    unfolding reverse_array_fun_def by simp
next
  case False
  have len_cond: "0 + (length xs - 1) + 1 = length xs"
    using False by simp
  have bound_cond: "0 \<le> (length xs - 1) + 1"
    by simp
  
  have "rev_swap_step 0 (length xs - 1) xs =
    take 0 xs @ rev (take (Suc (length xs - 1)) (drop 0 xs)) @ drop (Suc (length xs - 1)) xs"
    using rev_swap_step_correct[OF len_cond bound_cond] by simp
  also have "\<dots> = rev xs"
    using False by simp
  finally show ?thesis
    unfolding reverse_array_fun_def using False by simp
qed

section \<open>Taylor\<close>

fun ruffini_step :: "'a::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ruffini_step c a [] = [a]"
| "ruffini_step c a (q # qs) = (a + c * q) # ruffini_step c q qs"

fun taylor_shift_list :: "'a::comm_ring_1 \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "taylor_shift_list c [] = []"
| "taylor_shift_list c (a # as) = ruffini_step c a (taylor_shift_list c as)"

lemma Poly_ruffini_step:
  "Poly (ruffini_step c a qs) = [:a:] + [:c, 1:] * Poly qs"
proof (induction qs arbitrary: a)
  case Nil
  show ?case by simp
next
  case (Cons q qs)
  have "Poly (ruffini_step c a (q # qs)) = pCons (a + c * q) (Poly (ruffini_step c q qs))"
    by simp
  also have "\<dots> = pCons (a + c * q) ([:q:] + [:c, 1:] * Poly qs)"
    using Cons.IH by simp
  also have "\<dots> = [:a:] + [:c, 1:] * Poly (q # qs)"
    by (simp add: algebra_simps)
  finally show ?case .
qed

lemma Poly_taylor_shift_list:
  "Poly (taylor_shift_list c as) = pcompose (Poly as) [:c, 1:]"
proof (induction as)
  case Nil
  show ?case 
    by simp
next
  case (Cons a as)
  have "Poly (taylor_shift_list c (a # as)) = Poly (ruffini_step c a (taylor_shift_list c as))"
    by simp
  also have "\<dots> = [:a:] + [:c, 1:] * Poly (taylor_shift_list c as)"
    using Poly_ruffini_step by simp
  also have "\<dots> = [:a:] + [:c, 1:] * pcompose (Poly as) [:c, 1:]"
    using Cons.IH by simp
  also have "\<dots> = pcompose (Poly (a # as)) [:c, 1:]"
    by simp
  finally show ?case .
qed

lemma taylor_shift_correct:
  "taylor_shift c p = Poly (taylor_shift_list c (coeffs p))"
  unfolding taylor_shift_def using Poly_taylor_shift_list 
  by (metis Poly_taylor_shift_list Poly_coeffs)


section \<open>Fast\<close>

definition fast_descartes_list :: "rat \<Rightarrow> rat \<Rightarrow> rat list \<Rightarrow> nat" where
  "fast_descartes_list a b xs = 
    sign_changes_fold (taylor_shift_list (1::rat) (reverse_array_fun (scale_poly_list (b - a) (taylor_shift_list a xs))))"

lemma length_ruffini_step [simp]:
  "length (ruffini_step c a qs) = Suc (length qs)"
  by (induction qs arbitrary: a) auto

lemma length_taylor_shift_list [simp]:
  "length (taylor_shift_list c as) = length as"
  by (induction as) auto

lemma last_ruffini_step:
  "qs \<noteq> [] \<Longrightarrow> last (ruffini_step c a qs) = last qs"
proof (induction qs arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons a qs)
  then show ?case
    by (metis last_ConsR list.distinct(1) ruffini_step.elims
        ruffini_step.simps(2))
qed

lemma last_taylor_shift_list:
  "as \<noteq> [] \<Longrightarrow> last (taylor_shift_list c as) = last as"
proof (induction as)
  case Nil then show ?case by simp
next
  case (Cons a as)
  then show ?case
  proof (cases "as = []")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using last_ruffini_step
      by (metis last_ruffini_step False local.Cons(1) taylor_shift_list.simps(2) last_ConsR ruffini_step.elims list.distinct(1))
  qed
qed

lemma coeffs_taylor_shift_list:
  assumes "as = coeffs p"
  shows "taylor_shift_list c as = coeffs (taylor_shift c p)"
proof (cases "p = 0")
  case True then show ?thesis using assms taylor_shift_def
    by (simp add: taylor_shift_correct)
next
  case False
  have "Poly (taylor_shift_list c as) = taylor_shift c p"
    using assms Poly_taylor_shift_list taylor_shift_def
    by (simp add: taylor_shift_correct)
  moreover have "taylor_shift_list c as \<noteq> []"
    using False assms
    by (metis coeffs_eq_Nil length_0_conv
        length_taylor_shift_list)
  moreover have "last (taylor_shift_list c as) = last as"
    using last_taylor_shift_list assms False
    by (metis assms last_taylor_shift_list coeffs_eq_Nil)
  moreover have "last as \<noteq> 0"
    using False assms no_trailing_coeffs
    by (metis coeffs_eq_Nil no_trailing_unfold)
  ultimately show ?thesis 
    using coeffs_Poly strip_while_coeffs
    by (metis (mono_tags, lifting) no_trailing_unfold
        strip_while_idem)
qed

lemma length_scale_poly_list_aux [simp]:
  "length (scale_poly_list_aux c acc xs) = length xs"
  by (induction xs arbitrary: acc) auto

lemma length_scale_poly_list [simp]:
  "length (scale_poly_list c xs) = length xs"
  unfolding scale_poly_list_def by simp

lemma last_scale_poly_list_aux:
  "xs \<noteq> [] \<Longrightarrow> last (scale_poly_list_aux c acc xs) = last xs * acc * c ^ (length xs - 1)"
proof (induction xs arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "xs = []")
    case True then show ?thesis by simp
  next
    case False
    have "last (scale_poly_list_aux c acc (x # xs)) = last (scale_poly_list_aux c (acc * c) xs)"
      using False
      by (metis last_ConsR length_0_conv length_scale_poly_list_aux
          scale_poly_list_aux.simps(2))
    also have "... = last xs * (acc * c) * c ^ (length xs - 1)"
      using Cons.IH False by simp
    also have "... = last xs * acc * (c * c ^ (length xs - 1))"
      by (simp add: algebra_simps)
    also have "... = last xs * acc * c ^ length xs"
      using False
      by (simp add: power_eq_if)
    finally show ?thesis using False by simp
  qed
qed

lemma last_scale_poly_list:
  "xs \<noteq> [] \<Longrightarrow> last (scale_poly_list c xs) = last xs * c ^ (length xs - 1)"
  unfolding scale_poly_list_def using last_scale_poly_list_aux[of xs c 1] by simp

lemma coeffs_scale_poly_list:
  fixes c :: "'a::idom" and p :: "'a poly"
  assumes "as = coeffs p" and "c \<noteq> 0"
  shows "scale_poly_list c as = coeffs (scale_poly c p)"
proof (cases "p = 0")
  case True then show ?thesis using assms scale_poly_def
    using scale_poly_list_eq_map 
    by (metis True assms(2) scale_poly_def assms(1) scale_poly_list_eq_map scale_poly_list_correct length_scale_poly_list coeffs_eq_Nil length_0_conv Poly.simps(1))
next
  case False
  have "Poly (scale_poly_list c as) = scale_poly c p"
    using assms scale_poly_list_correct
    by metis
  moreover have "scale_poly_list c as \<noteq> []"
    using False assms
    by (metis coeffs_eq_Nil length_greater_0_conv
        length_scale_poly_list)
  moreover have "last (scale_poly_list c as) = last as * c ^ (length as - 1)"
    using False assms last_scale_poly_list
    using coeffs_eq_Nil by blast
  moreover have "last as \<noteq> 0"
    using False assms no_trailing_coeffs
    by (metis assms(2) no_trailing_coeffs assms(1) False coeffs_eq_Nil no_trailing_unfold)
  ultimately show ?thesis
    using `c \<noteq> 0` coeffs_Poly no_zero_divisors strip_while_coeffs
    by (metis (mono_tags, opaque_lifting) no_trailing_unfold power_eq_0_iff
        strip_while_idem)
qed

lemma filter_sgn_strip_while_0:
  fixes xs :: "'a::linordered_idom list"
  shows "filter (\<lambda>x. x \<noteq> 0) (map sgn (strip_while (\<lambda>x. x = 0) xs)) = filter (\<lambda>x. x \<noteq> 0) (map sgn xs)"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  show ?case
  proof (cases "x = 0")
    case True
    have "filter (\<lambda>x. x \<noteq> 0) (map sgn (strip_while (\<lambda>x. x = 0) (xs @ [x]))) = 
          filter (\<lambda>x. x \<noteq> 0) (map sgn (strip_while (\<lambda>x. x = 0) xs))"
      using True by simp
    also have "\<dots> = filter (\<lambda>x. x \<noteq> 0) (map sgn xs)"
      using snoc.IH by simp
    also have "\<dots> = filter (\<lambda>x. x \<noteq> 0) (map sgn xs) @ filter (\<lambda>x. x \<noteq> 0) [0]"
      by simp
    also have "\<dots> = filter (\<lambda>x. x \<noteq> 0) (map sgn xs) @ filter (\<lambda>x. x \<noteq> 0) [sgn x]"
      using True by simp
    also have "\<dots> = filter (\<lambda>x. x \<noteq> 0) (map sgn xs @ [sgn x])"
      by simp
    also have "\<dots> = filter (\<lambda>x. x \<noteq> 0) (map sgn (xs @ [x]))"
      by simp
    finally show ?thesis .
  next
    case False
    have "strip_while (\<lambda>x. x = 0) (xs @ [x]) = xs @ [x]"
      using False by simp
    then show ?thesis
      by simp
  qed
qed

lemma sign_changes_fold_Poly:
  "sign_changes_fold xs = Descartes_Sign_Rule.sign_changes (coeffs (Poly xs))"
proof -
  have "sign_changes_fold xs = snd (fold sign_step (filter (\<lambda>x. x \<noteq> 0) (map sgn xs)) (0, 0))"
    using fold_sign_step_map_filter unfolding sign_changes_fold_def by metis
  also have "... = snd (fold sign_step (filter (\<lambda>x. x \<noteq> 0) (map sgn (strip_while (\<lambda>x. x = 0) xs))) (0, 0))"
    using filter_sgn_strip_while_0 by metis
  also have "... = sign_changes_fold (strip_while (\<lambda>x. x = 0) xs)"
    using fold_sign_step_map_filter unfolding sign_changes_fold_def by metis
  also have "... = sign_changes_fold (coeffs (Poly xs))"
    by (metis calculation sign_changes_coeff_sign_changes
        sign_changes_eq_fold)
  also have "... = Descartes_Sign_Rule.sign_changes (coeffs (Poly xs))"
    using sign_changes_eq_fold by metis
  finally show ?thesis .
qed

lemma fast_descartes_list_equiv:
  assumes "a \<noteq> b"
  shows "fast_descartes_list a b (coeffs p) = descartes_roots_test_sc_rat a b p"
proof -
  let ?L1 = "taylor_shift_list a (coeffs p)"
  let ?L2 = "scale_poly_list (b - a) ?L1"
  let ?L3 = "reverse_array_fun ?L2"
  let ?L4 = "taylor_shift_list 1 ?L3"

  have L1_eq: "?L1 = coeffs (taylor_shift a p)"
    by (simp add: coeffs_taylor_shift_list)

  have L2_eq: "?L2 = coeffs (scale_poly (b - a) (taylor_shift a p))"
    using L1_eq coeffs_scale_poly_list[of ?L1 "taylor_shift a p" "b - a"] assms by simp

  have "Poly ?L3 = Poly (rev ?L2)"
    by (simp add: reverse_array_fun_eq_rev)
  also have "... = Poly (rev (coeffs (scale_poly (b - a) (taylor_shift a p))))"
    using L2_eq by simp
  also have "... = reverse_poly (scale_poly (b - a) (taylor_shift a p))"
    unfolding reverse_poly_def by simp
  finally have Poly_L3: "Poly ?L3 = reverse_poly (scale_poly (b - a) (taylor_shift a p))" .

  have "Poly ?L4 = pcompose (Poly ?L3) [:1, 1:]"
    by (simp add: Poly_taylor_shift_list)
  also have "... = pcompose (reverse_poly (scale_poly (b - a) (taylor_shift a p))) [:1, 1:]"
    using Poly_L3 by simp
  also have "... = taylor_shift 1 (reverse_poly (scale_poly (b - a) (taylor_shift a p)))"
    unfolding taylor_shift_def by simp
  finally have Poly_L4: "Poly ?L4 = fast_descartes_transform a b p"
    unfolding fast_descartes_transform_def by simp

  have "fast_descartes_list a b (coeffs p) = sign_changes_fold ?L4"
    unfolding fast_descartes_list_def by simp
  also have "... = Descartes_Sign_Rule.sign_changes (coeffs (Poly ?L4))"
    using sign_changes_fold_Poly by simp
  also have "... = Descartes_Sign_Rule.sign_changes (coeffs (fast_descartes_transform a b p))"
    using Poly_L4 by simp
  also have "... = fast_descartes_roots_test a b p"
    unfolding fast_descartes_roots_test_def by simp
  also have "... = descartes_roots_test_sc_rat a b p"
    using fast_descartes assms by simp
  finally show ?thesis .
qed

end