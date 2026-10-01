theory Bernstein_Split

imports
  Main
  List_Changes
  Three_Circles.Bernstein
begin

text \<open>Bernstein-basis splitting: the coefficient identities behind the de Casteljau split.
  Layer: FUNCTIONAL SPEC.
  Main exports: \<open>Bernstein_changes_01_eq_sign_changes\<close> and the split/elevation transport lemmas.\<close>

lemma Bernstein_changes_01_eq_sign_changes:
  "Bernstein_changes_01 p P = sign_changes (Bernstein_coeffs_01 p P)"
proof -
  have "Bernstein_changes_01 p P = nat (changes (Bernstein_coeffs_01 p P))"
    by (simp add: Bernstein_changes_01_def)
  also have "... = nat (int (sign_changes (Bernstein_coeffs_01 p P)))"
    by (simp add: changes_eq_sign_changes)
  also have "... = sign_changes (Bernstein_coeffs_01 p P)"
    by simp
  finally show ?thesis .
qed

theorem Bernstein_changes_01_split:
  assumes t0: "0 < t" and t1: "t < 1" and deg: "degree P \<le> p"
  shows "Bernstein_changes_01 p (P \<circ>\<^sub>p [:0, t:]) +
         Bernstein_changes_01 p (P \<circ>\<^sub>p [:t, 1-t:]) \<le> Bernstein_changes_01 p P"
proof -
  let ?xs = "Bernstein_coeffs_01 p P"

  have L: "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:0, t:]) = dc_left t ?xs"
    using Bernstein_coeffs_01_split_left[OF deg] .
  have R: "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:t, 1-t:]) = dc_right t ?xs"
    using Bernstein_coeffs_01_split_right[OF deg] .

  have sc: "sign_changes (dc_left t ?xs) + sign_changes (dc_right t ?xs)
            \<le> sign_changes ?xs"
    using sign_changes_dc_split[OF t0 t1] 
    by (simp add: sign_changes_final t0 t1)

  show ?thesis
    unfolding Bernstein_changes_01_def L R
    by (metis changes_eq_sign_changes nat_int of_nat_add of_nat_le_iff sc)
qed


lemma Bernstein_changes_split:
  fixes P :: "real poly"
  assumes ac: "a < c" and cb: "c < b" 
      and deg: "degree P \<le> p"
  shows "Bernstein_changes p a c P + Bernstein_changes p c b P \<le> Bernstein_changes p a b P"
proof -
  let ?t = "(c - a) / (b - a)"

  from ac cb have ab: "a < b" by simp
  then have anb : "a \<noteq> b" by simp
  have t_pos: "0 < ?t" using ac ab by simp
  have t_less: "?t < 1" using cb ab by (simp add: field_simps)

  define Q where "Q = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]"
  have degQ: "degree Q \<le> p" 
    using deg Q_def by (simp)

  have "Bernstein_changes p a b P = Bernstein_changes_01 p Q"
    using Bernstein_changes_eq_rescale[OF \<open>a \<noteq> b\<close> deg] Q_def by simp

  moreover have "Bernstein_changes p a c P = Bernstein_changes_01 p (Q \<circ>\<^sub>p [:0, ?t:])"
  proof -
    have "Q \<circ>\<^sub>p [:0, ?t:] = (P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]) \<circ>\<^sub>p [:0, (c - a) / (b - a):]"
      unfolding Q_def by simp
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:0, (c - a) / (b - a):])"
      by (simp add: pcompose_assoc)
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, c - a:]"
      using \<open>a < b\<close> by (simp add: pcompose_pCons)
    finally have "Q \<circ>\<^sub>p [:0, ?t:] = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, c - a:]" .
    
    then show ?thesis
      using Bernstein_changes_eq_rescale ac deg by auto
  qed

  moreover have "Bernstein_changes p c b P = Bernstein_changes_01 p (Q \<circ>\<^sub>p [:?t, 1 - ?t:])"
  proof -
    have "1 - ?t = (b - c) / (b - a)"
      using ab by (simp add: field_simps)
      
    have "Q \<circ>\<^sub>p [:?t, 1 - ?t:] = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:]"
      unfolding Q_def by simp
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:])"
      by (simp add: pcompose_assoc)

    have "[:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:] = [: (b-a)*?t, (b-a)*(1-?t) :]"
      by (simp add: pcompose_pCons)

    then have composite: "[:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:] = [: c - a, b - c :]" 
      using \<open>1 - (c - a) / (b - a) = (b - c) / (b - a)\<close> by fastforce

    then have "Q \<circ>\<^sub>p [:?t, 1 - ?t:] = P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, b - c:]"
    by (smt (verit, del_insts) Q_def add_pCons mult.right_neutral one_poly_eq_simps(2)
        pcompose_assoc pcompose_const pcompose_pCons)
      
    then show ?thesis
      using Bernstein_changes_eq_rescale cb deg by force
  qed

  ultimately show ?thesis
    using Bernstein_changes_01_split[OF t_pos t_less degQ]
    by simp
qed


lemma reflect_linear_poly:
  fixes a b :: "'a::zero_neq_one"
  assumes "b \<noteq> 0"
  shows "reflect_poly [:a, b:] = [:b, a:]"
proof -
  have "pCons b 0 \<noteq> 0" using assms by (simp )
  
  have "coeffs [:a, b:] = coeffs (pCons a (pCons b 0))" by simp
  also have "\<dots> = a # coeffs (pCons b 0)"
    using \<open>pCons b 0 \<noteq> 0\<close> by (simp )
  also have "\<dots> = a # b # coeffs 0"
    using assms by (simp )
  also have "\<dots> = [a, b]" by simp
  finally have coeffs_eq: "coeffs [:a, b:] = [a, b]"
    using \<open>a # coeffs [:b:] = a # b # coeffs 0\<close> coeffs_0_eq_Nil by force

  have "rev (coeffs [:a, b:]) = [b, a]" using coeffs_eq by simp
  then have "Poly (rev (coeffs [:a, b:])) = Poly [b, a]" by simp
  also have "\<dots> = [:b, a:]" by simp
  finally show ?thesis unfolding reflect_poly_def .
qed



lemma Bernstein_boundary_invariance_left:
  assumes P_eq: "P = R * [:-t, 1:]" 
      and t_pos: "t > 0"
      and deg: "degree P \<le> p"
      and P_nz: "P \<noteq> 0"
  shows "Bernstein_changes_01 p (P \<circ>\<^sub>p [:0, t:]) = Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:0, t:])"
proof -
  let ?P_L = "P \<circ>\<^sub>p [:0, t:]"
  let ?R_L = "R \<circ>\<^sub>p [:0, t:]"
  
  have "[: -t, 1 :] \<circ>\<^sub>p [:0, t:] = [: -t, t :]"
    by (simp add: pcompose_pCons)
  also have "\<dots> = smult t [: -1, 1 :]"
    by simp
  finally have lin_trans: "[: -t, 1 :] \<circ>\<^sub>p [:0, t:] = smult t [: -1, 1 :]" .
  
  have P_L_eq: "?P_L = smult t (?R_L * [: -1, 1 :])"
    using P_eq 
    by (metis lin_trans mult_smult_right pcompose_mult)
  
  have deg_R: "degree R \<le> p - 1" 
    using deg P_eq 
    by (metis (no_types, lifting) ext Nat.le_diff_conv2 One_nat_def Suc_pred add_gr_0
        degree_0 degree_mult_eq degree_pCons_eq_if diff_is_0_eq' le_add_diff_inverse
        le_eq_less_or_eq linorder_not_less one_neq_zero one_pCons
        zero_less_one_class.zero_le_one)
  hence deg_R_L: "degree ?R_L \<le> p - 1"
    by simp
    

  let ?rec_P = "reciprocal_poly p ?P_L"
  let ?rec_R = "reciprocal_poly (p - 1) ?R_L"
  
  have rec_eq: "?rec_P = smult t (?rec_R * [: 1, -1 :])" 
  proof -
    have "reflect_poly [: (-1), 1 :] = [: 1, (-1)::real :]"
      by (simp add: reflect_linear_poly)
      
    have "reciprocal_poly p (?R_L * [: (-1)::real, 1 :]) = ?rec_R * [: 1, (-1)::real :]"
      by (smt (verit) One_nat_def P_L_eq \<open>reflect_poly [:- 1, 1:] = [:1, - 1:]\<close> deg
          deg_R_L degree_mult_eq degree_pCons_eq_if degree_pcompose degree_smult_eq
          diff_diff_left mult.assoc mult.commute mult.right_neutral mult_cancel_left
          pCons_eq_0_iff reciprocal_0_iff reciprocal_reflect_poly reflect_poly_mult
          t_pos)
    
    thus ?thesis using P_L_eq reciprocal_smult
      by (smt (verit, best) One_nat_def deg degree_pCons_eq_if degree_pcompose
          degree_smult_eq mult.right_neutral pCons_eq_0_iff t_pos)
  qed

  let ?Q_P = "?rec_P \<circ>\<^sub>p [:1, 1:]"
  let ?Q_R = "?rec_R \<circ>\<^sub>p [:1, 1:]"
  
  have "?Q_P = smult t (?Q_R * ([: 1, (-1)::real :] \<circ>\<^sub>p [: 1, 1 :]))"
    unfolding rec_eq 
    by (metis pcompose_mult pcompose_smult)
    
  have "[: 1, (-1)::real :] \<circ>\<^sub>p [: 1, 1 :] = [: 0, (-1)::real :]"
    unfolding pcompose_pCons by simp
    
  have Q_P_eq: "?Q_P = smult (-t) (pCons 0 ?Q_R)"
    using \<open>[:1, - 1:] \<circ>\<^sub>p [:1, 1:] = [:0, - 1:]\<close>
      \<open>reciprocal_poly p (P \<circ>\<^sub>p [:0, t:]) \<circ>\<^sub>p [:1, 1:] = smult t (reciprocal_poly (p - 1) (R \<circ>\<^sub>p [:0, t:]) \<circ>\<^sub>p [:1, 1:] * [:1, - 1:] \<circ>\<^sub>p [:1, 1:])\<close>
      minus_pCons mult.commute mult_smult_right smult_minus_left by auto
  have "changes (coeffs ?Q_P) = changes (coeffs (smult (-t) (pCons 0 ?Q_R)))"
    using Q_P_eq by simp
  also have "\<dots> = changes (coeffs (pCons 0 ?Q_R))"
    using t_pos changes_scale_const[of "-t"] 
    by (smt (verit, ccfv_threshold) coeffs_smult)
  also have "\<dots> = changes (coeffs ?Q_R)"
    using changes_pCons by simp
  finally show ?thesis
    unfolding Bernstein_changes_01_def 
    by (smt (verit, del_insts) Bernstein_changes_01_def'
        Bernstein_changes_01_eq_changes Bernstein_coeffs_01_def One_nat_def deg deg_R_L
        degree_pCons_eq_if degree_pcompose mult.right_neutral pCons_eq_0_iff
        t_pos)
qed

lemma Bernstein_boundary_invariance_right:
  assumes P_eq: "P = R * [:-t, (1::real):]" 
      and t_less: "t < 1"
      and deg: "degree P \<le> p"
      and P_nz: "P \<noteq> 0"
  shows "Bernstein_changes_01 p (P \<circ>\<^sub>p [:t, 1-t:]) = Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:t, 1-t:])"
proof -
  let ?S = "1 - t"
  let ?P_R = "P \<circ>\<^sub>p [:t, ?S:]"
  let ?R_R = "R \<circ>\<^sub>p [:t, ?S:]"
  
  have S_pos: "?S > 0" using t_less by simp
  
  have "[: -t, 1 :] \<circ>\<^sub>p [:t, ?S:] = [: -t + t, ?S :]"
    by (simp add: pcompose_pCons)
  also have "\<dots> = smult ?S [: 0, 1 :]"
    by (simp)
  finally have lin_trans: "[: -t, 1 :] \<circ>\<^sub>p [:t, ?S:] = smult ?S [: 0, 1 :]" .
  
  have P_R_eq: "?P_R = smult ?S (?R_R * [: 0, 1 :])"
    using P_eq 
    by (metis lin_trans mult_smult_right pcompose_mult)

  have deg_R: "degree R \<le> p - 1" 
    using deg P_eq 
    by (metis (no_types, lifting) ext Nat.le_diff_conv2 One_nat_def Suc_pred add_gr_0 
        degree_0 degree_mult_eq degree_pCons_eq_if diff_is_0_eq' le_add_diff_inverse 
        le_eq_less_or_eq linorder_not_less one_neq_zero one_pCons 
        zero_less_one_class.zero_le_one)
  hence deg_R_R: "degree ?R_R \<le> p - 1"
    by simp

  let ?rec_P = "reciprocal_poly p ?P_R"
  let ?rec_R = "reciprocal_poly (p-1) ?R_R"
  
  have rec_eq: "?rec_P = smult ?S ?rec_R"
  proof -
    have "reflect_poly [: 0, (1::real) :] = [: 1, (0::real) :]"
      by (simp add: reflect_linear_poly)
      
    have "reciprocal_poly p (?R_R * [: 0, (1::real) :]) = ?rec_R * [: 1 :]"
      by (smt (verit) One_nat_def P_R_eq S_pos \<open>reflect_poly [:0, 1:] = [:1, 0:]\<close> deg 
          deg_R_R degree_mult_eq degree_pCons_eq_if degree_pcompose degree_smult_eq 
          diff_diff_left mult.assoc mult.commute mult.right_neutral mult_cancel_left 
          pCons_eq_0_iff reciprocal_0_iff reciprocal_reflect_poly reflect_poly_mult)
    
    also have "\<dots> = ?rec_R" by simp
    
    finally show ?thesis 
      using P_R_eq reciprocal_smult 
      by (smt (verit, ccfv_threshold) \<open>[:- t + t, 1 - t:] = smult (1 - t) [:0, 1:]\<close> deg
          degree_pCons_eq_if degree_pcompose degree_smult_eq pcompose_idR t_less)
  qed

  let ?Q_P = "?rec_P \<circ>\<^sub>p [:1, 1:]"
  let ?Q_R = "?rec_R \<circ>\<^sub>p [:1, 1:]"
  
  have "?Q_P = smult ?S (?Q_R * ([: 1 :] \<circ>\<^sub>p [: 1, 1 :]))"
    unfolding rec_eq 
    by (simp add: pcompose_smult)
    
  have "[: 1 :] \<circ>\<^sub>p [: 1, 1 :] = [: 1 :]"
    by (simp add: pcompose_pCons)
    
  have Q_P_eq: "?Q_P = smult ?S ?Q_R"
    using \<open>[: 1 :] \<circ>\<^sub>p [: 1, 1 :] = ...\<close> 
      \<open>reciprocal_poly p (P \<circ>\<^sub>p [:t, 1 - t:]) \<circ>\<^sub>p [:1, 1:] = smult (1 - t) (reciprocal_poly (p - 1) (R \<circ>\<^sub>p [:t, 1 - t:]) \<circ>\<^sub>p [:1, 1:] * [:1:] \<circ>\<^sub>p [:1, 1:])\<close>
    by auto

  have "changes (coeffs ?Q_P) = changes (coeffs (smult ?S ?Q_R))"
    using Q_P_eq by simp
  also have "\<dots> = changes (coeffs ?Q_R)"
    using S_pos changes_scale_const[of "?S"] 
    by (smt (verit, ccfv_threshold) coeffs_smult)
  finally show ?thesis
    unfolding Bernstein_changes_01_def 
    by (smt (verit, del_insts) Bernstein_changes_01_def' 
        Bernstein_changes_01_eq_changes Bernstein_coeffs_01_def One_nat_def deg deg_R_R 
        degree_pCons_eq_if degree_pcompose mult.right_neutral pCons_eq_0_iff S_pos)
qed


lemma Bernstein_changes_01_split_root:
  assumes t_pos: "0 < t" and t_less: "t < 1" 
      and deg: "degree P \<le> p"
      and root: "poly P t = 0"
      and P_nz: "P \<noteq> 0"
  shows "Bernstein_changes_01 p (P \<circ>\<^sub>p [:0, t:]) + 
         Bernstein_changes_01 p (P \<circ>\<^sub>p [:t, 1-t:]) + 1 \<le> Bernstein_changes_01 p P"
proof -
  obtain R where P_eq: "P = [:-t, 1:] * R"
    using root poly_eq_0_iff_dvd by (metis dvdE)
  
  have R_nz: "R \<noteq> 0" using P_nz P_eq by auto
  have deg_R: "degree R = degree P - 1" using P_eq R_nz 
    by (smt (verit, ccfv_SIG) add.right_neutral degree_synthetic_div mult_left_cancel
        pCons_0_0 pCons_eq_iff root synthetic_div_correct')
  
  let ?Trans = "\<lambda>f. reciprocal_poly (degree f) f \<circ>\<^sub>p [:1, 1:]"

  have lin_trans: "?Trans [:-t, 1:] = [:1 - t, -t:]"
    unfolding reciprocal_poly_def 
    by (auto simp: pcompose_pCons monom_altdef Poly_append)

  let ?a = "(1-t)/t"
  have a_pos: "?a > 0" using t_pos t_less by (simp add: field_simps)

  have "[:1 - t, -t:] = smult t [:?a, -1:]"
    using t_pos by (simp add: field_simps)
  
  define Q_R where "Q_R = reciprocal_poly (p-1) R \<circ>\<^sub>p [:1, 1:]"
  define Q_P where "Q_P = reciprocal_poly p P \<circ>\<^sub>p [:1, 1:]"
  
  have "changes (coeffs Q_P) \<ge> changes (coeffs Q_R) + 1"
  proof -
    have "reciprocal_poly p P = reciprocal_poly p ([:-t, 1:] * R)"
      using P_eq by simp

      have "changes (coeffs Q_P) \<ge> changes (coeffs Q_R) + 1"
  proof -
    have deg_lin: "degree [:-t, 1:] = 1" by simp
    have "degree P = 1 + degree R"
      using P_eq R_nz 
    by (metis deg_lin degree_0 degree_mult_eq one_neq_zero)
    have "reciprocal_poly p P = monom 1 (p - degree P) * reflect_poly P"
      using reciprocal_reflect_poly[OF deg] .
    also have "\<dots> = monom 1 (p - (1 + degree R)) * (reflect_poly [:-t, 1:] * reflect_poly R)"
      using P_eq \<open>degree P = 1 + degree R\<close> reflect_poly_mult
      by metis
    also have "\<dots> = (reflect_poly [:-t, 1:]) * (monom 1 ((p - 1) - degree R) * reflect_poly R)"
      by (simp add: mult.assoc mult.left_commute)
    also have "\<dots> = [:1, -t:] * reciprocal_poly (p - 1) R"
    proof -
      have "reciprocal_poly (p - 1) R = monom 1 ((p - 1) - degree R) * reflect_poly R"
        apply (rule reciprocal_reflect_poly)
        using deg \<open>degree P = 1 + degree R\<close> by simp
      moreover have "reflect_poly [:-t, 1:] = [:1, -t:]"
        unfolding reflect_poly_def by (simp add: coeffs_eq_iff)
      ultimately show ?thesis by simp
    qed
    finally have rec_eq: "reciprocal_poly p P = [:1, -t:] * reciprocal_poly (p - 1) R" .
    
    have "Q_P = ([:1, -t:] * reciprocal_poly (p - 1) R) \<circ>\<^sub>p [:1, 1:]"
      unfolding Q_P_def rec_eq ..
    also have "\<dots> = ([:1, -t:] \<circ>\<^sub>p [:1, 1:]) * (reciprocal_poly (p - 1) R \<circ>\<^sub>p [:1, 1:])"
    using pcompose_mult by blast
    also have "\<dots> = ([:1, -t:] \<circ>\<^sub>p [:1, 1:]) * Q_R"
      unfolding Q_R_def by simp
    finally have Q_P_factor: "Q_P = ([:1, -t:] \<circ>\<^sub>p [:1, 1:]) * Q_R" .

    have "[:1, -t:] \<circ>\<^sub>p [:1, 1:] = [:1, -t:] \<circ>\<^sub>p ([:1:] + monom 1 1)"
      using pCons_one
      by (metis mult.right_neutral pcompose_idR pcompose_pCons x_as_monom)

    have "[:1, -t:] \<circ>\<^sub>p [:1, 1:] = [:1:] + smult (-t) [:1, 1:]"
      unfolding pcompose_pCons by simp
    also have "\<dots> = [:1:] + [:-t, -t:]"
      by (simp add: smult_add_left)
    also have "\<dots> = [:1 - t, -t:]"
      by simp
    finally have lin_trans_eq: "[:1, -t:] \<circ>\<^sub>p [:1, 1:] = [:1 - t, -t:]" .
    
    let ?a = "(1 - t) / t"
    have a_pos: "?a > 0" using t_pos t_less by (simp add: field_simps)
    
    have "[:1 - t, -t:] = smult t [:?a, -1:]"
      using t_pos by (simp add: field_simps)
      
    hence "Q_P = smult t ([:?a, -1:] * Q_R)"
      using Q_P_factor lin_trans_eq
      by (metis mult_smult_left)
    
    have "changes (coeffs Q_P) = changes (coeffs (smult t ([:?a, -1:] * Q_R)))"
      by (simp add: \<open>Q_P = ...\<close>)
    also have "\<dots> = changes (coeffs ([:?a, -1:] * Q_R))"
      using t_pos changes_scale_const 
      by (smt (verit) coeffs_smult)
    also have "changes (coeffs Q_P) \<ge> changes (coeffs Q_R) + 1"
    proof -
      have "Q_R \<noteq> 0" 
        unfolding Q_R_def using R_nz deg_R deg 
      by (metis (no_types, opaque_lifting) P_nz add.commute diff_add_cancel
          mult.right_neutral mult_zero_right one_poly_eq_simps(1) pcompose_0
          pcompose_assoc pcompose_idR pcompose_pCons rec_eq reciprocal_0_iff)
      
      have lemma_result: "changes (coeffs ([:?a, -1:] * Q_R)) - changes (coeffs Q_R) > 0"
        using sign_changes_poly_times_root_minus_x[OF \<open>Q_R \<noteq> 0\<close> a_pos] changes_eq_sign_changes
        by (metis (mono_tags, opaque_lifting) int_ops(6) less_numeral_extra(3)
            of_nat_0_less_iff)
      have "changes (coeffs ([:?a, -1:] * Q_R)) \<ge> changes (coeffs Q_R) + 1"
        using lemma_result by simp

      have "coeffs Q_P = map ((*) t) (coeffs ([:?a, -1:] * Q_R))"
        using \<open>Q_P = smult t ([:?a, -1:] * Q_R)\<close> 
        by (metis coeffs_smult order_less_irrefl t_pos)
      
      hence "changes (coeffs Q_P) = changes (coeffs ([:?a, -1:] * Q_R))"
        using changes_scale_const[of t] t_pos by simp
        
      show ?thesis 
        using \<open>changes (coeffs ([:?a, -1:] * Q_R)) \<ge> changes (coeffs Q_R) + 1\<close> 
        using calculation by presburger
    qed
    finally show ?thesis 
      using \<open>changes (coeffs Q_R) + 1 \<le> changes (coeffs Q_P)\<close> by force
  qed
  show ?thesis
    by (simp add: \<open>changes (coeffs Q_R) + 1 \<le> changes (coeffs Q_P)\<close>)
qed
  
  hence V_diff: "Bernstein_changes_01 p P \<ge> Bernstein_changes_01 (p-1) R + 1"
    unfolding Bernstein_changes_01_eq_changes
    using Q_P_def Q_R_def
  by (simp add: Bernstein_changes_01_eq_changes deg deg_R diff_le_mono)
  have split_R: "Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:0, t:]) + 
                 Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:t, 1-t:]) 
                 \<le> Bernstein_changes_01 (p-1) R"
    using Bernstein_changes_01_split[OF t_pos t_less] 
    using deg_R deg by simp

  have V_left: "Bernstein_changes_01 p (P \<circ>\<^sub>p [:0, t:]) = Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:0, t:])"
    using Bernstein_boundary_invariance_left P_eq P_nz deg t_pos by auto
    
  have V_right: "Bernstein_changes_01 p (P \<circ>\<^sub>p [:t, 1-t:]) = Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:t, 1-t:])"
    using Bernstein_boundary_invariance_right P_eq P_nz deg t_pos t_less by auto

  have "Bernstein_changes_01 p (P \<circ>\<^sub>p [:0, t:]) + Bernstein_changes_01 p (P \<circ>\<^sub>p [:t, 1-t:]) + 1
        = Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:0, t:]) + Bernstein_changes_01 (p-1) (R \<circ>\<^sub>p [:t, 1-t:]) + 1"
    using V_left V_right by simp
  also have "\<dots> \<le> Bernstein_changes_01 (p-1) R + 1"
    using split_R by simp
  also have "\<dots> \<le> Bernstein_changes_01 p P"
    using V_diff by simp
  finally show ?thesis .
qed

lemma Bernstein_changes_split_root:
  fixes P :: "real poly"
  assumes ac: "a < c" and cb: "c < b" and root : "poly P c = 0"
      and deg: "degree P \<le> p" and P_nz: "P \<noteq> 0"
  shows "Bernstein_changes p a c P + Bernstein_changes p c b P + 
         1 \<le> Bernstein_changes p a b P"
proof -
  let ?t = "(c - a) / (b - a)"

  from ac cb have ab: "a < b" by simp
  then have anb : "a \<noteq> b" by simp
  have t_pos: "0 < ?t" using ac ab by simp
  have t_less: "?t < 1" using cb ab by (simp add: field_simps)

  define Q where "Q = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]"
  have degQ: "degree Q \<le> p" 
    using deg Q_def by (simp)

  have term_total: "Bernstein_changes p a b P = Bernstein_changes_01 p Q"
    using Bernstein_changes_eq_rescale[OF \<open>a \<noteq> b\<close> deg] Q_def by simp

  have term_left: "Bernstein_changes p a c P = Bernstein_changes_01 p (Q \<circ>\<^sub>p [:0, ?t:])"
  proof -
    have "Q \<circ>\<^sub>p [:0, ?t:] = (P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]) \<circ>\<^sub>p [:0, (c - a) / (b - a):]"
      unfolding Q_def by simp
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:0, (c - a) / (b - a):])"
      by (simp add: pcompose_assoc)
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, c - a:]"
      using \<open>a < b\<close> by (simp add: pcompose_pCons)
    finally have "Q \<circ>\<^sub>p [:0, ?t:] = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, c - a:]" .
    
    then show ?thesis
      using Bernstein_changes_eq_rescale ac deg by force
  qed

  have term_right: "Bernstein_changes p c b P = Bernstein_changes_01 p (Q \<circ>\<^sub>p [:?t, 1 - ?t:])"
  proof -
    have "1 - ?t = (b - c) / (b - a)"
      using ab by (simp add: field_simps)
      
    have "Q \<circ>\<^sub>p [:?t, 1 - ?t:] = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:]"
      unfolding Q_def by simp
    also have "\<dots> = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:])"
      by (simp add: pcompose_assoc)
    
    have "[:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:] = [: (b-a)*?t, (b-a)*(1-?t) :]"
      by (simp add: pcompose_pCons)
    have "\<dots> = [: c - a, b - c :]"
      using ab \<open>1 - ?t = (b - c) / (b - a)\<close> by fastforce
    have composite: "[:0, b - a:] \<circ>\<^sub>p [:?t, 1 - ?t:] = [: c - a, b - c :]" 
      using
        \<open>[:(b - a) * ((c - a) / (b - a)), (b - a) * (1 - (c - a) / (b - a)):] = [:c - a, b - c:]\<close>
        \<open>[:0, b - a:] \<circ>\<^sub>p [:(c - a) / (b - a), 1 - (c - a) / (b - a):] = [:(b - a) * ((c - a) / (b - a)), (b - a) * (1 - (c - a) / (b - a)):]\<close>
      by presburger
    have "P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:c - a, b - c:] = P \<circ>\<^sub>p ([:a, 1:] \<circ>\<^sub>p [:c - a, b - c:])"
      by (simp add: pcompose_assoc)
    have "[:a, 1:] \<circ>\<^sub>p [:c - a, b - c:] = [:c, b - c:]"
      by (simp add: pcompose_pCons)
    have "\<dots> = [:c, 1:] \<circ>\<^sub>p [:0, b - c:]"
      by (simp add: pcompose_pCons)
    have "Q \<circ>\<^sub>p [:?t, 1 - ?t:] = P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, b - c:]"
      using composite
    by (metis Q_def \<open>[:a, 1:] \<circ>\<^sub>p [:c - a, b - c:] = [:c, b - c:]\<close>
        \<open>[:c, b - c:] = [:c, 1:] \<circ>\<^sub>p [:0, b - c:]\<close> pcompose_assoc)
      
    then show ?thesis
      using Bernstein_changes_eq_rescale cb deg by force
  qed

  have root_eq: "(poly P c = 0) \<longleftrightarrow> (poly Q ?t = 0)"
  proof -
    have "poly Q ?t = poly (P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]) ?t"
      unfolding Q_def by simp
    also have "\<dots> = poly P (poly [:a, 1:] (poly [:0, b - a:] ?t))"
      by (simp add: poly_pcompose)
    also have "\<dots> = poly P (poly [:a, 1:] (?t * (b - a)))"
      by simp
    also have "\<dots> = poly P (a + (c - a))"
      using ab by simp
    also have "\<dots> = poly P c"
      by simp
    finally show ?thesis by simp
  qed

  then have rootQ:  "poly Q ?t = 0" 
    using root by blast

  have Qnz: "Q \<noteq> 0" using P_nz 
    by (metis Q_def Suc_eq_plus1 add_0 bot_nat_0.not_eq_extremum degree_pCons_eq_if
        divide_eq_0_iff less_irrefl one_neq_zero pCons_0_0 pCons_eq_iff pcompose_eq_0
        t_pos)

  show ?thesis
    using Bernstein_changes_01_split_root[OF t_pos t_less degQ rootQ Qnz]
    using term_left term_right term_total by presburger
qed

lemma Bernstein_coeffs_split:
  fixes P :: "real poly"
  assumes ac: "a < c" and cb: "c < b"
      and deg: "degree P \<le> p"
  defines "t \<equiv> (c - a) / (b - a)"
  shows
    "Bernstein_coeffs p a c P = dc_left t (Bernstein_coeffs p a b P)"
    "Bernstein_coeffs p c b P = dc_right t (Bernstein_coeffs p a b P)"
proof -
  have ab: "a < b" using ac cb by linarith
  have anb: "a \<noteq> b" using ab by simp
  have anc: "a \<noteq> c" using ac by simp
  have cnb: "c \<noteq> b" using cb by simp

  define Q where "Q = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, b - a:]"
  have degQ: "degree Q \<le> p"
    using deg by (simp add: Q_def)

  have coeff_ab:
    "Bernstein_coeffs p a b P = Bernstein_coeffs_01 p Q"
    using Bernstein_coeffs_eq_rescale[OF anb]  
    by (simp add: Q_def)

  have Q_left:
    "Q \<circ>\<^sub>p [:0, t:] = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, c - a:]"
  proof -
    have "Q \<circ>\<^sub>p [:0, t:]
        = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:0, t:])"
      by (simp add: Q_def pcompose_assoc)
    also have "[:0, b - a:] \<circ>\<^sub>p [:0, t:] = [:0, (b - a) * t:]"
      by (simp add: pcompose_pCons)
    also have "(b - a) * t = c - a"
      using ab by (simp add: t_def field_simps)
    finally show ?thesis
      by (simp add: pcompose_assoc)
  qed

  have coeff_ac:
    "Bernstein_coeffs p a c P =
     Bernstein_coeffs_01 p (Q \<circ>\<^sub>p [:0, t:])"
  proof -
    have "Bernstein_coeffs p a c P =
          Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, c - a:])"
      using Bernstein_coeffs_eq_rescale[OF anc]  
      by simp
    also have "... = Bernstein_coeffs_01 p (Q \<circ>\<^sub>p [:0, t:])"
      by (simp add: Q_left)
    finally show ?thesis .
  qed

  have Q_right:
    "Q \<circ>\<^sub>p [:t, 1 - t:] = P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, b - c:]"
  proof -
    have "Q \<circ>\<^sub>p [:t, 1 - t:]
        = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:t, 1 - t:])"
      by (simp add: Q_def pcompose_assoc)
    also have "[:0, b - a:] \<circ>\<^sub>p [:t, 1 - t:] = [:(b - a) * t, (b - a) * (1 - t):]"
      by (simp add: pcompose_pCons)
    also have "(b - a) * t = c - a"
      using ab by (simp add: t_def field_simps)
    also have "(b - a) * (1 - t) = b - c"
      using ab by (simp add: t_def field_simps)
    finally have inner:
      "[:0, b - a:] \<circ>\<^sub>p [:t, 1 - t:] = [:(c - a), b - c:]"
      using \<open>(b - a) * (1 - t) = b - c\<close> \<open>(b - a) * t = c - a\<close>
        \<open>[:0, b - a:] \<circ>\<^sub>p [:t, 1 - t:] = [:(b - a) * t, (b - a) * (1 - t):]\<close> by presburger

    have "P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:(c - a), b - c:]
        = P \<circ>\<^sub>p [:c, b - c:]"
      by (smt (verit, del_insts) add_0 add_pCons mult.right_neutral one_pCons pcompose_assoc pcompose_const
          pcompose_pCons)
    also have "... = P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, b - c:]"
      by (metis (no_types, opaque_lifting) mult.comm_neutral pCons_0_as_mult pcompose_1 pcompose_assoc
          pcompose_idR pcompose_pCons)
    finally show ?thesis
      using inner \<open>Q \<circ>\<^sub>p [:t, 1 - t:] = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p ([:0, b - a:] \<circ>\<^sub>p [:t, 1 - t:])\<close> by presburger
  qed

  have coeff_cb:
    "Bernstein_coeffs p c b P =
     Bernstein_coeffs_01 p (Q \<circ>\<^sub>p [:t, 1 - t:])"
  proof -
    have "Bernstein_coeffs p c b P =
          Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:c, 1:] \<circ>\<^sub>p [:0, b - c:])"
      using Bernstein_coeffs_eq_rescale[OF cnb]  
      by simp
    also have "... = Bernstein_coeffs_01 p (Q \<circ>\<^sub>p [:t, 1 - t:])"
      by (simp add: Q_right)
    finally show ?thesis .
  qed

  have L01:
    "Bernstein_coeffs_01 p (Q \<circ>\<^sub>p [:0, t:]) =
     dc_left t (Bernstein_coeffs_01 p Q)"
    using Bernstein_coeffs_01_split_left[OF degQ] .

  have R01:
    "Bernstein_coeffs_01 p (Q \<circ>\<^sub>p [:t, 1 - t:]) =
     dc_right t (Bernstein_coeffs_01 p Q)"
    using Bernstein_coeffs_01_split_right[OF degQ] .

  show "Bernstein_coeffs p a c P = dc_left t (Bernstein_coeffs p a b P)"
    using coeff_ac coeff_ab L01 by simp

  show "Bernstein_coeffs p c b P = dc_right t (Bernstein_coeffs p a b P)"
    using coeff_cb coeff_ab R01 by simp
qed

lemma Bernstein_coeffs_split_mid:
  fixes P :: "real poly"
  assumes ab: "a < b" and deg: "degree P \<le> p"
  defines "m \<equiv> (a + b) / 2"
  shows
    "Bernstein_coeffs p a m P = dc_left (1/2) (Bernstein_coeffs p a b P)"
    "Bernstein_coeffs p m b P = dc_right (1/2) (Bernstein_coeffs p a b P)"
proof -
  have am: "a < m" and mb: "m < b"
    using ab by (simp_all add: m_def)

  have t_half: "(m - a) / (b - a) = (1/2::real)"
    using ab by (simp add: m_def field_simps)

  have L:
    "Bernstein_coeffs p a m P =
     dc_left ((m - a) / (b - a)) (Bernstein_coeffs p a b P)"
    using Bernstein_coeffs_split(1) am deg mb by blast

  have R:
    "Bernstein_coeffs p m b P =
     dc_right ((m - a) / (b - a)) (Bernstein_coeffs p a b P)"
    using Bernstein_coeffs_split(2) am deg mb by blast

  show "Bernstein_coeffs p a m P = dc_left (1/2) (Bernstein_coeffs p a b P)"
    using L by (simp add: t_half)

  show "Bernstein_coeffs p m b P = dc_right (1/2) (Bernstein_coeffs p a b P)"
    using R by (simp add: t_half)
qed




end