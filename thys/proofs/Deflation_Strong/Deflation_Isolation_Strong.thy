theory Deflation_Isolation_Strong
  imports
    IsaRRI_Refine.Isolation_Contract
    IsaRRI_Refine.Kiou_Bound_Defl_Reflect
begin

text \<open>\<^bold>\<open>The deflating path of the solver, proven to emit pairwise-disjoint windows above the
  origin.\<close> @{thm [source] defl_isolate_all_split_main_correct} gives, per half, soundness
  (@{const defl_acc_isolates}) and strict-or-degenerate coverage (@{const defl_acc_covers}).
  This theory adds the two missing clauses of the isolation contract: the emitted windows are
  pairwise disjoint (@{const iv_disj_mset}) and every point of every window is positive.

  \<^bold>\<open>The route is one geometric invariant carried beside the existing loop bundle\<close>,
  \<open>defl_geom\<close>: the accumulated windows together with the pending worklist boxes are
  pairwise disjoint, lie above \<open>glo\<close>, and every pending box is proper. That machinery, and the
  geometry-carrying loop capstone \<open>defl_main_list_correct_geom\<close>, live in \<open>Deflation_Loop_Geom\<close>,
  where the loop's own word budget needs them; this theory holds the two halves and the capstone.\<close>



lemma defl_split_pos_solve_half_geom:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_defl_pre xs"
  shows "defl_split_pos_solve_monadic xs
    \<le> SPEC (\<lambda>accP. dyadic_interval_vec_invar accP \<and>
        length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        defl_acc_isolates (of_int_poly (Poly xs) :: real poly) accP \<and>
        defl_acc_covers (of_int_poly (Poly xs) :: real poly) 0 accP \<and>
        iv_disj_mset (mset (defl_wins accP)) \<and>
        (\<forall>w \<in> set (defl_wins accP). \<forall>x. iv_in x w \<longrightarrow> 0 < x))"
proof -
  from pre have pre': "dsc_isolate_all_split_lin_pre xs"
    and lenb3: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    unfolding dsc_isolate_all_split_defl_pre_def by simp_all
  from pre' have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and canonxs: "coeffs (Poly xs) = xs"
    unfolding dsc_isolate_all_split_lin_pre_def by auto
  have P0: "Poly xs \<noteq> 0" using sfxs unfolding square_free_def by simp
  from pre have xs_small: "length xs < 1099511627776"
    unfolding dsc_isolate_all_split_defl_pre_def by simp
  have capY: "kiou_bound_k_monadic xs \<le> SPEC (split_cap_lin xs)"
    using pre' unfolding dsc_isolate_all_split_lin_pre_def by (simp add: Let_def)
  have capD: "kiou_bound_k_monadic xs \<le> SPEC (defl_depth_cap xs)"
    using pre unfolding dsc_isolate_all_split_defl_pre_def by (simp add: Let_def)
  \<comment> \<open>\<^bold>\<open>The two capacities have to be MERGED into one \<open>SPEC\<close>\<close>, exactly as on
     the classic side: only ONE \<open>\<le> SPEC\<close> fact fires per producer call, so a second one would
     never reach the continuation. @{thm [source] kiou_le_SPEC_conj} is what makes that legal.\<close>
  have merged: "kiou_bound_k_monadic xs \<le> SPEC (\<lambda>k.
      ((\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ k) \<and>
       k * length xs < max_snat LENGTH(gmp_poly_len) \<and>
       k < max_snat LENGTH(gmp_poly_len) \<and> split_cap_lin xs k)
      \<and> defl_depth_cap xs k)"
    by (rule kiou_le_SPEC_conj[OF kiou_bound_k_monadic_spec_capped_lin[OF len2 lastnz hr capY] capD])
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  show ?thesis
    unfolding defl_split_pos_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg merged[THEN order_trans])
    \<comment> \<open>the four ASSERT side goals, exactly as @{thm [source] hybrid_split_pos_solve_half_strong}
       takes them (the seeding chain is the same operation sequence). \<open>(cases xs)\<close>, not bare
       \<open>simp\<close>: \<open>0 < length xs\<close> normalises to \<open>xs \<noteq> []\<close>, which \<open>simp\<close> will not then
       derive from \<open>2 \<le> length xs\<close>.\<close>
    subgoal using len2 lenb by (cases xs) auto
    subgoal using lenb by simp
    subgoal premises p using p by simp
    subgoal premises p using p by simp
    subgoal premises kp for kpos
    proof -
      from kp have kpos_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ kpos"
        and kpos_cap: "kpos * length xs < max_snat LENGTH(gmp_poly_len)"
        and kpos_lt: "kpos < max_snat LENGTH(gmp_poly_len)"
        and cap_at: "split_cap_lin xs kpos"
        and depth_at: "defl_depth_cap xs kpos" by blast+
      define Pinit0 where "Pinit0 = scale_poly_list (2 ^ kpos) xs"
      define Pr where "Pr = (map_poly of_int (Poly Pinit0) :: real poly)"
      have rp_eq: "poly_copy_monadic xs \<le> RETURN xs" by (rule poly_copy_correct[OF lenb])
      have Pinit_eq: "split_init_pow2_l0_monadic kpos xs \<le> RETURN Pinit0"
        using split_init_pow2_l0_monadic_correct[OF lenb kpos_cap]
        by (simp add: Pinit0_def split_init_pow2_l0_eq_scale_poly_list)
      note sd = defl_seed_facts[OF len2 lastnz sfxs lenb3, of kpos, folded Pinit0_def]
      have len2P: "Suc 0 < length Pinit0" by (rule sd(1))
      have sfPr: "square_free (map_poly of_int (Poly Pinit0) :: real poly)" by (rule sd(2))
      have canonP: "coeffs (Poly Pinit0) = Pinit0" by (rule sd(3))
      have lenbP: "length Pinit0 + 2 < max_snat LENGTH(gmp_poly_len)" by (rule sd(4))
      have P_eqP: "Pinit0 = carried_init_same_den 0 (2 ^ 0) (2 ^ kpos) xs" by (rule sd(5))
      have rpsmallP: "length xs < 1099511627776" by (rule xs_small)
      have lenPx: "length Pinit0 = length xs" by (simp add: Pinit0_def)
      \<comment> \<open>the one length premise the bundle does NOT state: \<open>nat_bitlen\<close> is a \<open>LEAST\<close>, so
         \<open>length < 2\<^sup>4\<^sup>0\<close> caps it at 40 and the product at \<open>40 \<cdot> 2\<^sup>4\<^sup>0\<close>.\<close>
      have bl40: "nat_bitlen (length Pinit0) \<le> 40"
        unfolding nat_bitlen_def by (rule Least_le) (use rpsmallP lenPx in simp)
      have pbP: "length Pinit0 * nat_bitlen (length Pinit0) < max_snat LENGTH(gmp_poly_len)"
      proof -
        have "length Pinit0 * nat_bitlen (length Pinit0) \<le> length Pinit0 * 40"
          using bl40 by (rule mult_le_mono2)
        also have "\<dots> < 1099511627776 * 40" using rpsmallP lenPx by simp
        finally show ?thesis by (simp add: max_snat_def)
      qed
      have potform: "hybrid_root_potential (delta_defl Pr) 0
                       = int (2 ^ newton_pol_ecap + 2)
                           * int (dyadic_iv_interval_mu (delta_defl Pr) (0, 1))"
        by (simp add: hybrid_root_potential_def)
      from depth_at[unfolded defl_depth_cap_def Let_def]
      have dcap1: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                            * int (dyadic_iv_interval_mu (delta_defl Pr) (0, 1))
                   \<Longrightarrow> kD * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
        and dcap2: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                             * int (dyadic_iv_interval_mu (delta_defl Pr) (0, 1))
                    \<Longrightarrow> (kD + 1) * length xs < 1099511627776"
        unfolding Pr_def Pinit0_def by blast+
      have caps: "int (dyadic_iv_interval_mu (delta_defl Pr) (0, 1)) + 3
                    < int (max_snat LENGTH(gmp_poly_len))"
                 "hybrid_root_potential (delta_defl Pr) 0 < int (max_snat LENGTH(gmp_poly_len))"
                 "hybrid_root_potential (delta_defl Pr) 0 + 258
                    < int (max_snat LENGTH(gmp_poly_len))"
      proof -
        have n1: "1 \<le> length xs" using len2 by linarith
        show "int (dyadic_iv_interval_mu (delta_defl Pr) (0, 1)) + 3 < int (max_snat LENGTH(gmp_poly_len))"
             "hybrid_root_potential (delta_defl Pr) 0 < int (max_snat LENGTH(gmp_poly_len))"
             "hybrid_root_potential (delta_defl Pr) 0 + 258 < int (max_snat LENGTH(gmp_poly_len))"
          using defl_caps_of_depth[OF dcap2 n1] by auto
      qed
      have solver: "defl_main_list_monadic split_pipeline_e0 0 (2 ^ kpos) 0 Pinit0 xs
          \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
              length (dyadic_interval_vec_triples acc) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
              defl_acc_isolates (of_int_poly (Poly xs) :: real poly) acc \<and>
              defl_acc_covers (of_int_poly (Poly xs) :: real poly) 0 acc \<and>
              iv_disj_mset (mset (defl_wins acc)) \<and>
              (\<forall>w \<in> set (defl_wins acc). \<forall>x. iv_in x w \<longrightarrow> 0 < x))"
        apply (rule defl_main_list_correct_geom[where \<delta> = "delta_defl Pr" and glo = 0])
        \<comment> \<open>26 premises, in order. Everything \<open>\<delta>\<close>-free comes from \<open>npre\<close>, because the deflating
           precondition strengthens that bundle; only 22--26 are re-derived at \<open>delta_defl\<close>.\<close>
        subgoal by (rule defl_delta_defl_pos_always)
        subgoal by simp
        subgoal by (rule P_eqP)
        subgoal by (rule canonP)
        subgoal using sfPr unfolding square_free_def Pr_def by simp
        subgoal using sfPr unfolding Pr_def by simp
        subgoal unfolding Pr_def by simp
        subgoal using sfxs unfolding square_free_def by simp
        subgoal using sfxs by simp
        \<comment> \<open>@{const ripoly} is an \<open>abbreviation (input)\<close>, so it is ALREADY unfolded in both
           the goal and \<open>kpos_sound\<close> --- there is no \<open>ripoly_def\<close> to add.\<close>
        subgoal using kpos_sound by simp
        subgoal using len2P by simp
        subgoal using lenbP by simp
        subgoal by (simp add: max_snat_def)
        \<comment> \<open>\<open>(cases xs)\<close>, not bare \<open>simp\<close>: \<open>0 < length xs\<close> normalises to \<open>xs \<noteq> []\<close>,
           which \<open>simp\<close> will not then derive from \<open>2 \<le> length xs\<close>.\<close>
        subgoal using len2 by (cases xs) auto
        subgoal using lenb by simp
        subgoal by (simp add: max_snat_def)
        subgoal using pbP canonP by simp
        subgoal using rpsmallP lenPx canonP by (simp add: max_snat_def)
        subgoal using rpsmallP lenPx canonP by (simp add: max_sint_def)
        subgoal using rpsmallP lenPx canonP by simp
        subgoal using len2P canonP by simp
        subgoal by (rule caps(1))
        subgoal by (rule caps(2))
        subgoal by (rule caps(3))
        subgoal premises p for kD using dcap1[of kD] p canonP lenPx potform by simp
        subgoal premises p for kD using dcap2[of kD] p canonP lenPx potform by simp
        subgoal by simp
        done
      show ?thesis
        apply (refine_vcg rp_eq[THEN order_trans]
            Pinit_eq[unfolded Pinit0_def, THEN order_trans]
            mpz_pow2_monadic_spec[OF kpos_lt, THEN order_trans]
            solver[unfolded Pinit0_def, THEN order_trans])
        \<comment> \<open>the two post-copy ASSERTs at \<open>rp = xs\<close>, then the two at the seed poly\<close>
        subgoal using len2 lenb by (cases xs) auto
        subgoal using lenb by simp
        subgoal using len2P unfolding Pinit0_def[symmetric] by simp
        subgoal using lenbP unfolding Pinit0_def[symmetric] by simp
        \<comment> \<open>and the four SPEC conjuncts, which ARE \<open>solver\<close>'s postcondition\<close>
        apply (all \<open>((elim conjE, assumption); fail)?\<close>)
        done
    qed
    done
qed

lemma defl_split_neg_solve_half_geom:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_defl_pre xs"
  shows "defl_split_neg_solve_monadic xs
    \<le> SPEC (\<lambda>accQ. dyadic_interval_vec_invar accQ \<and>
        length (dyadic_interval_vec_triples accQ) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        defl_acc_isolates (of_int_poly (Poly (refl_list xs)) :: real poly) accQ \<and>
        defl_acc_covers (of_int_poly (Poly (refl_list xs)) :: real poly) 0 accQ \<and>
        iv_disj_mset (mset (defl_wins accQ)) \<and>
        (\<forall>w \<in> set (defl_wins accQ). \<forall>x. iv_in x w \<longrightarrow> 0 < x))"
proof -
  from pre have pre': "dsc_isolate_all_split_lin_pre xs"
    and lenb3: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    and xs_small: "length xs < 1099511627776"
    unfolding dsc_isolate_all_split_defl_pre_def by simp_all
  from pre' have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    unfolding dsc_isolate_all_split_lin_pre_def by auto
  have xsne: "xs \<noteq> []" using len2 by auto
  \<comment> \<open>the reflected list's own well-formedness, verbatim from
     @{thm [source] hybrid_split_neg_solve_half}\<close>
  have sfQb: "square_free (map_poly of_int (Poly (refl_list xs)) :: real poly)"
    using square_free_pcompose_linear[OF sfxs, of "-1"]
    by (simp add: refl_list_eq_scale_poly_list_neg1 Poly_scale_poly_list_eq_pcompose)
  have Q0: "Poly (refl_list xs) \<noteq> 0" using sfQb unfolding square_free_def by simp
  have lastnzQb: "last (refl_list xs) \<noteq> 0" using last_refl_list_nz[OF xsne lastnz] .
  have hrQb: "kiou_headroom (refl_list xs)" using kiou_headroom_refl_list[of xs] hr by simp
  have len2Qb: "2 \<le> length (refl_list xs)" using len2 by simp
  have capYQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (split_cap_lin (refl_list xs))"
    using pre' unfolding dsc_isolate_all_split_lin_pre_def by (auto simp: Let_def)
  have capDQb: "kiou_bound_k_monadic (refl_list xs)
                  \<le> SPEC (defl_depth_cap (refl_list xs))"
    using pre unfolding dsc_isolate_all_split_defl_pre_def by (auto simp: Let_def)
  \<comment> \<open>\<^bold>\<open>MERGED\<close>, exactly as on the classic side and the positive half: only ONE \<open>\<le> SPEC\<close> fact fires
     per producer call, so a second one would never reach the continuation.\<close>
  have mergedQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (\<lambda>k.
      ((\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ k) \<and>
       k * length (refl_list xs) < max_snat LENGTH(gmp_poly_len) \<and>
       k < max_snat LENGTH(gmp_poly_len) \<and> split_cap_lin (refl_list xs) k)
      \<and> defl_depth_cap (refl_list xs) k)"
    by (rule kiou_le_SPEC_conj[OF kiou_bound_k_monadic_spec_capped_lin[OF len2Qb lastnzQb hrQb capYQb]
          capDQb])
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have lenbQb: "length (refl_list xs) + 1 < max_snat LENGTH(gmp_poly_len)" using lenb by simp
  have copy_correct: "poly_copy_monadic xs \<le> RETURN xs" by (rule poly_copy_correct[OF lenb])
  have poly_reflect_correct: "poly_reflect_in_place_monadic xs \<le> RETURN (refl_list xs)"
    using poly_reflect_in_place_correct[OF lenb] by (simp add: refl_list_def)
  show ?thesis
    unfolding defl_split_neg_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg
        copy_correct[THEN order_trans]
        poly_reflect_correct[THEN order_trans]
        mergedQb[THEN order_trans])
    subgoal using len2Qb lenb lenbQb by (cases xs) auto
    subgoal using len2Qb lenb lenbQb by auto
    subgoal using len2Qb lenb lenbQb by auto
    subgoal premises p using p by simp
    subgoal premises p using p by simp
    subgoal premises kp for kneg
    proof -
      from kp have kneg_sound:
          "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ kneg"
        and kneg_cap: "kneg * length (refl_list xs) < max_snat LENGTH(gmp_poly_len)"
        and kneg_lt: "kneg < max_snat LENGTH(gmp_poly_len)"
        and cap_at: "split_cap_lin (refl_list xs) kneg"
        and depth_at: "defl_depth_cap (refl_list xs) kneg" by blast+
      define Qinit0 where "Qinit0 = scale_poly_list (2 ^ kneg) (refl_list xs)"
      define Qr where "Qr = (map_poly of_int (Poly Qinit0) :: real poly)"
      have Qinit_eq: "split_init_pow2_l0_monadic kneg (refl_list xs) \<le> RETURN Qinit0"
        using split_init_pow2_l0_monadic_correct[OF lenbQb kneg_cap]
        by (simp add: Qinit0_def split_init_pow2_l0_eq_scale_poly_list)
      have lenb3Q: "length (refl_list xs) + 3 < max_snat LENGTH(gmp_poly_len)" using lenb3 by simp
      note sd = defl_seed_facts[OF len2Qb lastnzQb sfQb lenb3Q, of kneg, folded Qinit0_def]
      have len2Q: "Suc 0 < length Qinit0" by (rule sd(1))
      have sfQ: "square_free (map_poly of_int (Poly Qinit0) :: real poly)" by (rule sd(2))
      have canonQ: "coeffs (Poly Qinit0) = Qinit0" by (rule sd(3))
      have lenbQ: "length Qinit0 + 2 < max_snat LENGTH(gmp_poly_len)" by (rule sd(4))
      have Q_eqQ: "Qinit0 = carried_init_same_den 0 (2 ^ 0) (2 ^ kneg) (refl_list xs)" by (rule sd(5))
      have rpsmallQ: "length (refl_list xs) < 1099511627776" using xs_small by simp
      have lenQx: "length Qinit0 = length (refl_list xs)" by (simp add: Qinit0_def)
      have bl40: "nat_bitlen (length Qinit0) \<le> 40"
        unfolding nat_bitlen_def by (rule Least_le) (use rpsmallQ lenQx in simp)
      have pbQ: "length Qinit0 * nat_bitlen (length Qinit0) < max_snat LENGTH(gmp_poly_len)"
      proof -
        have "length Qinit0 * nat_bitlen (length Qinit0) \<le> length Qinit0 * 40"
          using bl40 by (rule mult_le_mono2)
        also have "\<dots> < 1099511627776 * 40" using rpsmallQ lenQx by simp
        finally show ?thesis by (simp add: max_snat_def)
      qed
      have potform: "hybrid_root_potential (delta_defl Qr) 0
                       = int (2 ^ newton_pol_ecap + 2)
                           * int (dyadic_iv_interval_mu (delta_defl Qr) (0, 1))"
        by (simp add: hybrid_root_potential_def)
      from depth_at[unfolded defl_depth_cap_def Let_def]
      have dcap1: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                            * int (dyadic_iv_interval_mu (delta_defl Qr) (0, 1))
                   \<Longrightarrow> kD * (length (refl_list xs) - 1) < max_snat LENGTH(gmp_poly_len)"
        and dcap2: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                             * int (dyadic_iv_interval_mu (delta_defl Qr) (0, 1))
                    \<Longrightarrow> (kD + 1) * length (refl_list xs) < 1099511627776"
        unfolding Qr_def Qinit0_def by blast+
      have caps: "int (dyadic_iv_interval_mu (delta_defl Qr) (0, 1)) + 3
                    < int (max_snat LENGTH(gmp_poly_len))"
                 "hybrid_root_potential (delta_defl Qr) 0 < int (max_snat LENGTH(gmp_poly_len))"
                 "hybrid_root_potential (delta_defl Qr) 0 + 258
                    < int (max_snat LENGTH(gmp_poly_len))"
      proof -
        have n1: "1 \<le> length (refl_list xs)" using len2Qb by linarith
        show "int (dyadic_iv_interval_mu (delta_defl Qr) (0, 1)) + 3 < int (max_snat LENGTH(gmp_poly_len))"
             "hybrid_root_potential (delta_defl Qr) 0 < int (max_snat LENGTH(gmp_poly_len))"
             "hybrid_root_potential (delta_defl Qr) 0 + 258 < int (max_snat LENGTH(gmp_poly_len))"
          using defl_caps_of_depth[OF dcap2 n1] by auto
      qed
      have solver: "defl_main_list_monadic split_pipeline_e0 0 (2 ^ kneg) 0 Qinit0 (refl_list xs)
          \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
              length (dyadic_interval_vec_triples acc) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
              defl_acc_isolates (of_int_poly (Poly (refl_list xs)) :: real poly) acc \<and>
              defl_acc_covers (of_int_poly (Poly (refl_list xs)) :: real poly) 0 acc \<and>
              iv_disj_mset (mset (defl_wins acc)) \<and>
              (\<forall>w \<in> set (defl_wins acc). \<forall>x. iv_in x w \<longrightarrow> 0 < x))"
        apply (rule defl_main_list_correct_geom[where \<delta> = "delta_defl Qr" and glo = 0])
        \<comment> \<open>26 premises, in the positive half's own order; only 22--26 are \<open>\<delta>\<close>-dependent.\<close>
        subgoal by (rule defl_delta_defl_pos_always)
        subgoal by simp
        subgoal by (rule Q_eqQ)
        subgoal by (rule canonQ)
        subgoal using sfQ unfolding square_free_def Qr_def by simp
        subgoal using sfQ unfolding Qr_def by simp
        subgoal unfolding Qr_def by simp
        subgoal using sfQb unfolding square_free_def by simp
        subgoal using sfQb by simp
        subgoal using kneg_sound by simp
        subgoal using len2Q by simp
        subgoal using lenbQ by simp
        subgoal by (simp add: max_snat_def)
        subgoal using len2Qb by (cases xs) auto
        subgoal using lenbQb by simp
        subgoal by (simp add: max_snat_def)
        subgoal using pbQ canonQ by simp
        subgoal using rpsmallQ lenQx canonQ by (simp add: max_snat_def)
        subgoal using rpsmallQ lenQx canonQ by (simp add: max_sint_def)
        subgoal using rpsmallQ lenQx canonQ by simp
        subgoal using len2Q canonQ by simp
        subgoal by (rule caps(1))
        subgoal by (rule caps(2))
        subgoal by (rule caps(3))
        subgoal premises p for kD using dcap1[of kD] p canonQ lenQx potform by simp
        subgoal premises p for kD using dcap2[of kD] p canonQ lenQx potform by simp
        subgoal by simp
        done
      show ?thesis
        apply (refine_vcg Qinit_eq[unfolded Qinit0_def, THEN order_trans]
            mpz_pow2_monadic_spec[OF kneg_lt, THEN order_trans]
            solver[unfolded Qinit0_def, THEN order_trans])
        subgoal using len2Q unfolding Qinit0_def[symmetric] by simp
        subgoal using lenbQ unfolding Qinit0_def[symmetric] by simp
        subgoal using len2Qb by (cases xs) auto
        apply (all \<open>((elim conjE, assumption); fail)?\<close>)
        done
    qed
    done
qed

theorem defl_isolate_all_split_main_correct_geom:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_defl_pre xs"
  shows "defl_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accN, xs0).
      dyadic_interval_vec_invar accP \<and>
      length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      defl_acc_isolates (of_int_poly (Poly xs) :: real poly) accP \<and>
      defl_acc_covers (of_int_poly (Poly xs) :: real poly) 0 accP \<and>
      iv_disj_mset (mset (defl_wins accP)) \<and>
      (\<forall>w \<in> set (defl_wins accP). \<forall>x. iv_in x w \<longrightarrow> 0 < x) \<and>
      dyadic_interval_vec_invar accN \<and>
      length (dyadic_interval_vec_triples accN) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      defl_acc_isolates (of_int_poly (Poly (refl_list xs)) :: real poly) accN \<and>
      defl_acc_covers (of_int_poly (Poly (refl_list xs)) :: real poly) 0 accN \<and>
      iv_disj_mset (mset (defl_wins accN)) \<and>
      (\<forall>w \<in> set (defl_wins accN). \<forall>x. iv_in x w \<longrightarrow> 0 < x) \<and>
      xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  have len2: "2 \<le> length xs"
    using pre unfolding dsc_isolate_all_split_defl_pre_def dsc_isolate_all_split_lin_pre_def by auto
  show ?thesis
    unfolding defl_isolate_all_split_main_def PR_CONST_def
    apply (refine_vcg
        defl_split_pos_solve_half_geom[OF pre, THEN order_trans]
        defl_split_neg_solve_half_geom[OF pre, THEN order_trans]
        dsc_split_zero_check_correct_len2[OF len2, THEN order_trans])
    using len2 by auto
qed

end
