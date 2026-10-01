theory Fast_Descartes
imports Poly_Ops
begin

text \<open>Fast-Descartes count kernel: assembles the GMP polynomial kernels into a
  refinement of \<open>descartes_list_int\<close>. Layer: SEPREF, over a small abstract
  \<open>_nd\<close> (numerator/denominator, no GMP packing) layer at the top --- that layer is the
  FUNCTIONAL SPEC the GMP/mpz ops below are proven against.

  Main exports: \<open>descartes_preprocess_monadic\<close> and
  \<open>_same_den_mpz\<close>, each with an \<open>_impl\<close> Sepref definition and \<open>_correct\<close> lemma.
  Consumed by the endpoint/dyadic/carried count kernels.\<close>

definition descartes_transform ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat" where
"descartes_transform na da nw dw xs \<equiv>
  (let
     p1 = taylor_shift_list na
       (rev (scale_for_fractional_shift da 1 (rev xs)));
     p3 = scale_for_fractional_shift dw 1
       (rev (scale_poly_list nw p1));
     p4 = taylor_shift_list 1 p3
   in sign_changes_fold p4)"

lemma descartes_transform_eq_fast:
  assumes "quotient_of a = (na, da)"
    and "quotient_of ((b - a) * of_int da) = (nw, dw)"
  shows "descartes_transform na da nw dw xs =
    descartes_list_int a b xs"
  using assms
  unfolding descartes_transform_def
    descartes_list_int_def fractional_taylor_shift_def
  by (simp add: Let_def split_def)

lemma map_rat_of_int_fractional_taylor_shift_nd:
  fixes a :: rat and xs :: "int list"
  assumes "da > 0"
    and a_eq: "a = rat_of_int na / rat_of_int da"
  shows "map rat_of_int
      (taylor_shift_list na (rev (scale_for_fractional_shift da 1 (rev xs)))) =
    smult_list (rat_of_int da ^ (length xs - 1))
      (scale_poly_list (1 / rat_of_int da)
        (taylor_shift_list a (map rat_of_int xs)))"
proof (cases "xs = []")
  case True
  then show ?thesis
    by (simp add: smult_list_def scale_poly_list_def
      scale_for_fractional_shift_eq_scale_poly_list)
next
  case False
  have da_neq_0: "rat_of_int da \<noteq> 0"
    using assms(1) by simp

  have "map rat_of_int
      (taylor_shift_list na (rev (scale_for_fractional_shift da 1 (rev xs)))) =
    taylor_shift_list (rat_of_int na)
      (map rat_of_int (rev (scale_poly_list da (rev xs))))"
    by (simp add: map_rat_of_int_taylor_shift_list
      scale_for_fractional_shift_eq_scale_poly_list)
  also have "... =
    taylor_shift_list (rat_of_int na)
      (rev (scale_poly_list (rat_of_int da) (map rat_of_int (rev xs))))"
    using map_rat_of_int_scale_poly_list rev_map by metis
  also have "... =
    taylor_shift_list (rat_of_int na)
      (rev (scale_poly_list (rat_of_int da) (rev (map rat_of_int xs))))"
    by (simp add: rev_map)
  also have "... =
    taylor_shift_list (rat_of_int na)
      (rev (smult_list (rat_of_int da ^ (length xs - 1))
        (rev (scale_poly_list (1 / rat_of_int da) (map rat_of_int xs)))))"
    using scale_poly_list_rev[OF da_neq_0, of "map rat_of_int xs"] by simp
  also have "... =
    taylor_shift_list (rat_of_int na)
      (smult_list (rat_of_int da ^ (length xs - 1))
        (scale_poly_list (1 / rat_of_int da) (map rat_of_int xs)))"
    by (simp add: rev_map smult_list_def)
  also have "... =
    smult_list (rat_of_int da ^ (length xs - 1))
      (taylor_shift_list (rat_of_int na)
        (scale_poly_list (1 / rat_of_int da) (map rat_of_int xs)))"
    by (simp add: taylor_shift_list_smult)
  also have "... =
    smult_list (rat_of_int da ^ (length xs - 1))
      (scale_poly_list (1 / rat_of_int da)
        (taylor_shift_list (rat_of_int na * (1 / rat_of_int da))
          (map rat_of_int xs)))"
    by (simp add: taylor_scale_commute_rat)
  also have "... =
    smult_list (rat_of_int da ^ (length xs - 1))
      (scale_poly_list (1 / rat_of_int da)
        (taylor_shift_list a (map rat_of_int xs)))"
    using a_eq by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma descartes_transform_p3_rat_equiv:
  fixes a b :: rat and xs :: "int list"
  assumes "length xs > 0"
    and "da > 0"
    and "dw > 0"
    and a_eq: "a = rat_of_int na / rat_of_int da"
    and width_eq: "rat_of_int nw / (rat_of_int da * rat_of_int dw) = b - a"
  defines "k \<equiv> length xs - 1"
  defines "p1 \<equiv> taylor_shift_list na
    (rev (scale_for_fractional_shift da 1 (rev xs)))"
  defines "p3 \<equiv> scale_for_fractional_shift dw 1
    (rev (scale_poly_list nw p1))"
  shows "map rat_of_int p3 =
    smult_list ((rat_of_int da * rat_of_int dw) ^ k)
      (rev (scale_poly_list (b - a)
        (taylor_shift_list a (map rat_of_int xs))))"
proof -
  have da_neq_0: "rat_of_int da \<noteq> 0"
    using assms(2) by simp
  have dw_neq_0: "rat_of_int dw \<noteq> 0"
    using assms(3) by simp

  let ?L_inner = "taylor_shift_list a (map rat_of_int xs)"

  have "map rat_of_int p3 =
    scale_poly_list (rat_of_int dw)
      (rev (scale_poly_list (rat_of_int nw) (map rat_of_int p1)))"
    unfolding p3_def scale_for_fractional_shift_eq_scale_poly_list
    by (metis map_rat_of_int_scale_poly_list rev_map)
  also have "... =
    scale_poly_list (rat_of_int dw)
      (rev (scale_poly_list (rat_of_int nw)
        (smult_list (rat_of_int da ^ k)
          (scale_poly_list (1 / rat_of_int da) ?L_inner))))"
    using map_rat_of_int_fractional_taylor_shift_nd[OF assms(2) a_eq, of xs]
    by (simp add: k_def p1_def)
  also have "... =
    scale_poly_list (rat_of_int dw)
      (rev (smult_list (rat_of_int da ^ k)
        (scale_poly_list (rat_of_int nw)
          (scale_poly_list (1 / rat_of_int da) ?L_inner))))"
    by (simp add: scale_poly_list_smult_list)
  also have "... =
    scale_poly_list (rat_of_int dw)
      (smult_list (rat_of_int da ^ k)
        (rev (scale_poly_list (rat_of_int nw * (1 / rat_of_int da))
          ?L_inner)))"
    by (simp add: scale_poly_list_scale_poly_list rev_smult_list)
  also have "... =
    smult_list (rat_of_int da ^ k)
      (scale_poly_list (rat_of_int dw)
        (rev (scale_poly_list (rat_of_int nw / rat_of_int da)
          ?L_inner)))"
    by (simp add: scale_poly_list_smult_list)
  also have "... =
    smult_list (rat_of_int da ^ k)
      (smult_list (rat_of_int dw ^ k)
        (rev (scale_poly_list (1 / rat_of_int dw)
          (scale_poly_list (rat_of_int nw / rat_of_int da)
            ?L_inner))))"
  proof -
    have len_eq:
      "length (scale_poly_list (rat_of_int nw / rat_of_int da) ?L_inner) - 1 = k"
      using k_def by simp
    show ?thesis
      using scale_poly_list_rev[OF dw_neq_0,
        of "scale_poly_list (rat_of_int nw / rat_of_int da) ?L_inner"]
        len_eq
      by simp
  qed
  also have "... =
    smult_list ((rat_of_int da * rat_of_int dw) ^ k)
      (rev (scale_poly_list
        (1 / rat_of_int dw * (rat_of_int nw / rat_of_int da))
        ?L_inner))"
    by (simp add: scale_poly_list_scale_poly_list
      smult_list_smult_list power_mult_distrib)
  also have "... =
    smult_list ((rat_of_int da * rat_of_int dw) ^ k)
      (rev (scale_poly_list (b - a) ?L_inner))"
    using width_eq
    by (metis divide_divide_eq_left more_arith_simps(5)
      times_divide_eq_left)
  finally show ?thesis .
qed

lemma descartes_transform_p4_rat_equiv:
  fixes a b :: rat and xs :: "int list"
  assumes "length xs > 0"
    and "da > 0"
    and "dw > 0"
    and a_eq: "a = rat_of_int na / rat_of_int da"
    and width_eq: "rat_of_int nw / (rat_of_int da * rat_of_int dw) = b - a"
  defines "k \<equiv> length xs - 1"
  defines "p1 \<equiv> taylor_shift_list na
    (rev (scale_for_fractional_shift da 1 (rev xs)))"
  defines "p3 \<equiv> scale_for_fractional_shift dw 1
    (rev (scale_poly_list nw p1))"
  defines "p4 \<equiv> taylor_shift_list 1 p3"
  shows "map rat_of_int p4 =
    smult_list ((rat_of_int da * rat_of_int dw) ^ k)
      (taylor_shift_list 1
        (rev (scale_poly_list (b - a)
          (taylor_shift_list a (map rat_of_int xs)))))"
proof -
  have "map rat_of_int p4 =
    taylor_shift_list 1 (map rat_of_int p3)"
    unfolding p4_def by (simp add: map_rat_of_int_taylor_shift_list)
  also have "... =
    taylor_shift_list 1
      (smult_list ((rat_of_int da * rat_of_int dw) ^ k)
        (rev (scale_poly_list (b - a)
          (taylor_shift_list a (map rat_of_int xs)))))"
    using descartes_transform_p3_rat_equiv[OF assms(1-3) a_eq width_eq]
    by (simp add: k_def p1_def p3_def)
  also have "... =
    smult_list ((rat_of_int da * rat_of_int dw) ^ k)
      (taylor_shift_list 1
        (rev (scale_poly_list (b - a)
          (taylor_shift_list a (map rat_of_int xs)))))"
    by (simp add: taylor_shift_list_smult)
  finally show ?thesis .
qed

lemma descartes_transform_eq_fast_general:
  assumes "length xs > 0"
    and "a < b"
    and "da > 0"
    and "dw > 0"
    and a_eq: "a = rat_of_int na / rat_of_int da"
    and width_eq: "rat_of_int nw / (rat_of_int da * rat_of_int dw) = b - a"
  shows "descartes_transform na da nw dw xs =
    descartes_list_int a b xs"
proof -
  let ?k = "length xs - 1"
  let ?p1 = "taylor_shift_list na
    (rev (scale_for_fractional_shift da 1 (rev xs)))"
  let ?p3 = "scale_for_fractional_shift dw 1
    (rev (scale_poly_list nw ?p1))"
  let ?p4 = "taylor_shift_list 1 ?p3"

  have scalar_pos: "(rat_of_int da * rat_of_int dw) ^ ?k > 0"
    using assms(3,4) by simp

  have "descartes_transform na da nw dw xs =
    sign_changes_fold ?p4"
    unfolding descartes_transform_def Let_def by simp
  also have "... = sign_changes_fold (map rat_of_int ?p4)"
    by (simp add: sign_changes_fold_map_rat_of_int)
  also have "... =
    sign_changes_fold
      (smult_list ((rat_of_int da * rat_of_int dw) ^ ?k)
        (taylor_shift_list 1
          (rev (scale_poly_list (b - a)
            (taylor_shift_list a (map rat_of_int xs))))))"
    using descartes_transform_p4_rat_equiv[
      OF assms(1,3,4) a_eq width_eq]
    by simp
  also have "... =
    sign_changes_fold
      (taylor_shift_list 1
        (rev (scale_poly_list (b - a)
          (taylor_shift_list a (map rat_of_int xs)))))"
    using sign_changes_fold_smult_list_pos[OF scalar_pos] by simp
  also have "... =
    sign_changes_fold
      (taylor_shift_list 1
        (reverse_array_fun (scale_poly_list (b - a)
          (taylor_shift_list a (map rat_of_int xs)))))"
    by (simp add: reverse_array_fun_eq_rev)
  also have "... = fast_descartes_list a b (map rat_of_int xs)"
    unfolding fast_descartes_list_def by simp
  also have "... = descartes_list_int a b xs"
    using descartes_list_int_correct[OF assms(1,2)] by simp
  finally show ?thesis .
qed

lemma poly_sign_changes_monadic_free_correct:
  assumes "length ys < max_snat LENGTH(gmp_poly_len)"
  shows "poly_sign_changes_monadic ys \<bind>
    (\<lambda>sc. poly_free_monadic ys \<bind>
      (\<lambda>_. RETURN sc))
    \<le> RETURN (sign_changes_fold ys)"
  using poly_sign_changes_monadic_correct[OF assms]
  by (auto simp: pw_le_iff refine_pw_simps)

definition descartes_finish_monadic ::
  "gmp_poly \<Rightarrow> nat nres" where
"descartes_finish_monadic p3 \<equiv> doN {
  ASSERT (length p3 + 1 < max_snat LENGTH(gmp_poly_len));
  p3 \<leftarrow> (PR_CONST poly_taylor_shift_one_in_place_monadic) p3;
  ASSERT (length p3 < max_snat LENGTH(gmp_poly_len));
  sc \<leftarrow> (PR_CONST poly_sign_changes_monadic) p3;
  (PR_CONST poly_free_monadic) p3;
  RETURN sc
}"

lemma descartes_finish_monadic_correct:
  assumes "length p3 + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "descartes_finish_monadic p3
    \<le> RETURN (sign_changes_fold (taylor_shift_list 1 p3))"
  unfolding descartes_finish_monadic_def PR_CONST_def
  apply (refine_vcg
      poly_taylor_shift_one_in_place_monadic_correct[THEN order_trans]
      poly_sign_changes_monadic_free_correct[THEN order_trans])
  using assms apply (auto simp: length_taylor_shift_list)
  done

sepref_register "PR_CONST descartes_finish_monadic"
  :: "gmp_poly \<Rightarrow> nat nres"

sepref_definition descartes_finish_impl [llvm_inline] is
  "descartes_finish_monadic" ::
  "[\<lambda>p3. length p3 + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding descartes_finish_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma descartes_finish_impl_hnr[sepref_fr_rules]:
  "(descartes_finish_impl,
    PR_CONST descartes_finish_monadic) \<in>
    [\<lambda>p3. length p3 + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using descartes_finish_impl.refine
  by (simp add: PR_CONST_def)


definition descartes_transform_monadic ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"descartes_transform_monadic na da nw dw xs \<equiv> doN {
  p1 \<leftarrow> (PR_CONST poly_fractional_taylor_shift_nd_monadic) na da xs;
  ASSERT (length p1 + 1 < max_snat LENGTH(gmp_poly_len));
  p2 \<leftarrow> (PR_CONST poly_scale_monadic) nw p1;
  (PR_CONST poly_free_monadic) p1;
  ASSERT (length p2 + 1 < max_snat LENGTH(gmp_poly_len));
  rp2 \<leftarrow> (PR_CONST poly_reverse_monadic) p2;
  (PR_CONST poly_free_monadic) p2;
  ASSERT (length rp2 + 1 < max_snat LENGTH(gmp_poly_len));
  p3 \<leftarrow> (PR_CONST poly_scale_monadic) dw rp2;
  (PR_CONST poly_free_monadic) rp2;
  ASSERT (length p3 + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST descartes_finish_monadic) p3
}"

lemma descartes_transform_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "descartes_transform_monadic na da nw dw xs
    \<le> RETURN (descartes_transform na da nw dw xs)"
  using assms
  unfolding descartes_transform_monadic_def
    descartes_transform_def PR_CONST_def
  apply (refine_vcg
    poly_fractional_taylor_shift_nd_monadic_correct[THEN order_trans]
    poly_scale_correct[THEN order_trans]
    poly_reverse_monadic_correct[THEN order_trans]
    descartes_finish_monadic_correct[THEN order_trans]
    poly_free_monadic_rule)
  apply (simp_all add: scale_for_fractional_shift_eq_scale_poly_list
    mpzb_discard_monadic_def mpz_from_int_def)
  done

sepref_register "PR_CONST descartes_transform_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

sepref_definition descartes_transform_impl [llvm_code] is
  "uncurry4 descartes_transform_monadic" ::
  "[\<lambda>((((_, _), _), _), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
      snat_assn' TYPE(gmp_poly_len)"
  unfolding descartes_transform_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma descartes_transform_impl_hnr[sepref_fr_rules]:
  "(uncurry4 descartes_transform_impl,
    uncurry4 (PR_CONST descartes_transform_monadic)) \<in>
    [\<lambda>((((_, _), _), _), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
        snat_assn' TYPE(gmp_poly_len)"
  using descartes_transform_impl.refine
  by (simp add: PR_CONST_def)

definition descartes_preprocess ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat" where
"descartes_preprocess na da nb db xs \<equiv>
  descartes_transform na da (nb * da - na * db) db xs"

definition descartes_preprocess_same_denom ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat" where
"descartes_preprocess_same_denom na d nb xs \<equiv>
  descartes_transform na d (nb - na) 1 xs"

lemma descartes_preprocess_eq_fast:
  assumes "length xs > 0"
    and "da > 0"
    and "db > 0"
    and "na * db < nb * da"
  shows "descartes_preprocess na da nb db xs =
    descartes_list_int
      (rat_of_int na / rat_of_int da)
      (rat_of_int nb / rat_of_int db) xs"
proof -
  let ?a = "rat_of_int na / rat_of_int da"
  let ?b = "rat_of_int nb / rat_of_int db"
  let ?nw = "nb * da - na * db"

  have a_lt_b: "?a < ?b"
  proof -
    have cross_lt: "rat_of_int na * rat_of_int db <
      rat_of_int nb * rat_of_int da"
      using assms(4)
      by (metis of_int_less_iff of_int_mult)
    show ?thesis
      using assms(2,3) cross_lt
      by (simp add: field_simps)
  qed

  have width_eq:
    "rat_of_int ?nw / (rat_of_int da * rat_of_int db) = ?b - ?a"
    using assms(2,3)
    by (simp add: field_simps)

  show ?thesis
    unfolding descartes_preprocess_def
    by (rule descartes_transform_eq_fast_general[
        OF assms(1) a_lt_b assms(2) assms(3) refl width_eq])
qed

lemma descartes_preprocess_same_denom_eq_interval:
  assumes "length xs > 0"
    and "d > 0"
    and "na < nb"
  shows "descartes_preprocess_same_denom na d nb xs =
    descartes_preprocess na d nb d xs"
proof -
  let ?a = "rat_of_int na / rat_of_int d"
  let ?b = "rat_of_int nb / rat_of_int d"

  have a_lt_b: "?a < ?b"
    using assms(2,3) by (simp add: field_simps)
  have width_eq:
    "rat_of_int (nb - na) / (rat_of_int d * rat_of_int 1) =
      ?b - ?a"
    using assms(2) by (simp add: field_simps)
  have same_eq_fast:
    "descartes_preprocess_same_denom na d nb xs =
      descartes_list_int ?a ?b xs"
    unfolding descartes_preprocess_same_denom_def
    by (rule descartes_transform_eq_fast_general[
      OF assms(1) a_lt_b assms(2) _ refl width_eq], simp)
  have cross_lt: "na * d < nb * d"
    using assms(2,3) by (simp add: mult_less_cancel_right_pos)
  have interval_eq_fast:
    "descartes_preprocess na d nb d xs =
      descartes_list_int ?a ?b xs"
    by (rule descartes_preprocess_eq_fast[
      OF assms(1) assms(2) assms(2) cross_lt])
  show ?thesis
    using same_eq_fast interval_eq_fast by simp
qed

definition fast_descartes_interval ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"fast_descartes_interval na da nb db xs \<equiv> doN {
  g_na \<leftarrow> RETURN (mpz_from_int na);
  g_da \<leftarrow> RETURN (mpz_from_int da);
  g_nb \<leftarrow> RETURN (mpz_from_int nb);
  g_db \<leftarrow> RETURN (mpz_from_int db);
  g_na_tmp \<leftarrow> RETURN (mpz_from_int na);
  nb_da \<leftarrow> (PR_CONST mpz_mul.amop_r1) g_nb g_da;
  na_db \<leftarrow> (PR_CONST mpz_mul.amop_r1) g_na_tmp g_db;
  nw \<leftarrow> (PR_CONST mpz_sub.amop_r1) nb_da na_db;
  (PR_CONST mpzb_discard_monadic) na_db;
  sc \<leftarrow> (PR_CONST descartes_transform_monadic) g_na g_da nw g_db xs;
  (PR_CONST mpzb_discard_monadic) g_na;
  (PR_CONST mpzb_discard_monadic) g_da;
  (PR_CONST mpzb_discard_monadic) nw;
  (PR_CONST mpzb_discard_monadic) g_db;
  RETURN sc
}"

lemma fast_descartes_interval_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "fast_descartes_interval na da nb db xs
    \<le> RETURN (descartes_preprocess na da nb db xs)"
  using assms
  unfolding fast_descartes_interval_def
    descartes_preprocess_def PR_CONST_def
  apply refine_vcg
  apply (simp_all add: mpzb_discard_monadic_def mpz_from_int_def)
  apply (rule order_trans)
  apply (rule descartes_transform_monadic_correct)
  apply simp
  apply simp
  done

sepref_register "PR_CONST fast_descartes_interval"
  :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

sepref_definition fast_descartes_interval_impl [llvm_inline] is
  "uncurry4 fast_descartes_interval" ::
  "[\<lambda>((((_, _), _), _), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_slong_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k *\<^sub>a
      gmp_slong_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding fast_descartes_interval_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma fast_descartes_interval_impl_hnr[sepref_fr_rules]:
  "(uncurry4 fast_descartes_interval_impl,
    uncurry4 (PR_CONST fast_descartes_interval)) \<in>
    [\<lambda>((((_, _), _), _), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_slong_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k *\<^sub>a
        gmp_slong_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using fast_descartes_interval_impl.refine
  by (simp add: PR_CONST_def)

definition descartes_preprocess_monadic ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"descartes_preprocess_monadic na da nb db xs \<equiv> doN {
  c_nb \<leftarrow> RETURN (COPY nb);
  c_na \<leftarrow> RETURN (COPY na);
  nb_da \<leftarrow> (PR_CONST mpz_mul.amop_r1) c_nb da;
  na_db \<leftarrow> (PR_CONST mpz_mul.amop_r1) c_na db;
  nw \<leftarrow> (PR_CONST mpz_sub.amop_r1) nb_da na_db;
  (PR_CONST mpzb_discard_monadic) na_db;
  sc \<leftarrow> (PR_CONST descartes_transform_monadic) na da nw db xs;
  (PR_CONST mpzb_discard_monadic) nw;
  RETURN sc
}"

lemma descartes_preprocess_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "descartes_preprocess_monadic na da nb db xs
    \<le> RETURN (descartes_preprocess na da nb db xs)"
  using assms
  unfolding descartes_preprocess_monadic_def
    descartes_preprocess_def PR_CONST_def
  apply refine_vcg
  apply (simp_all add: mpzb_discard_monadic_def)
  apply (rule order_trans)
   apply (rule descartes_transform_monadic_correct)
   apply simp
  apply simp
  done

definition descartes_preprocess_same_denom_monadic ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"descartes_preprocess_same_denom_monadic na d nb xs \<equiv> doN {
  nw \<leftarrow> RETURN (COPY nb);
  nw \<leftarrow> (PR_CONST mpz_sub.amop_r1) nw na;
  one \<leftarrow> RETURN (mpz_from_int 1);
  sc \<leftarrow> (PR_CONST descartes_transform_monadic) na d nw one xs;
  (PR_CONST mpzb_discard_monadic) nw;
  (PR_CONST mpzb_discard_monadic) one;
  RETURN sc
}"

lemma descartes_preprocess_same_denom_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "descartes_preprocess_same_denom_monadic na d nb xs
    \<le> RETURN (descartes_preprocess_same_denom na d nb xs)"
  using assms
  unfolding descartes_preprocess_same_denom_monadic_def
    descartes_preprocess_same_denom_def PR_CONST_def
  apply refine_vcg
  apply (simp_all add: mpzb_discard_monadic_def mpz_from_int_def)
  apply (rule order_trans)
   apply (rule descartes_transform_monadic_correct)
   apply simp
  apply simp
  done

lemma descartes_preprocess_same_denom_monadic_correct_interval:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length xs > 0"
    and "d > 0"
    and "na < nb"
  shows "descartes_preprocess_same_denom_monadic na d nb xs
    \<le> RETURN (descartes_preprocess na d nb d xs)"
  apply (rule order_trans[
    OF descartes_preprocess_same_denom_monadic_correct[
      OF assms(1)]])
  by (simp add:
    descartes_preprocess_same_denom_eq_interval[OF assms(2-4)])

sepref_register
  "PR_CONST descartes_preprocess_same_denom_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

sepref_definition
  descartes_preprocess_same_denom_impl [llvm_inline] is
  "uncurry3 descartes_preprocess_same_denom_monadic" ::
  "[\<lambda>(((_, _), _), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding descartes_preprocess_same_denom_monadic_def
  apply (annot_uint_const "TYPE(gmp_long_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma descartes_preprocess_same_denom_impl_hnr[
  sepref_fr_rules]:
  "(uncurry3 descartes_preprocess_same_denom_impl,
    uncurry3
      (PR_CONST descartes_preprocess_same_denom_monadic)) \<in>
    [\<lambda>(((_, _), _), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using descartes_preprocess_same_denom_impl.refine
  by (simp add: PR_CONST_def)

sepref_register "PR_CONST descartes_preprocess_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

sepref_definition descartes_preprocess_impl [llvm_inline] is
  "uncurry4 descartes_preprocess_monadic" ::
  "[\<lambda>((((_, _), _), _), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
      snat_assn' TYPE(gmp_poly_len)"
  unfolding descartes_preprocess_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma descartes_preprocess_impl_hnr[sepref_fr_rules]:
  "(uncurry4 descartes_preprocess_impl,
    uncurry4 (PR_CONST descartes_preprocess_monadic)) \<in>
    [\<lambda>((((_, _), _), _), xs).
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
        snat_assn' TYPE(gmp_poly_len)"
  using descartes_preprocess_impl.refine
  by (simp add: PR_CONST_def)

end
