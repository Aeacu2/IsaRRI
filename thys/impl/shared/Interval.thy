theory Interval
imports Fast_Descartes
begin

text \<open>GMP-backed interval vectors — four owned GMP integer vectors, one per endpoint
  component.
  Layer: SEPREF.
  Main exports: \<open>interval_\<close> vector ops and the \<open>rat_pair\<close> num/den scalar container.

  The current exported main loops store rational endpoints as signed-long
  numerator/denominator pairs.  This theory starts the replacement container:
  four owned GMP integer vectors, one per endpoint component.  It deliberately
  reuses gmp_poly_assn as a generic owned GMP-int vector so the option-slot
  ownership proofs from Array remain the only array ownership story.\<close>

type_synonym gmp_interval_vec =
  "gmp_poly \<times> gmp_poly \<times> gmp_poly \<times> gmp_poly"

abbreviation gmp_interval_vec_assn where
"gmp_interval_vec_assn \<equiv>
  gmp_poly_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a
    gmp_poly_assn \<times>\<^sub>a gmp_poly_assn"

definition interval_vec_invar ::
  "gmp_interval_vec \<Rightarrow> bool" where
"interval_vec_invar v \<equiv>
  (let (lna, lda, rnb, rdb) = v in
    length lna = length lda \<and>
    length lna = length rnb \<and>
    length lna = length rdb)"

definition rat_of_pair :: "int \<times> int \<Rightarrow> rat" where
"rat_of_pair x \<equiv>
  rat_of_int (fst x) / rat_of_int (snd x)"

definition interval_of_pair ::
  "(int \<times> int) \<times> (int \<times> int) \<Rightarrow> rat \<times> rat" where
"interval_of_pair I \<equiv>
  (rat_of_pair (fst I), rat_of_pair (snd I))"

definition interval_vec_pairs ::
  "gmp_interval_vec \<Rightarrow> ((int \<times> int) \<times> (int \<times> int)) list" where
"interval_vec_pairs v \<equiv>
  (let (lna, lda, rnb, rdb) = v in zip (zip lna lda) (zip rnb rdb))"

definition interval_vec_to_list ::
  "gmp_interval_vec \<Rightarrow> (rat \<times> rat) list" where
"interval_vec_to_list v \<equiv>
  map interval_of_pair (interval_vec_pairs v)"

lemma interval_vec_pairs_simps:
  "interval_vec_pairs (lna, lda, rnb, rdb) =
    zip (zip lna lda) (zip rnb rdb)"
  unfolding interval_vec_pairs_def by simp

lemma interval_vec_to_list_simps:
  "interval_vec_to_list (lna, lda, rnb, rdb) =
    map interval_of_pair (zip (zip lna lda) (zip rnb rdb))"
  unfolding interval_vec_to_list_def
  by (simp add: interval_vec_pairs_simps)

lemma interval_vec_invar_empty[simp]:
  "interval_vec_invar ([], [], [], [])"
  unfolding interval_vec_invar_def by simp

lemma interval_vec_pairs_empty[simp]:
  "interval_vec_pairs ([], [], [], []) = []"
  by (simp add: interval_vec_pairs_simps)

lemma interval_vec_to_list_empty[simp]:
  "interval_vec_to_list ([], [], [], []) = []"
  by (simp add: interval_vec_to_list_simps)

lemma interval_vec_pairs_length:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "length (interval_vec_pairs (lna, lda, rnb, rdb)) = length lna"
  using assms
  unfolding interval_vec_invar_def
  by (simp add: interval_vec_pairs_simps)

lemma interval_vec_to_list_length:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "length (interval_vec_to_list (lna, lda, rnb, rdb)) = length lna"
  unfolding interval_vec_to_list_def
  by (simp add: interval_vec_pairs_length[OF assms])

lemma interval_vec_pairs_nth:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "i < length lna"
  shows "interval_vec_pairs (lna, lda, rnb, rdb) ! i =
    ((lna ! i, lda ! i), (rnb ! i, rdb ! i))"
  using assms
  unfolding interval_vec_invar_def
  by (simp add: interval_vec_pairs_simps)

lemma interval_vec_to_list_nth:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "i < length lna"
  shows "interval_vec_to_list (lna, lda, rnb, rdb) ! i =
    (rat_of_pair (lna ! i, lda ! i),
     rat_of_pair (rnb ! i, rdb ! i))"
proof -
  have len: "i < length (interval_vec_pairs (lna, lda, rnb, rdb))"
    using assms interval_vec_pairs_length[OF assms(1)]
    by simp
  show ?thesis
    using interval_vec_pairs_nth[OF assms]
    unfolding interval_vec_to_list_def
      interval_of_pair_def
    by (simp add: len)
qed

lemma interval_vec_invar_push[simp]:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "interval_vec_invar
    (lna @ [na], lda @ [da], rnb @ [nb], rdb @ [db])"
  using assms
  unfolding interval_vec_invar_def
  by simp

lemma interval_vec_pairs_push:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "interval_vec_pairs
      (lna @ [na], lda @ [da], rnb @ [nb], rdb @ [db]) =
    interval_vec_pairs (lna, lda, rnb, rdb) @
      [((na, da), (nb, db))]"
  using assms
  unfolding interval_vec_invar_def
  by (simp add: interval_vec_pairs_simps)

lemma interval_vec_to_list_push:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "interval_vec_to_list
      (lna @ [na], lda @ [da], rnb @ [nb], rdb @ [db]) =
    interval_vec_to_list (lna, lda, rnb, rdb) @
      [interval_of_pair ((na, da), (nb, db))]"
  using assms
  unfolding interval_vec_to_list_def
  by (simp add: interval_vec_pairs_push)

lemma interval_vec_invar_push_point[simp]:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "interval_vec_invar
    (lna @ [n], lda @ [d], rnb @ [n], rdb @ [d])"
  using assms by simp

lemma interval_vec_pairs_push_point:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "interval_vec_pairs
      (lna @ [n], lda @ [d], rnb @ [n], rdb @ [d]) =
    interval_vec_pairs (lna, lda, rnb, rdb) @
      [((n, d), (n, d))]"
  using interval_vec_pairs_push[OF assms, of n d n d] by simp

lemma interval_vec_to_list_push_point:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "interval_vec_to_list
      (lna @ [n], lda @ [d], rnb @ [n], rdb @ [d]) =
    interval_vec_to_list (lna, lda, rnb, rdb) @
      [interval_of_pair ((n, d), (n, d))]"
  using interval_vec_to_list_push[OF assms, of n d n d] by simp

lemma interval_vec_invar_push_children[simp]:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "interval_vec_invar
    (lna @ [na, mn], lda @ [da, md], rnb @ [mn, nb], rdb @ [md, db])"
  using assms
  unfolding interval_vec_invar_def
  by simp

lemma interval_vec_pairs_push_children:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "interval_vec_pairs
      (lna @ [na, mn], lda @ [da, md],
       rnb @ [mn, nb], rdb @ [md, db]) =
    interval_vec_pairs (lna, lda, rnb, rdb) @
      [((na, da), (mn, md)), ((mn, md), (nb, db))]"
  using assms
  unfolding interval_vec_invar_def
  by (simp add: interval_vec_pairs_simps)

lemma interval_vec_to_list_push_children:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "interval_vec_to_list
      (lna @ [na, mn], lda @ [da, md],
       rnb @ [mn, nb], rdb @ [md, db]) =
    interval_vec_to_list (lna, lda, rnb, rdb) @
      [interval_of_pair ((na, da), (mn, md)),
       interval_of_pair ((mn, md), (nb, db))]"
  using assms
  unfolding interval_vec_to_list_def
  by (simp add: interval_vec_pairs_push_children)

definition interval_vec_pushable ::
  "gmp_interval_vec \<Rightarrow> bool" where
"interval_vec_pushable v \<equiv>
  (let (lna, lda, rnb, rdb) = v in
    length lna + 1 < max_snat LENGTH(gmp_poly_len) \<and>
    length lda + 1 < max_snat LENGTH(gmp_poly_len) \<and>
    length rnb + 1 < max_snat LENGTH(gmp_poly_len) \<and>
    length rdb + 1 < max_snat LENGTH(gmp_poly_len))"

definition interval_vec_pushable2 ::
  "gmp_interval_vec \<Rightarrow> bool" where
"interval_vec_pushable2 v \<equiv>
  (let (lna, lda, rnb, rdb) = v in
    length lna + 2 < max_snat LENGTH(gmp_poly_len) \<and>
    length lda + 2 < max_snat LENGTH(gmp_poly_len) \<and>
    length rnb + 2 < max_snat LENGTH(gmp_poly_len) \<and>
    length rdb + 2 < max_snat LENGTH(gmp_poly_len))"

lemma interval_vec_pushable2_pushable_after:
  assumes "interval_vec_pushable2 v"
    and "v = (lna, lda, rnb, rdb)"
  shows "interval_vec_pushable (lna @ [a], lda @ [b], rnb @ [c], rdb @ [d])"
  using assms
  unfolding interval_vec_pushable_def
    interval_vec_pushable2_def
  by auto

lemma dsc_gcd_nonzero_if_pos2[simp]:
  fixes n d :: int
  assumes "0 < d"
  shows "gcd n d \<noteq> 0"
  using assms
  by auto

definition poly_push2_coeffs_monadic ::
  "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly nres" where
"poly_push2_coeffs_monadic p x y \<equiv> doN {
  ASSERT (length p + 2 < max_snat LENGTH(gmp_poly_len));
  p \<leftarrow> (PR_CONST poly_push_coeff_monadic) p x;
  ASSERT (length p + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_push_coeff_monadic) p y
}"

lemma poly_push2_coeffs_monadic_spec:
  assumes "length p + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_push2_coeffs_monadic p x y \<le> SPEC (\<lambda>p'. p' = p @ [x, y])"
  using assms
  unfolding poly_push2_coeffs_monadic_def poly_push_coeff_monadic_def
    PR_CONST_def
  by refine_vcg auto

sepref_register "PR_CONST poly_push2_coeffs_monadic"
  :: "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly nres"

sepref_definition poly_push2_coeffs_impl [llvm_inline] is
  "uncurry2 poly_push2_coeffs_monadic" ::
  "[\<lambda>((p, _), _). length p + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      gmp_poly_assn"
  unfolding poly_push2_coeffs_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

lemma poly_push2_coeffs_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_push2_coeffs_impl,
    uncurry2 (PR_CONST poly_push2_coeffs_monadic)) \<in>
    [\<lambda>((p, _), _). length p + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        gmp_poly_assn"
  using poly_push2_coeffs_impl.refine
  by (simp add: PR_CONST_def)

definition rat_normalize_monadic ::
  "int \<Rightarrow> int \<Rightarrow> (int \<times> int) nres" where
"rat_normalize_monadic n d \<equiv> doN {
  ASSERT (0 < d);
  gsrc \<leftarrow> RETURN (COPY n);
  g \<leftarrow> (PR_CONST mpz_gcd.amop_r1) gsrc d;
  n \<leftarrow> (PR_CONST mpz_divexact.amop_r1) n g;
  d \<leftarrow> (PR_CONST mpz_divexact.amop_r1) d g;
  (PR_CONST mpzb_discard_monadic) g;
  RETURN (n, d)
}"

lemma rat_of_div_gcd:
  fixes n d :: int
  assumes "0 < d"
  shows "rat_of_int (n div gcd n d) / rat_of_int (d div gcd n d) =
    rat_of_int n / rat_of_int d"
proof -
  let ?g = "gcd n d"
  have gpos: "0 < ?g"
    using assms by (simp add: gcd_pos_int)
  have n_div: "rat_of_int (n div ?g) = rat_of_int n / rat_of_int ?g"
    by (simp add: of_int_div)
  have d_div: "rat_of_int (d div ?g) = rat_of_int d / rat_of_int ?g"
    by (simp add: of_int_div)
  show ?thesis
    using gpos assms
    by (simp add: n_div d_div field_simps)
qed

lemma den_div_gcd_pos:
  fixes n d :: int
  assumes "0 < d"
  shows "0 < d div gcd n d"
proof -
  let ?g = "gcd n d"
  have gpos: "0 < ?g"
    using assms by (simp add: gcd_pos_int)
  have "?g \<le> d"
    using assms by simp
  then show ?thesis
    using gpos by (simp add: pos_imp_zdiv_pos_iff)
qed

lemma rat_normalize_monadic_spec:
  assumes "0 < d"
  shows "rat_normalize_monadic n d \<le>
    SPEC (\<lambda>nd.
      rat_of_pair nd = rat_of_int n / rat_of_int d \<and>
      0 < snd nd)"
  using assms
  unfolding rat_normalize_monadic_def mpz_divexact_pre_def
    rat_of_pair_def PR_CONST_def
    mpz_gcd.amop_r1_def mpz_gcd.aop_r1_def
    mpz_divexact.amop_r1_def mpz_divexact.aop_r1_def
  apply refine_vcg
  apply (simp_all add: COPY_def mpzb_discard_monadic_def
    rat_of_div_gcd den_div_gcd_pos)
  done

sepref_register "PR_CONST rat_normalize_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> (int \<times> int) nres"

sepref_definition rat_normalize_impl [llvm_inline] is
  "uncurry rat_normalize_monadic" ::
  "[\<lambda>(_, d). 0 < d]\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  unfolding rat_normalize_monadic_def
  supply [simp] = mpz_divexact_pre_def
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

lemma rat_normalize_impl_hnr[sepref_fr_rules]:
  "(uncurry rat_normalize_impl,
    uncurry (PR_CONST rat_normalize_monadic)) \<in>
    [\<lambda>(_, d). 0 < d]\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  using rat_normalize_impl.refine
  by (simp add: PR_CONST_def)

definition rat_mid_monadic ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (int \<times> int) nres" where
"rat_mid_monadic na da nb db \<equiv> doN {
  ASSERT (0 < da);
  ASSERT (0 < db);
  c_na \<leftarrow> RETURN (COPY na);
  c_nb \<leftarrow> RETURN (COPY nb);
  na_db \<leftarrow> (PR_CONST mpz_mul.amop_r1) c_na db;
  nb_da \<leftarrow> (PR_CONST mpz_mul.amop_r1) c_nb da;
  num \<leftarrow> (PR_CONST mpz_add.amop_r1) na_db nb_da;
  (PR_CONST mpzb_discard_monadic) nb_da;
  c_da \<leftarrow> RETURN (COPY da);
  den0 \<leftarrow> (PR_CONST mpz_mul.amop_r1) c_da db;
  den0_copy \<leftarrow> RETURN (COPY den0);
  den \<leftarrow> (PR_CONST mpz_add.amop_r1) den0 den0_copy;
  (PR_CONST mpzb_discard_monadic) den0_copy;
  ASSERT (0 < den);
  (PR_CONST rat_normalize_monadic) num den
}"

lemma rat_mid_monadic_raw:
  assumes "0 < da" and "0 < db"
  shows "rat_of_int (na * db + nb * da) /
      rat_of_int (da * db + da * db) =
    (rat_of_int na / rat_of_int da +
     rat_of_int nb / rat_of_int db) / 2"
proof -
  have sum:
    "rat_of_int na / rat_of_int da + rat_of_int nb / rat_of_int db =
      (rat_of_int na * rat_of_int db + rat_of_int nb * rat_of_int da) /
        (rat_of_int da * rat_of_int db)"
    using assms
    by (subst add_frac_eq) simp_all
  have "rat_of_int (na * db + nb * da) /
      rat_of_int (da * db + da * db) =
    (rat_of_int na * rat_of_int db + rat_of_int nb * rat_of_int da) /
      (2 * (rat_of_int da * rat_of_int db))"
    by (simp add: algebra_simps)
  also have "\<dots> =
    ((rat_of_int na * rat_of_int db + rat_of_int nb * rat_of_int da) /
      (rat_of_int da * rat_of_int db)) / 2"
    by simp
  also have "\<dots> =
    (rat_of_int na / rat_of_int da +
     rat_of_int nb / rat_of_int db) / 2"
    using sum by simp
  finally show ?thesis .
qed

lemma rat_mid_monadic_raw_twice:
  assumes "0 < da" and "0 < db"
  shows "rat_of_int (na * db + nb * da) * 2 /
      rat_of_int (2 * (da * db)) =
    rat_of_int na / rat_of_int da +
    rat_of_int nb / rat_of_int db"
  using rat_mid_monadic_raw[OF assms, of na nb]
  by simp

lemma rat_mid_monadic_normalized_twice:
  fixes a b na da nb db :: int
  assumes "0 < da" and "0 < db"
    and "rat_of_int a / rat_of_int b =
      (rat_of_int na * rat_of_int db + rat_of_int nb * rat_of_int da) /
        (2 * (rat_of_int da * rat_of_int db))"
  shows "rat_of_int a * 2 / rat_of_int b =
    rat_of_int na / rat_of_int da +
    rat_of_int nb / rat_of_int db"
proof -
  have "rat_of_int a * 2 / rat_of_int b =
    (rat_of_int a / rat_of_int b) * 2"
    by simp
  also have "\<dots> =
    ((rat_of_int na * rat_of_int db + rat_of_int nb * rat_of_int da) /
      (2 * (rat_of_int da * rat_of_int db))) * 2"
    using assms(3) by simp
  also have "\<dots> =
    rat_of_int (na * db + nb * da) * 2 / rat_of_int (2 * (da * db))"
    by simp
  also have "\<dots> =
    rat_of_int na / rat_of_int da + rat_of_int nb / rat_of_int db"
    using rat_mid_monadic_raw_twice[OF assms(1,2), of na nb] .
  finally show ?thesis .
qed

lemma rat_mid_monadic_spec:
  assumes "0 < da" and "0 < db"
  shows "rat_mid_monadic na da nb db \<le>
    SPEC (\<lambda>md.
      rat_of_pair md =
        (rat_of_pair (na, da) +
         rat_of_pair (nb, db)) / 2 \<and>
      0 < snd md)"
  using assms
  unfolding rat_mid_monadic_def rat_of_pair_def PR_CONST_def
    mpz_mul.amop_r1_def mpz_mul.aop_r1_def
    mpz_add.amop_r1_def mpz_add.aop_r1_def
  apply refine_vcg
  apply (simp_all add: COPY_def mpzb_discard_monadic_def)
  apply (rule order_trans[OF rat_normalize_monadic_spec])
   apply (simp add: assms)
  apply (clarsimp simp: rat_of_pair_def
    rat_mid_monadic_normalized_twice)
  done

sepref_register "PR_CONST rat_mid_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (int \<times> int) nres"

sepref_definition rat_mid_impl [llvm_inline] is
  "uncurry3 rat_mid_monadic" ::
  "[\<lambda>(((_, da), _), db). 0 < da \<and> 0 < db]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  unfolding rat_mid_monadic_def
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

lemma rat_mid_impl_hnr[sepref_fr_rules]:
  "(uncurry3 rat_mid_impl,
    uncurry3 (PR_CONST rat_mid_monadic)) \<in>
    [\<lambda>(((_, da), _), db). 0 < da \<and> 0 < db]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  using rat_mid_impl.refine
  by (simp add: PR_CONST_def)

definition interval_vec_empty_sz_monadic ::
  "nat \<Rightarrow> gmp_interval_vec nres" where
"interval_vec_empty_sz_monadic n \<equiv> doN {
  lna \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
  lda \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
  rnb \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
  rdb \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
  RETURN (lna, lda, rnb, rdb)
}"

lemma interval_vec_empty_sz_monadic_spec:
  "interval_vec_empty_sz_monadic n \<le>
    SPEC (\<lambda>v. interval_vec_invar v \<and>
      interval_vec_pairs v = [] \<and>
      interval_vec_to_list v = [])"
  unfolding interval_vec_empty_sz_monadic_def poly_empty_sz_monadic_def
    PR_CONST_def
  by refine_vcg auto

sepref_register "PR_CONST interval_vec_empty_sz_monadic"
  :: "nat \<Rightarrow> gmp_interval_vec nres"

sepref_definition interval_vec_empty_sz_impl [llvm_inline] is
  "interval_vec_empty_sz_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>d \<rightarrow>\<^sub>a
    gmp_interval_vec_assn"
  unfolding interval_vec_empty_sz_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma interval_vec_empty_sz_impl_hnr[sepref_fr_rules]:
  "(interval_vec_empty_sz_impl,
    PR_CONST interval_vec_empty_sz_monadic) \<in>
      (snat_assn' TYPE(gmp_poly_len))\<^sup>d \<rightarrow>\<^sub>a
        gmp_interval_vec_assn"
  using interval_vec_empty_sz_impl.refine
  by (simp add: PR_CONST_def)

definition interval_vec_length_monadic ::
  "gmp_interval_vec \<Rightarrow> nat nres" where
"interval_vec_length_monadic v \<equiv> doN {
  let (lna, _, _, _) = v;
  (PR_CONST poly_length_monadic) lna
}"

lemma interval_vec_length_monadic_spec:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
  shows "interval_vec_length_monadic (lna, lda, rnb, rdb) \<le>
    SPEC (\<lambda>n. n =
      length (interval_vec_pairs (lna, lda, rnb, rdb)) \<and>
      n = length (interval_vec_to_list (lna, lda, rnb, rdb)))"
  using assms
  unfolding interval_vec_length_monadic_def poly_length_monadic_def
    PR_CONST_def
  by (simp add: interval_vec_pairs_length
    interval_vec_to_list_length)

sepref_register "PR_CONST interval_vec_length_monadic"
  :: "gmp_interval_vec \<Rightarrow> nat nres"

sepref_definition interval_vec_length_impl [llvm_inline] is
  "interval_vec_length_monadic" ::
  "gmp_interval_vec_assn\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  unfolding interval_vec_length_monadic_def
  unfolding Let_def
  by sepref

lemma interval_vec_length_impl_hnr[sepref_fr_rules]:
  "(interval_vec_length_impl,
    PR_CONST interval_vec_length_monadic) \<in>
      gmp_interval_vec_assn\<^sup>k \<rightarrow>\<^sub>a
        snat_assn' TYPE(gmp_poly_len)"
  using interval_vec_length_impl.refine
  by (simp add: PR_CONST_def)

definition interval_vec_push_monadic ::
  "gmp_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
    gmp_interval_vec nres" where
"interval_vec_push_monadic v lna_i lda_i rnb_i rdb_i \<equiv> doN {
  let (lna, lda, rnb, rdb) = v;
  ASSERT (interval_vec_pushable v);
  lna \<leftarrow> (PR_CONST poly_push_coeff_monadic) lna lna_i;
  lda \<leftarrow> (PR_CONST poly_push_coeff_monadic) lda lda_i;
  rnb \<leftarrow> (PR_CONST poly_push_coeff_monadic) rnb rnb_i;
  rdb \<leftarrow> (PR_CONST poly_push_coeff_monadic) rdb rdb_i;
  RETURN (lna, lda, rnb, rdb)
}"

lemma interval_vec_push_monadic_spec:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "interval_vec_pushable (lna, lda, rnb, rdb)"
  shows "interval_vec_push_monadic
      (lna, lda, rnb, rdb) na da nb db \<le>
    SPEC (\<lambda>v. interval_vec_invar v \<and>
      interval_vec_pairs v =
        interval_vec_pairs (lna, lda, rnb, rdb) @
          [((na, da), (nb, db))] \<and>
      interval_vec_to_list v =
        interval_vec_to_list (lna, lda, rnb, rdb) @
          [interval_of_pair ((na, da), (nb, db))])"
  using assms
  unfolding interval_vec_push_monadic_def interval_vec_pushable_def
    poly_push_coeff_monadic_def PR_CONST_def
  by refine_vcg (auto simp: interval_vec_pairs_push
    interval_vec_to_list_push)

sepref_register "PR_CONST interval_vec_push_monadic"
  :: "gmp_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
      gmp_interval_vec nres"

sepref_definition interval_vec_push_impl [llvm_inline] is
  "uncurry4 interval_vec_push_monadic" ::
  "[\<lambda>((((v, _), _), _), _).
      interval_vec_pushable v]\<^sub>a
    gmp_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      gmp_interval_vec_assn"
  unfolding interval_vec_push_monadic_def
  unfolding interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

lemma interval_vec_push_impl_hnr[sepref_fr_rules]:
  "(uncurry4 interval_vec_push_impl,
    uncurry4 (PR_CONST interval_vec_push_monadic)) \<in>
    [\<lambda>((((v, _), _), _), _).
      interval_vec_pushable v]\<^sub>a
      gmp_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        gmp_interval_vec_assn"
  using interval_vec_push_impl.refine
  by (simp add: PR_CONST_def)

definition interval_vec_push_point_monadic ::
  "gmp_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
    gmp_interval_vec nres" where
"interval_vec_push_point_monadic acc n d \<equiv> doN {
  n1 \<leftarrow> RETURN (COPY n);
  d1 \<leftarrow> RETURN (COPY d);
  n2 \<leftarrow> RETURN (COPY n);
  d2 \<leftarrow> RETURN (COPY d);
  ASSERT (interval_vec_pushable acc);
  (PR_CONST interval_vec_push_monadic) acc n1 d1 n2 d2
}"

lemma interval_vec_push_point_monadic_spec:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "interval_vec_pushable (lna, lda, rnb, rdb)"
  shows "interval_vec_push_point_monadic (lna, lda, rnb, rdb) n d \<le>
    SPEC (\<lambda>v. interval_vec_invar v \<and>
      interval_vec_pairs v =
        interval_vec_pairs (lna, lda, rnb, rdb) @
          [((n, d), (n, d))] \<and>
      interval_vec_to_list v =
        interval_vec_to_list (lna, lda, rnb, rdb) @
          [interval_of_pair ((n, d), (n, d))])"
  using assms
  unfolding interval_vec_push_point_monadic_def PR_CONST_def
  apply refine_vcg
  apply (rule order_trans[OF interval_vec_push_monadic_spec])
    apply simp_all
  done

sepref_register "PR_CONST interval_vec_push_point_monadic"
  :: "gmp_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
      gmp_interval_vec nres"

sepref_definition interval_vec_push_point_impl [llvm_inline] is
  "uncurry2 interval_vec_push_point_monadic" ::
  "[\<lambda>((acc, _), _). interval_vec_pushable acc]\<^sub>a
    gmp_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>
      gmp_interval_vec_assn"
  unfolding interval_vec_push_point_monadic_def
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

lemma interval_vec_push_point_impl_hnr[sepref_fr_rules]:
  "(uncurry2 interval_vec_push_point_impl,
    uncurry2 (PR_CONST interval_vec_push_point_monadic)) \<in>
    [\<lambda>((acc, _), _). interval_vec_pushable acc]\<^sub>a
      gmp_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>
        gmp_interval_vec_assn"
  using interval_vec_push_point_impl.refine
  by (simp add: PR_CONST_def)

definition interval_vec_push_children_monadic ::
  "gmp_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> gmp_interval_vec nres" where
"interval_vec_push_children_monadic todo na da nb db mn md \<equiv> doN {
  let (lna, lda, rnb, rdb) = todo;
  mn_r \<leftarrow> RETURN (COPY mn);
  md_r \<leftarrow> RETURN (COPY md);
  ASSERT (interval_vec_pushable2 todo);
  lna \<leftarrow> (PR_CONST poly_push2_coeffs_monadic) lna na mn_r;
  lda \<leftarrow> (PR_CONST poly_push2_coeffs_monadic) lda da md_r;
  rnb \<leftarrow> (PR_CONST poly_push2_coeffs_monadic) rnb mn nb;
  rdb \<leftarrow> (PR_CONST poly_push2_coeffs_monadic) rdb md db;
  RETURN (lna, lda, rnb, rdb)
}"

lemma interval_vec_push_children_monadic_spec:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "interval_vec_pushable2 (lna, lda, rnb, rdb)"
  shows "interval_vec_push_children_monadic
      (lna, lda, rnb, rdb) na da nb db mn md \<le>
    SPEC (\<lambda>v. interval_vec_invar v \<and>
      interval_vec_pairs v =
        interval_vec_pairs (lna, lda, rnb, rdb) @
          [((na, da), (mn, md)), ((mn, md), (nb, db))] \<and>
      interval_vec_to_list v =
        interval_vec_to_list (lna, lda, rnb, rdb) @
          [interval_of_pair ((na, da), (mn, md)),
           interval_of_pair ((mn, md), (nb, db))])"
  using assms
  unfolding interval_vec_push_children_monadic_def
    interval_vec_pushable2_def
    poly_push2_coeffs_monadic_def poly_push_coeff_monadic_def
    PR_CONST_def
  by refine_vcg (auto simp: interval_vec_pairs_push_children
    interval_vec_to_list_push_children)

sepref_register "PR_CONST interval_vec_push_children_monadic"
  :: "gmp_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> gmp_interval_vec nres"

sepref_definition interval_vec_push_children_impl [llvm_inline] is
  "uncurry6 interval_vec_push_children_monadic" ::
  "[\<lambda>((((((todo, _), _), _), _), _), _).
      interval_vec_pushable2 todo]\<^sub>a
    gmp_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      gmp_interval_vec_assn"
  unfolding interval_vec_push_children_monadic_def
  unfolding interval_vec_pushable_def
    interval_vec_pushable2_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

lemma interval_vec_push_children_impl_hnr[sepref_fr_rules]:
  "(uncurry6 interval_vec_push_children_impl,
    uncurry6 (PR_CONST interval_vec_push_children_monadic)) \<in>
    [\<lambda>((((((todo, _), _), _), _), _), _).
      interval_vec_pushable2 todo]\<^sub>a
      gmp_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        gmp_interval_vec_assn"
  using interval_vec_push_children_impl.refine
  by (simp add: PR_CONST_def)

definition interval_vec_copy_get_monadic ::
  "gmp_interval_vec \<Rightarrow> nat \<Rightarrow>
    (int \<times> int \<times> int \<times> int) nres" where
"interval_vec_copy_get_monadic v i \<equiv> doN {
  let (lna, lda, rnb, rdb) = v;
  ASSERT (i < length lna);
  ASSERT (i < length lda);
  ASSERT (i < length rnb);
  ASSERT (i < length rdb);
  lna_i \<leftarrow> (PR_CONST poly_copy_coeff_monadic) lna i;
  lda_i \<leftarrow> (PR_CONST poly_copy_coeff_monadic) lda i;
  rnb_i \<leftarrow> (PR_CONST poly_copy_coeff_monadic) rnb i;
  rdb_i \<leftarrow> (PR_CONST poly_copy_coeff_monadic) rdb i;
  RETURN (lna_i, lda_i, rnb_i, rdb_i)
}"

lemma interval_vec_copy_get_monadic_spec:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "i < length lna"
  shows "interval_vec_copy_get_monadic (lna, lda, rnb, rdb) i \<le>
    SPEC (\<lambda>(na, da, nb, db).
      ((na, da), (nb, db)) =
        interval_vec_pairs (lna, lda, rnb, rdb) ! i \<and>
      (rat_of_pair (na, da), rat_of_pair (nb, db)) =
        interval_vec_to_list (lna, lda, rnb, rdb) ! i)"
proof -
  have i_lda: "i < length lda"
    using assms unfolding interval_vec_invar_def by simp
  have i_rnb: "i < length rnb"
    using assms unfolding interval_vec_invar_def by simp
  have i_rdb: "i < length rdb"
    using assms unfolding interval_vec_invar_def by simp
  have pair_nth:
    "((lna ! i, lda ! i), (rnb ! i, rdb ! i)) =
      interval_vec_pairs (lna, lda, rnb, rdb) ! i"
    using interval_vec_pairs_nth[OF assms] by simp
  have rat_nth:
    "(rat_of_pair (lna ! i, lda ! i),
      rat_of_pair (rnb ! i, rdb ! i)) =
      interval_vec_to_list (lna, lda, rnb, rdb) ! i"
    using interval_vec_to_list_nth[OF assms] by simp
  show ?thesis
    unfolding interval_vec_copy_get_monadic_def
      poly_copy_coeff_monadic_def PR_CONST_def
    using assms i_lda i_rnb i_rdb pair_nth rat_nth
    by (simp add: refine_pw_simps)
qed

sepref_register "PR_CONST interval_vec_copy_get_monadic"
  :: "gmp_interval_vec \<Rightarrow> nat \<Rightarrow>
      (int \<times> int \<times> int \<times> int) nres"

sepref_definition interval_vec_copy_get_impl [llvm_inline] is
  "uncurry interval_vec_copy_get_monadic" ::
  "[\<lambda>(v, i). case v of (lna, lda, rnb, rdb) \<Rightarrow>
      i < length lna \<and> i < length lda \<and>
      i < length rnb \<and> i < length rdb]\<^sub>a
    gmp_interval_vec_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      mpzb_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn"
  unfolding interval_vec_copy_get_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

lemma interval_vec_copy_get_impl_hnr[sepref_fr_rules]:
  "(uncurry interval_vec_copy_get_impl,
    uncurry (PR_CONST interval_vec_copy_get_monadic)) \<in>
    [\<lambda>(v, i). case v of (lna, lda, rnb, rdb) \<Rightarrow>
      i < length lna \<and> i < length lda \<and>
      i < length rnb \<and> i < length rdb]\<^sub>a
      gmp_interval_vec_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
        mpzb_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn"
  using interval_vec_copy_get_impl.refine
  by (simp add: PR_CONST_def)

definition interval_vec_free_monadic ::
  "gmp_interval_vec \<Rightarrow> unit nres" where
"interval_vec_free_monadic v \<equiv> doN {
  let (lna, lda, rnb, rdb) = v;
  (PR_CONST poly_free_monadic) lna;
  (PR_CONST poly_free_monadic) lda;
  (PR_CONST poly_free_monadic) rnb;
  (PR_CONST poly_free_monadic) rdb;
  RETURN ()
}"

sepref_register "PR_CONST interval_vec_free_monadic"
  :: "gmp_interval_vec \<Rightarrow> unit nres"

sepref_definition interval_vec_free_impl [llvm_inline] is
  "interval_vec_free_monadic" ::
  "gmp_interval_vec_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  unfolding interval_vec_free_monadic_def
  unfolding Let_def
  by sepref

lemma interval_vec_free_impl_hnr[sepref_fr_rules]:
  "(interval_vec_free_impl,
    PR_CONST interval_vec_free_monadic) \<in>
      gmp_interval_vec_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  using interval_vec_free_impl.refine
  by (simp add: PR_CONST_def)

end
