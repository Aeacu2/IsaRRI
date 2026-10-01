theory Bisection_Solver
  imports Bisection "IsaRRI_LLVM.Poly_Vec" "IsaRRI_LLVM.Dyadic_Interval" "IsaRRI_LLVM.Interval_Eval" Count
begin

text \<open>The carried-transform Descartes loop.

  The todo interval stack and the carried-polynomial stack are kept in lockstep: each polynomial
  is already transformed to its dyadic interval, which avoids recomputing the endpoint Descartes
  transform for every child.

  Main definition: \<open>bisection_main_list_impl\<close>. Its end-to-end refinement to \<open>dsc_int\<close>,
  \<open>bilr_main_list_impl_refine_dsc_int\<close>, is in \<open>Bisection_Loop_Refine\<close>.\<close>


section \<open>Specialized \<open>Q(1/2)=0\<close> midpoint test (Horner by shift-and-add)\<close>

text \<open>The midpoint zero test \<open>Q(1/2) = 0\<close> without general multiplication. The numerator
  \<open>N = (\<Sum>i. c_i 2^(deg-i))\<close> is computed by the Horner recurrence \<open>acc := (acc << 1) + xs!i\<close> from
  \<open>i=1\<close>, seeded with \<open>acc = xs!0\<close>. Each step is one shift (\<open>mpz_shift_left_snat_monadic\<close>) and one
  borrowing add (\<open>poly_hom_eval_addmul_monadic\<close> with \<open>dpow = 1\<close>, i.e. \<open>acc + xs!i\<cdot>1\<close>), and
  \<open>Q(1/2)=0 \<longleftrightarrow> N=0 \<longleftrightarrow> sign acc = 0\<close>.\<close>


text \<open>Finish op, hand-proven exactly like the working analog \<open>poly_hom_eval_finish_monadic\<close>
  (\<open>Interval_Eval.thy\<close>) -- automatic \<open>by sepref\<close>/the dbg chain cannot ID-tag a bare
  \<open>RETURN (mpz_sgn acc)\<close> tail, so this needs the same hand-written \<open>sepref_to_hoare\<close>+\<open>vcg'\<close>
  route as the proven original. Reuses that theory's already-proven \<open>int_word_dvd_zero\<close>/
  \<open>int_word_mod_nonzero\<close> bridging lemmas (in scope transitively).\<close>


text \<open>Wrapper: seed \<open>acc = copy xs!0\<close> (owned), a borrowed \<open>one = 1\<close>, \<open>WHILET\<close> over \<open>i = 1..len-1\<close>,
  finish via the hand-proven op above.\<close>


text \<open>Correctness target: the SAME \<open>RETURN\<close>-form conclusion as the proven analog
  \<open>poly_hom_eval_zero_mpz_monadic_spec\<close> (\<open>poly (Poly xs) (n/d) = 0\<close>). Proof strategy: the loop
  computes the INTEGER \<open>N = poly (Poly (rev xs)) 2\<close> (Horner shift-and-add from the LOW end, i.e.
  evaluating the REVERSED coefficient list at \<open>2\<close> -- purely integer, no rationals in the loop
  invariant). The reciprocal identity \<open>poly_Poly_nth_sum\<close> + \<open>rev_nth\<close> reindexing connects this
  to \<open>2^(n-1) * poly (Poly xs) (1/2)\<close> (lemma \<open>reverse_eval_recip\<close>), giving
  \<open>N = 0 \<longleftrightarrow> poly (Poly xs) (1/2) = 0\<close> since \<open>2^(n-1) \<noteq> 0\<close>.\<close>


section \<open>Carried_Kernel loop\<close>


lemma bisection_mid_zero_impl_hnr[sepref_fr_rules]:
  "(bisection_mid_zero_impl,
    PR_CONST bisection_mid_zero_monadic) \<in>
    [\<lambda>Q. 0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using bisection_mid_zero_impl.refine
  by (simp add: PR_CONST_def)

definition bisection_loop_cond ::
  "bisection_loop_state \<Rightarrow> bool" where
"bisection_loop_cond st \<equiv>
  (let ((todo, _), _) = st in
    let (lns, _, _) = todo in lns \<noteq> [])"

sepref_register "PR_CONST bisection_loop_cond"
  :: "bisection_loop_state \<Rightarrow> bool"


definition bisection_loop_cond_args_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> bool nres" where
"bisection_loop_cond_args_monadic todo qtodo acc \<equiv> doN {
    n \<leftarrow> (PR_CONST dyadic_interval_vec_length_monadic) todo;
    qn \<leftarrow> (PR_CONST poly_vec_length_monadic) qtodo;
    an \<leftarrow> (PR_CONST dyadic_interval_vec_length_monadic) acc;
    ASSERT (qn = qn);
    ASSERT (an = an);
    RETURN (0 < n)
  }"


sepref_register "PR_CONST bisection_loop_cond_args_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> bool nres"

lemma bisection_loop_cond_mop_monadic_eq:
  "bisection_loop_cond_mop_monadic =
    RETURN o bisection_loop_cond"
  unfolding bisection_loop_cond_mop_monadic_def
    gmp_dyadic_interval_vec_nonempty_def
    bisection_loop_cond_def
    dyadic_interval_vec_length_monadic_def poly_length_monadic_def
    PR_CONST_def
  by (auto intro!: ext split: prod.splits)

sepref_definition bisection_loop_cond_impl [llvm_inline] is
  "bisection_loop_cond_mop_monadic" ::
  "bisection_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding bisection_loop_cond_mop_monadic_def
  by sepref

lemma bisection_loop_cond_impl_hnr[sepref_fr_rules]:
  "(bisection_loop_cond_impl,
    RETURN o (PR_CONST bisection_loop_cond)) \<in>
    bisection_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using bisection_loop_cond_impl.refine
  by (simp add: bisection_loop_cond_mop_monadic_eq PR_CONST_def)


sepref_definition bisection_branch_zero_impl [llvm_inline] is
  "uncurry6 bisection_branch_zero_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
    bisection_loop_state_assn"
  unfolding bisection_branch_zero_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma bisection_branch_zero_impl_hnr[sepref_fr_rules]:
  "(uncurry6 bisection_branch_zero_impl,
    uncurry6 (PR_CONST bisection_branch_zero_monadic)) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
      bisection_loop_state_assn"
  using bisection_branch_zero_impl.refine
  by (simp add: PR_CONST_def)


sepref_definition bisection_branch_one_impl [llvm_inline] is
  "uncurry6 bisection_branch_one_monadic" ::
  "[\<lambda>((((((_, _), acc), _), _), _), _).
      dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_branch_one_monadic_def
  unfolding dyadic_interval_vec_pushable_def
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

lemma bisection_branch_one_impl_hnr[sepref_fr_rules]:
  "(uncurry6 bisection_branch_one_impl,
    uncurry6 (PR_CONST bisection_branch_one_monadic)) \<in>
    [\<lambda>((((((_, _), acc), _), _), _), _).
      dyadic_interval_vec_pushable acc]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_branch_one_impl.refine
  by (simp add: PR_CONST_def)


definition bisection_keep_acc_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_dyadic_interval_vec nres" where
"bisection_keep_acc_monadic acc l_num r_num k \<equiv> RETURN acc"

sepref_register "PR_CONST bisection_keep_acc_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_dyadic_interval_vec nres"

sepref_definition bisection_keep_acc_impl [llvm_inline] is
  "uncurry3 bisection_keep_acc_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    gmp_dyadic_interval_vec_assn"
  unfolding bisection_keep_acc_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma bisection_keep_acc_impl_hnr[sepref_fr_rules]:
  "(uncurry3 bisection_keep_acc_impl,
    uncurry3 (PR_CONST bisection_keep_acc_monadic)) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn"
  using bisection_keep_acc_impl.refine
  by (simp add: PR_CONST_def)

definition bisection_maybe_push_mid_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    bool \<Rightarrow> gmp_dyadic_interval_vec nres" where
"bisection_maybe_push_mid_monadic acc l_num r_num k is_root \<equiv>
  (if is_root then
    (PR_CONST carried_push_mid_monadic) acc l_num r_num k
   else
    (PR_CONST bisection_keep_acc_monadic) acc l_num r_num k)"

sepref_register "PR_CONST bisection_maybe_push_mid_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      bool \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition bisection_maybe_push_mid_impl [llvm_inline] is
  "uncurry4 bisection_maybe_push_mid_monadic" ::
  "[\<lambda>((((acc, _), _), k), _).
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      bool1_assn\<^sup>k \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding bisection_maybe_push_mid_monadic_def
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

lemma bisection_maybe_push_mid_impl_hnr[sepref_fr_rules]:
  "(uncurry4 bisection_maybe_push_mid_impl,
    uncurry4 (PR_CONST bisection_maybe_push_mid_monadic)) \<in>
    [\<lambda>((((acc, _), _), k), _).
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable acc]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        bool1_assn\<^sup>k \<rightarrow>
        gmp_dyadic_interval_vec_assn"
  using bisection_maybe_push_mid_impl.refine
  by (simp add: PR_CONST_def)

definition bisection_test_children_monadic ::
  "gmp_poly \<Rightarrow> (bool \<times> gmp_poly \<times> gmp_poly) nres" where
"bisection_test_children_monadic Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  is_root \<leftarrow> (PR_CONST bisection_mid_zero_monadic) Q;
  (ql, qr) \<leftarrow> (PR_CONST carried_left_right_monadic) Q;
  \<comment> \<open>\<open>carried_left_right\<close> consumes \<open>Q\<close> in place (left = \<open>shift_pow_in_place 1 Q\<close>), so there is no free here\<close>
  RETURN (is_root, ql, qr)
}"

sepref_register "PR_CONST bisection_test_children_monadic"
  :: "gmp_poly \<Rightarrow> (bool \<times> gmp_poly \<times> gmp_poly) nres"

sepref_definition bisection_test_children_impl [llvm_code] is
  "bisection_test_children_monadic" ::
  "[\<lambda>Q. 0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow>
      bool1_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a gmp_poly_assn"
  unfolding bisection_test_children_monadic_def
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

lemma bisection_test_children_impl_hnr[sepref_fr_rules]:
  "(bisection_test_children_impl,
    PR_CONST bisection_test_children_monadic) \<in>
    [\<lambda>Q. 0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
        bool1_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a gmp_poly_assn"
  using bisection_test_children_impl.refine
  by (simp add: PR_CONST_def)

definition bisection_test_push_children_monadic ::
  "gmp_poly list \<Rightarrow> gmp_poly \<Rightarrow> (bool \<times> gmp_poly list) nres" where
"bisection_test_push_children_monadic qtodo Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
  is_root \<leftarrow> (PR_CONST bisection_mid_zero_monadic) Q;
  (ql, qr) \<leftarrow> (PR_CONST carried_left_right_monadic) Q;
  \<comment> \<open>\<open>carried_left_right\<close> consumes \<open>Q\<close> in place, so there is no free here\<close>
  qtodo \<leftarrow> (PR_CONST poly_vec_push2_monadic) qtodo ql qr;
  RETURN (is_root, qtodo)
}"

sepref_register "PR_CONST bisection_test_push_children_monadic"
  :: "gmp_poly list \<Rightarrow> gmp_poly \<Rightarrow> (bool \<times> gmp_poly list) nres"

sepref_definition bisection_test_push_children_impl [llvm_code] is
  "uncurry bisection_test_push_children_monadic" ::
  "[\<lambda>(qtodo, Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      bool1_assn \<times>\<^sub>a gmp_poly_vec_assn"
  unfolding bisection_test_push_children_monadic_def
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

lemma bisection_test_push_children_impl_hnr[sepref_fr_rules]:
  "(uncurry bisection_test_push_children_impl,
    uncurry (PR_CONST bisection_test_push_children_monadic)) \<in>
    [\<lambda>(qtodo, Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
        bool1_assn \<times>\<^sub>a gmp_poly_vec_assn"
  using bisection_test_push_children_impl.refine
  by (simp add: PR_CONST_def)


lemma bisection_split_pair_state_impl_hnr[sepref_fr_rules]:
  "(uncurry4 bisection_split_pair_state_impl,
    uncurry4 (PR_CONST bisection_split_pair_state_monadic)) \<in>
    [\<lambda>((((st, _), _), k), Q).
      let (todo, qtodo) = st in
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (gmp_dyadic_interval_vec_assn \<times>\<^sub>a
        gmp_poly_vec_assn)\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_poly_vec_assn"
  using bisection_split_pair_state_impl.refine
  by (simp add: PR_CONST_def)


sepref_definition bisection_branch_split_nonroot_impl [llvm_code] is
  "uncurry6 bisection_branch_split_nonroot_monadic" ::
  "[\<lambda>((((((todo, qtodo), _), _), _), k), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_branch_split_nonroot_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma bisection_branch_split_nonroot_impl_hnr[sepref_fr_rules]:
  "(uncurry6 bisection_branch_split_nonroot_impl,
    uncurry6 (PR_CONST bisection_branch_split_nonroot_monadic)) \<in>
    [\<lambda>((((((todo, qtodo), _), _), _), k), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_branch_split_nonroot_impl.refine
  by (simp add: PR_CONST_def)


sepref_definition bisection_branch_split_root_impl [llvm_code] is
  "uncurry6 bisection_branch_split_root_monadic" ::
  "[\<lambda>((((((todo, qtodo), acc), _), _), k), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_branch_split_root_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma bisection_branch_split_root_impl_hnr[sepref_fr_rules]:
  "(uncurry6 bisection_branch_split_root_impl,
    uncurry6 (PR_CONST bisection_branch_split_root_monadic)) \<in>
    [\<lambda>((((((todo, qtodo), acc), _), _), k), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_branch_split_root_impl.refine
  by (simp add: PR_CONST_def)


sepref_definition bisection_branch_split_impl [llvm_code] is
  "uncurry6 bisection_branch_split_monadic" ::
  "[\<lambda>((((((todo, qtodo), acc), _), _), k), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_branch_split_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma bisection_branch_split_impl_hnr[sepref_fr_rules]:
  "(uncurry6 bisection_branch_split_impl,
    uncurry6 (PR_CONST bisection_branch_split_monadic)) \<in>
    [\<lambda>((((((todo, qtodo), acc), _), _), k), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_branch_split_impl.refine
  by (simp add: PR_CONST_def)


sepref_definition bisection_after_pop_impl [llvm_code] is
  "uncurry6 bisection_after_pop_monadic" ::
  "[\<lambda>((((((todo, qtodo), acc), _), _), k), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_after_pop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma bisection_after_pop_impl_hnr[sepref_fr_rules]:
  "(uncurry6 bisection_after_pop_impl,
    uncurry6 (PR_CONST bisection_after_pop_monadic)) \<in>
    [\<lambda>((((((todo, qtodo), acc), _), _), k), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_after_pop_impl.refine
  by (simp add: PR_CONST_def)


definition bisection_loop_step_pre ::
  "bisection_loop_state \<Rightarrow> bool" where
"bisection_loop_step_pre st \<equiv>
  bisection_loop_state_invar st \<and>
  bisection_loop_cond st \<and>
  (case st of (((lns, rns, ks), qtodo), acc) \<Rightarrow>
    dyadic_interval_vec_pushable2
      (butlast lns, butlast rns, butlast ks) \<and>
    dyadic_interval_vec_pushable acc \<and>
    length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
    list_all (\<lambda>Q. 0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len)) qtodo \<and>
    last ks + 1 < max_snat LENGTH(gmp_poly_len))"

definition bisection_loop_step_args_pre ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> bool" where
"bisection_loop_step_args_pre todo qtodo acc \<equiv>
  bisection_loop_step_pre ((todo, qtodo), acc)"

type_synonym bisection_poly_pop_result =
  "gmp_poly \<times> gmp_poly list"

abbreviation bisection_poly_pop_result_assn where
"bisection_poly_pop_result_assn \<equiv>
  gmp_poly_assn \<times>\<^sub>a gmp_poly_vec_assn"

definition bisection_after_qpop_pre ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow>
    nat \<Rightarrow> bisection_poly_pop_result \<Rightarrow> bool" where
"bisection_after_qpop_pre todo acc k qpop \<equiv>
  (case qpop of (Q, qtodo) \<Rightarrow>
    0 < length Q \<and>
    length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
    k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
    dyadic_interval_vec_pushable2 todo \<and>
    dyadic_interval_vec_pushable acc \<and>
    length qtodo + 2 < max_snat LENGTH(gmp_poly_len))"

definition bisection_after_qpop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bisection_poly_pop_result \<Rightarrow>
    bisection_loop_state nres" where
"bisection_after_qpop_monadic todo acc l_num r_num k qpop \<equiv>
  (case qpop of (Q, qtodo) \<Rightarrow>
    (PR_CONST bisection_after_pop_monadic) todo qtodo acc l_num r_num k Q)"

sepref_register "PR_CONST bisection_after_qpop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bisection_poly_pop_result \<Rightarrow>
      bisection_loop_state nres"

sepref_definition bisection_after_qpop_impl [llvm_code] is
  "uncurry5 bisection_after_qpop_monadic" ::
  "[\<lambda>(((((todo, acc), _), _), k), qpop).
      bisection_after_qpop_pre todo acc k qpop]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      bisection_poly_pop_result_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_after_qpop_monadic_def
  unfolding bisection_after_qpop_pre_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma bisection_after_qpop_impl_hnr[sepref_fr_rules]:
  "(uncurry5 bisection_after_qpop_impl,
    uncurry5 (PR_CONST bisection_after_qpop_monadic)) \<in>
    [\<lambda>(((((todo, acc), _), _), k), qpop).
      bisection_after_qpop_pre todo acc k qpop]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        bisection_poly_pop_result_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_after_qpop_impl.refine
  by (simp add: PR_CONST_def)

(* Keep PR_CONST wrappers intact in generated Sepref blocks below. Unfolding
   them here prevents operation identification from using registered callees. *)

definition bisection_pop_poly_args_pre ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> nat \<Rightarrow> bool" where
"bisection_pop_poly_args_pre todo qtodo acc k \<equiv>
  qtodo \<noteq> [] \<and>
  0 < length (last qtodo) \<and>
  length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
  k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
  dyadic_interval_vec_pushable2 todo \<and>
  dyadic_interval_vec_pushable acc \<and>
  length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"

definition bisection_pop_poly_args_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    bisection_loop_state nres" where
"bisection_pop_poly_args_monadic todo qtodo acc l_num r_num k \<equiv> doN {
  ASSERT (bisection_pop_poly_args_pre todo qtodo acc k);
  qpop \<leftarrow> (PR_CONST poly_vec_pop_last_monadic) qtodo;
  case qpop of (Q, qtodo) \<Rightarrow> doN {
    ASSERT (0 < length Q);
    ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (dyadic_interval_vec_pushable2 todo);
    ASSERT (dyadic_interval_vec_pushable acc);
    ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
    (PR_CONST bisection_after_pop_monadic) todo qtodo acc l_num r_num k Q
  }
}"

sepref_register "PR_CONST bisection_pop_poly_args_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      bisection_loop_state nres"

sepref_definition bisection_pop_poly_args_impl [llvm_code] is
  "uncurry5 bisection_pop_poly_args_monadic" ::
  "[\<lambda>(((((todo, qtodo), acc), _), _), k).
      bisection_pop_poly_args_pre todo qtodo acc k]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_pop_poly_args_monadic_def
  unfolding bisection_pop_poly_args_pre_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] =
    poly_vec_pop_last_impl_hnr
    bisection_after_pop_impl_hnr
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

lemma bisection_pop_poly_args_impl_hnr[sepref_fr_rules]:
  "(uncurry5 bisection_pop_poly_args_impl,
    uncurry5 (PR_CONST bisection_pop_poly_args_monadic)) \<in>
    [\<lambda>(((((todo, qtodo), acc), _), _), k).
      bisection_pop_poly_args_pre todo qtodo acc k]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
        bisection_loop_state_assn"
  using bisection_pop_poly_args_impl.refine
  by (simp add: PR_CONST_def)


definition bisection_loop_step_args_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> bisection_loop_state nres" where
"bisection_loop_step_args_monadic todo qtodo acc \<equiv> doN {
    ((l_num, r_num, k), todo) \<leftarrow>
      (PR_CONST dyadic_interval_vec_pop_last_monadic) todo;
    ASSERT (qtodo \<noteq> []);
    ASSERT (0 < length (last qtodo));
    ASSERT (length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (dyadic_interval_vec_pushable2 todo);
    ASSERT (dyadic_interval_vec_pushable acc);
    ASSERT (length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (bisection_pop_poly_args_pre todo qtodo acc k);
    (PR_CONST bisection_pop_poly_args_monadic)
      todo qtodo acc l_num r_num k
  }"

definition bisection_loop_step_monadic ::
  "bisection_loop_state \<Rightarrow> bisection_loop_state nres" where
"bisection_loop_step_monadic st \<equiv>
  (case st of ((todo, qtodo), acc) \<Rightarrow>
    (PR_CONST bisection_loop_step_args_monadic) todo qtodo acc)"

sepref_register "PR_CONST bisection_loop_step_monadic"
  :: "bisection_loop_state \<Rightarrow> bisection_loop_state nres"

sepref_register "PR_CONST bisection_loop_step_args_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> bisection_loop_state nres"

sepref_definition bisection_loop_step_args_impl [llvm_code] is
  "uncurry2 bisection_loop_step_args_monadic" ::
  "[\<lambda>((todo, qtodo), acc).
      bisection_loop_step_args_pre todo qtodo acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_loop_step_args_monadic_def
  unfolding bisection_loop_step_args_pre_def
  unfolding bisection_loop_step_pre_def
  unfolding bisection_loop_state_invar_def
  unfolding bisection_loop_cond_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [simp] = bisection_pop_poly_args_pre_def
  supply [sepref_fr_rules] =
    dyadic_interval_vec_pop_last_impl_hnr
    bisection_pop_poly_args_impl_hnr
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

lemma bisection_loop_step_args_impl_hnr[sepref_fr_rules]:
  "(uncurry2 bisection_loop_step_args_impl,
    uncurry2 (PR_CONST bisection_loop_step_args_monadic)) \<in>
    [\<lambda>((todo, qtodo), acc).
      bisection_loop_step_args_pre todo qtodo acc]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_loop_step_args_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition bisection_loop_step_impl [llvm_code] is
  "bisection_loop_step_monadic" ::
  "[bisection_loop_step_pre]\<^sub>a
    bisection_loop_state_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_loop_step_monadic_def
  supply [simp] = bisection_loop_step_args_pre_def
  supply [sepref_fr_rules] = bisection_loop_step_args_impl_hnr
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

lemma bisection_loop_step_impl_hnr[sepref_fr_rules]:
  "(bisection_loop_step_impl,
    PR_CONST bisection_loop_step_monadic) \<in>
    [bisection_loop_step_pre]\<^sub>a
      bisection_loop_state_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_loop_step_impl.refine
  by (simp add: PR_CONST_def)


definition bisection_loop_body_checked_monadic ::
  "bisection_loop_state \<Rightarrow> bisection_loop_state nres" where
"bisection_loop_body_checked_monadic st \<equiv>
  (if (PR_CONST bisection_loop_cond) st then
    (PR_CONST bisection_loop_step_monadic) st
   else
    RETURN st)"

sepref_register "PR_CONST bisection_loop_body_checked_monadic"
  :: "bisection_loop_state \<Rightarrow>
      bisection_loop_state nres"

definition bisection_loop_safe_invar ::
  "bisection_loop_state \<Rightarrow> bool" where
"bisection_loop_safe_invar st \<equiv>
  bisection_loop_state_invar st \<and>
  (bisection_loop_cond st \<longrightarrow>
    bisection_loop_step_pre st)"

sepref_definition bisection_loop_body_checked_impl [llvm_code] is
  "bisection_loop_body_checked_monadic" ::
  "[bisection_loop_safe_invar]\<^sub>a
    bisection_loop_state_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_loop_body_checked_monadic_def
  unfolding bisection_loop_safe_invar_def
  supply [sepref_fr_rules] =
    bisection_loop_cond_impl_hnr
    bisection_loop_step_impl_hnr
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

lemma bisection_loop_body_checked_impl_hnr[sepref_fr_rules]:
  "(bisection_loop_body_checked_impl,
    PR_CONST bisection_loop_body_checked_monadic) \<in>
    [bisection_loop_safe_invar]\<^sub>a
      bisection_loop_state_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_loop_body_checked_impl.refine
  by (simp add: PR_CONST_def)


definition bisection_loop_stateful_monadic ::
  "bisection_loop_state \<Rightarrow> bisection_loop_state nres" where
"bisection_loop_stateful_monadic st0 \<equiv> doN {
  st0 \<leftarrow> RETURN ((PR_CONST (ASSN_ANNOT bisection_loop_state_assn)) st0);
  WHILEIT bisection_loop_safe_invar
    (\<lambda>st. (PR_CONST bisection_loop_cond) st)
    (\<lambda>st. (PR_CONST bisection_loop_body_checked_monadic) st)
    st0
}"

sepref_register "PR_CONST bisection_loop_stateful_monadic"
  :: "bisection_loop_state \<Rightarrow>
      bisection_loop_state nres"

sepref_definition bisection_loop_stateful_impl [llvm_code] is
  "bisection_loop_stateful_monadic" ::
  "[bisection_loop_safe_invar]\<^sub>a
    bisection_loop_state_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_loop_stateful_monadic_def
  supply [sepref_fr_rules] =
    bisection_loop_cond_impl_hnr
    bisection_loop_body_checked_impl_hnr
  by sepref_dbg_keep

lemma bisection_loop_stateful_impl_hnr[sepref_fr_rules]:
  "(bisection_loop_stateful_impl,
    PR_CONST bisection_loop_stateful_monadic) \<in>
    [bisection_loop_safe_invar]\<^sub>a
      bisection_loop_state_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_loop_stateful_impl.refine
  by (simp add: PR_CONST_def)

definition bisection_loop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow>
    bisection_loop_state nres" where
"bisection_loop_monadic todo qtodo acc \<equiv> doN {
  (PR_CONST bisection_loop_stateful_monadic) ((todo, qtodo), acc)
}"

sepref_register "PR_CONST bisection_loop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow>
      bisection_loop_state nres"

sepref_definition bisection_loop_impl [llvm_code] is
  "uncurry2 bisection_loop_monadic" ::
  "[\<lambda>((todo, qtodo), acc).
      bisection_loop_safe_invar ((todo, qtodo), acc)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
      bisection_loop_state_assn"
  unfolding bisection_loop_monadic_def
  supply [sepref_fr_rules] = bisection_loop_stateful_impl_hnr
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

lemma bisection_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry2 bisection_loop_impl,
    uncurry2 (PR_CONST bisection_loop_monadic)) \<in>
    [\<lambda>((todo, qtodo), acc).
      bisection_loop_safe_invar ((todo, qtodo), acc)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
        bisection_loop_state_assn"
  using bisection_loop_impl.refine
  by (simp add: PR_CONST_def)

definition bisection_main_list ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_dyadic_interval_vec nres" where
"bisection_main_list l_num r_num k P \<equiv> doN {
  todo0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 1;
  c_l \<leftarrow> RETURN (COPY l_num);
  c_r \<leftarrow> RETURN (COPY r_num);
  let (todo_lns, todo_rns, todo_ks) = todo0;
  ASSERT (dyadic_interval_vec_pushable todo0);
  todo_lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) todo_lns c_l;
  todo_rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) todo_rns c_r;
  ASSERT (length todo_ks + 1 < max_snat LENGTH(gmp_poly_len));
  todo_ks \<leftarrow> mop_list_append todo_ks k;
  let todo1 = (todo_lns, todo_rns, todo_ks);
  qtodo0 \<leftarrow> (PR_CONST poly_vec_empty_sz_monadic) 1;
  ASSERT (length qtodo0 + 1 < max_snat LENGTH(gmp_poly_len));
  qtodo1 \<leftarrow> (PR_CONST poly_vec_push_monadic) qtodo0 P;
  acc0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 1;
  ASSERT (bisection_loop_safe_invar ((todo1, qtodo1), acc0));
  st \<leftarrow> (PR_CONST bisection_loop_monadic) todo1 qtodo1 acc0;
  let ((todo, qtodo), acc) = st;
  ASSERT (qtodo = []);
  (PR_CONST poly_vec_free_empty_monadic) qtodo;
  (PR_CONST dyadic_interval_vec_free_monadic) todo;
  RETURN acc
}"

sepref_register "PR_CONST bisection_main_list"
  :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
      gmp_dyadic_interval_vec nres"

sepref_definition bisection_main_list_impl [llvm_code] is
  "uncurry3 bisection_main_list" ::
  "[\<lambda>(((_, _), k), P).
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding bisection_main_list_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [simp] =
    bisection_loop_safe_invar_def
    bisection_loop_state_invar_def
    bisection_loop_step_pre_def
    bisection_loop_cond_def
    dyadic_interval_vec_invar_def
    dyadic_interval_vec_pushable_def
    dyadic_interval_vec_pushable2_def
  supply [sepref_fr_rules] =
    bisection_loop_impl_hnr
    poly_vec_free_empty_impl_hnr
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma bisection_main_list_impl_hnr[sepref_fr_rules]:
  "(uncurry3 bisection_main_list_impl,
    uncurry3 (PR_CONST bisection_main_list)) \<in>
    [\<lambda>(((_, _), k), P).
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        gmp_dyadic_interval_vec_assn"
  using bisection_main_list_impl.refine
  by (simp add: PR_CONST_def)

end
