theory Bisection
  imports "IsaRRI_LLVM.Poly_Vec" "IsaRRI_LLVM.Dyadic_Interval" "IsaRRI_LLVM.Interval_Eval" Count
begin

text \<open>The subdivision loop shared by every bisection-based solver: loop state, the midpoint
  zero test, the three branch arms (zero / one / split), child push, after-pop and the loop
  step. Main definitions: \<open>bisection_loop_state\<close> and the \<open>bisection_*\<close> loop and branch operations.
  The \<open>half_eval_*\<close> midpoint zero test they rest on is in \<open>Interval_Eval\<close>. The Newton and
  truncating solvers are bisection solvers with extra machinery on top, so they share this loop.\<close>

type_synonym bisection_loop_state =
  "(gmp_dyadic_interval_vec \<times> gmp_poly list) \<times>
    gmp_dyadic_interval_vec"

abbreviation bisection_loop_state_assn where
"bisection_loop_state_assn \<equiv>
  (gmp_dyadic_interval_vec_assn \<times>\<^sub>a
    gmp_poly_vec_assn) \<times>\<^sub>a
    gmp_dyadic_interval_vec_assn"

definition bisection_loop_state_invar ::
  "bisection_loop_state \<Rightarrow> bool" where
"bisection_loop_state_invar st \<equiv>
  (let ((todo, qtodo), acc) = st in
    dyadic_interval_vec_invar todo \<and>
    dyadic_interval_vec_invar acc \<and>
    (case todo of (lns, _, _) \<Rightarrow> length qtodo = length lns))"

definition bisection_mid_zero_monadic :: "gmp_poly \<Rightarrow> bool nres" where
"bisection_mid_zero_monadic Q \<equiv> (PR_CONST half_eval_zero_monadic) Q"

sepref_register "PR_CONST bisection_mid_zero_monadic"
  :: "gmp_poly \<Rightarrow> bool nres"

sepref_definition bisection_mid_zero_impl [llvm_inline] is
  "bisection_mid_zero_monadic" ::
  "[\<lambda>Q. 0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding bisection_mid_zero_monadic_def
  supply [sepref_fr_rules] = half_eval_zero_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

definition bisection_loop_cond_mop_monadic ::
  "bisection_loop_state \<Rightarrow> bool nres" where
"bisection_loop_cond_mop_monadic st \<equiv>
  (case st of ((todo, qtodo), acc) \<Rightarrow>
    (PR_CONST gmp_dyadic_interval_vec_nonempty) todo)"

definition bisection_branch_zero_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> bisection_loop_state nres" where
"bisection_branch_zero_monadic todo qtodo acc l_num r_num k Q \<equiv> doN {
  (PR_CONST mpzb_discard_monadic) l_num;
  (PR_CONST mpzb_discard_monadic) r_num;
  (PR_CONST poly_free_monadic) Q;
  RETURN ((todo, qtodo), acc)
}"

sepref_register "PR_CONST bisection_branch_zero_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> bisection_loop_state nres"

definition bisection_branch_one_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> bisection_loop_state nres" where
"bisection_branch_one_monadic todo qtodo acc l_num r_num k Q \<equiv> doN {
  let (lns, rns, ks) = acc;
  ASSERT (dyadic_interval_vec_pushable acc);
  lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) lns l_num;
  rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) rns r_num;
  ASSERT (length ks + 1 < max_snat LENGTH(gmp_poly_len));
  ks \<leftarrow> mop_list_append ks k;
  (PR_CONST poly_free_monadic) Q;
  RETURN ((todo, qtodo), (lns, rns, ks))
}"

sepref_register "PR_CONST bisection_branch_one_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> bisection_loop_state nres"

definition bisection_push_children_monadic ::
  "gmp_poly list \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly list nres" where
"bisection_push_children_monadic qtodo Q \<equiv> doN {
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
  (ql, qr) \<leftarrow> (PR_CONST carried_left_right_monadic) Q;
  \<comment> \<open>\<open>carried_left_right\<close> consumes \<open>Q\<close> in place, so there is no free here\<close>
  (PR_CONST poly_vec_push2_monadic) qtodo ql qr
}"

sepref_register "PR_CONST bisection_push_children_monadic"
  :: "gmp_poly list \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly list nres"

sepref_definition bisection_push_children_impl [llvm_code] is
  "uncurry bisection_push_children_monadic" ::
  "[\<lambda>(qtodo, Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_vec_assn"
  unfolding bisection_push_children_monadic_def
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

lemma bisection_push_children_impl_hnr[sepref_fr_rules]:
  "(uncurry bisection_push_children_impl,
    uncurry (PR_CONST bisection_push_children_monadic)) \<in>
    [\<lambda>(qtodo, Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
        gmp_poly_vec_assn"
  using bisection_push_children_impl.refine
  by (simp add: PR_CONST_def)

definition bisection_split_pair_state_monadic ::
  "(gmp_dyadic_interval_vec \<times> gmp_poly list) \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    (gmp_dyadic_interval_vec \<times> gmp_poly list) nres" where
"bisection_split_pair_state_monadic st l_num r_num k Q \<equiv> doN {
  let (todo, qtodo) = st;
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable2 todo);
  todo \<leftarrow> (PR_CONST dyadic_interval_vec_push_children_monadic) todo l_num r_num k;
  qtodo \<leftarrow> (PR_CONST bisection_push_children_monadic) qtodo Q;
  RETURN (todo, qtodo)
}"

sepref_register "PR_CONST bisection_split_pair_state_monadic"
  :: "(gmp_dyadic_interval_vec \<times> gmp_poly list) \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
      (gmp_dyadic_interval_vec \<times> gmp_poly list) nres"

sepref_definition bisection_split_pair_state_impl [llvm_code] is
  "uncurry4 bisection_split_pair_state_monadic" ::
  "[\<lambda>((((st, _), _), k), Q).
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
  unfolding bisection_split_pair_state_monadic_def
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

definition bisection_branch_split_nonroot_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> bisection_loop_state nres" where
"bisection_branch_split_nonroot_monadic todo qtodo acc l_num r_num k Q \<equiv> doN {
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  pair \<leftarrow> (PR_CONST bisection_split_pair_state_monadic)
    (todo, qtodo) l_num r_num k Q;
  RETURN (pair, acc)
}"

sepref_register "PR_CONST bisection_branch_split_nonroot_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> bisection_loop_state nres"

definition bisection_branch_split_root_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> bisection_loop_state nres" where
"bisection_branch_split_root_monadic todo qtodo acc l_num r_num k Q \<equiv> doN {
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable acc);
  acc \<leftarrow> (PR_CONST carried_push_mid_monadic) acc l_num r_num k;
  pair \<leftarrow> (PR_CONST bisection_split_pair_state_monadic)
    (todo, qtodo) l_num r_num k Q;
  RETURN (pair, acc)
}"

sepref_register "PR_CONST bisection_branch_split_root_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> bisection_loop_state nres"

definition bisection_branch_split_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> bisection_loop_state nres" where
"bisection_branch_split_monadic todo qtodo acc l_num r_num k Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  is_root \<leftarrow> (PR_CONST bisection_mid_zero_monadic) Q;
  if is_root then
    (PR_CONST bisection_branch_split_root_monadic) todo qtodo acc l_num r_num k Q
  else
    (PR_CONST bisection_branch_split_nonroot_monadic) todo qtodo acc l_num r_num k Q
}"

sepref_register "PR_CONST bisection_branch_split_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> bisection_loop_state nres"

definition bisection_after_pop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> bisection_loop_state nres" where
"bisection_after_pop_monadic todo qtodo acc l_num r_num k Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  cnt \<leftarrow> (PR_CONST carried_descartes_count_trunc_monadic) Q;
  if cnt = 0 then
    (PR_CONST bisection_branch_zero_monadic)
      todo qtodo acc l_num r_num k Q
  else if cnt = 1 then
    (PR_CONST bisection_branch_one_monadic)
      todo qtodo acc l_num r_num k Q
  else
    (PR_CONST bisection_branch_split_monadic)
      todo qtodo acc l_num r_num k Q
}"

sepref_register "PR_CONST bisection_after_pop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> bisection_loop_state nres"

end
