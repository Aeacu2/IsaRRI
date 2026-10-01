theory Hybrid_Solver_Pipeline
  imports Hybrid_Solver_Window
begin

text \<open>Hybrid solver, part 3 of 3 (see \<open>Hybrid_Solver_Dispatch\<close> for the design note).
  Layer: SEPREF.
  Main exports: \<open>hybrid_loop_step_args_monadic\<close>, \<open>hybrid_loop_monadic\<close>,
  \<open>hybrid_main_list_monadic\<close> / \<open>_impl\<close>, and the all-roots split entry. Contents: the loop step,
  the loop, the main-list wrapper, and the rp-anchored all-roots split pipeline.\<close>

section \<open>Loop step, loop, main list\<close>

text \<open>The pop-and-dispatch body, taking every worklist column as a separate argument. Doing the
  pops and the arithmetic ASSERT chain (\<open>k * (length rp - 1) < max_snat\<close>) inside a wide
  state-\<open>case\<close> fails Sepref's \<open>trans\<close> phase (an inline \<open>op_snat_mul\<close> in a heap body); as a
  separate-columns op the phases handle it. The todo pop's conditional HNR needs \<open>invar todo\<close> and
  a non-empty \<open>lns\<close>, which are ASSERTed at the call.\<close>
definition hybrid_loop_step_args_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres" where
"hybrid_loop_step_args_monadic todo qtodo es ss cs gs acc rp \<equiv> doN {
    ASSERT (dyadic_interval_vec_invar todo);
    ASSERT (case todo of (lns, _, _) \<Rightarrow> lns \<noteq> []);
    ((l_num, r_num, k), todo) \<leftarrow> (PR_CONST dyadic_interval_vec_pop_last_monadic) todo;
    ASSERT (qtodo \<noteq> []);
    (Q, qtodo) \<leftarrow> (PR_CONST poly_vec_pop_last_monadic) qtodo;
    ASSERT (es \<noteq> []);
    (e, es) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) es;
    ASSERT (ss \<noteq> []);
    (s, ss) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) ss;
    ASSERT (cs \<noteq> []);
    (c, cs) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) cs;
    ASSERT (gs \<noteq> []);
    (g, gs) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) gs;
    ASSERT (0 < length Q);
    ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
    \<comment> \<open>\<^bold>\<open>The right-child decide needs one more unit of headroom.\<close> It evaluates the left child at
       \<open>1\<close>, and \<open>poly_eval1_pair_monadic\<close> needs \<open>+2\<close> where the other ops need \<open>+1\<close>. \<open>Q\<close> was just
       popped from the worklist, so there is no caller to demand it from: as for the \<open>+1\<close> assertion
       beside it, the loop invariant establishes it, and that is a refinement obligation.\<close>
    ASSERT (length Q + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len));
    ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (s + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (0 < length rp);
    ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
    ASSERT (dyadic_interval_vec_pushable2 todo);
    ASSERT (dyadic_interval_vec_pushable acc);
    ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length es + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length ss + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length cs + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length gs + 2 < max_snat LENGTH(gmp_poly_len));
    (PR_CONST hybrid_after_pop_monadic)
      todo qtodo es ss cs gs acc rp l_num r_num k e s c g Q
  }"

sepref_register "PR_CONST hybrid_loop_step_args_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres"

sepref_definition hybrid_loop_step_args_impl [llvm_code] is
  "uncurry7 hybrid_loop_step_args_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a hybrid_state_assn"
  unfolding hybrid_loop_step_args_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] =
    dyadic_interval_vec_pop_last_impl_hnr
    poly_vec_pop_last_impl_hnr
    dyadic_exp_pop_last_impl_hnr
    hybrid_after_pop_impl_hnr
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

lemma hybrid_loop_step_args_impl_hnr[sepref_fr_rules]:
  "(uncurry7 hybrid_loop_step_args_impl, uncurry7 (PR_CONST hybrid_loop_step_args_monadic)) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a hybrid_state_assn"
  using hybrid_loop_step_args_impl.refine by (simp add: PR_CONST_def)

definition hybrid_loop_step_monadic :: "hybrid_state \<Rightarrow> hybrid_state nres" where
"hybrid_loop_step_monadic st \<equiv>
  (case st of ((todo, qtodo, es, ss, cs, gs, rp), acc) \<Rightarrow>
    (PR_CONST hybrid_loop_step_args_monadic) todo qtodo es ss cs gs acc rp)"

sepref_register "PR_CONST hybrid_loop_step_monadic" :: "hybrid_state \<Rightarrow> hybrid_state nres"

definition hybrid_loop_step_pre :: "hybrid_state \<Rightarrow> bool" where
"hybrid_loop_step_pre st \<equiv>
  (case st of ((todo, qtodo, es, ss, cs, gs, rp), acc) \<Rightarrow>
    (case todo of (lns, rns, ks) \<Rightarrow>
      lns \<noteq> [] \<and>
      dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks) \<and>
      dyadic_interval_vec_pushable acc \<and>
      qtodo \<noteq> [] \<and> es \<noteq> [] \<and> ss \<noteq> [] \<and> cs \<noteq> [] \<and> gs \<noteq> [] \<and>
      0 < length (last qtodo) \<and>
      length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      last ks + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      last ss + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      last ks * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length (butlast gs) + 2 < max_snat LENGTH(gmp_poly_len)))"

sepref_definition hybrid_loop_step_impl [llvm_code] is
  "hybrid_loop_step_monadic" ::
  "[hybrid_loop_step_pre]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  unfolding hybrid_loop_step_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] = hybrid_loop_step_args_impl_hnr
  by sepref

lemma hybrid_loop_step_impl_hnr[sepref_fr_rules]:
  "(hybrid_loop_step_impl, PR_CONST hybrid_loop_step_monadic) \<in>
    [hybrid_loop_step_pre]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  using hybrid_loop_step_impl.refine by (simp add: PR_CONST_def)

definition hybrid_loop_safe_invar :: "hybrid_state \<Rightarrow> bool" where
"hybrid_loop_safe_invar st \<equiv>
  hybrid_loop_state_invar st \<and> (hybrid_loop_cond st \<longrightarrow> hybrid_loop_step_pre st)"

definition hybrid_loop_body_checked_monadic :: "hybrid_state \<Rightarrow> hybrid_state nres" where
"hybrid_loop_body_checked_monadic st \<equiv>
  (if (PR_CONST hybrid_loop_cond) st then
    (PR_CONST hybrid_loop_step_monadic) st
   else RETURN st)"

sepref_register "PR_CONST hybrid_loop_body_checked_monadic"
  :: "hybrid_state \<Rightarrow> hybrid_state nres"

sepref_definition hybrid_loop_body_checked_impl [llvm_code] is
  "hybrid_loop_body_checked_monadic" ::
  "[hybrid_loop_safe_invar]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  unfolding hybrid_loop_body_checked_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [simp] = hybrid_loop_safe_invar_def hybrid_loop_step_pre_def
  supply [sepref_fr_rules] = hybrid_loop_cond_impl_hnr hybrid_loop_step_impl_hnr
  by sepref

lemma hybrid_loop_body_checked_impl_hnr[sepref_fr_rules]:
  "(hybrid_loop_body_checked_impl, PR_CONST hybrid_loop_body_checked_monadic) \<in>
    [hybrid_loop_safe_invar]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  using hybrid_loop_body_checked_impl.refine by (simp add: PR_CONST_def)

definition hybrid_loop_stateful_monadic :: "hybrid_state \<Rightarrow> hybrid_state nres" where
"hybrid_loop_stateful_monadic st0 \<equiv> doN {
  st0 \<leftarrow> RETURN ((PR_CONST (ASSN_ANNOT hybrid_state_assn)) st0);
  WHILEIT hybrid_loop_safe_invar
    (\<lambda>st. (PR_CONST hybrid_loop_cond) st)
    (\<lambda>st. (PR_CONST hybrid_loop_body_checked_monadic) st)
    st0
}"

sepref_register "PR_CONST hybrid_loop_stateful_monadic" :: "hybrid_state \<Rightarrow> hybrid_state nres"

sepref_definition hybrid_loop_stateful_impl [llvm_code] is
  "hybrid_loop_stateful_monadic" ::
  "[hybrid_loop_safe_invar]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  unfolding hybrid_loop_stateful_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_fr_rules] = hybrid_loop_cond_impl_hnr hybrid_loop_body_checked_impl_hnr
  by sepref

lemma hybrid_loop_stateful_impl_hnr[sepref_fr_rules]:
  "(hybrid_loop_stateful_impl, PR_CONST hybrid_loop_stateful_monadic) \<in>
    [hybrid_loop_safe_invar]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  using hybrid_loop_stateful_impl.refine by (simp add: PR_CONST_def)

definition hybrid_loop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> hybrid_state nres" where
"hybrid_loop_monadic todo qtodo es ss cs gs rp acc \<equiv>
  (PR_CONST hybrid_loop_stateful_monadic) ((todo, qtodo, es, ss, cs, gs, rp), acc)"

sepref_register "PR_CONST hybrid_loop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> hybrid_state nres"

sepref_definition hybrid_loop_impl [llvm_code] is
  "uncurry7 hybrid_loop_monadic" ::
  "[\<lambda>(((((((todo, qtodo), es), ss), cs), gs), rp), acc).
      hybrid_loop_safe_invar (((todo, qtodo, es, ss, cs, gs, rp), acc))]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  unfolding hybrid_loop_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  by sepref

lemma hybrid_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry7 hybrid_loop_impl, uncurry7 (PR_CONST hybrid_loop_monadic)) \<in>
    [\<lambda>(((((((todo, qtodo), es), ss), cs), gs), rp), acc).
      hybrid_loop_safe_invar (((todo, qtodo, es, ss, cs, gs, rp), acc))]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  using hybrid_loop_impl.refine by (simp add: PR_CONST_def)

text \<open>The main-list entry: bail's seeding + \<open>gs = [0]\<close> (root exact, guard 0) + the
  OWNED anchor \<open>rp\<close> threaded into the state and freed at the end.\<close>
definition hybrid_main_list_monadic ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_dyadic_interval_vec nres" where
"hybrid_main_list_monadic e0 l_num r_num k P rp \<equiv> doN {
  \<comment> \<open>Seed capacity \<open>64\<close>: \<open>n\<close> is a pure array-list capacity hint
    (@{const poly_empty_sz_monadic}/@{const poly_vec_empty_sz_monadic} both \<open>RETURN []\<close>
    regardless of \<open>n\<close>), so this only avoids early-growth reallocation on the
    worklist/queue vectors; no SPEC change.\<close>
  todo0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 64;
  c_l \<leftarrow> RETURN (COPY l_num);
  c_r \<leftarrow> RETURN (COPY r_num);
  let (todo_lns, todo_rns, todo_ks) = todo0;
  ASSERT (dyadic_interval_vec_pushable (todo_lns, todo_rns, todo_ks));
  todo_lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) todo_lns c_l;
  todo_rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) todo_rns c_r;
  ASSERT (length todo_ks + 1 < max_snat LENGTH(gmp_poly_len));
  todo_ks \<leftarrow> mop_list_append todo_ks k;
  todo1 \<leftarrow> RETURN (todo_lns, todo_rns, todo_ks);
  c0 \<leftarrow> (PR_CONST carried_descartes_count_trunc_monadic) P;
  qtodo0 \<leftarrow> (PR_CONST poly_vec_empty_sz_monadic) 64;
  ASSERT (length qtodo0 + 1 < max_snat LENGTH(gmp_poly_len));
  qtodo1 \<leftarrow> (PR_CONST poly_vec_push_monadic) qtodo0 P;
  let es0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length es0 + 1 < max_snat LENGTH(gmp_poly_len));
  es1 \<leftarrow> mop_list_append es0 e0;
  let ss0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length ss0 + 1 < max_snat LENGTH(gmp_poly_len));
  ss1 \<leftarrow> mop_list_append ss0 0;
  let cs0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length cs0 + 1 < max_snat LENGTH(gmp_poly_len));
  cs1 \<leftarrow> mop_list_append cs0 c0;
  let gs0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length gs0 + 1 < max_snat LENGTH(gmp_poly_len));
  gs1 \<leftarrow> mop_list_append gs0 0;
  acc0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 64;
  ASSERT (hybrid_loop_safe_invar ((todo1, qtodo1, es1, ss1, cs1, gs1, rp), acc0));
  st \<leftarrow> (PR_CONST hybrid_loop_monadic) todo1 qtodo1 es1 ss1 cs1 gs1 rp acc0;
  let ((todo, qtodo, es, ss, cs, gs, rpf), acc) = st;
  ASSERT (qtodo = []);
  (PR_CONST poly_vec_free_empty_monadic) qtodo;
  (PR_CONST dyadic_interval_vec_free_monadic) todo;
  (PR_CONST poly_free_monadic) rpf;
  RETURN acc
}"

sepref_register "PR_CONST hybrid_main_list_monadic"
  :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
      gmp_dyadic_interval_vec nres"

sepref_definition hybrid_main_list_impl [llvm_code] is
  "uncurry5 hybrid_main_list_monadic" ::
  "[\<lambda>(((((_, _), _), k), P), rp).
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding hybrid_main_list_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma hybrid_main_list_impl_hnr[sepref_fr_rules]:
  "(uncurry5 hybrid_main_list_impl,
    uncurry5 (PR_CONST hybrid_main_list_monadic)) \<in>
    [\<lambda>(((((_, _), _), k), P), rp).
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  using hybrid_main_list_impl.refine by (simp add: PR_CONST_def)

section \<open>The split all-roots pipeline (rp-anchored halves, bail seeding)\<close>

definition hybrid_split_pos_solve_monadic ::
  "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"hybrid_split_pos_solve_monadic xs \<equiv> doN {
  ASSERT (1 \<le> length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
  kpos \<leftarrow> (PR_CONST kiou_bound_k_monadic) xs;
  ASSERT (kpos * length xs < max_snat LENGTH(gmp_poly_len) \<and>
          kpos < max_snat LENGTH(gmp_poly_len));
  rp \<leftarrow> (PR_CONST poly_copy_monadic) xs;  \<comment> \<open>\<open>poly_copy_monadic\<close> is a direct copy loop with the same \<open>= xs\<close> specification and borrowed
     ownership; a clone by scaling with \<open>1\<close> would allocate and multiply for nothing.\<close>
  ASSERT (0 < length rp \<and> length rp + 1 < max_snat LENGTH(gmp_poly_len));
  Pinit \<leftarrow> (PR_CONST split_init_pow2_l0_monadic) kpos xs;
  ASSERT (0 < length Pinit \<and> length Pinit + 1 < max_snat LENGTH(gmp_poly_len));
  zl \<leftarrow> RETURN (mpz_from_int 0);
  rpos \<leftarrow> (PR_CONST mpz_pow2_monadic) kpos;
  accP \<leftarrow> (PR_CONST hybrid_main_list_monadic) split_pipeline_e0 zl rpos 0 Pinit rp;
  (PR_CONST mpzb_discard_monadic) rpos;
  (PR_CONST mpzb_discard_monadic) zl;
  RETURN accP
}"

sepref_register "PR_CONST hybrid_split_pos_solve_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition hybrid_split_pos_solve_impl [llvm_code] is
  "hybrid_split_pos_solve_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding hybrid_split_pos_solve_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  unfolding split_pipeline_e0_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma hybrid_split_pos_solve_impl_hnr[sepref_fr_rules]:
  "(hybrid_split_pos_solve_impl, PR_CONST hybrid_split_pos_solve_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using hybrid_split_pos_solve_impl.refine by (simp add: PR_CONST_def)

definition hybrid_split_neg_solve_monadic ::
  "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"hybrid_split_neg_solve_monadic xs \<equiv> doN {
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  Qb \<leftarrow> (PR_CONST poly_copy_monadic) xs;  
  ASSERT (length Qb + 1 < max_snat LENGTH(gmp_poly_len));
  Qb \<leftarrow> (PR_CONST poly_reflect_in_place_monadic) Qb;
  ASSERT (1 \<le> length Qb \<and> length Qb + 1 < max_snat LENGTH(gmp_poly_len));
  kneg \<leftarrow> (PR_CONST kiou_bound_k_monadic) Qb;
  ASSERT (kneg * length Qb < max_snat LENGTH(gmp_poly_len) \<and>
          kneg < max_snat LENGTH(gmp_poly_len));
  Qinit \<leftarrow> (PR_CONST split_init_pow2_l0_monadic) kneg Qb;
  ASSERT (0 < length Qinit \<and> length Qinit + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length Qb);
  zln \<leftarrow> RETURN (mpz_from_int 0);
  rneg \<leftarrow> (PR_CONST mpz_pow2_monadic) kneg;
  accQ \<leftarrow> (PR_CONST hybrid_main_list_monadic) split_pipeline_e0 zln rneg 0 Qinit Qb;
  (PR_CONST mpzb_discard_monadic) rneg;
  (PR_CONST mpzb_discard_monadic) zln;
  RETURN accQ
}"

sepref_register "PR_CONST hybrid_split_neg_solve_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition hybrid_split_neg_solve_impl [llvm_code] is
  "hybrid_split_neg_solve_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding hybrid_split_neg_solve_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  unfolding split_pipeline_e0_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma hybrid_split_neg_solve_impl_hnr[sepref_fr_rules]:
  "(hybrid_split_neg_solve_impl, PR_CONST hybrid_split_neg_solve_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using hybrid_split_neg_solve_impl.refine by (simp add: PR_CONST_def)

definition hybrid_isolate_all_split_main ::
  "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres" where
"hybrid_isolate_all_split_main xs \<equiv> doN {
  ASSERT (2 \<le> length xs);
  accP \<leftarrow> (PR_CONST hybrid_split_pos_solve_monadic) xs;
  accQ \<leftarrow> (PR_CONST hybrid_split_neg_solve_monadic) xs;
  xs0 \<leftarrow> (PR_CONST dsc_split_zero_check_monadic) xs;
  RETURN (accP, accQ, xs0)
}"

sepref_register "PR_CONST hybrid_isolate_all_split_main"
  :: "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres"

sepref_definition hybrid_isolate_all_split_main_impl [llvm_code] is
  "hybrid_isolate_all_split_main" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
    gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  unfolding hybrid_isolate_all_split_main_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma hybrid_isolate_all_split_main_impl_hnr[sepref_fr_rules]:
  "(hybrid_isolate_all_split_main_impl, PR_CONST hybrid_isolate_all_split_main) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  using hybrid_isolate_all_split_main_impl.refine by (simp add: PR_CONST_def)
section \<open>The deflating stack: the loop chain over \<open>defl_branch_split\<close>\<close>

text \<open>Twins of the chain above that differ only in which child-build op they reach: every
  level calls its \<open>defl_\<close> twin, down to \<open>defl_dispatch_monadic\<close>/\<open>defl_gate_open_monadic\<close>
  (\<open>Hybrid_Solver_Window\<close>) and \<open>defl_branch_split_monadic\<close> (\<open>Hybrid_Solver_Dispatch\<close>). The loop
  predicates (\<open>hybrid_loop_cond\<close>, \<open>hybrid_loop_safe_invar\<close>, \<open>hybrid_loop_step_pre\<close>) and all
  leaf ops are shared, since their generated code does not depend on which stack calls them.
  Consumer: \<open>Power_Sub_Entry_Impl\<close>, through \<open>defl_isolate_all_split_main\<close>.\<close>

definition defl_loop_step_args_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres" where
"defl_loop_step_args_monadic todo qtodo es ss cs gs acc rp \<equiv> doN {
    ASSERT (dyadic_interval_vec_invar todo);
    ASSERT (case todo of (lns, _, _) \<Rightarrow> lns \<noteq> []);
    ((l_num, r_num, k), todo) \<leftarrow> (PR_CONST dyadic_interval_vec_pop_last_monadic) todo;
    ASSERT (qtodo \<noteq> []);
    (Q, qtodo) \<leftarrow> (PR_CONST poly_vec_pop_last_monadic) qtodo;
    ASSERT (es \<noteq> []);
    (e, es) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) es;
    ASSERT (ss \<noteq> []);
    (s, ss) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) ss;
    ASSERT (cs \<noteq> []);
    (c, cs) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) cs;
    ASSERT (gs \<noteq> []);
    (g, gs) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) gs;
    ASSERT (0 < length Q);
    ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
    \<comment> \<open>\<^bold>\<open>The right-child decide needs one more unit of headroom.\<close> It evaluates the left child at
       \<open>1\<close>, and \<open>poly_eval1_pair_monadic\<close> needs \<open>+2\<close> where the other ops need \<open>+1\<close>. \<open>Q\<close> was just
       popped from the worklist, so there is no caller to demand it from: as for the \<open>+1\<close> assertion
       beside it, the loop invariant establishes it, and that is a refinement obligation.\<close>
    ASSERT (length Q + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len));
    ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (s + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (0 < length rp);
    ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
    ASSERT (dyadic_interval_vec_pushable2 todo);
    ASSERT (dyadic_interval_vec_pushable acc);
    ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length es + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length ss + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length cs + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length gs + 2 < max_snat LENGTH(gmp_poly_len));
    (PR_CONST defl_after_pop_monadic)
      todo qtodo es ss cs gs acc rp l_num r_num k e s c g Q
  }"

sepref_register "PR_CONST defl_loop_step_args_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres"

sepref_definition defl_loop_step_args_impl [llvm_code] is
  "uncurry7 defl_loop_step_args_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a hybrid_state_assn"
  unfolding defl_loop_step_args_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] =
    dyadic_interval_vec_pop_last_impl_hnr
    poly_vec_pop_last_impl_hnr
    dyadic_exp_pop_last_impl_hnr
    defl_after_pop_impl_hnr
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

lemma defl_loop_step_args_impl_hnr[sepref_fr_rules]:
  "(uncurry7 defl_loop_step_args_impl, uncurry7 (PR_CONST defl_loop_step_args_monadic)) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a hybrid_state_assn"
  using defl_loop_step_args_impl.refine by (simp add: PR_CONST_def)

definition defl_loop_step_monadic :: "hybrid_state \<Rightarrow> hybrid_state nres" where
"defl_loop_step_monadic st \<equiv>
  (case st of ((todo, qtodo, es, ss, cs, gs, rp), acc) \<Rightarrow>
    (PR_CONST defl_loop_step_args_monadic) todo qtodo es ss cs gs acc rp)"

sepref_register "PR_CONST defl_loop_step_monadic" :: "hybrid_state \<Rightarrow> hybrid_state nres"

sepref_definition defl_loop_step_impl [llvm_code] is
  "defl_loop_step_monadic" ::
  "[hybrid_loop_step_pre]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  unfolding defl_loop_step_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] = defl_loop_step_args_impl_hnr
  by sepref

lemma defl_loop_step_impl_hnr[sepref_fr_rules]:
  "(defl_loop_step_impl, PR_CONST defl_loop_step_monadic) \<in>
    [hybrid_loop_step_pre]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  using defl_loop_step_impl.refine by (simp add: PR_CONST_def)

definition defl_loop_body_checked_monadic :: "hybrid_state \<Rightarrow> hybrid_state nres" where
"defl_loop_body_checked_monadic st \<equiv>
  (if (PR_CONST hybrid_loop_cond) st then
    (PR_CONST defl_loop_step_monadic) st
   else RETURN st)"

sepref_register "PR_CONST defl_loop_body_checked_monadic"
  :: "hybrid_state \<Rightarrow> hybrid_state nres"

sepref_definition defl_loop_body_checked_impl [llvm_code] is
  "defl_loop_body_checked_monadic" ::
  "[hybrid_loop_safe_invar]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  unfolding defl_loop_body_checked_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [simp] = hybrid_loop_safe_invar_def hybrid_loop_step_pre_def
  supply [sepref_fr_rules] = hybrid_loop_cond_impl_hnr defl_loop_step_impl_hnr
  by sepref

lemma defl_loop_body_checked_impl_hnr[sepref_fr_rules]:
  "(defl_loop_body_checked_impl, PR_CONST defl_loop_body_checked_monadic) \<in>
    [hybrid_loop_safe_invar]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  using defl_loop_body_checked_impl.refine by (simp add: PR_CONST_def)

definition defl_loop_stateful_monadic :: "hybrid_state \<Rightarrow> hybrid_state nres" where
"defl_loop_stateful_monadic st0 \<equiv> doN {
  st0 \<leftarrow> RETURN ((PR_CONST (ASSN_ANNOT hybrid_state_assn)) st0);
  WHILEIT hybrid_loop_safe_invar
    (\<lambda>st. (PR_CONST hybrid_loop_cond) st)
    (\<lambda>st. (PR_CONST defl_loop_body_checked_monadic) st)
    st0
}"

sepref_register "PR_CONST defl_loop_stateful_monadic" :: "hybrid_state \<Rightarrow> hybrid_state nres"

sepref_definition defl_loop_stateful_impl [llvm_code] is
  "defl_loop_stateful_monadic" ::
  "[hybrid_loop_safe_invar]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  unfolding defl_loop_stateful_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_fr_rules] = hybrid_loop_cond_impl_hnr defl_loop_body_checked_impl_hnr
  by sepref

lemma defl_loop_stateful_impl_hnr[sepref_fr_rules]:
  "(defl_loop_stateful_impl, PR_CONST defl_loop_stateful_monadic) \<in>
    [hybrid_loop_safe_invar]\<^sub>a hybrid_state_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  using defl_loop_stateful_impl.refine by (simp add: PR_CONST_def)

definition defl_loop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> hybrid_state nres" where
"defl_loop_monadic todo qtodo es ss cs gs rp acc \<equiv>
  (PR_CONST defl_loop_stateful_monadic) ((todo, qtodo, es, ss, cs, gs, rp), acc)"

sepref_register "PR_CONST defl_loop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> hybrid_state nres"

sepref_definition defl_loop_impl [llvm_code] is
  "uncurry7 defl_loop_monadic" ::
  "[\<lambda>(((((((todo, qtodo), es), ss), cs), gs), rp), acc).
      hybrid_loop_safe_invar (((todo, qtodo, es, ss, cs, gs, rp), acc))]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  unfolding defl_loop_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  by sepref

lemma defl_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry7 defl_loop_impl, uncurry7 (PR_CONST defl_loop_monadic)) \<in>
    [\<lambda>(((((((todo, qtodo), es), ss), cs), gs), rp), acc).
      hybrid_loop_safe_invar (((todo, qtodo, es, ss, cs, gs, rp), acc))]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  using defl_loop_impl.refine by (simp add: PR_CONST_def)

definition defl_main_list_monadic ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_dyadic_interval_vec nres" where
"defl_main_list_monadic e0 l_num r_num k P rp \<equiv> doN {
  \<comment> \<open>Seed capacity \<open>64\<close>: \<open>n\<close> is a pure array-list capacity hint
    (@{const poly_empty_sz_monadic}/@{const poly_vec_empty_sz_monadic} both \<open>RETURN []\<close>
    regardless of \<open>n\<close>), so this only avoids early-growth reallocation on the
    worklist/queue vectors; no SPEC change.\<close>
  todo0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 64;
  c_l \<leftarrow> RETURN (COPY l_num);
  c_r \<leftarrow> RETURN (COPY r_num);
  let (todo_lns, todo_rns, todo_ks) = todo0;
  ASSERT (dyadic_interval_vec_pushable (todo_lns, todo_rns, todo_ks));
  todo_lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) todo_lns c_l;
  todo_rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) todo_rns c_r;
  ASSERT (length todo_ks + 1 < max_snat LENGTH(gmp_poly_len));
  todo_ks \<leftarrow> mop_list_append todo_ks k;
  todo1 \<leftarrow> RETURN (todo_lns, todo_rns, todo_ks);
  c0 \<leftarrow> (PR_CONST carried_descartes_count_trunc_monadic) P;
  qtodo0 \<leftarrow> (PR_CONST poly_vec_empty_sz_monadic) 64;
  ASSERT (length qtodo0 + 1 < max_snat LENGTH(gmp_poly_len));
  qtodo1 \<leftarrow> (PR_CONST poly_vec_push_monadic) qtodo0 P;
  let es0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length es0 + 1 < max_snat LENGTH(gmp_poly_len));
  es1 \<leftarrow> mop_list_append es0 e0;
  let ss0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length ss0 + 1 < max_snat LENGTH(gmp_poly_len));
  ss1 \<leftarrow> mop_list_append ss0 0;
  let cs0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length cs0 + 1 < max_snat LENGTH(gmp_poly_len));
  cs1 \<leftarrow> mop_list_append cs0 c0;
  let gs0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length gs0 + 1 < max_snat LENGTH(gmp_poly_len));
  gs1 \<leftarrow> mop_list_append gs0 0;
  acc0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 64;
  ASSERT (hybrid_loop_safe_invar ((todo1, qtodo1, es1, ss1, cs1, gs1, rp), acc0));
  st \<leftarrow> (PR_CONST defl_loop_monadic) todo1 qtodo1 es1 ss1 cs1 gs1 rp acc0;
  let ((todo, qtodo, es, ss, cs, gs, rpf), acc) = st;
  ASSERT (qtodo = []);
  (PR_CONST poly_vec_free_empty_monadic) qtodo;
  (PR_CONST dyadic_interval_vec_free_monadic) todo;
  (PR_CONST poly_free_monadic) rpf;
  RETURN acc
}"

sepref_register "PR_CONST defl_main_list_monadic"
  :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
      gmp_dyadic_interval_vec nres"

sepref_definition defl_main_list_impl [llvm_code] is
  "uncurry5 defl_main_list_monadic" ::
  "[\<lambda>(((((_, _), _), k), P), rp).
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding defl_main_list_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma defl_main_list_impl_hnr[sepref_fr_rules]:
  "(uncurry5 defl_main_list_impl,
    uncurry5 (PR_CONST defl_main_list_monadic)) \<in>
    [\<lambda>(((((_, _), _), k), P), rp).
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  using defl_main_list_impl.refine by (simp add: PR_CONST_def)

definition defl_split_pos_solve_monadic ::
  "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"defl_split_pos_solve_monadic xs \<equiv> doN {
  ASSERT (1 \<le> length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
  kpos \<leftarrow> (PR_CONST kiou_bound_k_monadic) xs;
  ASSERT (kpos * length xs < max_snat LENGTH(gmp_poly_len) \<and>
          kpos < max_snat LENGTH(gmp_poly_len));
  rp \<leftarrow> (PR_CONST poly_copy_monadic) xs;  \<comment> \<open>\<open>poly_copy_monadic\<close> is a direct copy loop with the same \<open>= xs\<close> specification and borrowed
     ownership; a clone by scaling with \<open>1\<close> would allocate and multiply for nothing.\<close>
  ASSERT (0 < length rp \<and> length rp + 1 < max_snat LENGTH(gmp_poly_len));
  Pinit \<leftarrow> (PR_CONST split_init_pow2_l0_monadic) kpos xs;
  ASSERT (0 < length Pinit \<and> length Pinit + 1 < max_snat LENGTH(gmp_poly_len));
  zl \<leftarrow> RETURN (mpz_from_int 0);
  rpos \<leftarrow> (PR_CONST mpz_pow2_monadic) kpos;
  accP \<leftarrow> (PR_CONST defl_main_list_monadic) split_pipeline_e0 zl rpos 0 Pinit rp;
  (PR_CONST mpzb_discard_monadic) rpos;
  (PR_CONST mpzb_discard_monadic) zl;
  RETURN accP
}"

sepref_register "PR_CONST defl_split_pos_solve_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition defl_split_pos_solve_impl [llvm_code] is
  "defl_split_pos_solve_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding defl_split_pos_solve_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  unfolding split_pipeline_e0_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma defl_split_pos_solve_impl_hnr[sepref_fr_rules]:
  "(defl_split_pos_solve_impl, PR_CONST defl_split_pos_solve_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using defl_split_pos_solve_impl.refine by (simp add: PR_CONST_def)

definition defl_split_neg_solve_monadic ::
  "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"defl_split_neg_solve_monadic xs \<equiv> doN {
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  Qb \<leftarrow> (PR_CONST poly_copy_monadic) xs;  
  ASSERT (length Qb + 1 < max_snat LENGTH(gmp_poly_len));
  Qb \<leftarrow> (PR_CONST poly_reflect_in_place_monadic) Qb;
  ASSERT (1 \<le> length Qb \<and> length Qb + 1 < max_snat LENGTH(gmp_poly_len));
  kneg \<leftarrow> (PR_CONST kiou_bound_k_monadic) Qb;
  ASSERT (kneg * length Qb < max_snat LENGTH(gmp_poly_len) \<and>
          kneg < max_snat LENGTH(gmp_poly_len));
  Qinit \<leftarrow> (PR_CONST split_init_pow2_l0_monadic) kneg Qb;
  ASSERT (0 < length Qinit \<and> length Qinit + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length Qb);
  zln \<leftarrow> RETURN (mpz_from_int 0);
  rneg \<leftarrow> (PR_CONST mpz_pow2_monadic) kneg;
  accQ \<leftarrow> (PR_CONST defl_main_list_monadic) split_pipeline_e0 zln rneg 0 Qinit Qb;
  (PR_CONST mpzb_discard_monadic) rneg;
  (PR_CONST mpzb_discard_monadic) zln;
  RETURN accQ
}"

sepref_register "PR_CONST defl_split_neg_solve_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition defl_split_neg_solve_impl [llvm_code] is
  "defl_split_neg_solve_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding defl_split_neg_solve_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  unfolding split_pipeline_e0_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma defl_split_neg_solve_impl_hnr[sepref_fr_rules]:
  "(defl_split_neg_solve_impl, PR_CONST defl_split_neg_solve_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using defl_split_neg_solve_impl.refine by (simp add: PR_CONST_def)

definition defl_isolate_all_split_main ::
  "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres" where
"defl_isolate_all_split_main xs \<equiv> doN {
  ASSERT (2 \<le> length xs);
  accP \<leftarrow> (PR_CONST defl_split_pos_solve_monadic) xs;
  accQ \<leftarrow> (PR_CONST defl_split_neg_solve_monadic) xs;
  xs0 \<leftarrow> (PR_CONST dsc_split_zero_check_monadic) xs;
  RETURN (accP, accQ, xs0)
}"

sepref_register "PR_CONST defl_isolate_all_split_main"
  :: "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres"

sepref_definition defl_isolate_all_split_main_impl [llvm_code] is
  "defl_isolate_all_split_main" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
    gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  unfolding defl_isolate_all_split_main_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma defl_isolate_all_split_main_impl_hnr[sepref_fr_rules]:
  "(defl_isolate_all_split_main_impl, PR_CONST defl_isolate_all_split_main) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  using defl_isolate_all_split_main_impl.refine by (simp add: PR_CONST_def)

end
