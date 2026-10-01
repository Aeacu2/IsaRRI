theory Bail_Solver
  imports Newton_Solver
begin

text \<open>The cascade-bail solver: its loop and window machinery (the abstract layer is \<open>Bail_Spec\<close>).
  Main definitions: \<open>bail_main_list_monadic\<close> / \<open>_impl\<close> and the \<open>bail_\<close> loop family.

  A window is accepted by flank emptiness (\<open>var(left flank) = 0 \<and> var(right flank) = 0\<close> implies
  that every root of the node lies inside the window) rather than by the exact-count equality
  \<open>count cand = v\<close>, which removes the uncapped exact count from the try. The flanks are the
  ``side intervals'' of ANewDsc; the name \<open>side0\<close>/\<open>side1\<close> is already used for the two Newton probe
  locations (@{const newton_side0_monadic}).\<close>


subsection \<open>The after-pop / loop / main-list vertical (verbatim clones, choice swapped)\<close>

definition bail_after_pop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> newton_loop_state nres" where
"bail_after_pop_monadic todo qtodo es ss cs acc l_num r_num k e s c Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  if c = 0 then
    (PR_CONST newton_branch_zero_monadic) todo qtodo es ss cs acc l_num r_num k Q
  else if c = 1 then
    (PR_CONST newton_branch_one_monadic) todo qtodo es ss cs acc l_num r_num k Q
  else doN {
    gate \<leftarrow> (PR_CONST newton_pol_gate_mop) Q e k s;
    if \<not> gate then
      (PR_CONST newton_branch_split_monadic) todo qtodo es ss cs acc l_num r_num k e s Q
    else doN {
      ASSERT (1 < length Q);
      ASSERT (length Q + 2 < max_snat LENGTH(gmp_poly_len));
      ASSERT (e < LENGTH(gmp_poly_len));
      ASSERT (e + 1 < max_snat LENGTH(gmp_poly_len));
      ASSERT (2 ^ e + 2 < max_snat LENGTH(gmp_poly_len));
      ASSERT (k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len));
      ASSERT ((2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len));
      v \<leftarrow> (if 4 \<le> c then RETURN (c - 2)
             else (PR_CONST carried_descartes_count_exact_monadic) Q);
      ASSERT (int v < max_sint LENGTH(gmp_long_len));
      wc \<leftarrow> (PR_CONST newton_window_choice_bail_monadic) v e Q;
      if gmp_mpoly_opt.is_None wc then
        (PR_CONST newton_branch_split_monadic) todo qtodo es ss cs acc l_num r_num k e s Q
      else doN {
        ASSERT (dyadic_interval_vec_pushable todo);
        ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
        ASSERT (length es + 1 < max_snat LENGTH(gmp_poly_len));
        ASSERT (length ss + 1 < max_snat LENGTH(gmp_poly_len));
        ASSERT (length cs + 1 < max_snat LENGTH(gmp_poly_len));
        ASSERT (v + 2 < max_snat LENGTH(gmp_poly_len));
        let (m, cand) = gmp_mpoly_opt.the wc;
        cs \<leftarrow> mop_list_append cs (v + 2);
        triple \<leftarrow> (PR_CONST newton_window_push_monadic)
                    todo qtodo es ss cs l_num r_num k e s m Q cand;
        RETURN (triple, acc)
      }
    }
  }
}"

sepref_register "PR_CONST bail_after_pop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> newton_loop_state nres"

sepref_definition bail_after_pop_impl [llvm_code] is
  "uncurry12 bail_after_pop_monadic" ::
  "[\<lambda>((((((((((((todo, qtodo), es), ss), cs), acc), _), _), k), _), _), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding bail_after_pop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free gmp_poly_assn_free
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

lemma bail_after_pop_impl_hnr[sepref_fr_rules]:
  "(uncurry12 bail_after_pop_impl,
    uncurry12 (PR_CONST bail_after_pop_monadic)) \<in>
    [\<lambda>((((((((((((todo, qtodo), es), ss), cs), acc), _), _), k), _), _), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length cs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using bail_after_pop_impl.refine by (simp add: PR_CONST_def)

definition bail_loop_step_monadic ::
  "newton_loop_state \<Rightarrow> newton_loop_state nres" where
"bail_loop_step_monadic st \<equiv>
  (case st of ((todo, qtodo, es, ss, cs), acc) \<Rightarrow> doN {
    ((l_num, r_num, k), todo) \<leftarrow> (PR_CONST dyadic_interval_vec_pop_last_monadic) todo;
    ASSERT (qtodo \<noteq> []);
    (Q, qtodo) \<leftarrow> (PR_CONST poly_vec_pop_last_monadic) qtodo;
    ASSERT (es \<noteq> []);
    (e, es) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) es;
    ASSERT (ss \<noteq> []);
    (s, ss) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) ss;
    ASSERT (cs \<noteq> []);
    (c, cs) \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) cs;
    ASSERT (0 < length Q);
    ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (dyadic_interval_vec_pushable2 todo);
    ASSERT (dyadic_interval_vec_pushable acc);
    ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length es + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length ss + 2 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length cs + 2 < max_snat LENGTH(gmp_poly_len));
    (PR_CONST bail_after_pop_monadic) todo qtodo es ss cs acc l_num r_num k e s c Q
  })"

sepref_register "PR_CONST bail_loop_step_monadic"
  :: "newton_loop_state \<Rightarrow> newton_loop_state nres"

sepref_definition bail_loop_step_impl [llvm_code] is
  "bail_loop_step_monadic" ::
  "[newton_loop_step_pre]\<^sub>a
    newton_loop_state_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding bail_loop_step_monadic_def
  unfolding newton_loop_step_pre_def
  unfolding newton_loop_safe_invar_def
  unfolding newton_loop_state_invar_def
  unfolding newton_loop_cond_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] =
    dyadic_interval_vec_pop_last_impl_hnr
    poly_vec_pop_last_impl_hnr
    dyadic_exp_pop_last_impl_hnr
    bail_after_pop_impl_hnr
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

lemma bail_loop_step_impl_hnr[sepref_fr_rules]:
  "(bail_loop_step_impl, PR_CONST bail_loop_step_monadic) \<in>
    [newton_loop_step_pre]\<^sub>a
      newton_loop_state_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using bail_loop_step_impl.refine by (simp add: PR_CONST_def)

definition bail_loop_body_checked_monadic ::
  "newton_loop_state \<Rightarrow> newton_loop_state nres" where
"bail_loop_body_checked_monadic st \<equiv>
  (if (PR_CONST newton_loop_cond) st then
    (PR_CONST bail_loop_step_monadic) st
   else RETURN st)"

sepref_register "PR_CONST bail_loop_body_checked_monadic"
  :: "newton_loop_state \<Rightarrow> newton_loop_state nres"

sepref_definition bail_loop_body_checked_impl [llvm_code] is
  "bail_loop_body_checked_monadic" ::
  "[newton_loop_safe_invar]\<^sub>a
    newton_loop_state_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding bail_loop_body_checked_monadic_def
  supply [simp] = newton_loop_step_pre_def
  supply [sepref_fr_rules] =
    newton_loop_cond_impl_hnr
    bail_loop_step_impl_hnr
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

lemma bail_loop_body_checked_impl_hnr[sepref_fr_rules]:
  "(bail_loop_body_checked_impl,
    PR_CONST bail_loop_body_checked_monadic) \<in>
    [newton_loop_safe_invar]\<^sub>a
      newton_loop_state_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using bail_loop_body_checked_impl.refine by (simp add: PR_CONST_def)

definition bail_loop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> newton_loop_state nres" where
"bail_loop_monadic todo qtodo es ss cs acc \<equiv>
  WHILEIT newton_loop_safe_invar
    (\<lambda>st. (PR_CONST newton_loop_cond) st)
    (\<lambda>st. (PR_CONST bail_loop_body_checked_monadic) st)
    ((todo, qtodo, es, ss, cs), acc)"

definition bail_loop_stateful_monadic ::
  "newton_loop_state \<Rightarrow> newton_loop_state nres" where
"bail_loop_stateful_monadic st0 \<equiv> doN {
  st0 \<leftarrow> RETURN ((PR_CONST (ASSN_ANNOT newton_loop_state_assn)) st0);
  WHILEIT newton_loop_safe_invar
    (\<lambda>st. (PR_CONST newton_loop_cond) st)
    (\<lambda>st. (PR_CONST bail_loop_body_checked_monadic) st)
    st0
}"

lemma bail_loop_monadic_eq_stateful:
  "bail_loop_monadic todo qtodo es ss cs acc
     = (PR_CONST bail_loop_stateful_monadic) ((todo, qtodo, es, ss, cs), acc)"
  unfolding bail_loop_monadic_def bail_loop_stateful_monadic_def
    ASSN_ANNOT_def PR_CONST_def by simp

sepref_register "PR_CONST bail_loop_stateful_monadic"
  :: "newton_loop_state \<Rightarrow> newton_loop_state nres"

sepref_definition bail_loop_stateful_impl [llvm_code] is
  "bail_loop_stateful_monadic" ::
  "[newton_loop_safe_invar]\<^sub>a
    newton_loop_state_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding bail_loop_stateful_monadic_def
  supply [sepref_fr_rules] =
    newton_loop_cond_impl_hnr
    bail_loop_body_checked_impl_hnr
  by sepref_dbg_keep

lemma bail_loop_stateful_impl_hnr[sepref_fr_rules]:
  "(bail_loop_stateful_impl, PR_CONST bail_loop_stateful_monadic) \<in>
    [newton_loop_safe_invar]\<^sub>a
      newton_loop_state_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using bail_loop_stateful_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST bail_loop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> newton_loop_state nres"

sepref_definition bail_loop_impl [llvm_code] is
  "uncurry5 bail_loop_monadic" ::
  "[\<lambda>(((((todo, qtodo), es), ss), cs), acc).
      newton_loop_safe_invar ((todo, qtodo, es, ss, cs), acc)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
      newton_loop_state_assn"
  unfolding bail_loop_monadic_eq_stateful
  supply [sepref_fr_rules] = bail_loop_stateful_impl_hnr
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

lemma bail_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry5 bail_loop_impl, uncurry5 (PR_CONST bail_loop_monadic)) \<in>
    [\<lambda>(((((todo, qtodo), es), ss), cs), acc).
      newton_loop_safe_invar ((todo, qtodo, es, ss, cs), acc)]\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_poly_vec_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
        gmp_dyadic_interval_vec_assn\<^sup>d \<rightarrow>
        newton_loop_state_assn"
  using bail_loop_impl.refine by (simp add: PR_CONST_def)

definition bail_main_list_monadic ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"bail_main_list_monadic e0 l_num r_num k P \<equiv> doN {
  \<comment> \<open>Seed capacity \<open>64\<close>: \<open>n\<close> is a pure array-list capacity hint
    (@{const poly_empty_sz_monadic}/@{const poly_vec_empty_sz_monadic} both \<open>RETURN []\<close>
    regardless of \<open>n\<close>), so this only avoids early-growth reallocation on the
    worklist/queue vectors; no SPEC change.\<close>
  todo0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 64;
  c_l \<leftarrow> RETURN (COPY l_num);
  c_r \<leftarrow> RETURN (COPY r_num);
  let (todo_lns, todo_rns, todo_ks) = todo0;
  ASSERT (dyadic_interval_vec_pushable todo0);
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
  acc0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 64;
  ASSERT (newton_loop_safe_invar ((todo1, qtodo1, es1, ss1, cs1), acc0));
  st \<leftarrow> (PR_CONST bail_loop_monadic) todo1 qtodo1 es1 ss1 cs1 acc0;
  let ((todo, qtodo, es, ss, cs), acc) = st;
  ASSERT (qtodo = []);
  (PR_CONST poly_vec_free_empty_monadic) qtodo;
  (PR_CONST dyadic_interval_vec_free_monadic) todo;
  RETURN acc
}"

sepref_register "PR_CONST bail_main_list_monadic"
  :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition bail_main_list_impl [llvm_code] is
  "uncurry4 bail_main_list_monadic" ::
  "[\<lambda>((((_, _), _), k), P).
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding bail_main_list_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [simp] =
    dyadic_interval_vec_invar_def
    dyadic_interval_vec_pushable_def
    dyadic_interval_vec_pushable2_def
  supply [sepref_fr_rules] =
    bail_loop_impl_hnr
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

lemma bail_main_list_impl_hnr[sepref_fr_rules]:
  "(uncurry4 bail_main_list_impl,
    uncurry4 (PR_CONST bail_main_list_monadic)) \<in>
    [\<lambda>((((_, _), _), k), P).
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>d \<rightarrow>
        gmp_dyadic_interval_vec_assn"
  using bail_main_list_impl.refine by (simp add: PR_CONST_def)



end
