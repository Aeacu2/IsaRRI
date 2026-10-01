theory Hybrid_Solver_Window
  imports Hybrid_Solver_Dispatch
begin

text \<open>Flagship part 2 of 3 (see \<open>Hybrid_Solver_Dispatch\<close> for the vertical's
  design note).
  Layer: SEPREF.
  Main exports: \<open>hybrid_window_push_monadic\<close>, \<open>hybrid_cond_escalate_monadic\<close>,
  \<open>hybrid_resolve_count_monadic\<close>, \<open>hybrid_dispatch_monadic\<close>, \<open>hybrid_after_pop_monadic\<close>
  (+ their \<open>_impl\<close> twins). Contents: the window-accept push, the mixed-ownership result-packaging helpers, the
  cnt-dispatch branch-merge boundary, and the after-pop dispatch that is the hybrid's heart.\<close>

section \<open>The window-accept push (bail's, with the LOCK guard append)\<close>

definition hybrid_window_push_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
    hybrid_worklist nres" where
"hybrid_window_push_monadic todo qtodo es ss cs gs rp l_num r_num k e s m Q cand \<equiv> doN {
  (PR_CONST poly_free_monadic) Q;
  ASSERT (e < LENGTH(gmp_poly_len));
  ASSERT (((1::nat) << e) + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + (((1::nat) << e) + 2) < max_snat LENGTH(gmp_poly_len));
  ASSERT (e + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>\<open>base = l_num \<cdot> 2^(2^e+2)\<close> via the immediate shift on a copy of \<open>l_num\<close>
     (@{const mpz_shift_left_snat_monadic}): no materialised \<open>2^(2^e+2)\<close> and no general multiply.\<close>
  base \<leftarrow> RETURN (COPY l_num);
  base \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) base (((1::nat) << e) + 2);
  w \<leftarrow> (PR_CONST mpz_sub.amop_r1) r_num l_num;
  (PR_CONST mpzb_discard_monadic) l_num;
  z1 \<leftarrow> RETURN (mpz_from_int 0);
  mw \<leftarrow> (PR_CONST mpz_mul.amop) z1 m w;
  \<comment> \<open>\<open>m+4\<close> via the immediate @{const mpz_add_ui_snat_monadic} (\<open>m\<close> consumed destructively): no
     materialised \<open>4\<close>.\<close>
  m4 \<leftarrow> (PR_CONST mpz_add_ui_snat_monadic) m 4;
  m4w \<leftarrow> (PR_CONST mpz_mul.amop_r1) m4 w;
  (PR_CONST mpzb_discard_monadic) w;
  bcopy \<leftarrow> RETURN (COPY base);
  l' \<leftarrow> (PR_CONST mpz_add.amop_r1) bcopy mw;
  (PR_CONST mpzb_discard_monadic) mw;
  r' \<leftarrow> (PR_CONST mpz_add.amop_r1) base m4w;
  (PR_CONST mpzb_discard_monadic) m4w;
  let k' = k + (((1::nat) << e) + 2);
  let (lns, rns, ks) = todo;
  ASSERT (dyadic_interval_vec_pushable (lns, rns, ks));
  lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) lns l';
  rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) rns r';
  ASSERT (length ks + 1 < max_snat LENGTH(gmp_poly_len));
  ks \<leftarrow> mop_list_append ks k';
  ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
  qtodo \<leftarrow> (PR_CONST poly_vec_push_monadic) qtodo cand;
  ASSERT (length es + 1 < max_snat LENGTH(gmp_poly_len));
  es \<leftarrow> mop_list_append es (e + 1);
  ASSERT (length ss + 1 < max_snat LENGTH(gmp_poly_len));
  ss \<leftarrow> mop_list_append ss s;
  \<comment> \<open>The LOCK guard for this window child is appended by the CALLER
     (\<open>hybrid_gate_open_monadic\<close>), alongside the \<open>cs\<close> cache entry, because only the
     caller holds the exact \<open>v\<close> that the guard carries as its \<open>2^42 + v\<close> payload.
     Appending it here would need \<open>v\<close> as a 15th argument for no gain.\<close>
  RETURN ((lns, rns, ks), qtodo, es, ss, cs, gs, rp)
}"

sepref_register "PR_CONST hybrid_window_push_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
      hybrid_worklist nres"

sepref_definition hybrid_window_push_impl [llvm_code] is
  "uncurry14 hybrid_window_push_monadic" ::
  "[\<lambda>((((((((((((((todo, qtodo), es), ss), cs), gs), rp), _), _), k), e), s), _), Q), cand).
      e < LENGTH(gmp_poly_len) \<and>
      ((1::nat) << e) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      k + (((1::nat) << e) + 2) < max_snat LENGTH(gmp_poly_len) \<and>
      e + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_worklist_assn"
  unfolding hybrid_window_push_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
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

lemma hybrid_window_push_impl_hnr[sepref_fr_rules]:
  "(uncurry14 hybrid_window_push_impl,
    uncurry14 (PR_CONST hybrid_window_push_monadic)) \<in>
    [\<lambda>((((((((((((((todo, qtodo), es), ss), cs), gs), rp), _), _), k), e), s), _), Q), cand).
      e < LENGTH(gmp_poly_len) \<and>
      ((1::nat) << e) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      k + (((1::nat) << e) + 2) < max_snat LENGTH(gmp_poly_len) \<and>
      e + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_worklist_assn"
  using hybrid_window_push_impl.refine by (simp add: PR_CONST_def)

section \<open>Result-packaging helpers for the mixed-ownership tuples in after-pop\<close>

definition hybrid_cqgr_result_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (nat \<times> gmp_poly \<times> nat \<times> gmp_poly) nres" where
"hybrid_cqgr_result_monadic c Q g rp \<equiv> RETURN (c, Q, g, rp)"

sepref_register "PR_CONST hybrid_cqgr_result_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (nat \<times> gmp_poly \<times> nat \<times> gmp_poly) nres"

sepref_definition hybrid_cqgr_result_impl [llvm_inline] is
  "uncurry3 hybrid_cqgr_result_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
    (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a
      (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a gmp_poly_assn"
  unfolding hybrid_cqgr_result_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  by sepref

lemma hybrid_cqgr_result_impl_hnr[sepref_fr_rules]:
  "(uncurry3 hybrid_cqgr_result_impl,
    uncurry3 (PR_CONST hybrid_cqgr_result_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
      (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a
        (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a gmp_poly_assn"
  using hybrid_cqgr_result_impl.refine by (simp add: PR_CONST_def)

definition hybrid_qgr_result_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> nat \<times> gmp_poly) nres" where
"hybrid_qgr_result_monadic Q g rp \<equiv> RETURN (Q, g, rp)"

sepref_register "PR_CONST hybrid_qgr_result_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> nat \<times> gmp_poly) nres"

sepref_definition hybrid_qgr_result_impl [llvm_inline] is
  "uncurry2 hybrid_qgr_result_monadic" ::
  "gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
    gmp_poly_assn \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a gmp_poly_assn"
  unfolding hybrid_qgr_result_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  by sepref

lemma hybrid_qgr_result_impl_hnr[sepref_fr_rules]:
  "(uncurry2 hybrid_qgr_result_impl,
    uncurry2 (PR_CONST hybrid_qgr_result_monadic)) \<in>
    gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
      gmp_poly_assn \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a gmp_poly_assn"
  using hybrid_qgr_result_impl.refine by (simp add: PR_CONST_def)

text \<open>Conditional escalation. The Newton probe needs an exact polynomial, but
  \<open>truncate_count_escalate_monadic\<close> has already escalated the node when its truncated count was
  ambiguous, and @{const carried_descartes_count_g_monadic} treats the exact-lock sentinel \<open>2^42\<close> like
  \<open>g=0\<close>, so a locked cluster subtree is already exact. So \<open>gate_open\<close> does not re-escalate
  unconditionally (that would be a quadratic rebuild on every gate-open node): it reuses \<open>Q1\<close> when it
  is already exact (\<open>g = 0\<close> or \<open>2^42 \<le> g\<close>) and escalates only at the transition from truncated to
  exact (\<open>0 < g < 2^42\<close>, a decisive but truncated count). One rebuild per cluster, not per node.\<close>
definition hybrid_cond_escalate_monadic ::
  "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> (gmp_poly \<times> gmp_poly) nres" where
"hybrid_cond_escalate_monadic rp l_num r_num k Q g \<equiv>
  (if g = 0 \<or> 4398046511104 \<le> g then RETURN (Q, rp)
   else (PR_CONST carried_escalate_keep_monadic) rp l_num r_num k Q)"

sepref_register "PR_CONST hybrid_cond_escalate_monadic"
  :: "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> (gmp_poly \<times> gmp_poly) nres"

sepref_definition hybrid_cond_escalate_impl [llvm_code] is
  "uncurry5 hybrid_cond_escalate_monadic" ::
  "[\<lambda>(((((rp, l), r), k), Q), g).
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a gmp_poly_assn"
  unfolding hybrid_cond_escalate_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma hybrid_cond_escalate_impl_hnr[sepref_fr_rules]:
  "(uncurry5 hybrid_cond_escalate_impl, uncurry5 (PR_CONST hybrid_cond_escalate_monadic)) \<in>
    [\<lambda>(((((rp, l), r), k), Q), g).
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a gmp_poly_assn"
  using hybrid_cond_escalate_impl.refine by (simp add: PR_CONST_def)

text \<open>Resolve the class \<open>c\<close> cached at pop time. If \<open>c\<close> is the ambiguous sentinel \<open>4\<close> from the
  \<open>g\<close>-guarded push-time classification (i.e. \<open>0 \<le> g < 2^42\<close>: the polynomial is truncated and not yet
  locked), escalate once from the retained root \<open>rp\<close> and count exactly. Otherwise \<open>c\<close> can be used as
  it is: either a decisive class \<open>0..3\<close> from a truncated or exact node (the classification trichotomy
  survives truncation; \<open>truncate_dispatch_monadic\<close> dispatches \<open>cnt=0/1\<close> directly on a truncated
  polynomial), or a cached window count \<open>v+2 \<ge> 2\<close> from a locked node popped again after a Newton
  accept. The literal \<open>4\<close> cannot collide: a window-pushed child always carries \<open>g = 2^42\<close>, which the
  guard \<open>g < 2^42\<close> below excludes, and a locked node's push-time classification never produces the
  sentinel, since @{const carried_descartes_count_g_monadic} treats \<open>g \<ge> 2^42\<close> as decisive. So one
  count kernel runs per node.

  This branch uses the plain \<open>g\<close>-guarded kernel, like every other classification site. The resolved
  \<open>cnt\<close>'s \<open>2\<close> therefore means \<open>\<ge> 2\<close>, and \<open>cs\<close> keeps its capped-at-2 semantics, which the \<open>\<sigma>\<close> and
  run-length consumers read.\<close>
definition hybrid_resolve_count_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow>
    (nat \<times> gmp_poly \<times> nat \<times> gmp_poly) nres" where
"hybrid_resolve_count_monadic Q g l_num r_num k rp c \<equiv>
  (if c = 4 \<and> g < 4398046511104 then doN {
     (qx, rp2) \<leftarrow> (PR_CONST carried_escalate_keep_monadic) rp l_num r_num k Q;
     ASSERT (length qx + 1 < max_snat LENGTH(gmp_poly_len));
     (cx, _) \<leftarrow> (PR_CONST carried_descartes_count_g_monadic) qx 4398046511104;
     RETURN (cx, qx, 4398046511104, rp2)
   } else RETURN (c, Q, g, rp))"

sepref_register "PR_CONST hybrid_resolve_count_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow>
      (nat \<times> gmp_poly \<times> nat \<times> gmp_poly) nres"

sepref_definition hybrid_resolve_count_impl [llvm_code] is
  "uncurry6 hybrid_resolve_count_monadic" ::
  "[\<lambda>((((((Q, g), l), r), k), rp), c).
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"
  unfolding hybrid_resolve_count_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma hybrid_resolve_count_impl_hnr[sepref_fr_rules]:
  "(uncurry6 hybrid_resolve_count_impl, uncurry6 (PR_CONST hybrid_resolve_count_monadic)) \<in>
    [\<lambda>((((((Q, g), l), r), k), rp), c).
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"
  using hybrid_resolve_count_impl.refine by (simp add: PR_CONST_def)

text \<open>The inherited-\<open>v\<close> reader. Computing the window bound \<open>v\<close> (the node's exact count) is the
  gate-open arm's main per-node cost when the pop-time cache is absent (\<open>cnt < 4\<close>, i.e. every node
  reached by bisection rather than by a Newton accept). Three routes, cheapest first:
  \<^item> \<open>4 \<le> cnt\<close>: the cache from a prior accept, \<open>v = cnt - 2\<close>, no count at all.
  \<^item> \<open>g > 2^42\<close>: the node carries an inherited bound \<open>b = g - 2^42 \<ge> 2\<close> from its gate-open parent.
    Run the capped kernel at \<open>cap = b\<close>: it aborts at the \<open>b\<close>-th sign change instead of sweeping the
    whole coefficient list. The result is still exact, because the two halves of the cap contract
    close against the inherited bound:
    \<^item> \<open>r < b\<close> \<Rightarrow> \<open>r\<close> is the exact count (full run, cap never hit);
    \<^item> \<open>b \<le> r\<close> \<Rightarrow> \<open>b \<le> count\<close>, and the inheritance invariant gives \<open>count \<le> b\<close> (a child's Descartes
      count never exceeds its parent's: window children by @{thm [source] carried_window_count_mono},
      bisection children by the Bernstein split), hence \<open>count = b\<close>.
    So \<open>v = (if b \<le> r then b else r)\<close> is the true count, not a capped classification; a window
    accept must never be fed \<open>v\<close> from a capped classification.
  \<^item> otherwise (\<open>g = 2^42\<close> exactly, or \<open>g < 2^42\<close>, where \<open>qx\<close> was just rebuilt from \<open>rp\<close>): no bound
    is available, and the full exact count runs.
  The op returns what \<open>if 4 \<le> cnt then cnt - 2 else count_exact qx\<close> returns; the difference is
  cost only.\<close>
definition hybrid_window_v_monadic :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"hybrid_window_v_monadic cnt g Q \<equiv>
  (if 4 \<le> cnt then RETURN (cnt - 2)
   else if 4398046511106 \<le> g then doN {
     b \<leftarrow> RETURN (g - 4398046511104);
     ASSERT (2 \<le> b);
     ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
     r \<leftarrow> (PR_CONST carried_descartes_count_trunc_cap_monadic) b Q;
     RETURN (if b \<le> r then b else r)
   } else (PR_CONST carried_descartes_count_exact_monadic) Q)"

sepref_register "PR_CONST hybrid_window_v_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

sepref_definition hybrid_window_v_impl [llvm_code] is
  "uncurry2 hybrid_window_v_monadic" ::
  "[\<lambda>((cnt, g), Q). length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding hybrid_window_v_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma hybrid_window_v_impl_hnr[sepref_fr_rules]:
  "(uncurry2 hybrid_window_v_impl, uncurry2 (PR_CONST hybrid_window_v_monadic)) \<in>
    [\<lambda>((cnt, g), Q). length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using hybrid_window_v_impl.refine by (simp add: PR_CONST_def)

text \<open>The gate-OPEN Newton arm, isolated into its OWN op so its escalate-then-probe
  frame is solved locally: CONDITIONALLY
  escalate the node to exact from \<open>rp\<close> (only if \<open>Q1\<close> is truncated), run bail's window machinery on
  the exact poly, LOCK the region (children carry \<open>g = EXACT_LOCK\<close> via the branch/window ops'
  \<open>4398046511104\<close> guard).\<close>
definition hybrid_gate_open_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres" where
"hybrid_gate_open_monadic todo qtodo es ss cs gs acc rp1 l_num r_num k e s cnt g1 Q1 \<equiv> doN {
  \<comment> \<open>CONDITIONAL escalate (the optimality fix): reuse \<open>Q1\<close> when already exact, rebuild only
     at the dense\<rightarrow>cluster transition. Keeps the dispatch's \<open>else\<close>-arm a SINGLE op call
     (frame-merges with the \<open>branch_split\<close> arm); an inline two-op sequence does NOT merge.\<close>
  ASSERT (0 < length rp1);
  ASSERT (length rp1 + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp1 - 1) < max_snat LENGTH(gmp_poly_len));
  (qx, rpx) \<leftarrow> (PR_CONST hybrid_cond_escalate_monadic) rp1 l_num r_num k Q1 g1;
  ASSERT (1 < length qx);
  ASSERT (length qx + 2 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>The second headroom conjunct (\<open>+2\<close>), needed by the right-child decide.\<close>
  ASSERT (1 * (length qx - 1) < max_snat LENGTH(gmp_poly_len));
  ASSERT (e < LENGTH(gmp_poly_len));
  ASSERT (e + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (2 ^ e + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len));
  ASSERT ((2 ^ e + 2) * (length qx - 1) < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>\<open>v\<close> via the inherited-bound reader — the \<open>cs\<close> cache, else the CAPPED kernel at
     the parent's exact \<open>v\<close> carried in \<open>g1\<close>'s \<open>2^42 + v\<close> payload, else a full exact count.
     All three give the same VALUE.\<close>
  v \<leftarrow> (PR_CONST hybrid_window_v_monadic) cnt g1 qx;
  ASSERT (int v < max_sint LENGTH(gmp_long_len));
  ASSERT (4398046511104 + v < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>The LOCK guard every child of THIS node inherits, now carrying \<open>v\<close> as its payload.
     A \<open>RETURN\<close>-bound FULL application, not a pure op: a standalone \<open>\<lambda>v. 2^42 + v\<close> eta-contracts
     to the partial application \<open>(+) (snat_const 2^42)\<close>, for which \<open>sepref\<close> has no rule
     (\<open>Failed to apply initial proof method\<close>). Same shape as \<open>limit \<leftarrow> RETURN (len - 1)\<close> in
     @{const poly_ethorner_count_cap_monadic}.\<close>
  glock \<leftarrow> RETURN (4398046511104 + v);
  \<comment> \<open>Newton probe on the EXACT \<open>qx\<close> (bail's window arm). Accept \<Rightarrow> push the window child
     (EXACT-LOCKed \<open>gs=2^42\<close> by @{const hybrid_window_push_monadic}, count cached as \<open>v+2\<close>);
     reject \<Rightarrow> bisect, EXACT-LOCKing both children (\<open>g = 4398046511104 = 2^42\<close>) so the escalated
     Newton subtree never re-truncates. \<open>qx\<close> replaces the truncated \<open>Q1\<close> as the count
     poly; \<open>rpx\<close> is the kept exact root threaded to the children.\<close>
  wc \<leftarrow> (PR_CONST newton_window_choice_bail_monadic) v e qx;
  if gmp_mpoly_opt.is_None wc then
    (PR_CONST hybrid_branch_split_monadic)
      todo qtodo es ss cs gs rpx acc l_num r_num k e s glock qx
  else doN {
    ASSERT (dyadic_interval_vec_pushable todo);
    ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length es + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length ss + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length cs + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (v + 2 < max_snat LENGTH(gmp_poly_len));
    let (m, cand) = gmp_mpoly_opt.the wc;
    cs \<leftarrow> mop_list_append cs (v + 2);
    \<comment> \<open>The window child's LOCK guard, carrying this node's exact \<open>v\<close> — sound as
       an upper bound on the child's count by @{thm [source] carried_window_count_mono}.
       Appended HERE rather than inside @{const hybrid_window_push_monadic} (which has no \<open>v\<close>).\<close>
    gs \<leftarrow> mop_list_append gs glock;
    triple \<leftarrow> (PR_CONST hybrid_window_push_monadic)
                todo qtodo es ss cs gs rpx l_num r_num k e s m qx cand;
    RETURN (triple, acc)
  }
}"

sepref_register "PR_CONST hybrid_gate_open_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres"

abbreviation "hybrid_gate_open_pre \<equiv> (\<lambda>
    (((((((((((((((todo, qtodo), es), ss), cs), gs), acc), rp), _), _), k), _), s), _), _), Q).
        0 < length rp \<and>
        length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
        k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        s + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        dyadic_interval_vec_pushable2 todo \<and>
        dyadic_interval_vec_pushable acc \<and>
        length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length cs + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length gs + 2 < max_snat LENGTH(gmp_poly_len))"

sepref_definition hybrid_gate_open_impl [llvm_code] is
  "uncurry15 hybrid_gate_open_monadic" ::
  "[hybrid_gate_open_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  unfolding hybrid_gate_open_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free gmp_poly_assn_free
  supply [sepref_fr_rules] =
    newton_window_choice_bail_impl_hnr hybrid_branch_split_impl_hnr hybrid_window_push_impl_hnr
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const gmp_int_t)?
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

lemma hybrid_gate_open_impl_hnr[sepref_fr_rules]:
  "(uncurry15 hybrid_gate_open_impl, uncurry15 (PR_CONST hybrid_gate_open_monadic)) \<in>
    [hybrid_gate_open_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  using hybrid_gate_open_impl.refine by (simp add: PR_CONST_def)

section \<open>The cnt-dispatch (extracted as its OWN op — the branch-merge boundary)\<close>

text \<open>The 0/1/\<open>\<ge>2\<close> count cascade is its own registered op (the structure of
  \<open>truncate_dispatch_monadic\<close>, extended with the \<open>\<ge>2\<close> Newton \<open>gate\<close> fork). Inlined after the
  \<open>count_escalate\<close> bind, the cascade does not frame-merge: an \<open>if\<close> whose arms call different ops,
  composed after earlier binds, leaves an \<open>hn_invalid\<close>/\<open>cons_solve\<close> residual. As a standalone op every
  arm receives fresh parameters and returns the same @{typ hybrid_state}, so the arms merge.
  \<open>escalate\<close> borrows \<open>l/r\<close> and consumes \<open>rp\<close>/\<open>Q\<close>, like every other arm, so the gate-open arm passes
  the original \<open>l/r\<close> on to \<open>gate_open\<close> (which consumes them) without copies.\<close>

definition hybrid_dispatch_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> hybrid_state nres" where
"hybrid_dispatch_monadic todo qtodo es ss cs gs acc rp1 l_num r_num k e s g1 Q1 cnt \<equiv> doN {
  if cnt = 0 then
    (PR_CONST hybrid_branch_zero_monadic)
      todo qtodo es ss cs gs rp1 acc l_num r_num Q1
  else if cnt = 1 then
    (PR_CONST hybrid_branch_one_monadic)
      todo qtodo es ss cs gs rp1 acc l_num r_num k Q1
  else doN {
    gate \<leftarrow> (PR_CONST newton_pol_gate_mop) Q1 e k s;
    if \<not> gate then
      (PR_CONST hybrid_branch_split_monadic)
        todo qtodo es ss cs gs rp1 acc l_num r_num k e s g1 Q1
    else
      \<comment> \<open>SINGLE op call — gate_open CONDITIONALLY escalates \<open>rp1\<close>/\<open>Q1\<close> (only if truncated).\<close>
      (PR_CONST hybrid_gate_open_monadic)
        todo qtodo es ss cs gs acc rp1 l_num r_num k e s cnt g1 Q1
  }
}"

sepref_register "PR_CONST hybrid_dispatch_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> hybrid_state nres"

abbreviation "hybrid_dispatch_pre \<equiv> (\<lambda>
    (((((((((((((((todo, qtodo), es), ss), cs), gs), acc), rp), _), _), k), _), s), _), Q), _).
        0 < length Q \<and>
        length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        \<comment> \<open>The right-child decide evaluates the left child at \<open>1\<close>, and \<open>poly_eval1_pair_monadic\<close> needs
           \<open>+2\<close> where the other ops need \<open>+1\<close>. Stated as a second conjunct beside the first, as
           \<open>newton_side1_impl\<close> states the same pair.\<close>
        length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len) \<and>
        0 < length rp \<and>
        length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
        k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        s + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        dyadic_interval_vec_pushable2 todo \<and>
        dyadic_interval_vec_pushable acc \<and>
        length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length cs + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length gs + 2 < max_snat LENGTH(gmp_poly_len))"

sepref_definition hybrid_dispatch_impl [llvm_code] is
  "uncurry15 hybrid_dispatch_monadic" ::
  "[hybrid_dispatch_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      hybrid_state_assn"
  unfolding hybrid_dispatch_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const gmp_int_t)?
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

lemma hybrid_dispatch_impl_hnr[sepref_fr_rules]:
  "(uncurry15 hybrid_dispatch_impl, uncurry15 (PR_CONST hybrid_dispatch_monadic)) \<in>
    [hybrid_dispatch_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      hybrid_state_assn"
  using hybrid_dispatch_impl.refine by (simp add: PR_CONST_def)

section \<open>The after-pop dispatch (the hybrid's heart)\<close>

definition hybrid_after_pop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres" where
"hybrid_after_pop_monadic todo qtodo es ss cs gs acc rp l_num r_num k e s c g Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length rp);
  ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>Read the class \<open>c\<close> cached at pop time instead of recounting (see
     @{const hybrid_resolve_count_monadic}'s comment).\<close>
  (cnt, Q1, g1, rp1) \<leftarrow>
    (PR_CONST hybrid_resolve_count_monadic) Q g l_num r_num k rp c;
  ASSERT (0 < length Q1);
  ASSERT (length Q1 + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>The second headroom conjunct, about the resolved node \<open>Q1\<close>: the dispatch is called with \<open>Q1\<close>,
     not \<open>Q\<close>, so the pair is asserted here rather than inherited from the op's precondition.\<close>
  ASSERT (length Q1 + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (1 * (length Q1 - 1) < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length rp1);
  ASSERT (length rp1 + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp1 - 1) < max_snat LENGTH(gmp_poly_len));
  (PR_CONST hybrid_dispatch_monadic)
    todo qtodo es ss cs gs acc rp1 l_num r_num k e s g1 Q1 cnt
}"

sepref_register "PR_CONST hybrid_after_pop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres"

abbreviation "hybrid_after_pop_pre \<equiv> (\<lambda>
    (((((((((((((((todo, qtodo), es), ss), cs), gs), acc), _), _), _), k), _), s), _), _), Q).
        0 < length Q \<and>
        length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        \<comment> \<open>The second headroom conjunct, passed on from \<open>hybrid_dispatch_pre\<close>.\<close>
        length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len) \<and>
        k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        s + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        dyadic_interval_vec_pushable2 todo \<and>
        dyadic_interval_vec_pushable acc \<and>
        length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length es + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length ss + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length cs + 2 < max_snat LENGTH(gmp_poly_len) \<and>
        length gs + 2 < max_snat LENGTH(gmp_poly_len))"

sepref_definition hybrid_after_pop_impl [llvm_code] is
  "uncurry15 hybrid_after_pop_monadic" ::
  "[hybrid_after_pop_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  unfolding hybrid_after_pop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const gmp_int_t)?
  by sepref

lemma hybrid_after_pop_impl_hnr[sepref_fr_rules]:
  "(uncurry15 hybrid_after_pop_impl,
    uncurry15 (PR_CONST hybrid_after_pop_monadic)) \<in>
    [hybrid_after_pop_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  using hybrid_after_pop_impl.refine by (simp add: PR_CONST_def)

section \<open>The deflating twins of the window layer\<close>

text \<open>The deflation must not live on the hybrid solver's own path (the one that carries the
  multiset-equality guarantee), so every op whose emitted code embeds a child-build choice is
  duplicated with \<open>defl_\<close> twins calling \<open>defl_branch_split_monadic\<close>. Everything BELOW the branch
  choice (window push, count resolve, Newton probe, the 0/1 branches) is shared verbatim --- its
  codegen does not depend on which stack calls it. The classic ops above are unchanged.\<close>

definition defl_gate_open_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres" where
"defl_gate_open_monadic todo qtodo es ss cs gs acc rp1 l_num r_num k e s cnt g1 Q1 \<equiv> doN {
  \<comment> \<open>CONDITIONAL escalate (the optimality fix): reuse \<open>Q1\<close> when already exact, rebuild only
     at the dense\<rightarrow>cluster transition. Keeps the dispatch's \<open>else\<close>-arm a SINGLE op call
     (frame-merges with the \<open>branch_split\<close> arm); an inline two-op sequence does NOT merge.\<close>
  ASSERT (0 < length rp1);
  ASSERT (length rp1 + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp1 - 1) < max_snat LENGTH(gmp_poly_len));
  (qx, rpx) \<leftarrow> (PR_CONST hybrid_cond_escalate_monadic) rp1 l_num r_num k Q1 g1;
  ASSERT (1 < length qx);
  ASSERT (length qx + 2 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>The second headroom conjunct (\<open>+2\<close>), needed by the right-child decide.\<close>
  ASSERT (1 * (length qx - 1) < max_snat LENGTH(gmp_poly_len));
  ASSERT (e < LENGTH(gmp_poly_len));
  ASSERT (e + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (2 ^ e + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len));
  ASSERT ((2 ^ e + 2) * (length qx - 1) < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>\<open>v\<close> via the inherited-bound reader — the \<open>cs\<close> cache, else the CAPPED kernel at
     the parent's exact \<open>v\<close> carried in \<open>g1\<close>'s \<open>2^42 + v\<close> payload, else a full exact count.
     All three give the same VALUE.\<close>
  v \<leftarrow> (PR_CONST hybrid_window_v_monadic) cnt g1 qx;
  ASSERT (int v < max_sint LENGTH(gmp_long_len));
  ASSERT (4398046511104 + v < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>The LOCK guard every child of THIS node inherits, now carrying \<open>v\<close> as its payload.
     A \<open>RETURN\<close>-bound FULL application, not a pure op: a standalone \<open>\<lambda>v. 2^42 + v\<close> eta-contracts
     to the partial application \<open>(+) (snat_const 2^42)\<close>, for which \<open>sepref\<close> has no rule
     (\<open>Failed to apply initial proof method\<close>). Same shape as \<open>limit \<leftarrow> RETURN (len - 1)\<close> in
     @{const poly_ethorner_count_cap_monadic}.\<close>
  glock \<leftarrow> RETURN (4398046511104 + v);
  \<comment> \<open>Newton probe on the EXACT \<open>qx\<close> (bail's window arm). Accept \<Rightarrow> push the window child
     (EXACT-LOCKed \<open>gs=2^42\<close> by @{const hybrid_window_push_monadic}, count cached as \<open>v+2\<close>);
     reject \<Rightarrow> bisect, EXACT-LOCKing both children (\<open>g = 4398046511104 = 2^42\<close>) so the escalated
     Newton subtree never re-truncates. \<open>qx\<close> replaces the truncated \<open>Q1\<close> as the count
     poly; \<open>rpx\<close> is the kept exact root threaded to the children.\<close>
  \<comment> \<open>\<^bold>\<open>The \<open>2 \<le> v\<close> gate, which only the deflating twin needs.\<close>
     On the non-deflating stack this test always holds: the arm is reached with a cached class
     \<open>\<ge> 2\<close>, the node's exact object is its init, and @{const hybrid_cond_escalate_monadic} hands the
     window that same polynomial, so \<open>v = carried_descartes_count qx \<ge> 2\<close>. Here it need not: at
     \<open>0 < g < 2\<^sup>4\<^sup>2\<close> the escalation rebuilds the node to its init, discarding the shed factor, and a
     Descartes count does not transport across that step. The shed root lies at a local-frame endpoint
     or outside the box, so the deflated object and the init agree on roots in \<open>(0,1)\<close> but may disagree
     on sign variations, in the direction that lowers the init's count. So the cached \<open>\<ge> 2\<close> does not
     bound \<open>v\<close>, and the window can be reached at \<open>v \<in> {0, 1}\<close>.

     \<open>blr_window_choice_refine_bl\<close> (\<open>Bail_Loop_Refine\<close>), the contract of the concrete window cascade,
     takes \<open>2 \<le> v\<close>. Below it the op has no specification, so an accepted window could not be shown to
     contain the node's roots, and the window arm discards everything outside it. The gate restores
     the premise by construction.

     Where the premise already holds the test is true and the tree is unchanged; where it does not,
     \<open>v \<le> 1\<close> says the node has at most one root, and the node bisects instead.\<close>
  wc \<leftarrow> (if 2 \<le> v then (PR_CONST newton_window_choice_bail_monadic) v e qx
         else RETURN gmp_mpoly_opt.None);
  if gmp_mpoly_opt.is_None wc then
    (PR_CONST defl_branch_split_monadic)
      todo qtodo es ss cs gs rpx acc l_num r_num k e s glock qx
  else doN {
    ASSERT (dyadic_interval_vec_pushable todo);
    ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length es + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length ss + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length cs + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
    ASSERT (v + 2 < max_snat LENGTH(gmp_poly_len));
    let (m, cand) = gmp_mpoly_opt.the wc;
    cs \<leftarrow> mop_list_append cs (v + 2);
    \<comment> \<open>The window child's LOCK guard, carrying this node's exact \<open>v\<close> — sound as
       an upper bound on the child's count by @{thm [source] carried_window_count_mono}.
       Appended HERE rather than inside @{const hybrid_window_push_monadic} (which has no \<open>v\<close>).\<close>
    gs \<leftarrow> mop_list_append gs glock;
    triple \<leftarrow> (PR_CONST hybrid_window_push_monadic)
                todo qtodo es ss cs gs rpx l_num r_num k e s m qx cand;
    RETURN (triple, acc)
  }
}"

sepref_register "PR_CONST defl_gate_open_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres"

sepref_definition defl_gate_open_impl [llvm_code] is
  "uncurry15 defl_gate_open_monadic" ::
  "[hybrid_gate_open_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  unfolding defl_gate_open_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free gmp_poly_assn_free
  supply [sepref_fr_rules] =
    newton_window_choice_bail_impl_hnr defl_branch_split_impl_hnr hybrid_window_push_impl_hnr
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const gmp_int_t)?
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

lemma defl_gate_open_impl_hnr[sepref_fr_rules]:
  "(uncurry15 defl_gate_open_impl, uncurry15 (PR_CONST defl_gate_open_monadic)) \<in>
    [hybrid_gate_open_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  using defl_gate_open_impl.refine by (simp add: PR_CONST_def)

definition defl_dispatch_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> hybrid_state nres" where
"defl_dispatch_monadic todo qtodo es ss cs gs acc rp1 l_num r_num k e s g1 Q1 cnt \<equiv> doN {
  if cnt = 0 then
    (PR_CONST hybrid_branch_zero_monadic)
      todo qtodo es ss cs gs rp1 acc l_num r_num Q1
  else if cnt = 1 then
    (PR_CONST hybrid_branch_one_monadic)
      todo qtodo es ss cs gs rp1 acc l_num r_num k Q1
  else doN {
    gate \<leftarrow> (PR_CONST newton_pol_gate_mop) Q1 e k s;
    if \<not> gate then
      (PR_CONST defl_branch_split_monadic)
        todo qtodo es ss cs gs rp1 acc l_num r_num k e s g1 Q1
    else
      \<comment> \<open>SINGLE op call — gate_open CONDITIONALLY escalates \<open>rp1\<close>/\<open>Q1\<close> (only if truncated).\<close>
      (PR_CONST defl_gate_open_monadic)
        todo qtodo es ss cs gs acc rp1 l_num r_num k e s cnt g1 Q1
  }
}"

sepref_register "PR_CONST defl_dispatch_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> hybrid_state nres"

sepref_definition defl_dispatch_impl [llvm_code] is
  "uncurry15 defl_dispatch_monadic" ::
  "[hybrid_dispatch_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      hybrid_state_assn"
  unfolding defl_dispatch_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const gmp_int_t)?
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

lemma defl_dispatch_impl_hnr[sepref_fr_rules]:
  "(uncurry15 defl_dispatch_impl, uncurry15 (PR_CONST defl_dispatch_monadic)) \<in>
    [hybrid_dispatch_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      hybrid_state_assn"
  using defl_dispatch_impl.refine by (simp add: PR_CONST_def)

definition defl_after_pop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres" where
"defl_after_pop_monadic todo qtodo es ss cs gs acc rp l_num r_num k e s c g Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length rp);
  ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>Read the class \<open>c\<close> cached at pop time instead of recounting (see
     @{const hybrid_resolve_count_monadic}'s comment).\<close>
  (cnt, Q1, g1, rp1) \<leftarrow>
    (PR_CONST hybrid_resolve_count_monadic) Q g l_num r_num k rp c;
  ASSERT (0 < length Q1);
  ASSERT (length Q1 + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>The second headroom conjunct, about the resolved node \<open>Q1\<close>: the dispatch is called with \<open>Q1\<close>,
     not \<open>Q\<close>, so the pair is asserted here rather than inherited from the op's precondition.\<close>
  ASSERT (length Q1 + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (1 * (length Q1 - 1) < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length rp1);
  ASSERT (length rp1 + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp1 - 1) < max_snat LENGTH(gmp_poly_len));
  (PR_CONST defl_dispatch_monadic)
    todo qtodo es ss cs gs acc rp1 l_num r_num k e s g1 Q1 cnt
}"

sepref_register "PR_CONST defl_after_pop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres"

sepref_definition defl_after_pop_impl [llvm_code] is
  "uncurry15 defl_after_pop_monadic" ::
  "[hybrid_after_pop_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  unfolding defl_after_pop_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const gmp_int_t)?
  by sepref

lemma defl_after_pop_impl_hnr[sepref_fr_rules]:
  "(uncurry15 defl_after_pop_impl,
    uncurry15 (PR_CONST defl_after_pop_monadic)) \<in>
    [hybrid_after_pop_pre]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  using defl_after_pop_impl.refine by (simp add: PR_CONST_def)

end
