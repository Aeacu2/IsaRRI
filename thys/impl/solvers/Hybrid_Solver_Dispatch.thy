theory Hybrid_Solver_Dispatch
  imports Truncate Count Newton Split "IsaRRI_LLVM.Poly_Vec" Kiou_Bound
    Deflation_Node
begin


text \<open>The hybrid solver, part 1 of 3: worklist state, loop condition, and the three branch arms
  (zero / one / split) with their helpers. \<open>Hybrid_Solver_Pipeline\<close>, the last of the three, gives the whole
  solver. Main definitions: \<open>hybrid_loop_cond\<close>, \<open>hybrid_branch_{zero,one,split}_monadic\<close>,
  \<open>hybrid_classify_prebuilt_monadic\<close>, \<open>hybrid_split_pair_state_monadic\<close> (and their \<open>_impl\<close> twins).

  The solver combines the cascade-bail control flow (\<open>Bail_Solver\<close>) with carried truncation
  (\<open>Truncate_Solver\<close>), chosen per region by the \<open>\<sigma>\<close> gate:
  \<^item> gate closed (non-cluster region): truncated bisection, i.e. the truncating children build
    (\<open>carried_retrunc_mop\<close> under \<open>truncate_child_guards\<close>), the \<open>g\<close>-guarded midpoint test, and \<open>g\<close>-guarded child
    classification at push time for the \<open>cs\<close> column (ambiguous \<Rightarrow> the sentinel \<open>4\<close>, resolved at the child's own
    pop by \<open>truncate_count_escalate_monadic\<close>, with no child-box arithmetic at push);
  \<^item> gate open (cluster region): escalate the node once to exact from the per-solve anchor \<open>rp\<close>, set
    \<open>g := lock\<close>, then run the bail window machinery (probe-first cascade, \<open>count cand = v\<close> acceptance, the
    \<open>v+2\<close> count cache). Every child pushed from a gate-open node carries \<open>g = lock\<close>, so the Newton region stays
    exact; the gate-open frontier is an antichain, so escalations are bounded by its size.

  State: the bail solver's five-column worklist, the guard column \<open>gs\<close> and the anchor \<open>rp\<close>, a flat 7-tuple
  paired once with \<open>acc\<close>.

  \<^bold>\<open>The \<open>cs\<close> column's values\<close>:
  \<^item> node with \<open>g < lock\<close>: \<open>c \<in> {0,1,2,3}\<close> is a classification of the truncated polynomial (decisive under its
    guard), and \<open>c = 4\<close> is the ambiguous sentinel, resolved at pop;
  \<^item> node with \<open>g = lock\<close>: \<open>c \<in> {0,1,2,3}\<close> is a classification, and \<open>c \<ge> 4\<close> is the cached count \<open>v+2\<close>. There is no
    clash: only \<open>window_push\<close> callers write \<open>\<ge> 4\<close> on locked nodes, and only the gate-closed split writes \<open>4\<close> on
    \<open>g < lock\<close> nodes.
  The proper-split test of \<open>\<sigma>\<close> (\<open>hybrid_split_run_len\<close>) excludes the sentinel \<open>4\<close>: decay applies only when both
  children are decisive and nonzero (\<open>cl, cr \<in> {1,2,3}\<close>).

  \<open>hybrid_dispatch_monadic\<close> and \<open>hybrid_after_pop_monadic\<close> are in \<open>Hybrid_Solver_Window\<close> because they use
  the window ops.\<close>

section \<open>State: 7-column worklist \<times> acc\<close>

type_synonym hybrid_worklist =
  "gmp_dyadic_interval_vec \<times> gmp_poly list \<times> nat list \<times> nat list \<times> nat list \<times>
    nat list \<times> gmp_poly"

type_synonym hybrid_state = "hybrid_worklist \<times> gmp_dyadic_interval_vec"

abbreviation hybrid_worklist_assn where
"hybrid_worklist_assn \<equiv>
  gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_poly_vec_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn
    \<times>\<^sub>a gmp_dyadic_exp_list_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn
    \<times>\<^sub>a gmp_dyadic_exp_list_assn \<times>\<^sub>a gmp_poly_assn"

abbreviation hybrid_state_assn where
"hybrid_state_assn \<equiv> hybrid_worklist_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn"

definition hybrid_loop_state_invar :: "hybrid_state \<Rightarrow> bool" where
"hybrid_loop_state_invar st \<equiv>
  (let ((todo, qtodo, es, ss, cs, gs, rp), acc) = st in
    dyadic_interval_vec_invar todo \<and>
    dyadic_interval_vec_invar acc \<and>
    (case todo of (lns, _, _) \<Rightarrow> length qtodo = length lns \<and> length es = length lns
                                \<and> length ss = length lns \<and> length cs = length lns
                                \<and> length gs = length lns))"

definition hybrid_loop_cond :: "hybrid_state \<Rightarrow> bool" where
"hybrid_loop_cond st \<equiv>
  (let ((todo, _, _, _, _, _, _), _) = st in
    let (lns, _, _) = todo in lns \<noteq> [])"

sepref_register "PR_CONST hybrid_loop_cond" :: "hybrid_state \<Rightarrow> bool"

definition hybrid_loop_cond_mop_monadic :: "hybrid_state \<Rightarrow> bool nres" where
"hybrid_loop_cond_mop_monadic st \<equiv>
  (case st of ((todo, qtodo, es, ss, cs, gs, rp), acc) \<Rightarrow>
    (PR_CONST gmp_dyadic_interval_vec_nonempty) todo)"

lemma hybrid_loop_cond_mop_monadic_eq:
  "hybrid_loop_cond_mop_monadic = RETURN o hybrid_loop_cond"
  unfolding hybrid_loop_cond_mop_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
    gmp_dyadic_interval_vec_nonempty_def hybrid_loop_cond_def
    dyadic_interval_vec_length_monadic_def poly_length_monadic_def PR_CONST_def
  by (auto intro!: ext split: prod.splits)

sepref_definition hybrid_loop_cond_impl [llvm_inline] is
  "hybrid_loop_cond_mop_monadic" ::
  "hybrid_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding hybrid_loop_cond_mop_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  by sepref

lemma hybrid_loop_cond_impl_hnr[sepref_fr_rules]:
  "(hybrid_loop_cond_impl, RETURN o (PR_CONST hybrid_loop_cond)) \<in>
    hybrid_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using hybrid_loop_cond_impl.refine
  by (simp add: hybrid_loop_cond_mop_monadic_eq PR_CONST_def)

(*FASTLOOP_FREEZE_ABOVE*)

section \<open>The zero/one branches (7-column clones of the bail ones)\<close>

definition hybrid_branch_zero_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
    gmp_poly \<Rightarrow> hybrid_state nres" where
"hybrid_branch_zero_monadic todo qtodo es ss cs gs rp acc l_num r_num Q \<equiv> doN {
  (PR_CONST mpzb_discard_monadic) l_num;
  (PR_CONST mpzb_discard_monadic) r_num;
  (PR_CONST poly_free_monadic) Q;
  RETURN ((todo, qtodo, es, ss, cs, gs, rp), acc)
}"

sepref_register "PR_CONST hybrid_branch_zero_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
      gmp_poly \<Rightarrow> hybrid_state nres"

sepref_definition hybrid_branch_zero_impl [llvm_code] is
  "uncurry10 hybrid_branch_zero_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a hybrid_state_assn"
  unfolding hybrid_branch_zero_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma hybrid_branch_zero_impl_hnr[sepref_fr_rules]:
  "(uncurry10 hybrid_branch_zero_impl,
    uncurry10 (PR_CONST hybrid_branch_zero_monadic)) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a hybrid_state_assn"
  using hybrid_branch_zero_impl.refine by (simp add: PR_CONST_def)

text \<open>Push the isolating interval \<open>[l,r]/2^k\<close> onto \<open>acc\<close>, isolated into its OWN op so its
  \<open>acc\<close> destructure is the ONLY product-let in the op (a second simultaneous product-let in
  the same body defeats sepref's id-phase — the branch_one failure). Mirrors the inline push
  in \<open>newton_branch_one_monadic\<close>.\<close>
definition hybrid_acc_push_iv_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec nres" where
"hybrid_acc_push_iv_monadic acc l_num r_num k \<equiv> doN {
  let (lns, rns, ks) = acc;
  ASSERT (dyadic_interval_vec_pushable (lns, rns, ks));
  lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) lns l_num;
  rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) rns r_num;
  ASSERT (length ks + 1 < max_snat LENGTH(gmp_poly_len));
  ks \<leftarrow> mop_list_append ks k;
  RETURN (lns, rns, ks)
}"

sepref_register "PR_CONST hybrid_acc_push_iv_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition hybrid_acc_push_iv_impl [llvm_code] is
  "uncurry3 hybrid_acc_push_iv_monadic" ::
  "[\<lambda>(((acc, _), _), k). dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_dyadic_interval_vec_assn"
  unfolding hybrid_acc_push_iv_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma hybrid_acc_push_iv_impl_hnr[sepref_fr_rules]:
  "(uncurry3 hybrid_acc_push_iv_impl, uncurry3 (PR_CONST hybrid_acc_push_iv_monadic)) \<in>
    [\<lambda>(((acc, _), _), k). dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_dyadic_interval_vec_assn"
  using hybrid_acc_push_iv_impl.refine by (simp add: PR_CONST_def)

definition hybrid_branch_one_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    gmp_poly \<Rightarrow> hybrid_state nres" where
"hybrid_branch_one_monadic todo qtodo es ss cs gs rp acc l_num r_num k Q \<equiv> doN {
  acc \<leftarrow> (PR_CONST hybrid_acc_push_iv_monadic) acc l_num r_num k;
  (PR_CONST poly_free_monadic) Q;
  RETURN ((todo, qtodo, es, ss, cs, gs, rp), acc)
}"

sepref_register "PR_CONST hybrid_branch_one_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      gmp_poly \<Rightarrow> hybrid_state nres"

sepref_definition hybrid_branch_one_impl [llvm_code] is
  "uncurry11 hybrid_branch_one_monadic" ::
  "[\<lambda>(((((((((((todo, qtodo), es), ss), cs), gs), rp), acc), _), _), k), Q).
      dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  unfolding hybrid_branch_one_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma hybrid_branch_one_impl_hnr[sepref_fr_rules]:
  "(uncurry11 hybrid_branch_one_impl,
    uncurry11 (PR_CONST hybrid_branch_one_monadic)) \<in>
    [\<lambda>(((((((((((todo, qtodo), es), ss), cs), gs), rp), acc), _), _), k), Q).
      dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> hybrid_state_assn"
  using hybrid_branch_one_impl.refine by (simp add: PR_CONST_def)

section \<open>The dense-children split with push-time g-guarded classifies\<close>

text \<open>Tuple-packaging result op (the \<open>newton_pcc_result_monadic\<close> trick, one extra \<open>gs\<close>).\<close>
definition hybrid_pcc_result_monadic ::
  "gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (gmp_poly list \<times> nat list \<times> nat \<times> nat) nres" where
"hybrid_pcc_result_monadic qtodo gs cl cr \<equiv> RETURN (qtodo, gs, cl, cr)"

sepref_register "PR_CONST hybrid_pcc_result_monadic"
  :: "gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      (gmp_poly list \<times> nat list \<times> nat \<times> nat) nres"

sepref_definition hybrid_pcc_result_impl [llvm_inline] is
  "uncurry3 hybrid_pcc_result_monadic" ::
  "gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    gmp_poly_vec_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn \<times>\<^sub>a
      (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  unfolding hybrid_pcc_result_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  by sepref

lemma hybrid_pcc_result_impl_hnr[sepref_fr_rules]:
  "(uncurry3 hybrid_pcc_result_impl,
    uncurry3 (PR_CONST hybrid_pcc_result_monadic)) \<in>
    gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
      gmp_poly_vec_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn \<times>\<^sub>a
        (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  using hybrid_pcc_result_impl.refine by (simp add: PR_CONST_def)

text \<open>The pure classify-or-sentinel step, as its own op (no inline word arithmetic in heap bodies).\<close>
definition hybrid_class_of :: "bool \<Rightarrow> nat \<Rightarrow> nat" where
  "hybrid_class_of dec cnt = (if dec then cnt else 4)"

sepref_register "PR_CONST hybrid_class_of" :: "bool \<Rightarrow> nat \<Rightarrow> nat"

sepref_definition hybrid_class_of_impl [llvm_inline] is
  "uncurry (RETURN oo hybrid_class_of)" ::
  "bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding hybrid_class_of_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma hybrid_class_of_impl_hnr[sepref_fr_rules]:
  "(uncurry hybrid_class_of_impl, uncurry (RETURN oo PR_CONST hybrid_class_of)) \<in>
    bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using hybrid_class_of_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The hybrid solver's \<open>\<sigma>\<close> successor: \<open>newton_split_run_len\<close> with the sentinel \<open>4\<close> excluded.\<close> Decay
  applies only when both children are decisive and nonzero, \<open>cl, cr \<in> {1,2,3}\<close>: an ambiguous child (class \<open>4\<close>,
  resolved at pop) is not evidence of a proper split. A large interior cluster keeps its empty sibling's truncated
  classification persistently ambiguous, so counting the sentinel as a split would make every step look like a
  proper split and keep the gate closed.

  \<^bold>\<open>Why a separate constant.\<close> Only the hybrid solver's \<open>hybrid_classify_prebuilt_monadic\<close> emits the sentinel.
  The Newton and bail solvers classify through @{const carried_descartes_count_trunc_monadic}, bounded by \<open>3\<close>, so the
  conjunct would change nothing there, but their loop refinements use the exact @{const carried_descartes_count}
  (a child may have \<open>\<ge> 4\<close> variations) against \<open>split_run_len_int\<close>'s nonzero test, which a shared \<open>< 4\<close> conjunct
  would falsify.\<close>
definition hybrid_split_run_len :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "hybrid_split_run_len mid cl cr s =
     (if mid \<or> (0 < cl \<and> cl < 4 \<and> 0 < cr \<and> cr < 4) then s - s div 11 else s + 1)"

sepref_register "PR_CONST hybrid_split_run_len" :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

sepref_definition hybrid_split_run_len_impl [llvm_inline] is
  "uncurry3 (RETURN oooo hybrid_split_run_len)" ::
  "[\<lambda>(((mid, cl), cr), s). s + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding hybrid_split_run_len_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma hybrid_split_run_len_impl_hnr[sepref_fr_rules]:
  "(uncurry3 hybrid_split_run_len_impl, uncurry3 (RETURN oooo PR_CONST hybrid_split_run_len)) \<in>
    [\<lambda>(((mid, cl), cr), s). s + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using hybrid_split_run_len_impl.refine by (simp add: PR_CONST_def)

section \<open>Split branch: midpoint decision from the child's constant coefficient (O(1))\<close>

text \<open>The split branch is structured so the DENSE children are built FIRST (via
  @{const truncate_children_mid_monadic}, which reads \<open>qr!0\<close>'s sign/bitlen before the
  retruncation) and the guarded mid decision (@{const truncate_mid_decide_monadic})
  consumes that \<open>O(1)\<close> read instead of the \<open>O(len)\<close> half-eval. The children are then
  classified + pushed by \<open>hybrid_classify_prebuilt_monadic\<close> / the prebuilt pair-state
  op, avoiding a second build. On the rare AMBIGUOUS decision (\<open>code = 2\<close>) the truncated
  children are freed and the node is rebuilt exact from the loop-carried root \<open>rp\<close>, exactly
  matching \<open>truncate_mid_test_monadic\<close>'s escalate-to-exact semantics
  (guard reset to \<open>0\<close>, the mid path's differentiated non-lock escalation).\<close>

text \<open>The push-time g-guarded classify with the child BUILD hoisted out: the caller
  passes the already-built \<open>(ql, gl, qr, gr)\<close>, this op only g-classifies + pushes them.\<close>
definition hybrid_classify_prebuilt_monadic ::
  "gmp_poly list \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow>
    (gmp_poly list \<times> nat list \<times> nat \<times> nat) nres" where
"hybrid_classify_prebuilt_monadic qtodo gs ql gl qr gr \<equiv> doN {
  ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length qr + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>Per-child sign-variation counting under the capped-at-2 \<open>cs\<close> discipline.\<close>
  (cl0, decl) \<leftarrow> (PR_CONST carried_descartes_count_g_monadic) ql gl;
  let cl = (PR_CONST hybrid_class_of) decl cl0;
  (cr0, decr) \<leftarrow> (PR_CONST carried_descartes_count_g_monadic) qr gr;
  let cr = (PR_CONST hybrid_class_of) decr cr0;
  qtodo \<leftarrow> (PR_CONST poly_vec_push2_monadic) qtodo ql qr;
  ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
  gs \<leftarrow> mop_list_append gs gl;
  ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
  gs \<leftarrow> mop_list_append gs gr;
  (PR_CONST hybrid_pcc_result_monadic) qtodo gs cl cr
}"

sepref_register "PR_CONST hybrid_classify_prebuilt_monadic"
  :: "gmp_poly list \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow>
      (gmp_poly list \<times> nat list \<times> nat \<times> nat) nres"

sepref_definition hybrid_classify_prebuilt_impl [llvm_code] is
  "uncurry5 hybrid_classify_prebuilt_monadic" ::
  "[\<lambda>(((((qtodo, gs), ql), gl), qr), gr).
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length gs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_vec_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn \<times>\<^sub>a
        (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  unfolding hybrid_classify_prebuilt_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma hybrid_classify_prebuilt_impl_hnr[sepref_fr_rules]:
  "(uncurry5 hybrid_classify_prebuilt_impl,
    uncurry5 (PR_CONST hybrid_classify_prebuilt_monadic)) \<in>
    [\<lambda>(((((qtodo, gs), ql), gl), qr), gr).
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      length gs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_vec_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn \<times>\<^sub>a
        (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  using hybrid_classify_prebuilt_impl.refine by (simp add: PR_CONST_def)

text \<open>The pair-state split with the child build hoisted out: takes the
  already-built \<open>(ql, gl, qr, gr)\<close> (so no \<open>g\<close>/\<open>Q\<close> arg) and classifies via
  \<open>hybrid_classify_prebuilt_monadic\<close>.\<close>
definition hybrid_split_pair_state_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
    gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> hybrid_worklist nres" where
"hybrid_split_pair_state_monadic todo qtodo es ss cs gs rp l_num r_num k e s mid
    ql gl qr gr \<equiv> doN {
  ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length es + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length ss + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length cs + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length gs + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable2 todo);
  todo \<leftarrow> (PR_CONST dyadic_interval_vec_push_children_monadic) todo l_num r_num k;
  (qtodo, gs, cl, cr) \<leftarrow>
    (PR_CONST hybrid_classify_prebuilt_monadic) qtodo gs ql gl qr gr;
  let e' = (PR_CONST newton_child_exp) e;
  es \<leftarrow> (PR_CONST dyadic_exp_push2_monadic) es e';
  ASSERT (s + 1 < max_snat LENGTH(gmp_poly_len));
  let s' = (PR_CONST hybrid_split_run_len) mid cl cr s;
  ss \<leftarrow> (PR_CONST dyadic_exp_push2_monadic) ss s';
  ASSERT (length cs + 1 < max_snat LENGTH(gmp_poly_len));
  cs \<leftarrow> mop_list_append cs cl;
  ASSERT (length cs + 1 < max_snat LENGTH(gmp_poly_len));
  cs \<leftarrow> mop_list_append cs cr;
  RETURN (todo, qtodo, es, ss, cs, gs, rp)
}"

sepref_register "PR_CONST hybrid_split_pair_state_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
      gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> hybrid_worklist nres"

sepref_definition hybrid_split_pair_state_impl [llvm_code] is
  "uncurry16 hybrid_split_pair_state_monadic" ::
  "[\<lambda>((((((((((((((((todo, qtodo), es), ss), cs), gs), rp), _), _), k), _), s), _), _), _), _), gr).
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      s + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      hybrid_worklist_assn"
  unfolding hybrid_split_pair_state_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma hybrid_split_pair_state_impl_hnr[sepref_fr_rules]:
  "(uncurry16 hybrid_split_pair_state_impl,
    uncurry16 (PR_CONST hybrid_split_pair_state_monadic)) \<in>
    [\<lambda>((((((((((((((((todo, qtodo), es), ss), cs), gs), rp), _), _), k), _), s), _), _), _), _), gr).
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      s + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      hybrid_worklist_assn"
  using hybrid_split_pair_state_impl.refine by (simp add: PR_CONST_def)


text \<open>The split branch for count \<open>\<ge> 2\<close> (parallel to @{const hybrid_branch_zero_monadic} /
  @{const hybrid_branch_one_monadic}). It builds both children with an \<open>O(1)\<close> midpoint decision:
  @{const truncate_children_mid_monadic} reads the child's constant coefficient \<open>qr!0\<close> (sign and bit length) instead of
  evaluating the node at the midpoint. It escalates on an ambiguous decision (\<open>code = 2\<close>: discard the truncated
  children, rebuild exact), and otherwise classifies and pushes via @{const hybrid_split_pair_state_monadic}.\<close>
section \<open>Degree deflation at the split branch\<close>

text \<open>\<^bold>\<open>Why the deflation needs no extra guard here.\<close> @{const defl_half_cert} on a truncated operand is not a
  reliable root test: the one-sided coefficient error \<open>< 2\<^sup>g\<close> propagates into the certificate as \<open>< 2\<^sup>g\<^sup>+\<^sup>n\<^sup>+\<^sup>1\<close>, so a vanishing
  truncated certificate does not prove that the exact one vanishes. But @{const truncate_mid_decide_monadic} returns its
  root code \<open>1\<close> only under \<open>g = 0\<close> or \<open>g \<ge> 2\<^sup>4\<^sup>2\<close>, the exact and locked cases; on a truncated operand it returns only \<open>0\<close>
  (trusted nonzero) or \<open>2\<close> (escalate). Gating the deflation on the same condition inherits that guard, so no guarded
  certificate test is needed.

  The \<open>3 \<le> len\<close> clamp is a policy guard, not a bound: refusing to deflate is always sound, and below length 3 the
  quotient would be a constant with degenerate children.\<close>

abbreviation split_children_assn where
"split_children_assn \<equiv>
  gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
  gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"

text \<open>\<^bold>\<open>The shed gate on the exact lock.\<close> \<open>len0\<close> is the length of the loop-carried root polynomial \<open>rp\<close> and \<open>len\<close>
  that of the node; a node that has not been deflated has \<open>len = len0\<close>, because shifts and scalings preserve the degree.
  So \<open>len0 - len\<close> is the number of degrees this path has shed, available from two length reads with no new loop state.

  \<^bold>\<open>Why the lock is gated.\<close> \<open>g \<ge> 2\<^sup>4\<^sup>2\<close> means ``exact, never re-truncate'', so a locked subtree gives up truncation
  permanently, which is expensive where truncation carries the solve. Whether deflation pays is determined by the shed
  as a fraction of the degree rather than by how often a root is shed, and the gate measures that fraction directly:
  lock once the path has shed an eighth of the original degree (\<open>div 8\<close>). It is a policy guard: declining to lock is
  always sound, and it is not a word bound.\<close>

section \<open>Pushing the left child only\<close>

text \<open>When the right-child decide proves the right child empty, the program does not push it. This is the
  interval half, the left child's own \<open>((2l, l+r), k+1)\<close> slot, built from the single push
  @{const dyadic_interval_vec_push_monadic}.

  \<^bold>\<open>Ownership\<close>: @{const dyadic_interval_vec_push_children_monadic} consumes both endpoints (\<open>l_num\<close> via the doubling,
  \<open>r_num\<close> via its own push). Here only \<open>l_num\<close> is consumed, so \<open>r_num\<close>, which the addition borrows, is discarded
  explicitly.\<close>
definition dyadic_iv_push_left_child_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec nres" where
"dyadic_iv_push_left_child_monadic todo l_num r_num k \<equiv> doN {
  mid_src \<leftarrow> RETURN (COPY l_num);
  mid \<leftarrow> (PR_CONST mpz_add.amop_r1) mid_src r_num;
  l2 \<leftarrow> (PR_CONST mpz_double_shift_monadic) l_num;
  (PR_CONST mpzb_discard_monadic) r_num;
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable todo);
  (PR_CONST dyadic_interval_vec_push_monadic) todo l2 mid (k + 1)
}"

sepref_register "PR_CONST dyadic_iv_push_left_child_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec nres"

lemma dyadic_iv_push_left_child_monadic_spec:
  assumes inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and push: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "dyadic_iv_push_left_child_monadic (lns, rns, ks) l_num r_num k \<le>
    SPEC (\<lambda>v. dyadic_interval_vec_invar v \<and>
      dyadic_interval_vec_triples v =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num + l_num, l_num + r_num), k + 1)] \<and>
      dyadic_interval_vec_to_list v =
        dyadic_interval_vec_to_list (lns, rns, ks) @
          [dyadic_interval_of_triple ((l_num + l_num, l_num + r_num), k + 1)])"
  \<comment> \<open>The push spec's conclusion is a THREE-way conjunction (it also fixes
     \<open>to_list\<close>); stating only the first two makes it un-matchable as an \<open>intro\<close>, which is why
     this carries the full form. The \<open>to_list\<close> half is what the abstract worklist argument
     wants anyway.\<close>
  unfolding dyadic_iv_push_left_child_monadic_def PR_CONST_def
  apply (refine_vcg dyadic_interval_vec_push_monadic_spec
    mpz_double_shift_monadic_spec_plain[THEN order_trans])
  using assms
  by (auto simp: mpzb_discard_monadic_def mpz_add.aop_r1_def
                 top_fun_def top_bool_def
           intro: dyadic_interval_vec_push_monadic_spec)



sepref_definition dyadic_iv_push_left_child_impl [llvm_code] is
  "uncurry3 dyadic_iv_push_left_child_monadic" ::
  "[\<lambda>(((todo, l_num), r_num), k). k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_dyadic_interval_vec_assn"
  unfolding dyadic_iv_push_left_child_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma dyadic_iv_push_left_child_impl_hnr[sepref_fr_rules]:
  "(uncurry3 dyadic_iv_push_left_child_impl,
    uncurry3 (PR_CONST dyadic_iv_push_left_child_monadic)) \<in>
    [\<lambda>(((todo, l_num), r_num), k). k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_dyadic_interval_vec_assn"
  using dyadic_iv_push_left_child_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The left-only classify+push.\<close>
  @{const hybrid_classify_prebuilt_monadic} counts BOTH children and pushes both. When the
  decide has PROVEN the right child empty there is no right child to count or push --- but its
  class is not unknown, it is \<open>0\<close>, which is exactly what the two-child op would have computed.
  Returning \<open>0\<close> for \<open>cr\<close> therefore leaves every SCALAR consequence identical: in particular
  @{const hybrid_split_run_len}'s \<open>\<sigma>\<close> decay reads the same value it would have read, so the
  run-length column is unchanged. Only the PUSH is skipped.\<close>
definition hybrid_classify_prebuilt_left_monadic ::
  "gmp_poly list \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow>
    (gmp_poly list \<times> nat list \<times> nat \<times> nat) nres" where
"hybrid_classify_prebuilt_left_monadic qtodo gs ql gl \<equiv> doN {
  ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
  (cl0, decl) \<leftarrow> (PR_CONST carried_descartes_count_g_monadic) ql gl;
  let cl = (PR_CONST hybrid_class_of) decl cl0;
  qtodo \<leftarrow> (PR_CONST poly_vec_push_monadic) qtodo ql;
  ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
  gs \<leftarrow> mop_list_append gs gl;
  (PR_CONST hybrid_pcc_result_monadic) qtodo gs cl 0
}"

sepref_register "PR_CONST hybrid_classify_prebuilt_left_monadic"
  :: "gmp_poly list \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow>
      (gmp_poly list \<times> nat list \<times> nat \<times> nat) nres"

sepref_definition hybrid_classify_prebuilt_left_impl [llvm_code] is
  "uncurry3 hybrid_classify_prebuilt_left_monadic" ::
  "[\<lambda>(((qtodo, gs), ql), gl).
      length qtodo + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length gs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_vec_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn \<times>\<^sub>a
        (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  unfolding hybrid_classify_prebuilt_left_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma hybrid_classify_prebuilt_left_impl_hnr[sepref_fr_rules]:
  "(uncurry3 hybrid_classify_prebuilt_left_impl,
    uncurry3 (PR_CONST hybrid_classify_prebuilt_left_monadic)) \<in>
    [\<lambda>(((qtodo, gs), ql), gl).
      length qtodo + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length gs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_vec_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_vec_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn \<times>\<^sub>a
        (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  using hybrid_classify_prebuilt_left_impl.refine by (simp add: PR_CONST_def)



text \<open>\<^bold>\<open>The LEFT-ONLY pair-state step.\<close>
  @{const hybrid_split_pair_state_monadic} with the right child removed from every one of the
  six parallel worklist columns at once --- interval, poly, \<open>es\<close>, \<open>ss\<close>, \<open>cs\<close>, \<open>gs\<close>. It needs NO
  new primitives beyond the two above: \<open>es\<close>/\<open>ss\<close>/\<open>cs\<close> already append ONE element at a time
  (@{const mop_list_append}), so only the two genuinely paired pushes had to be cloned.
  \<open>cr = 0\<close> comes from the decide, so \<open>s'\<close> is the value the two-child step would have computed.\<close>
definition hybrid_split_pair_state_left_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
    gmp_poly \<Rightarrow> nat \<Rightarrow> hybrid_worklist nres" where
"hybrid_split_pair_state_left_monadic todo qtodo es ss cs gs rp l_num r_num k e s mid
    ql gl \<equiv> doN {
  ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length es + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length ss + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length cs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable todo);
  todo \<leftarrow> (PR_CONST dyadic_iv_push_left_child_monadic) todo l_num r_num k;
  (qtodo, gs, cl, cr) \<leftarrow>
    (PR_CONST hybrid_classify_prebuilt_left_monadic) qtodo gs ql gl;
  let e' = (PR_CONST newton_child_exp) e;
  es \<leftarrow> mop_list_append es e';
  ASSERT (s + 1 < max_snat LENGTH(gmp_poly_len));
  let s' = (PR_CONST hybrid_split_run_len) mid cl cr s;
  ss \<leftarrow> mop_list_append ss s';
  ASSERT (length cs + 1 < max_snat LENGTH(gmp_poly_len));
  cs \<leftarrow> mop_list_append cs cl;
  RETURN (todo, qtodo, es, ss, cs, gs, rp)
}"

sepref_register "PR_CONST hybrid_split_pair_state_left_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
      gmp_poly \<Rightarrow> nat \<Rightarrow> hybrid_worklist nres"

sepref_definition hybrid_split_pair_state_left_impl [llvm_code] is
  "uncurry14 hybrid_split_pair_state_left_monadic" ::
  "[\<lambda>((((((((((((((todo, qtodo), es), ss), cs), gs), rp), _), _), k), _), s), _), _), gl).
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      s + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      hybrid_worklist_assn"
  unfolding hybrid_split_pair_state_left_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma hybrid_split_pair_state_left_impl_hnr[sepref_fr_rules]:
  "(uncurry14 hybrid_split_pair_state_left_impl,
    uncurry14 (PR_CONST hybrid_split_pair_state_left_monadic)) \<in>
    [\<lambda>((((((((((((((todo, qtodo), es), ss), cs), gs), rp), _), _), k), _), s), _), _), gl).
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      s + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      hybrid_worklist_assn"
  using hybrid_split_pair_state_left_impl.refine by (simp add: PR_CONST_def)



section \<open>The right-child decide at the split, and the right-child stub\<close>

text \<open>Two NAMED right-child constructions, each with a one-line \<open>\<le> RETURN\<close> spec. Naming them
  is what makes \<open>carried_left_right_skip_right_monadic\<close>'s contract tractable: each branch of the
  decide becomes a SINGLE refinement step instead of an inline \<open>copy\<close>+\<open>shift\<close> chain that
  \<open>refine_vcg\<close> has to re-derive under a \<open>SPEC\<close> continuation.\<close>
\<comment> \<open>The parameter is \<open>ql\<close>, not \<open>left\<close>: \<open>left\<close> is a constant in scope (\<open>HM.h.left :: nat \<Rightarrow> nat\<close>), so a parameter of
  that name would bind to it and cause a type clash.\<close>
definition carried_right_of_left_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"carried_right_of_left_monadic ql \<equiv> doN {
  ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
  right \<leftarrow> (PR_CONST poly_copy_monadic) ql;
  \<comment> \<open>Sepref does NOT know \<open>poly_copy_monadic\<close> preserves length, so the shift's own HNR
     precondition has to be asserted about the COPY.\<close>
  ASSERT (length right + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_taylor_shift_one_in_place_monadic) right
}"

sepref_register "PR_CONST carried_right_of_left_monadic" :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition carried_right_of_left_impl [llvm_code] is
  "carried_right_of_left_monadic" ::
  "[\<lambda>ql. length ql + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding carried_right_of_left_monadic_def
  by sepref

lemma carried_right_of_left_impl_hnr[sepref_fr_rules]:
  "(carried_right_of_left_impl, PR_CONST carried_right_of_left_monadic) \<in>
    [\<lambda>ql. length ql + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using carried_right_of_left_impl.refine
  by (simp add: PR_CONST_def)

lemma carried_right_of_left_correct:
  assumes "length ql + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_right_of_left_monadic ql \<le> RETURN (taylor_shift_list 1 ql)"
  unfolding carried_right_of_left_monadic_def PR_CONST_def
  apply (refine_vcg poly_copy_correct[THEN order_trans]
    poly_taylor_shift_one_in_place_monadic_correct[THEN order_trans])
  using assms by auto

text \<open>The SINGLETON stub: the fast path's right child is \<open>[carried_right xs ! 0]\<close>, one \<open>mpz\<close>
  carrying the value both \<open>qr!0\<close> reads want.\<close>
definition carried_right_stub_monadic :: "int \<Rightarrow> gmp_poly nres" where
"carried_right_stub_monadic s \<equiv> doN {
  dst \<leftarrow> (PR_CONST poly_empty_sz_monadic) 1;
  \<comment> \<open>Same reason as in @{const carried_right_of_left_monadic}: Sepref cannot see that the
     fresh vector is EMPTY, so the push's own HNR precondition has to be asserted.\<close>
  ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_push_coeff_monadic) dst s
}"

sepref_register "PR_CONST carried_right_stub_monadic" :: "int \<Rightarrow> gmp_poly nres"

sepref_definition carried_right_stub_impl [llvm_code] is
  "carried_right_stub_monadic" ::
  "mpzb_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  unfolding carried_right_stub_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma carried_right_stub_impl_hnr[sepref_fr_rules]:
  "(carried_right_stub_impl, PR_CONST carried_right_stub_monadic) \<in>
    mpzb_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  using carried_right_stub_impl.refine
  by (simp add: PR_CONST_def)

lemma carried_right_stub_correct:
  "carried_right_stub_monadic s \<le> RETURN [s]"
  unfolding carried_right_stub_monadic_def PR_CONST_def
  by (auto simp: poly_empty_sz_monadic_def poly_push_coeff_monadic_def
                 max_snat_def pw_le_iff refine_pw_simps)



text \<open>\<^bold>\<open>@{const carried_left_right_monadic} with the right-child decide.\<close> It is that op's three instructions with a
  decide between them: \<open>poly_shift_pow_in_place\<close> (the \<open>O(n)\<close> left child), then @{const right_empty_decide_monadic},
  then the \<open>O(n\<^sup>2)\<close> copy and shift only if the decide did not fire. The caller decomposes the fused op; the op itself
  is unchanged.

  \<^bold>\<open>Why the fast path still returns a right child, of exactly one element.\<close> Both call sites read \<open>qr!0\<close>'s sign and
  bit length to drive \<open>truncate_mid_decide_monadic\<close>. On the fast path \<open>qr\<close> is not built, but
  \<open>carried_right xs ! 0 = sum_list (carried_left xs)\<close> (@{thm carried_right_nth0_sum_list}) is an \<open>O(n)\<close> sum computed
  anyway, so returning the singleton \<open>[carried_right xs ! 0]\<close> gives both reads their usual answers with no change at
  the read site. It is one \<open>mpz\<close>, and a real value rather than a placeholder, so the caller's guard cascade is
  unaffected.

  \<^bold>\<open>The deflation interlock\<close> (@{thm carried_right_nth0_nz_iff}): a Descartes count of \<open>0\<close> does not imply that the
  midpoint is not a root, since the count is about the open box and a root at the shared endpoint contributes no sign
  variation. If the sum is \<open>0\<close>, the midpoint is a root and \<open>defl_children_monadic\<close> would shed a linear factor, which must
  not be taken from a child that was never built. So \<open>s = 0\<close> falls back to the exact build, at no cost, since the sum is
  already computed.\<close>
definition carried_left_right_skip_right_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> gmp_poly \<times> bool) nres" where
"carried_left_right_skip_right_monadic g xs \<equiv> doN {
  ASSERT (0 < length xs);
  ASSERT (length xs + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (1 * (length xs - 1) < max_snat LENGTH(gmp_poly_len));
  lc \<leftarrow> (PR_CONST poly_shift_pow_in_place_monadic) 1 xs;
  \<comment> \<open>All three consumers of \<open>lc\<close> want their OWN HNR precondition about \<open>lc\<close>, and Sepref does
     not derive \<open>+1\<close> from \<open>+2\<close> nor \<open>0 < length lc\<close> from \<open>0 < length xs\<close> --- it cannot see that
     the shift preserves length. \<open>poly_eval1_pair\<close> is the one that needs BOTH.\<close>
  ASSERT (0 < length lc);
  ASSERT (length lc + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length lc + 2 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>\<open>g\<close> is the node's guard: the mirror arm ramps by it at a truncated guard only
     (\<open>err_ramp_opt\<close>), which is what lets \<open>right_empty_certified_count_zero\<close> reach the EXACT node.\<close>
  rz \<leftarrow> (PR_CONST right_empty_decide_monadic) g lc;
  if \<not> rz then doN {
    right \<leftarrow> (PR_CONST carried_right_of_left_monadic) lc;
    RETURN (lc, right, False)
  } else doN {
    (s, ds) \<leftarrow> (PR_CONST poly_eval1_pair_monadic) lc;
    (PR_CONST mpzb_discard_monadic) ds;
    sg \<leftarrow> (PR_CONST mpz_sgn_mop) s;
    if sg = 0 then doN {
      (PR_CONST mpzb_discard_monadic) s;
      right \<leftarrow> (PR_CONST carried_right_of_left_monadic) lc;
      RETURN (lc, right, False)
    } else doN {
      right \<leftarrow> (PR_CONST carried_right_stub_monadic) s;
      RETURN (lc, right, True)
    }
  }
}"

sepref_register "PR_CONST carried_left_right_skip_right_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> gmp_poly \<times> bool) nres"



text \<open>\<^bold>\<open>The contract.\<close> On \<open>\<not>rz\<close> this is the original op exactly. On \<open>rz\<close> the right child is proved empty, its \<open>!0\<close>
  read is preserved, and that entry is nonzero (the interlock). The precondition \<open>length xs + 2\<close> is one more than the
  other ops carry (@{thm poly_eval1_pair_monadic_correct} needs it), and both call sites pass it on.

  \<^bold>\<open>Proof shape.\<close> \<open>refine_vcg\<close> does not bridge the decide's \<open>\<le> SPEC (\<lambda>b. b \<longrightarrow> C)\<close> to the continuation by itself. The
  route is: \<open>refine_vcg\<close> once for the left-child build (it applies its own \<open>bind_rule\<close>), then \<open>order_trans\<close> with the
  decide, then \<open>SPEC_rule\<close>, and no \<open>refine_vcg\<close> in the branches: every op below the decide concludes \<open>\<le> RETURN v\<close>, so
  \<open>bind_le_of_RETURN\<close> handles them. \<open>pw_le_iff refine_pw_simps\<close> is kept out, since it produces 42 \<open>nofail\<close>/\<open>inres\<close>
  subgoals where this route leaves one. \<open>left_eq\<close> is needed in both spellings (see \<open>left_eq'\<close>).\<close>
text \<open>\<^bold>\<open>\<open>SPEC\<close> is an abbreviation.\<close> \<^term>\<open>SPEC \<Phi>\<close> is \<^term>\<open>RES (Collect \<Phi>)\<close> (\<open>Refine_Basic\<close>). A postcondition that
  \<open>refine_vcg\<close> has normalised into \<open>RES (\<open>{v}\<close> \<times> \<dots>)\<close>, which happens whenever the first component of a pair-shaped \<open>SPEC\<close> is
  pinned to a value, is a \<^const>\<open>Sigma\<close>, not a \<^const>\<open>Collect\<close>, and does not unify with \<open>SPEC ?\<Phi>\<close>, so subsequent
  \<open>bind_rule\<close>s do not match. This lemma rewrites the \<^const>\<open>Sigma\<close> back into a \<^const>\<open>Collect\<close>. The contract below avoids
  the normalisation through \<open>bind_le_of_RETURN\<close>; the two split-children call sites use this lemma.\<close>
lemma RES_Times_eq_SPEC: "RES (A \<times> B) = SPEC (\<lambda>(x, y). x \<in> A \<and> y \<in> B)"
  by (rule arg_cong[where f = RES]) auto

text \<open>\<^bold>\<open>Every op in both branches is deterministic\<close> --- \<open>poly_eval1_pair\<close>, \<open>mpz_sgn_mop\<close>,
  \<open>mpzb_discard\<close>, \<open>carried_right_of_left\<close> and the stub all conclude \<open>\<le> RETURN v\<close>, never a
  proper \<open>SPEC\<close>. So the branches do not need \<open>refine_vcg\<close> at all: this one lemma walks each
  bind by rewriting it to its value, which is both shorter and immune to the \<^const>\<open>Sigma\<close>
  normalisation above.\<close>
lemma bind_le_of_RETURN:
  assumes "m \<le> RETURN v"
  shows "m \<bind> f \<le> f v"
proof -
  have "m \<bind> f \<le> RETURN v \<bind> f" by (rule bind_mono(1)[OF assms]) simp
  thus ?thesis by simp
qed

text \<open>\<^bold>\<open>The frame transfer: the decide can run on a truncated node.\<close> The decide receives the stored node \<open>Y\<close>; the
  abstract discard is about the exact node \<open>X\<close>, and at a truncated guard they differ. The gap closes on the
  non-negative arm because the frame is one-sided: \<open>gframe s g X Y\<close> gives \<open>2\<^sup>s * Y ! i \<le> X ! i\<close>, \<open>carried_left\<close> scales by
  the non-negative weight \<open>2 ^ (n - 1 - i)\<close>, and \<open>Ffun\<close> is a linear map with non-negative coefficients (\<open>F_mono\<close>,
  \<open>F_smult\<close>), so \<open>Ffun (carried_left X) \<ge> 2\<^sup>s * Ffun (carried_left Y) \<ge> 0\<close>, and a non-negative list has no sign changes.

  It is proved here rather than in \<open>Count\<close> because \<open>gframe\<close> is declared in \<open>Truncate_Spec\<close>, which \<open>Count\<close> does not
  import.

  The mirror arm does not transfer this way: it concludes \<open>Ffun (carried_left Y) \<le> 0\<close>, and \<open>2\<^sup>s * (\<le> 0) + (\<ge> 0)\<close> has no
  determined sign. See below.\<close>

lemma gframe_F_nonneg_transfer:
  fixes X Y :: "int list"
  assumes fr: "gframe s g X Y"
    and nn: "\<And>j. j < length (carried_left Y) \<Longrightarrow> 0 \<le> Ffun (carried_left Y) ! j"
    and i: "i < length (carried_left X)"
  shows "0 \<le> Ffun (carried_left X) ! i"
proof -
  have len: "length X = length Y" by (rule gframe_length[OF fr])
  have lenL: "length (carried_left Y) = length Y"
    and lenLX: "length (carried_left X) = length X" by (simp_all add: carried_left_def)
  have le: "2 ^ s * Y ! j \<le> X ! j" if "j < length Y" for j
    using fr that unfolding gframe_def by auto
  \<comment> \<open>indexed on \<open>length Y\<close>, NOT on \<open>length (carried_left Y)\<close>: the two are equal by
     \<open>lenL\<close>, but stating it the second way leaves \<open>intro\<close> a residual
     \<open>j < length (carried_left Y) \<Longrightarrow> \<dots> \<Longrightarrow> j < length Y\<close> that the closer has to re-derive.
     \<open>length Y\<close> is also exactly the index \<open>F_mono\<close> asks for, since
     \<open>length (map ((*) (2 ^ s)) (carried_left Y)) = length Y\<close>.\<close>
  have step: "map ((*) (2 ^ s)) (carried_left Y) ! j \<le> carried_left X ! j"
    if "j < length Y" for j
    by (rule carried_left_nth_mono[OF len le that])
  have iY: "i < length (carried_left Y)" using i lenL lenLX len by simp
  have A: "Ffun (map ((*) (2 ^ s)) (carried_left Y)) ! i \<le> Ffun (carried_left X) ! i"
    by (rule F_mono) (use iY lenL lenLX len step in simp_all)
  have B: "Ffun (map ((*) (2 ^ s)) (carried_left Y)) ! i = 2 ^ s * (Ffun (carried_left Y) ! i)"
    using iY by (simp add: F_smult)
  have "0 \<le> 2 ^ s * (Ffun (carried_left Y) ! i)" using nn[OF iY] by simp
  with A B show ?thesis by linarith
qed

text \<open>\<^bold>\<open>The payoff, in the shape the caller needs\<close>: a NON-NEGATIVE arm fired on the stored
  node discharges the abstract discard for the EXACT node.\<close>
lemma gframe_carried_right_count_zero:
  fixes X Y :: "int list"
  assumes fr: "gframe s g X Y"
    and nn: "\<And>j. j < length (carried_left Y) \<Longrightarrow> 0 \<le> Ffun (carried_left Y) ! j"
  shows "carried_descartes_count (carried_right X) = 0"
\<comment> \<open>\<^bold>\<open>\<open>key\<close> is bound first, with an explicit \<open>if \<dots> for\<close>.\<close> With \<open>using gframe_F_nonneg_transfer[OF fr nn]\<close>, \<open>OF\<close> finds
   multiple unifiers (\<open>nn\<close>'s bound \<open>j\<close> is schematic, so it matches the index premise as well as the non-negativity
   premise), and \<open>metis\<close> does not terminate on the resulting fact. Discharging the index premise explicitly with \<open>that\<close>
   gives \<open>metis\<close> the shape of \<open>F_nonneg_sound\<close>.\<close>
proof -
  have key: "0 \<le> Ffun (carried_left X) ! i" if "i < length (carried_left X)" for i
    by (rule gframe_F_nonneg_transfer[OF fr nn that])
  have "\<forall>x \<in> set (Ffun (carried_left X)). 0 \<le> x"
    using key by (metis in_set_conv_nth F_len)
  hence "sign_changes_fold (Ffun (carried_left X)) = 0" by (rule sign_changes_fold_nonneg)
  thus ?thesis by (simp add: carried_descartes_count_def carried_right_def)
qed

text \<open>\<^bold>\<open>The mirror arm's transfer, at the cost of an \<open>O(n)\<close> addition.\<close> The mirror concludes
  \<open>Ffun (carried_left Y) \<le> 0\<close>, which does not transfer as the non-negative arm does. The frame's upper bound gives

    \<open>X ! j < 2\<^sup>s * Y ! j + 2\<^sup>s\<^sup>+\<^sup>g = 2\<^sup>s * (Y ! j + 2\<^sup>g)\<close>

  so running the same rule on \<open>Y + 2\<^sup>g\<close> (componentwise) certifies \<open>X\<close>. \<open>carried_left\<close> is linear, so
  \<open>carried_left (Y + 2\<^sup>g) = carried_left Y + 2\<^sup>g * carried_left 1s\<close>, and no separate error vector is built. The cost is one
  \<open>O(n)\<close> addition of a \<open>g\<close>-bit constant, against the \<open>O(n\<^sup>2)\<close> build it avoids.\<close>

lemma carried_left_nth_antimono:
  fixes X Y :: "int list"
  assumes len: "length X = length Y"
    and le: "\<And>j. j < length Y \<Longrightarrow> X ! j \<le> 2 ^ s * Y ! j"
    and i: "i < length Y"
  shows "carried_left X ! i \<le> map ((*) (2 ^ s)) (carried_left Y) ! i"
proof -
  have lenL: "length (carried_left Y) = length Y" by (simp add: carried_left_def)
  have nthY: "carried_left Y ! i = Y ! i * 2 ^ (length Y - 1 - i)"
    using i by (simp add: nth_carried_left carried_left_coeff_def)
  have nthX: "carried_left X ! i = X ! i * 2 ^ (length X - 1 - i)"
    using i len by (simp add: nth_carried_left carried_left_coeff_def)
  have "(X ! i) * 2 ^ (length Y - 1 - i) \<le> (2 ^ s * Y ! i) * 2 ^ (length Y - 1 - i)"
    by (rule mult_right_mono) (use le[OF i] in simp_all)
  also have "\<dots> = 2 ^ s * (Y ! i * 2 ^ (length Y - 1 - i))" by (simp add: algebra_simps)
  finally show ?thesis using i lenL nthY nthX len by simp
qed

text \<open>\<^bold>\<open>The bridge from the LEMMA's operand to the one the IMPLEMENTATION can build.\<close>
  \<open>gframe_F_nonpos_transfer\<close> is stated about \<open>carried_left (Y + 2\<^sup>g)\<close> --- the node shifted
  BEFORE the scale. The mirror arm, however, is handed \<open>lc = carried_left Y\<close> and never sees
  \<open>Y\<close>. The two coincide index-wise because \<open>carried_left\<close> is a per-index SCALING: the constant
  \<open>2\<^sup>g\<close> at the node becomes the RAMP \<open>2\<^sup>g\<^sup>+\<^sup>n\<^sup>-\<^sup>1\<^sup>-\<^sup>j\<close> after it. So the arm can add the ramp to its
  OWN copy and never needs the node --- which is what keeps the extra cost at one \<open>O(n)\<close> pass
  and one scratch vector the arm already allocates.\<close>
lemma carried_left_shift_const_nth:
  fixes Y :: "int list"
  assumes j: "j < length Y"
  shows "carried_left (map (\<lambda>y. y + 2 ^ g) Y) ! j
       = carried_left Y ! j + 2 ^ (g + (length Y - 1 - j))"
proof -
  have lenm: "length (map (\<lambda>y. y + 2 ^ g) Y) = length Y" by simp
  have A: "carried_left (map (\<lambda>y. y + 2 ^ g) Y) ! j = (Y ! j + 2 ^ g) * 2 ^ (length Y - 1 - j)"
    using j lenm by (simp add: nth_carried_left carried_left_coeff_def)
  have B: "carried_left Y ! j = Y ! j * 2 ^ (length Y - 1 - j)"
    using j by (simp add: nth_carried_left carried_left_coeff_def)
  show ?thesis
    unfolding A B by (simp add: algebra_simps power_add)
qed

lemma gframe_F_nonpos_transfer:
  fixes X Y :: "int list"
  assumes fr: "gframe s g X Y"
    and np: "\<And>j. j < length (carried_left (map (\<lambda>y. y + 2 ^ g) Y))
                  \<Longrightarrow> Ffun (carried_left (map (\<lambda>y. y + 2 ^ g) Y)) ! j \<le> 0"
    and i: "i < length (carried_left X)"
  shows "Ffun (carried_left X) ! i \<le> 0"
proof -
  define Y' where "Y' = map (\<lambda>y. y + 2 ^ g) Y"
  have lenY': "length Y' = length Y" by (simp add: Y'_def)
  have len: "length X = length Y" by (rule gframe_length[OF fr])
  have lenXY': "length X = length Y'" using len lenY' by simp
  have lenL: "length (carried_left Y') = length Y'"
    and lenLX: "length (carried_left X) = length X" by (simp_all add: carried_left_def)
  \<comment> \<open>the frame's UPPER bound, re-associated as \<open>2\<^sup>s * (Y ! j + 2\<^sup>g)\<close>.\<close>
  have le: "X ! j \<le> 2 ^ s * Y' ! j" if "j < length Y'" for j
  proof -
    have jY: "j < length Y" using that lenY' by simp
    have "X ! j - 2 ^ s * Y ! j < 2 ^ (s + g)" using fr jY unfolding gframe_def by auto
    hence "X ! j < 2 ^ s * Y ! j + 2 ^ s * 2 ^ g" by (simp add: power_add)
    also have "\<dots> = 2 ^ s * (Y ! j + 2 ^ g)" by (simp add: algebra_simps)
    finally show ?thesis using jY by (simp add: Y'_def)
  qed
  have step: "carried_left X ! j \<le> map ((*) (2 ^ s)) (carried_left Y') ! j"
    if "j < length Y'" for j
    by (rule carried_left_nth_antimono[OF lenXY' le that])
  have iY: "i < length (carried_left Y')" using i lenL lenLX lenXY' by simp
  have A: "Ffun (carried_left X) ! i \<le> Ffun (map ((*) (2 ^ s)) (carried_left Y')) ! i"
    by (rule F_mono) (use iY lenL lenLX lenXY' step in simp_all)
  have B: "Ffun (map ((*) (2 ^ s)) (carried_left Y')) ! i = 2 ^ s * (Ffun (carried_left Y') ! i)"
    using iY by (simp add: F_smult)
  have "2 ^ s * (Ffun (carried_left Y') ! i) \<le> 0"
    using np[OF iY[unfolded Y'_def]] by (simp add: Y'_def mult_nonneg_nonpos)
  with A B show ?thesis by linarith
qed

lemma gframe_carried_right_count_zero_mirror:
  fixes X Y :: "int list"
  assumes fr: "gframe s g X Y"
    and np: "\<And>j. j < length (carried_left (map (\<lambda>y. y + 2 ^ g) Y))
                  \<Longrightarrow> Ffun (carried_left (map (\<lambda>y. y + 2 ^ g) Y)) ! j \<le> 0"
  shows "carried_descartes_count (carried_right X) = 0"
proof -
  have key: "Ffun (carried_left X) ! i \<le> 0" if "i < length (carried_left X)" for i
    by (rule gframe_F_nonpos_transfer[OF fr np that])
  \<comment> \<open>\<^bold>\<open>Explicit, not \<open>metis\<close>.\<close> A five-lemma \<open>metis\<close> call here does not terminate; the membership unfolds
     deterministically.\<close>
  have "\<forall>x \<in> set (map uminus (Ffun (carried_left X))). 0 \<le> x"
  proof
    fix x assume "x \<in> set (map uminus (Ffun (carried_left X)))"
    then obtain i where i: "i < length (Ffun (carried_left X))"
      and x: "x = - (Ffun (carried_left X) ! i)"
      by (auto simp: in_set_conv_nth)
    have "i < length (carried_left X)" using i by simp
    thus "0 \<le> x" using key x by simp
  qed
  hence "sign_changes_fold (map uminus (Ffun (carried_left X))) = 0"
    by (rule sign_changes_fold_nonneg)
  hence "sign_changes_fold (Ffun (carried_left X)) = 0"
    by (simp add: sign_changes_fold_uminus)
  thus ?thesis by (simp add: carried_descartes_count_def carried_right_def)
qed

text \<open>\<^bold>\<open>The mirror arm at an EXACT node\<close> --- no shift, hence no frame: a non-positive \<open>Ffun\<close>
  has no sign changes. The tail of @{thm [source] gframe_carried_right_count_zero_mirror}, stated
  on its own because at \<open>g = 0\<close> and under the lock the arm runs WITHOUT the ramp.\<close>
lemma F_nonpos_count_zero:
  fixes X :: "int list"
  assumes np: "\<And>j. j < length (carried_left X) \<Longrightarrow> Ffun (carried_left X) ! j \<le> 0"
  shows "carried_descartes_count (carried_right X) = 0"
proof -
  have "\<forall>x \<in> set (map uminus (Ffun (carried_left X))). 0 \<le> x"
  proof
    fix x assume "x \<in> set (map uminus (Ffun (carried_left X)))"
    then obtain i where i: "i < length (Ffun (carried_left X))"
      and x: "x = - (Ffun (carried_left X) ! i)"
      by (auto simp: in_set_conv_nth)
    have "i < length (carried_left X)" using i by simp
    thus "0 \<le> x" using np x by simp
  qed
  hence "sign_changes_fold (map uminus (Ffun (carried_left X))) = 0"
    by (rule sign_changes_fold_nonneg)
  hence "sign_changes_fold (Ffun (carried_left X)) = 0"
    by (simp add: sign_changes_fold_uminus)
  thus ?thesis by (simp add: carried_descartes_count_def carried_right_def)
qed

text \<open>\<^bold>\<open>THE TRANSFER THE CONSUMERS APPLY\<close>: a fired decide on the STORED node \<open>Y\<close> discharges the
  abstract discard for the EXACT node \<open>X\<close>, at EVERY guard. Three cases, and they are exactly the
  three the ramp distinguishes:
  \<^item> \<open>0 < g < 2\<^sup>4\<^sup>2\<close> (truncated): \<open>node_frameE\<close> gives \<open>gframe\<close>; the non-negative arm transfers as it
    stands, the mirror arm through the ramp's \<open>err_shift g Y = Y + 2\<^sup>g\<close>;
  \<^item> \<open>g = 0\<close>: \<open>node_frame\<close> IS \<open>X = Y\<close>;
  \<^item> the lock \<open>2\<^sup>4\<^sup>2 \<le> g\<close>: \<open>X = Y\<close> by \<open>lk\<close> --- which BOTH loops carry
    (\<open>hybrid_trunc_coupling\<close>'s lock clause; \<open>defl_node_ok\<close>'s \<open>4398046511104 \<le> g \<longrightarrow> q = X\<close>).\<close>
lemma right_empty_certified_count_zero:
  fixes X Y :: "int list"
  assumes nf: "node_frame X Y g"
    and lk: "4398046511104 \<le> g \<longrightarrow> X = Y"
    and c: "right_empty_certified g Y"
  shows "carried_descartes_count (carried_right X) = 0"
proof (cases "0 < g \<and> g < 4398046511104")
  case True
  obtain s where fr: "gframe s g X Y" using nf by (rule node_frameE)
  have sh: "err_shift g Y = map (\<lambda>y. y + 2 ^ g) Y" using True by (simp add: err_shift_def)
  show ?thesis
    using c unfolding right_empty_certified_def
  proof (elim disjE)
    assume nn: "\<forall>j < length (carried_left Y). 0 \<le> Ffun (carried_left Y) ! j"
    show ?thesis by (rule gframe_carried_right_count_zero[OF fr]) (use nn in simp_all)
  next
    assume np: "\<forall>j < length (carried_left (err_shift g Y)).
                  Ffun (carried_left (err_shift g Y)) ! j \<le> 0"
    show ?thesis by (rule gframe_carried_right_count_zero_mirror[OF fr]) (use np sh in simp_all)
  qed
next
  case False
  hence gg: "g = 0 \<or> 4398046511104 \<le> g" by auto
  have XY: "X = Y" using gg nf lk by (auto simp: node_frame_def)
  have fr: "gframe 0 0 X Y" using gframe_exact[of X] XY by simp
  \<comment> \<open>\<open>if_not_P\<close>, not \<open>simp\<close>: \<open>simp\<close> first rewrites \<open>False\<close> into \<open>g = 0 \<or> \<not> g < 2\<^sup>4\<^sup>2\<close> and the
     \<open>if\<close> into an implication, and cannot recombine them.\<close>
  have sh: "err_shift g Y = Y" unfolding err_shift_def by (rule if_not_P[OF False])
  show ?thesis
    using c unfolding right_empty_certified_def
  proof (elim disjE)
    assume nn: "\<forall>j < length (carried_left Y). 0 \<le> Ffun (carried_left Y) ! j"
    show ?thesis by (rule gframe_carried_right_count_zero[OF fr]) (use nn in simp_all)
  next
    assume np: "\<forall>j < length (carried_left (err_shift g Y)).
                  Ffun (carried_left (err_shift g Y)) ! j \<le> 0"
    show ?thesis by (rule F_nonpos_count_zero) (use np sh XY in simp_all)
  qed
qed

lemma carried_left_right_skip_right_correct:
  assumes ne: "0 < length xs"
    and cap: "length xs + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the ramp's word bound; NOT a new caller obligation --- both keystones carry
       \<open>gcap_rp : max g 2\<^sup>4\<^sup>2 + length rp < max_snat\<close>.\<close>
    and kb: "g + length xs < max_snat LENGTH(gmp_poly_len)"
  shows "carried_left_right_skip_right_monadic g xs \<le> SPEC (\<lambda>(l, r, rz).
      l = carried_left xs \<and>
      (\<not> rz \<longrightarrow> r = carried_right xs) \<and>
      (rz \<longrightarrow> r = [carried_right xs ! 0] \<and> carried_right xs ! 0 \<noteq> 0 \<and>
              carried_descartes_count (carried_right xs) = 0 \<and> right_empty_certified g xs))"
proof -
  have left_eq: "map (\<lambda>i. xs ! i * 2 ^ (1 * (length xs - 1 - i))) [0..<length xs]
      = carried_left xs"
    by (intro nth_equalityI) (simp_all add: nth_carried_left carried_left_coeff_def)
  \<comment> \<open>\<open>refine_vcg\<close>'s discharge \<open>simp\<close>s the exponent to \<open>length xs - Suc i\<close> in the OUTER
     positions but not under the monad congruences, so the one goal it leaves carries BOTH
     spellings. Both are needed, and they must go in by \<open>unfold\<close>: \<open>simp only\<close> is blocked at
     exactly the inner positions that \<open>simp_all\<close> already failed to reach.\<close>
  have left_eq': "map (\<lambda>i. xs ! i * 2 ^ (length xs - Suc i)) [0..<length xs]
      = carried_left xs"
    by (intro nth_equalityI) (simp_all add: nth_carried_left carried_left_coeff_def)
  have lenL: "length (carried_left xs) = length xs" by (simp add: carried_left_def)
  \<comment> \<open>The three deterministic arm values, each peeled with \<open>bind_le_of_RETURN\<close>. Stating them
     HERE rather than inside the \<open>apply\<close> script is what keeps \<open>refine_vcg\<close> out of the branches
     entirely --- and with it the \<^const>\<open>Sigma\<close> normalisation that stalled every earlier attempt.\<close>
  have crol: "carried_right_of_left_monadic (carried_left xs) \<le> RETURN (carried_right xs)"
    using carried_right_of_left_correct[of "carried_left xs"] cap lenL
    by (simp add: carried_right_def)
  have plain: "carried_right_of_left_monadic (carried_left xs)
      \<bind> (\<lambda>right. RETURN (carried_left xs, right, False))
      \<le> RETURN (carried_left xs, carried_right xs, False)"
    by (rule bind_le_of_RETURN[OF crol])
  have stub: "carried_right_stub_monadic s
      \<bind> (\<lambda>right. RETURN (carried_left xs, right, True))
      \<le> RETURN (carried_left xs, [s], True)" for s
    by (rule bind_le_of_RETURN[OF carried_right_stub_correct])
  have ev: "poly_eval1_pair_monadic (carried_left xs)
      \<le> RETURN (poly_eval1_pair (carried_left xs))"
    using poly_eval1_pair_monadic_correct[of "carried_left xs"] ne cap lenL by simp
  have fst_ev: "fst (poly_eval1_pair (carried_left xs)) = carried_right xs ! 0"
    using carried_right_nth0_eval1[OF ne] by simp
  have decide: "right_empty_decide_monadic g (carried_left xs)
      \<le> SPEC (\<lambda>rz. rz \<longrightarrow> carried_descartes_count (carried_right xs) = 0 \<and> right_empty_certified g xs)"
    using right_empty_decide_monadic_certifies[of xs g] ne cap kb lenL by simp
  show ?thesis
    unfolding carried_left_right_skip_right_monadic_def PR_CONST_def
    \<comment> \<open>\<open>refine_vcg\<close> ALREADY applies \<open>bind_rule\<close> here: it leaves six goals, of which the last IS
       \<open>decide\<close>'s. Adding a \<open>bind_rule\<close> of one's own is what made the earlier attempts fail.
       \<open>left_eq\<close> goes into the discharge so the map-form normalises to \<open>carried_left xs\<close> and
       \<open>decide\<close> matches syntactically.\<close>
    apply (refine_vcg poly_shift_pow_in_place_monadic_correct[THEN order_trans])
    using ne cap dep apply (simp_all add: left_eq)
    apply (unfold left_eq left_eq')
    apply (rule order_trans[OF decide])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>SPEC_rule\<close> has ALREADY split the \<open>if\<close> into the two implications --- a \<open>split if_split\<close>
       here fails, because there is no \<open>if\<close> left at the head of the conclusion.\<close>
    apply (intro conjI impI)
    subgoal
      \<comment> \<open>The fired arm. \<open>ev\<close> peels the evaluation, the two \<open>mpzb_discard\<close>s and \<open>mpz_sgn_mop\<close> are
         all \<open>RETURN\<close>s and collapse under \<open>nres_monad1\<close>, and \<open>prod.split\<close> leaves ONE \<open>\<forall>\<close>-goal
         carrying the sign test. The count obligation is already discharged from \<open>decide\<close>.\<close>
      apply (rule order_trans[OF bind_le_of_RETURN[OF ev]])
      apply (simp add: mpzb_discard_monadic_def mpz_sgn_mop_def split: prod.split)
      apply (intro allI conjI impI; elim exE)
      \<comment> \<open>\<open>sgn = 0\<close>: the midpoint may be a root, so fall back to the exact right child.\<close>
       apply (rule order_trans[OF plain], simp)
      \<comment> \<open>\<open>sgn \<noteq> 0\<close>: the interlock. \<open>fst_ev\<close> identifies the evaluated value with \<open>qr!0\<close>, which is
         what both readers of the skipped child in the two-child path read.\<close>
      apply (rule order_trans[OF stub])
      using fst_ev apply (auto simp: sgn_0_0)
      done
    apply (rule order_trans[OF plain])
    apply simp
    done
qed

text \<open>\<^bold>\<open>The form the CALL SITES actually consume.\<close> Neither site cares which branch ran; both
  read \<open>qr!0\<close>'s sign and bitlen and then drive \<open>truncate_mid_decide_monadic\<close>. This states the
  one fact that makes that read branch-independent --- \<open>r ! 0 = carried_right Q ! 0\<close> on BOTH
  paths --- so a caller never has to case-split to know its guard cascade is unchanged. It is
  the contract weakened, not new mathematics.\<close>
lemma carried_left_right_skip_right_nth0:
  assumes ne: "0 < length xs"
    and cap: "length xs + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length xs < max_snat LENGTH(gmp_poly_len)"
  shows "carried_left_right_skip_right_monadic g xs \<le> SPEC (\<lambda>(l, r, rz).
      l = carried_left xs \<and> 0 < length r \<and> r ! 0 = carried_right xs ! 0 \<and>
      (\<not> rz \<longrightarrow> r = carried_right xs) \<and>
      (rz \<longrightarrow> carried_right xs ! 0 \<noteq> 0 \<and>
              carried_descartes_count (carried_right xs) = 0 \<and> right_empty_certified g xs))"
proof -
  have lenR: "length (carried_right xs) = length xs"
    by (simp add: carried_right_def)
  show ?thesis
    apply (rule order_trans[OF carried_left_right_skip_right_correct[OF ne cap dep kb]])
    apply (rule SPEC_rule)
    using ne lenR by auto
qed

sepref_definition carried_left_right_skip_right_impl [llvm_code] is
  "uncurry carried_left_right_skip_right_monadic" ::
  "[\<lambda>(g, xs). 0 < length xs \<and> length xs + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length xs - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a bool1_assn"
  unfolding carried_left_right_skip_right_monadic_def
  \<comment> \<open>\<^bold>\<open>Both annotations are needed.\<close> \<open>sg\<close> is an mpz-typed \<^typ>\<open>int\<close> (\<open>mpz_sgn_mop\<close> returns
     \<open>sint_assn\<close>), so the \<open>0\<close> in \<open>sg = 0\<close> is an INT literal, and without \<open>annot_sint_const\<close>
     \<open>sepref_dbg_id_keep\<close> stops with an unidentified \<open>ID 0 ?x TYPE(int)\<close> --- which surfaces at
     the top only as \<open>Failed to apply initial proof method\<close>.\<close>
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const "TYPE(gmp_int_len)")?
  by sepref

lemma carried_left_right_skip_right_impl_hnr[sepref_fr_rules]:
  "(uncurry carried_left_right_skip_right_impl, uncurry (PR_CONST carried_left_right_skip_right_monadic)) \<in>
    [\<lambda>(g, xs). 0 < length xs \<and> length xs + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length xs - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a bool1_assn"
  using carried_left_right_skip_right_impl.refine
  by (simp add: PR_CONST_def)


subsection \<open>Threading a pure value past the deflation\<close>

text \<open>\<^bold>\<open>A minimal reproducer, kept because it decides the site-B design.\<close> Site B's blocker is
  that \<open>rz\<close> must reach the return alongside children that @{const defl_children_monadic} has
  consumed and rebound. The tell is that \<open>fired\<close> crosses the same point WITHOUT trouble --- and
  \<open>fired\<close> comes OUT of the consuming op. This op is that observation at minimum size: thread a
  pure \<^typ>\<open>bool\<close> through the shed and return it beside \<open>fired\<close>. If it synthesises, site B is
  rebuildable around it; if not, no placement of \<open>rz\<close> can work and the decide has to move up to
  \<open>defl_branch_split_monadic\<close>, where it only ever drives an \<open>if\<close>.\<close>
definition defl_children_rz_monadic ::
  "bool \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
    (gmp_poly \<times> gmp_poly \<times> bool \<times> bool) nres" where
"defl_children_rz_monadic rz c ql qr \<equiv> doN {
  (ql, qr, fired) \<leftarrow> (PR_CONST defl_children_monadic) c ql qr;
  RETURN (ql, qr, fired, rz)
}"

sepref_register "PR_CONST defl_children_rz_monadic"
  :: "bool \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
      (gmp_poly \<times> gmp_poly \<times> bool \<times> bool) nres"

sepref_definition defl_children_rz_impl [llvm_code] is
  "uncurry3 defl_children_rz_monadic" ::
  "[\<lambda>(((rz, c), ql), qr).
      0 < length ql \<and> length ql + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length qr \<and> length qr + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn"
  unfolding defl_children_rz_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma defl_children_rz_impl_hnr[sepref_fr_rules]:
  "(uncurry3 defl_children_rz_impl, uncurry3 (PR_CONST defl_children_rz_monadic)) \<in>
    [\<lambda>(((rz, c), ql), qr).
      0 < length ql \<and> length ql + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length qr \<and> length qr + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn"
  using defl_children_rz_impl.refine
  by (simp add: PR_CONST_def)


text \<open>\<^bold>\<open>The deflating children build, as its own op so that its frame is solved locally.\<close>
  \<^item> \<open>rz\<close> comes out of @{const defl_children_rz_monadic}, so after the deflation it is an ordinary result crossing only
    the two @{const carried_retrunc_mop} calls, the pattern \<open>truncate_children_mid_skip_right_monadic\<close> (below) uses. A
    value that merely passes unchanged through the consuming op does not synthesise.
  \<^item> The caller ends in a bare call to this op and rebuilds no tuple, avoiding the shape of a pass-through op that
    returns its bundled input.\<close>
definition defl_split_children_tail_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
    (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> bool \<times> bool) nres" where
"defl_split_children_tail_monadic g len lockok gl0 gr0 rz ql qr \<equiv> doN {
   ASSERT (0 < length qr);
   mids \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) qr 0;
   midbl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) qr 0;
   code \<leftarrow> (PR_CONST truncate_mid_decide_monadic) g len mids midbl;
   ASSERT (0 < length ql);
   ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
   ASSERT (length qr + 1 < max_snat LENGTH(gmp_poly_len));
   \<comment> \<open>\<^bold>\<open>Why the singleton stub is safe here.\<close> On the fast path \<open>qr\<close> is \<open>[carried_right Q ! 0]\<close>, and deflating
      that would shed a factor from a child that was never built. It cannot happen: the interlock in
      @{thm carried_left_right_skip_right_correct} gives \<open>rz \<longrightarrow> carried_right Q ! 0 \<noteq> 0\<close>, hence \<open>mids \<noteq> 0\<close>, and
      @{const truncate_mid_decide_monadic} returns \<open>1\<close> only when \<open>mids = 0\<close>, on the \<open>g = 0\<close> / locked branches this op runs
      under. So \<open>rz \<longrightarrow> code \<noteq> 1\<close>, and the deflation never receives a stub. The capstone discharges that implication.\<close>
   (ql, qr, fired, rz) \<leftarrow> (PR_CONST defl_children_rz_monadic) rz (code = 1) ql qr;
   ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
   (ql, gl) \<leftarrow> (PR_CONST carried_retrunc_mop) ql
                  (if fired \<and> lockok then 4398046511104 else gl0);
   ASSERT (length qr + 1 < max_snat LENGTH(gmp_poly_len));
   (qr, gr) \<leftarrow> (PR_CONST carried_retrunc_mop) qr
                  (if fired \<and> lockok then 4398046511104 else gr0);
   RETURN (ql, gl, qr, gr, fired, rz)
 }"

sepref_register "PR_CONST defl_split_children_tail_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
      (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> bool \<times> bool) nres"

abbreviation split_children_skip_right_assn where
"split_children_skip_right_assn \<equiv>
  gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
  gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
  bool1_assn \<times>\<^sub>a bool1_assn"

sepref_definition defl_split_children_tail_impl [llvm_code] is
  "uncurry7 defl_split_children_tail_monadic" ::
  "[\<lambda>(((((((g, len), lockok), gl0), gr0), rz), ql), qr).
      0 < length ql \<and> length ql + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length qr \<and> length qr + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      split_children_skip_right_assn"
  unfolding defl_split_children_tail_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma defl_split_children_tail_impl_hnr[sepref_fr_rules]:
  "(uncurry7 defl_split_children_tail_impl,
    uncurry7 (PR_CONST defl_split_children_tail_monadic)) \<in>
    [\<lambda>(((((((g, len), lockok), gl0), gr0), rz), ql), qr).
      0 < length ql \<and> length ql + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length qr \<and> length qr + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      split_children_skip_right_assn"
  using defl_split_children_tail_impl.refine
  by (simp add: PR_CONST_def)


subsection \<open>The \<open>trunc_mid\<close> children build with the right-child decide\<close>

text \<open>\<^bold>\<open>The \<open>trunc_mid\<close> children build, with the right-child decide.\<close> It is defined here because
  @{const carried_left_right_skip_right_monadic} is defined in this theory, which comes after \<open>Truncate\<close>. The original
  op is unchanged and remains used by \<open>defl_split_children_lockonly_monadic\<close>.

  \<^bold>\<open>Both \<open>qr!0\<close> reads are unchanged.\<close> On \<open>rz\<close> the right child is \<open>[carried_right Q ! 0]\<close>, so \<open>poly_coeff_sgn\<close> and
  \<open>poly_coeff_bitlen2\<close> at index \<open>0\<close> return what they would return on the fully built child, which keeps
  \<open>truncate_mid_decide_monadic\<close>'s guard cascade and the deflation interlock sound.

  The precondition is \<open>length Q + 2\<close>, one more than the original op's \<open>+1\<close>
  (@{thm carried_left_right_skip_right_correct} needs it, via \<open>poly_eval1_pair\<close>), and the caller branches on the extra
  \<open>rz\<close> component: on \<open>rz\<close> it frees \<open>qr\<close> and pushes only the left child.\<close>
definition truncate_children_mid_skip_right_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow>
    (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> int \<times> nat \<times> bool) nres" where
"truncate_children_mid_skip_right_monadic g Q \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) Q;
  ASSERT (len = length Q);
  ASSERT (0 < len);
  ASSERT (len + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (1 * (len - 1) < max_snat LENGTH(gmp_poly_len));
  (gl0, gr0) \<leftarrow> (PR_CONST truncate_child_guards_mop) g len;
  (ql, qr, rz) \<leftarrow> (PR_CONST carried_left_right_skip_right_monadic) g Q;
  ASSERT (0 < length qr);
  mids \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) qr 0;
  midbl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) qr 0;
  ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
  (ql, gl) \<leftarrow> (PR_CONST carried_retrunc_mop) ql gl0;
  ASSERT (length qr + 1 < max_snat LENGTH(gmp_poly_len));
  (qr, gr) \<leftarrow> (PR_CONST carried_retrunc_mop) qr gr0;
  RETURN (ql, gl, qr, gr, mids, midbl, rz)
}"

sepref_register "PR_CONST truncate_children_mid_skip_right_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow>
      (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> int \<times> nat \<times> bool) nres"

abbreviation children_mid_skip_right_assn where
"children_mid_skip_right_assn \<equiv>
  gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
  gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
  gmp_sint_assn \<times>\<^sub>a gmp_size_assn \<times>\<^sub>a bool1_assn"

sepref_definition truncate_children_mid_skip_right_impl [llvm_code] is
  "uncurry truncate_children_mid_skip_right_monadic" ::
  "[\<lambda>(g, Q). 0 < length Q \<and> length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      children_mid_skip_right_assn"
  unfolding truncate_children_mid_skip_right_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma truncate_children_mid_skip_right_impl_hnr[sepref_fr_rules]:
  "(uncurry truncate_children_mid_skip_right_impl,
    uncurry (PR_CONST truncate_children_mid_skip_right_monadic)) \<in>
    [\<lambda>(g, Q). 0 < length Q \<and> length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      children_mid_skip_right_assn"
  using truncate_children_mid_skip_right_impl.refine
  by (simp add: PR_CONST_def)


definition defl_lock_guard_mop :: "nat \<Rightarrow> nat \<Rightarrow> bool nres" where
"defl_lock_guard_mop len0 len \<equiv> doN {
   thr \<leftarrow> RETURN (len0 div 8);
   if len < len0 then doN {
     ASSERT (len \<le> len0);
     shed \<leftarrow> RETURN (len0 - len);
     RETURN (thr \<le> shed)
   } else RETURN False
 }"

sepref_register "PR_CONST defl_lock_guard_mop" :: "nat \<Rightarrow> nat \<Rightarrow> bool nres"

sepref_definition defl_lock_guard_impl [llvm_inline] is
  "uncurry defl_lock_guard_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k
    \<rightarrow>\<^sub>a bool1_assn"
  unfolding defl_lock_guard_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma defl_lock_guard_impl_hnr[sepref_fr_rules]:
  "(uncurry defl_lock_guard_impl, uncurry (PR_CONST defl_lock_guard_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k
      \<rightarrow>\<^sub>a bool1_assn"
  using defl_lock_guard_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The deflating child build.\<close> One \<open>O(n)\<close> pass decides the midpoint root AND produces
  the deflated polynomial, so the children are built at degree \<open>n-1\<close> instead of \<open>n\<close>. That
  ordering is the whole point: the classic test reads \<open>qr!0\<close> off an ALREADY-BUILT child, so it
  cannot learn the midpoint is a root until it has paid the \<open>O(n\<^sup>2)\<close> build at the
  undeflated degree.\<close>

definition defl_split_children_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow>
    (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> bool \<times> bool) nres" where
"defl_split_children_monadic g len lockok Q \<equiv> doN {
   ASSERT (0 < length Q);
   ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
   \<comment> \<open>the extra headroom conjunct; see \<open>hybrid_split_children_classic_monadic\<close> below.\<close>
   ASSERT (length Q + 2 < max_snat LENGTH(gmp_poly_len));
   ASSERT (1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len));
   \<comment> \<open>\<^bold>\<open>This op is @{const truncate_children_mid_monadic} with the deflation placed after the children are built
      and their \<open>qr!0\<close> read is taken, and before @{const carried_retrunc_mop}\<close>; the constituents are that op's, in its
      order.

      \<^bold>\<open>Before the re-truncation\<close>, because a truncated operand's certificate proves nothing: \<open>carried_retrunc_mop\<close>
      may truncate a child even when the parent is exact, so deflating afterwards could divide by a factor the child
      does not carry.

      \<^bold>\<open>After the build\<close>, because the read \<open>carried_right Q ! 0\<close> is \<open>defl_half_cert Q\<close>
      (\<open>Deflation_Bridge.carried_right_nth0_eq_defl_one_cert\<close>), so no separate certificate pass is needed and a node
      that does not shed pays nothing.\<close>
   (gl0, gr0) \<leftarrow> (PR_CONST truncate_child_guards_mop) g len;
   \<comment> \<open>\<^bold>\<open>The right-child decide in the deflating build\<close>, the other site where the children are built.\<close>
   (ql, qr, rz) \<leftarrow> (PR_CONST carried_left_right_skip_right_monadic) g Q;
   ASSERT (0 < length ql);
   ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
   ASSERT (0 < length qr);
   ASSERT (length qr + 1 < max_snat LENGTH(gmp_poly_len));
   \<comment> \<open>A bare tail call: this op rebuilds no tuple.\<close>
   (PR_CONST defl_split_children_tail_monadic) g len lockok gl0 gr0 rz ql qr
 }"

text \<open>\<^bold>\<open>The lock-only variant.\<close> The deflating op above changes two things at once: it sheds a degree, and it
  takes the exact lock on the subtree. This op takes the lock and does not deflate (same decision, same guard, original
  polynomial), so the two effects can be separated.\<close>

definition defl_split_children_lockonly_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> bool) nres" where
"defl_split_children_lockonly_monadic g Q \<equiv> doN {
   ASSERT (0 < length Q);
   ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
   ASSERT (slong_bounds (int 0));
   c \<leftarrow> (PR_CONST defl_cert_monadic) Q;
   z \<leftarrow> (PR_CONST snat_to_slong_monadic) 0;
   sg \<leftarrow> (PR_CONST mpz_cmp_si_sgn_monadic) c z;
   (PR_CONST mpzb_discard_monadic) c;
   (ql, gl, qr, gr, mids, midbl) \<leftarrow>
     (PR_CONST truncate_children_mid_monadic) (if sg = 0 then 4398046511104 else g) Q;
   RETURN (ql, gl, qr, gr, sg = 0)
 }"

sepref_register "PR_CONST defl_split_children_lockonly_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> bool) nres"

sepref_definition defl_split_children_lockonly_impl [llvm_code] is
  "uncurry defl_split_children_lockonly_monadic" ::
  "[\<lambda>(g, Q). 0 < length Q \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      split_children_assn"
  unfolding defl_split_children_lockonly_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const "TYPE(gmp_int_len)")?
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

lemma defl_split_children_lockonly_impl_hnr[sepref_fr_rules]:
  "(uncurry defl_split_children_lockonly_impl,
    uncurry (PR_CONST defl_split_children_lockonly_monadic)) \<in>
    [\<lambda>(g, Q). 0 < length Q \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
        split_children_assn"
  using defl_split_children_lockonly_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_split_children_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow>
      (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> bool \<times> bool) nres"

sepref_definition defl_split_children_impl [llvm_code] is
  "uncurry3 defl_split_children_monadic" ::
  "[\<lambda>(((g, len), lockok), Q). 0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      split_children_skip_right_assn"
  unfolding defl_split_children_monadic_def
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

lemma defl_split_children_impl_hnr[sepref_fr_rules]:
  "(uncurry3 defl_split_children_impl, uncurry3 (PR_CONST defl_split_children_monadic)) \<in>
    [\<lambda>(((g, len), lockok), Q). 0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
        split_children_skip_right_assn"
  using defl_split_children_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The classic (non-deflating) child build\<close>, lifted out
  of the branch so that the branch has exactly ONE tail. Includes the \<open>code = 2\<close> escalate arm;
  the node it rebuilds is EXACT, so that arm deflates too (via the op above) whenever the
  rebuilt length allows.\<close>

definition hybrid_split_children_classic_monadic ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> bool \<times> bool) nres" where
"hybrid_split_children_classic_monadic l_num r_num k rp g len Q \<equiv> doN {
   ASSERT (0 < length Q);
   ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
   \<comment> \<open>\<^bold>\<open>The extra headroom obligation.\<close> The right-child decide evaluates the left child at \<open>1\<close>, and
      \<open>poly_eval1_pair_monadic\<close> needs \<open>+2\<close> where the other ops here need \<open>+1\<close>. It is a second conjunct beside the first,
      as \<open>newton_side1_impl\<close> states the same pair, and it holds whenever the first does under the length bound of the
      caller contract (\<open>len \<le> 69 859 052\<close>).\<close>
   ASSERT (length Q + 2 < max_snat LENGTH(gmp_poly_len));
   ASSERT (1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len));
   ASSERT (0 < length rp);
   ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
   ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
   \<comment> \<open>\<^bold>\<open>The escalating arm's lock is gated on the escalating node's shed\<close>, \<open>len0 - len\<close>, from parameters this op
      already has, with threshold \<open>0\<close> (any shed at all). The operand is this node's shed, not the rebuilt length:
      \<open>carried_init_inplace_monadic\<close> restores the undeflated degree, so \<open>qx\<close>'s own shed is \<open>0\<close> by construction. An
      escalation is never the root's first action, so the gate can fire here.\<close>
   (ql, gl, qr, gr, mids, midbl, rz) \<leftarrow> (PR_CONST truncate_children_mid_skip_right_monadic) g Q;
   code \<leftarrow> (PR_CONST truncate_mid_decide_monadic) g len mids midbl;
   if code = 2 then doN {
     \<comment> \<open>AMBIGUOUS: discard the truncated children and rebuild exact from the loop-carried
        root, exactly as the classic build does. The rebuilt node carries guard \<open>0\<close>, i.e. it
        is EXACT — which is precisely the condition under which the deflation is licensed.
        \<^bold>\<open>The first \<open>rz\<close> dies here\<close>: both children are freed, so whatever the decide said
        about the DISCARDED right child is irrelevant, and the rebuilt node runs its own
        decide. Reporting \<open>rz\<close> from before the rebuild would skip a push that is now owed.\<close>
     (PR_CONST poly_free_monadic) ql;
     (PR_CONST poly_free_monadic) qr;
     qx \<leftarrow> (PR_CONST carried_init_inplace_monadic) l_num k r_num rp;
     ASSERT (0 < length qx);
     ASSERT (length qx + 1 < max_snat LENGTH(gmp_poly_len));
     ASSERT (length qx + 2 < max_snat LENGTH(gmp_poly_len));
     ASSERT (1 * (length qx - 1) < max_snat LENGTH(gmp_poly_len));
     len2 \<leftarrow> (PR_CONST poly_length_monadic) qx;
     \<comment> \<open>\<open>False\<close>, not a computed guard: \<open>qx\<close> was just rebuilt from \<open>rp\<close>, so its shed is zero by construction, and an
        unconditional lock on this arm would give up truncation for the whole subtree.\<close>
     (ql, gl, qr, gr, mids2, midbl2, rz2) \<leftarrow> (PR_CONST truncate_children_mid_skip_right_monadic) 0 qx;
     code2 \<leftarrow> (PR_CONST truncate_mid_decide_monadic) 0 len2 mids2 midbl2;
     RETURN (ql, gl, qr, gr, code2 = 1, rz2)
   } else RETURN (ql, gl, qr, gr, code = 1, rz)
 }"

sepref_register "PR_CONST hybrid_split_children_classic_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
      (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> bool \<times> bool) nres"

sepref_definition hybrid_split_children_classic_impl [llvm_code] is
  "uncurry6 hybrid_split_children_classic_monadic" ::
  "[\<lambda>((((((_, _), k), rp), _), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      split_children_skip_right_assn"
  unfolding hybrid_split_children_classic_monadic_def
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

lemma hybrid_split_children_classic_impl_hnr[sepref_fr_rules]:
  "(uncurry6 hybrid_split_children_classic_impl,
    uncurry6 (PR_CONST hybrid_split_children_classic_monadic)) \<in>
    [\<lambda>((((((_, _), k), rp), _), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      split_children_skip_right_assn"
  using hybrid_split_children_classic_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The split branch, now with ONE tail.\<close> The two child-build ops above return the same
  shape \<open>(ql, gl, qr, gr, mid)\<close>, so the midpoint push and the pair-state append are written
  once instead of three times — which is also why the deflating arm costs no extra branches in
  the synthesised code.\<close>

definition hybrid_branch_split_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres" where
"hybrid_branch_split_monadic todo qtodo es ss cs gs rp acc l_num r_num k e s g Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>the extra headroom conjunct, passed on from @{const hybrid_split_children_classic_monadic}.\<close>
  ASSERT (length Q + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length rp);
  ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
  len \<leftarrow> (PR_CONST poly_length_monadic) Q;
  \<comment> \<open>The non-deflating child build. The deflating variant of this op is \<open>defl_branch_split_monadic\<close> below.\<close>
  (ql, gl, qr, gr, mid, rz) \<leftarrow>
    (PR_CONST hybrid_split_children_classic_monadic) l_num r_num k rp g len Q;
  \<comment> \<open>\<^bold>\<open>The right-empty branch.\<close> On \<open>rz\<close> the decide has proved \<open>carried_descartes_count (carried_right Q) = 0\<close>
     (@{thm carried_left_right_skip_right_correct}), so that child contributes no window and is not pushed. \<open>qr\<close> here is
     the singleton stub, already consumed by the two \<open>qr!0\<close> reads, so it is freed. The worklist is LIFO, so the skipped
     box is exactly the one the program would have popped next and discarded at \<open>cnt = 0\<close>; that is why the abstract step
     composes as (two-child push) \<circ> (\<open>v = 0\<close> discard).\<close>
  if rz then doN {
    (PR_CONST poly_free_monadic) qr;
    if mid then doN {
      ASSERT (dyadic_interval_vec_pushable acc);
      acc \<leftarrow> (PR_CONST carried_push_mid_monadic) acc l_num r_num k;
      wl' \<leftarrow> (PR_CONST hybrid_split_pair_state_left_monadic)
        todo qtodo es ss cs gs rp l_num r_num k e s True ql gl;
      RETURN (wl', acc)
    } else doN {
      wl' \<leftarrow> (PR_CONST hybrid_split_pair_state_left_monadic)
        todo qtodo es ss cs gs rp l_num r_num k e s False ql gl;
      RETURN (wl', acc)
    }
  } else if mid then doN {
    ASSERT (dyadic_interval_vec_pushable acc);
    acc \<leftarrow> (PR_CONST carried_push_mid_monadic) acc l_num r_num k;
    wl' \<leftarrow> (PR_CONST hybrid_split_pair_state_monadic)
      todo qtodo es ss cs gs rp l_num r_num k e s True ql gl qr gr;
    RETURN (wl', acc)
  } else doN {
    wl' \<leftarrow> (PR_CONST hybrid_split_pair_state_monadic)
      todo qtodo es ss cs gs rp l_num r_num k e s False ql gl qr gr;
    RETURN (wl', acc)
  }
}"

sepref_register "PR_CONST hybrid_branch_split_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres"

sepref_definition hybrid_branch_split_impl [llvm_code] is
  "uncurry14 hybrid_branch_split_monadic" ::
  "[\<lambda>((((((((((((((todo, qtodo), es), ss), cs), gs), rp), acc), _), _), k), _), s), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      s + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  unfolding hybrid_branch_split_monadic_def
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

lemma hybrid_branch_split_impl_hnr[sepref_fr_rules]:
  "(uncurry14 hybrid_branch_split_impl,
    uncurry14 (PR_CONST hybrid_branch_split_monadic)) \<in>
    [\<lambda>((((((((((((((todo, qtodo), es), ss), cs), gs), rp), acc), _), _), k), _), s), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      s + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  using hybrid_branch_split_impl.refine by (simp add: PR_CONST_def)


section \<open>The deflating twins\<close>

text \<open>\<^bold>\<open>Why these are twins and not a flag.\<close> The non-deflating stack carries a multiset equality against
  \<open>dsc_int\<close>, and deflation cannot preserve it (the children's \<open>Bernstein_changes\<close> differ at a shared endpoint root, so the
  emitted intervals move). A \<open>deflate?\<close> flag threaded through the existing stack would enter every statement of
  \<open>Hybrid_Keystone\<close>. Duplicating the two ops that differ leaves the non-deflating stack unchanged and confines the new
  proof obligations to the new stack.\<close>

definition defl_split_children_escalate_monadic ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> bool \<times> bool) nres" where
"defl_split_children_escalate_monadic l_num r_num k rp g len Q \<equiv> doN {
   ASSERT (0 < length Q);
   ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
   \<comment> \<open>the extra headroom conjunct; see \<open>hybrid_split_children_classic_monadic\<close> below.\<close>
   ASSERT (length Q + 2 < max_snat LENGTH(gmp_poly_len));
   ASSERT (1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len));
   ASSERT (0 < length rp);
   ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
   ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
   \<comment> \<open>\<^bold>\<open>The escalating arm's lock is gated on the escalating node's shed\<close>, \<open>len0 - len\<close>, from parameters this op
      already has, with threshold \<open>0\<close> (any shed at all). The operand is this node's shed, not the rebuilt length:
      \<open>carried_init_inplace_monadic\<close> restores the undeflated degree, so \<open>qx\<close>'s own shed is \<open>0\<close> by construction. An
      escalation is never the root's first action, so the gate can fire here.\<close>
   len0 \<leftarrow> (PR_CONST poly_length_monadic) rp;
   (ql, gl, qr, gr, mids, midbl, rz) \<leftarrow> (PR_CONST truncate_children_mid_skip_right_monadic) g Q;
   code \<leftarrow> (PR_CONST truncate_mid_decide_monadic) g len mids midbl;
   if code = 2 then doN {
     \<comment> \<open>AMBIGUOUS: discard the truncated children and rebuild exact from the loop-carried
        root, exactly as the classic build does. The rebuilt node carries guard \<open>0\<close>, i.e. it
        is EXACT — which is precisely the condition under which the deflation is licensed.\<close>
     (PR_CONST poly_free_monadic) ql;
     (PR_CONST poly_free_monadic) qr;
     qx \<leftarrow> (PR_CONST carried_init_inplace_monadic) l_num k r_num rp;
     ASSERT (0 < length qx);
     ASSERT (length qx + 1 < max_snat LENGTH(gmp_poly_len));
     ASSERT (length qx + 2 < max_snat LENGTH(gmp_poly_len));
     ASSERT (1 * (length qx - 1) < max_snat LENGTH(gmp_poly_len));
     len2 \<leftarrow> (PR_CONST poly_length_monadic) qx;
     \<comment> \<open>\<open>False\<close>, not a computed guard: \<open>qx\<close> was just rebuilt from \<open>rp\<close>, so its shed is zero by construction, and an
        unconditional lock on this arm would give up truncation for the whole subtree.\<close>
     if 3 \<le> len2 then (PR_CONST defl_split_children_monadic) 0 len2 (len < len0) qx
     else doN {
       (ql, gl, qr, gr, mids2, midbl2, rz2) \<leftarrow>
         (PR_CONST truncate_children_mid_skip_right_monadic) 0 qx;
       code2 \<leftarrow> (PR_CONST truncate_mid_decide_monadic) 0 len2 mids2 midbl2;
       RETURN (ql, gl, qr, gr, code2 = 1, rz2)
     }
   } else RETURN (ql, gl, qr, gr, code = 1, rz)
 }"

sepref_register "PR_CONST defl_split_children_escalate_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
      (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> bool \<times> bool) nres"

sepref_definition defl_split_children_escalate_impl [llvm_code] is
  "uncurry6 defl_split_children_escalate_monadic" ::
  "[\<lambda>((((((_, _), k), rp), _), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      split_children_skip_right_assn"
  unfolding defl_split_children_escalate_monadic_def
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

lemma defl_split_children_escalate_impl_hnr[sepref_fr_rules]:
  "(uncurry6 defl_split_children_escalate_impl,
    uncurry6 (PR_CONST defl_split_children_escalate_monadic)) \<in>
    [\<lambda>((((((_, _), k), rp), _), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      split_children_skip_right_assn"
  using defl_split_children_escalate_impl.refine by (simp add: PR_CONST_def)

definition defl_branch_split_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
    nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres" where
"defl_branch_split_monadic todo qtodo es ss cs gs rp acc l_num r_num k e s g Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length rp);
  ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
  len \<leftarrow> (PR_CONST poly_length_monadic) Q;
  \<comment> \<open>\<open>g = 0\<close> or \<open>g \<ge> 2\<^sup>4\<^sup>2\<close> is EXACTLY the condition under which
     @{const truncate_mid_decide_monadic} is willing to say \<open>the midpoint IS a root\<close> — the
     exact and EXACT-LOCKed cases. Gating the deflation on it inherits that guard, so
     the certificate is never read off a truncated operand. \<open>3 \<le> len\<close> is policy: below it the
     quotient is a constant.\<close>
  \<comment> \<open>\<^bold>\<open>The main branch locks unconditionally when the deflation fires.\<close> Gating this lock on
     @{const defl_lock_guard_mop} would never lock the root (its shed is \<open>0\<close>), and an unlocked root is truncated by
     \<open>carried_retrunc_mop\<close> and does not re-enter the deflating build, so the whole subtree's deflation would be lost. The
     shed gate belongs on the escalating arm (see @{const hybrid_split_children_classic_monadic}).\<close>
  (ql, gl, qr, gr, mid, rz) \<leftarrow>
    (if (g = 0 \<or> 4398046511104 \<le> g) \<and> 3 \<le> len
     then (PR_CONST defl_split_children_monadic) g len True Q
     else (PR_CONST defl_split_children_escalate_monadic) l_num r_num k rp g len Q);
  \<comment> \<open>\<^bold>\<open>The right-empty branch on the deflating stack\<close>, of the same shape as the non-deflating one. The deflation
     has already run and, on \<open>rz\<close>, provably did not fire (the interlock; see \<open>defl_split_children_tail_monadic\<close>), so \<open>ql\<close>
     has its undeflated degree and the skipped child is the empty one.\<close>
  if rz then doN {
    (PR_CONST poly_free_monadic) qr;
    if mid then doN {
      ASSERT (dyadic_interval_vec_pushable acc);
      acc \<leftarrow> (PR_CONST carried_push_mid_monadic) acc l_num r_num k;
      wl' \<leftarrow> (PR_CONST hybrid_split_pair_state_left_monadic)
        todo qtodo es ss cs gs rp l_num r_num k e s True ql gl;
      RETURN (wl', acc)
    } else doN {
      wl' \<leftarrow> (PR_CONST hybrid_split_pair_state_left_monadic)
        todo qtodo es ss cs gs rp l_num r_num k e s False ql gl;
      RETURN (wl', acc)
    }
  } else if mid then doN {
    ASSERT (dyadic_interval_vec_pushable acc);
    acc \<leftarrow> (PR_CONST carried_push_mid_monadic) acc l_num r_num k;
    wl' \<leftarrow> (PR_CONST hybrid_split_pair_state_monadic)
      todo qtodo es ss cs gs rp l_num r_num k e s True ql gl qr gr;
    RETURN (wl', acc)
  } else doN {
    wl' \<leftarrow> (PR_CONST hybrid_split_pair_state_monadic)
      todo qtodo es ss cs gs rp l_num r_num k e s False ql gl qr gr;
    RETURN (wl', acc)
  }
}"

sepref_register "PR_CONST defl_branch_split_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow>
      nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> gmp_poly \<Rightarrow> hybrid_state nres"

sepref_definition defl_branch_split_impl [llvm_code] is
  "uncurry14 defl_branch_split_monadic" ::
  "[\<lambda>((((((((((((((todo, qtodo), es), ss), cs), gs), rp), acc), _), _), k), _), s), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      s + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  unfolding defl_branch_split_monadic_def
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

lemma defl_branch_split_impl_hnr[sepref_fr_rules]:
  "(uncurry14 defl_branch_split_impl,
    uncurry14 (PR_CONST defl_branch_split_monadic)) \<in>
    [\<lambda>((((((((((((((todo, qtodo), es), ss), cs), gs), rp), acc), _), _), k), _), s), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 2 < max_snat LENGTH(gmp_poly_len) \<and>
      1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      s + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      hybrid_state_assn"
  using defl_branch_split_impl.refine by (simp add: PR_CONST_def)


end
