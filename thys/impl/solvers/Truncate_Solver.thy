theory Truncate_Solver
  imports Bisection_Solver Truncate Bisection
begin

text \<open>The truncating carried loop: a sibling of the bisection loop (\<open>Bisection\<close>) that
  (a) carries a per-node guard column \<open>gs\<close> (the node's accumulated one-sided slack exponent \<open>g\<close>;
  \<open>g = 0\<close> means exact), (b) carries the borrowed root \<open>rp\<close> in the loop state for exact-rebuild
  escalation, (c) at pop counts the (possibly truncated) node with the \<open>g\<close>-guarded count and escalates
  on ambiguity (rebuilding the exact node from \<open>rp\<close>), and (d) at each bisection child re-truncates in
  place, so the carried operands stay near \<open>2\<cdot>len\<close> bits.

  Escalation from the root held in the loop state (owned by the body) uses the \<open>_keep\<close> variant; the
  plain \<open>^k\<close> escalation @{const carried_escalate_exact_monadic} is for a caller-borrowed root.\<close>

section \<open>The dense loop state (guard column + carried root)\<close>

text \<open>The worklist gains \<open>gs :: nat list\<close> (one guard per carried node, in lockstep with
  \<open>qtodo\<close>); the outer state gains the borrowed root \<open>rp\<close> (a kept copy of the input
  polynomial, freed once at loop exit).\<close>
text \<open>\<open>truncate_todo3\<close> is the PLAIN \<open>(todo,qtodo,gs)\<close> triple
  \<open>truncate_split_pair_state_monadic\<close> builds/returns. The top-level LOOP
  state bundles \<open>rp\<close> IN with it (making \<open>truncate_worklist\<close> a flat 4-tuple)
  so the overall state \<open>truncate_state\<close> pairs with \<open>acc\<close> at ONE nesting level
  only — matching the bisection solver's
  \<open>bisection_loop_state = (todo,qtodo) \<times> acc\<close> and the Newton loop's
  \<open>newton_loop_state = (todo,qtodo,es,ss,cs) \<times> acc\<close>, both a flat inner
  tuple paired with \<open>acc\<close> ONCE (2 top-level components). A 3-level nesting
  \<open>(worklist \<times> acc) \<times> rp\<close> makes Sepref raise an internal exception
  (\<open>THM 0\<close> in \<open>INTRO_KD\<close>/\<open>SPEC_RES_ASSN\<close>) at \<open>truncate_after_pop_impl\<close>'s
  \<open>sepref_definition\<close>, independently of the body, so it is a TYPE-shape issue.\<close>
type_synonym truncate_todo3 =
  "gmp_dyadic_interval_vec \<times> gmp_poly list \<times> nat list"

type_synonym truncate_worklist =
  "gmp_dyadic_interval_vec \<times> gmp_poly list \<times> nat list \<times> gmp_poly"

type_synonym truncate_state =
  "truncate_worklist \<times> gmp_dyadic_interval_vec"

abbreviation truncate_todo3_assn where
"truncate_todo3_assn \<equiv>
  gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_poly_vec_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn"

abbreviation truncate_worklist_assn where
"truncate_worklist_assn \<equiv>
  gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_poly_vec_assn \<times>\<^sub>a gmp_dyadic_exp_list_assn
    \<times>\<^sub>a gmp_poly_assn"

abbreviation truncate_state_assn where
"truncate_state_assn \<equiv>
  truncate_worklist_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn"

section \<open>Push side: build both bisection children and re-truncate each\<close>


text \<open>Clone of @{const carried_left_right_monadic} (\<open>Carried_Kernel.thy\<close>) followed by an
  in-place nb-gated re-truncation of BOTH children (@{const carried_retrunc_mop}),
  threaded with the AMPLIFIED per-child guards from @{const truncate_child_guards_mop}
  (see its note — the reset-gate needs the child's TRUE incoming slack to size the
  budget, and the pass-through branches must return the amplified guard, not the
  parent's). Returns the two truncated children and their new guards.\<close>
definition truncate_children_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> nat \<times> gmp_poly \<times> nat) nres" where
"truncate_children_monadic g Q \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) Q;
  ASSERT (len = length Q);
  (gl0, gr0) \<leftarrow> (PR_CONST truncate_child_guards_mop) g len;
  (ql, qr) \<leftarrow> (PR_CONST carried_left_right_monadic) Q;
  ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
  (ql, gl) \<leftarrow> (PR_CONST carried_retrunc_mop) ql gl0;
  ASSERT (length qr + 1 < max_snat LENGTH(gmp_poly_len));
  (qr, gr) \<leftarrow> (PR_CONST carried_retrunc_mop) qr gr0;
  RETURN (ql, gl, qr, gr)
}"

sepref_register "PR_CONST truncate_children_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> nat \<times> gmp_poly \<times> nat) nres"

sepref_definition truncate_children_impl [llvm_code] is
  "uncurry truncate_children_monadic" ::
  "[\<lambda>(g, Q). length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
      gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding truncate_children_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma truncate_children_impl_hnr[sepref_fr_rules]:
  "(uncurry truncate_children_impl,
    uncurry (PR_CONST truncate_children_monadic)) \<in>
    [\<lambda>(g, Q). length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
      gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using truncate_children_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Pop side: guarded count with exact-rebuild escalation\<close>


text \<open>The dense count at pop: guard-count the (possibly truncated) node \<open>Q\<close> at guard
  \<open>g\<close>. DECISIVE \<Rightarrow> keep \<open>Q\<close> and its actual guard \<open>g\<close> (the poly is unchanged — only its
  COUNT is certified). AMBIGUOUS \<Rightarrow> ESCALATE: rebuild the exact node \<open>qx\<close> from the root,
  exact-count it, return guard \<open>0\<close> (genuinely exact now). The returned guard is what
  child-building must seed with (@{const truncate_children_monadic}) — so it is
  returned, not silently reset.\<close>
definition truncate_count_escalate_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    (nat \<times> gmp_poly \<times> nat \<times> gmp_poly) nres" where
"truncate_count_escalate_monadic Q g l r k rp \<equiv> doN {
  (cnt, dec) \<leftarrow> (PR_CONST carried_descartes_count_g_monadic) Q g;
  if dec then RETURN (cnt, Q, g, rp)
  else doN {
    (qx, rp) \<leftarrow> (PR_CONST carried_escalate_keep_monadic) rp l r k Q;
    ASSERT (length qx + 1 < max_snat LENGTH(gmp_poly_len));
    \<comment> \<open>\<open>qx\<close> is the EXACT rebuilt node, so the bisection solver's pop-count
       (@{const carried_descartes_count_trunc_monadic}, with its own exact-on-ambiguity
       fallback) returns the correct capped \<open>{0,1,2,3}\<close> — reuse it, no new op.\<close>
    cx \<leftarrow> (PR_CONST carried_descartes_count_trunc_monadic) qx;
    \<comment> \<open>EXACT-LOCK sentinel \<open>2^42\<close> (see the retrunc note in
       \<open>Truncate.thy\<close>): the escalated subtree is locked exact-forever —
       one rebuild, then exact behaviour; this breaks the per-node rebuild cycle on
       truncation-hostile (cluster-descent) subtrees.\<close>
    RETURN (cx, qx, 4398046511104, rp)
  }
}"

sepref_register "PR_CONST truncate_count_escalate_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
      (nat \<times> gmp_poly \<times> nat \<times> gmp_poly) nres"

sepref_definition truncate_count_escalate_impl [llvm_code] is
  "uncurry5 truncate_count_escalate_monadic" ::
  "[\<lambda>(((((Q, g), l), r), k), rp).
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"
  unfolding truncate_count_escalate_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma truncate_count_escalate_impl_hnr[sepref_fr_rules]:
  "(uncurry5 truncate_count_escalate_impl,
    uncurry5 (PR_CONST truncate_count_escalate_monadic)) \<in>
    [\<lambda>(((((Q, g), l), r), k), rp).
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"
  using truncate_count_escalate_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Guarded midpoint test\<close>


text \<open>Guarded hom-eval TRUST test: the SHIFT-based half-eval loop —
  shares @{const half_eval_cond} + @{const half_eval_body_mop_monadic} with
  @{const half_eval_zero_monadic} (each step \<open>acc \<lless> 1\<close> then a borrowed-read in-place add
  @{const poly_acc_add_coeff_monadic}) — with a sign+bitlen TAIL instead of the zero-test
  finish. It computes the integer
  \<open>S = (\<Sum>i<len. xs!i \<cdot> 2^(len-1-i)) = poly (Poly (rev xs)) 2\<close>, whose sign equals that of the
  true eval at \<open>1/2\<close> up to the positive factor \<open>2^(len-1)\<close>, without a per-step multiply or a
  growing power of the denominator. Returns True iff the truncated eval
  CERTIFIES the true eval is nonzero (mid is trustedly NOT a root). Uses the
  one-sided fdiv error direction (\<open>S_tilde \<le> S_true < S_tilde + 2^gm\<close>):
  \<open>S_tilde > 0 \<Rightarrow> S_true > 0\<close> unconditionally, and \<open>S_tilde < 0\<close> with
  \<open>bitlen |S_tilde| > gm\<close> \<Rightarrow> \<open>S_true < 0\<close> — exactly @{const lead_trust_mop}'s contract
  (reused verbatim). \<open>S_tilde = 0\<close> or small-negative \<Rightarrow> False (ambiguous, caller
  escalates). \<open>bitlen 0 = 1\<close> (the @{const mpz_bitlen2_monadic} spec) is harmless:
  \<open>s = 0\<close> already fails both trust disjuncts.\<close>
definition poly_hom_eval_trust_half_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
"poly_hom_eval_trust_half_monadic g xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (0 < len);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  acc0 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 0;
  st \<leftarrow> WHILET
    (\<lambda>st. (PR_CONST half_eval_cond) len st)
    (\<lambda>st. (PR_CONST half_eval_body_mop_monadic) xs len st)
    (1, acc0);
  let (i, acc2) = st;
  s \<leftarrow> (PR_CONST mpz_sgn_mop) acc2;
  bl \<leftarrow> (PR_CONST mpz_bitlen2_monadic) acc2;
  gm \<leftarrow> (PR_CONST mid_guard_mop) g len;
  tr \<leftarrow> (PR_CONST lead_trust_mop) s bl gm;
  (PR_CONST mpzb_discard_monadic) acc2;
  RETURN tr
}"

sepref_register "PR_CONST poly_hom_eval_trust_half_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

sepref_definition poly_hom_eval_trust_half_impl [llvm_code] is
  "uncurry poly_hom_eval_trust_half_monadic" ::
  "[\<lambda>(_, xs).
      0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding poly_hom_eval_trust_half_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_fr_rules] = half_eval_cond_impl_hnr half_eval_body_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
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

lemma poly_hom_eval_trust_half_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_hom_eval_trust_half_impl,
    uncurry (PR_CONST poly_hom_eval_trust_half_monadic)) \<in>
    [\<lambda>(_, xs).
      0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using poly_hom_eval_trust_half_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The guarded midpoint test-or-escalate, with the decisive/escalate shape of
  @{const truncate_count_escalate_monadic}: an exact node (\<open>g = 0\<close>) gets the plain exact midpoint
  zero test and is unchanged. A truncated node gets the trusted evaluation: trusted not-a-root
  proceeds truncated (\<open>is_root = False\<close>, node unchanged); ambiguous rebuilds the exact node from the
  borrowed root, runs the exact test on it, and returns it with guard 0.\<close>
definition truncate_mid_test_monadic ::
  "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    (bool \<times> gmp_poly \<times> nat \<times> gmp_poly) nres" where
"truncate_mid_test_monadic rp l r k g Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  if g = 0 then doN {
    is_root \<leftarrow> (PR_CONST bisection_mid_zero_monadic) Q;
    RETURN (is_root, Q, g, rp)
  } else if 4398046511104 \<le> g then doN {
    \<comment> \<open>EXACT-LOCK: the poly is exact — the plain exact mid test, lock preserved.\<close>
    is_root \<leftarrow> (PR_CONST bisection_mid_zero_monadic) Q;
    RETURN (is_root, Q, g, rp)
  } else if 1099511627776 \<le> g then doN {
    \<comment> \<open>\<^bold>\<open>Outside the trust window.\<close> For \<open>g \<ge> 2^40\<close> the trust kernel's @{const mid_guard_mop} clamps
       its guard to \<open>2^41\<close>, which under-approximates the true error bound \<open>g + len\<close> once
       \<open>g > 2^41 - len\<close>, so a trusted sign could be overturned by the truncation error. Such nodes
       escalate instead of trusting (the same code as the ambiguous arm below), which keeps
       \<open>g < 2^40\<close>, the window of the trust-soundness lemma, an invariant of every trust call.\<close>
    (qx, rp2) \<leftarrow> (PR_CONST carried_escalate_keep_monadic) rp l r k Q;
    ASSERT (0 < length qx);
    ASSERT (length qx + 1 < max_snat LENGTH(gmp_poly_len));
    is_root \<leftarrow> (PR_CONST bisection_mid_zero_monadic) qx;
    RETURN (is_root, qx, 0, rp2)
  } else doN {
    tr \<leftarrow> (PR_CONST poly_hom_eval_trust_half_monadic) g Q;
    if tr then RETURN (False, Q, g, rp)
    else doN {
      (qx, rp2) \<leftarrow> (PR_CONST carried_escalate_keep_monadic) rp l r k Q;
      ASSERT (0 < length qx);
      ASSERT (length qx + 1 < max_snat LENGTH(gmp_poly_len));
      is_root \<leftarrow> (PR_CONST bisection_mid_zero_monadic) qx;
      \<comment> \<open>\<^bold>\<open>The midpoint path returns \<open>g = 0\<close>, not the exact lock.\<close> Ambiguity of the midpoint test is a
         transient geometric event (the midpoint landed near a root at this level; the next
         level's midpoint is elsewhere), unlike count ambiguity on a cluster, which recurs at every
         level. So the node becomes exact but stays eligible for truncation at the next child build.\<close>
      RETURN (is_root, qx, 0, rp2)
    }
  }
}"

sepref_register "PR_CONST truncate_mid_test_monadic"
  :: "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
      (bool \<times> gmp_poly \<times> nat \<times> gmp_poly) nres"

sepref_definition truncate_mid_test_impl [llvm_code] is
  "uncurry5 truncate_mid_test_monadic" ::
  "[\<lambda>(((((rp, _), _), k), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      bool1_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"
  unfolding truncate_mid_test_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_sint_const "TYPE(gmp_long_len)")?
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma truncate_mid_test_impl_hnr[sepref_fr_rules]:
  "(uncurry5 truncate_mid_test_impl,
    uncurry5 (PR_CONST truncate_mid_test_monadic)) \<in>
    [\<lambda>(((((rp, _), _), k), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      bool1_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"
  using truncate_mid_test_impl.refine
  by (simp add: PR_CONST_def)

section \<open>The dense split: build + retruncate BOTH children, push in lockstep with gs\<close>

text \<open>As @{const bisection_split_pair_state_monadic} (\<open>Bisection\<close>): pushes the two interval children
  onto \<open>todo\<close>, and pushes the two truncated children (@{const truncate_children_monadic}) onto
  \<open>qtodo\<close>/\<open>gs\<close> in lockstep.

  Every op below takes \<open>todo qtodo gs\<close> as three separate curried arguments rather than a bundled
  \<open>st :: truncate_worklist\<close>: constructing a fresh tuple inline right before passing it as a call
  argument does not compose in Sepref, whereas bundling in a terminal \<open>RETURN\<close> does.\<close>
text \<open>Threads \<open>rp\<close> through UNUSED (a pass-through \<open>\<^sup>k\<close> borrow) so its RETURN is
  ALREADY the fully-shaped 4-tuple \<open>truncate_worklist\<close> — avoiding EVER
  unpacking-then-repacking a 3-tuple sub-result with an externally-held \<open>rp\<close> at any
  call site (confirmed necessary: renaming the unpack to fresh names alone did NOT
  clear the internal Sepref exception at the caller; eliminating the
  repackage-into-a-bigger-tuple step entirely did).\<close>
definition truncate_split_pair_state_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
    truncate_worklist nres" where
"truncate_split_pair_state_monadic todo qtodo gs rp l_num r_num k g Q \<equiv> doN {
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable2 todo);
  todo \<leftarrow> (PR_CONST dyadic_interval_vec_push_children_monadic) todo l_num r_num k;
  (ql, gl, qr, gr) \<leftarrow> (PR_CONST truncate_children_monadic) g Q;
  ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
  qtodo \<leftarrow> (PR_CONST poly_vec_push2_monadic) qtodo ql qr;
  ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
  gs \<leftarrow> mop_list_append gs gl;
  ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
  gs \<leftarrow> mop_list_append gs gr;
  RETURN (todo, qtodo, gs, rp)
}"

sepref_register "PR_CONST truncate_split_pair_state_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
      truncate_worklist nres"

sepref_definition truncate_split_pair_state_impl [llvm_code] is
  "uncurry8 truncate_split_pair_state_monadic" ::
  "[\<lambda>((((((((todo, qtodo), _), _), _), _), k), _), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_worklist_assn"
  unfolding truncate_split_pair_state_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma truncate_split_pair_state_impl_hnr[sepref_fr_rules]:
  "(uncurry8 truncate_split_pair_state_impl,
    uncurry8 (PR_CONST truncate_split_pair_state_monadic)) \<in>
    [\<lambda>((((((((todo, qtodo), _), _), _), _), k), _), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_worklist_assn"
  using truncate_split_pair_state_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Branches (zero/one/split), es-column-free clones of the bisection solver's\<close>

text \<open>\<open>cnt = 0\<close>/\<open>cnt = 1\<close> — behaviorally unchanged from
  @{const bisection_branch_zero_monadic}/@{const bisection_branch_one_monadic}: the popped
  node's guard is simply discarded (a dropped/finalized node's truncation state is
  irrelevant), \<open>gs\<close> (already shrunk by the caller's pop) threads through untouched.\<close>
definition truncate_branch_zero_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres" where
"truncate_branch_zero_monadic todo qtodo gs acc rp l_num r_num k Q \<equiv> doN {
  (PR_CONST mpzb_discard_monadic) l_num;
  (PR_CONST mpzb_discard_monadic) r_num;
  (PR_CONST poly_free_monadic) Q;
  RETURN ((todo, qtodo, gs, rp), acc)
}"

sepref_register "PR_CONST truncate_branch_zero_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres"

sepref_definition truncate_branch_zero_impl [llvm_inline] is
  "uncurry8 truncate_branch_zero_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
    truncate_state_assn"
  unfolding truncate_branch_zero_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma truncate_branch_zero_impl_hnr[sepref_fr_rules]:
  "(uncurry8 truncate_branch_zero_impl,
    uncurry8 (PR_CONST truncate_branch_zero_monadic)) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
      truncate_state_assn"
  using truncate_branch_zero_impl.refine
  by (simp add: PR_CONST_def)

definition truncate_branch_one_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres" where
"truncate_branch_one_monadic todo qtodo gs acc rp l_num r_num k Q \<equiv> doN {
  let (lns, rns, ks) = acc;
  ASSERT (dyadic_interval_vec_pushable acc);
  lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) lns l_num;
  rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) rns r_num;
  ASSERT (length ks + 1 < max_snat LENGTH(gmp_poly_len));
  ks \<leftarrow> mop_list_append ks k;
  (PR_CONST poly_free_monadic) Q;
  RETURN ((todo, qtodo, gs, rp), (lns, rns, ks))
}"

sepref_register "PR_CONST truncate_branch_one_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres"

sepref_definition truncate_branch_one_impl [llvm_inline] is
  "uncurry8 truncate_branch_one_monadic" ::
  "[\<lambda>((((((((_, _), _), acc), _), _), _), _), _). dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_state_assn"
  unfolding truncate_branch_one_monadic_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma truncate_branch_one_impl_hnr[sepref_fr_rules]:
  "(uncurry8 truncate_branch_one_impl,
    uncurry8 (PR_CONST truncate_branch_one_monadic)) \<in>
    [\<lambda>((((((((_, _), _), acc), _), _), _), _), _). dyadic_interval_vec_pushable acc]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_state_assn"
  using truncate_branch_one_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Split — clones @{const bisection_branch_split_root_monadic}/
  @{const bisection_branch_split_nonroot_monadic} as TWO SEPARATE full ops (not a shared
  op with an inline partial-mutation \<open>if\<close>) — mirroring the bisection solver's structure
  exactly, since an \<open>if c then (op that mutates acc) else (RETURN acc unchanged)\<close>
  mux is harder for Sepref than two full branches each doing ONE complete thing. The
  \<open>bisection_mid_zero_monadic\<close> test itself is unaffected by truncation state: a
  truncated node's mid-zero test runs on truncated coefficients, which is SOUND for the
  0/1/split classification here since the eventual answer is re-derived from the CHILD counts
  either way, never trusted alone.\<close>
text \<open>The split-pair-state logic inlined rather than called as a sub-op. \<open>k\<close> and \<open>g\<close> are separate
  arguments (\<open>uncurry9\<close>), not a \<open>(nat\<times>nat)\<close> pair: a nested pair reaching the after-pop/dispatch
  boundary as a destructured bind result is not discharged by Sepref's \<open>opt\<close>/frame recombiner, while
  separate scalars synthesise (the Newton solver synthesises \<open>newton_branch_split_impl\<close> at
  \<open>uncurry11\<close> and \<open>newton_after_pop_impl\<close> at \<open>uncurry12\<close> with the same large return type).\<close>
definition truncate_branch_split_nonroot_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres" where
"truncate_branch_split_nonroot_monadic todo qtodo gs acc rp l_num r_num k g Q \<equiv> doN {
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable2 todo);
  todo \<leftarrow> (PR_CONST dyadic_interval_vec_push_children_monadic) todo l_num r_num k;
  (ql, gl, qr, gr) \<leftarrow> (PR_CONST truncate_children_monadic) g Q;
  ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
  qtodo \<leftarrow> (PR_CONST poly_vec_push2_monadic) qtodo ql qr;
  ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
  gs \<leftarrow> mop_list_append gs gl;
  ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
  gs \<leftarrow> mop_list_append gs gr;
  RETURN ((todo, qtodo, gs, rp), acc)
}"

sepref_register "PR_CONST truncate_branch_split_nonroot_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres"

sepref_definition truncate_branch_split_nonroot_impl [llvm_code] is
  "uncurry9 truncate_branch_split_nonroot_monadic" ::
  "[\<lambda>(((((((((todo, qtodo), _), _), _), _), _), k), _), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_state_assn"
  unfolding truncate_branch_split_nonroot_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma truncate_branch_split_nonroot_impl_hnr[sepref_fr_rules]:
  "(uncurry9 truncate_branch_split_nonroot_impl,
    uncurry9 (PR_CONST truncate_branch_split_nonroot_monadic)) \<in>
    [\<lambda>(((((((((todo, qtodo), _), _), _), _), _), k), _), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_state_assn"
  using truncate_branch_split_nonroot_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Same inlining + \<open>(k,g)\<close> bundling as \<open>truncate_branch_split_nonroot_monadic\<close>
  — see its comment for why.\<close>
definition truncate_branch_split_root_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres" where
"truncate_branch_split_root_monadic todo qtodo gs acc rp l_num r_num k g Q \<equiv> doN {
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable acc);
  acc' \<leftarrow> (PR_CONST carried_push_mid_monadic) acc l_num r_num k;
  ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
  ASSERT (dyadic_interval_vec_pushable2 todo);
  todo \<leftarrow> (PR_CONST dyadic_interval_vec_push_children_monadic) todo l_num r_num k;
  (ql, gl, qr, gr) \<leftarrow> (PR_CONST truncate_children_monadic) g Q;
  ASSERT (length qtodo + 1 < max_snat LENGTH(gmp_poly_len));
  qtodo \<leftarrow> (PR_CONST poly_vec_push2_monadic) qtodo ql qr;
  ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
  gs \<leftarrow> mop_list_append gs gl;
  ASSERT (length gs + 1 < max_snat LENGTH(gmp_poly_len));
  gs \<leftarrow> mop_list_append gs gr;
  RETURN ((todo, qtodo, gs, rp), acc')
}"

sepref_register "PR_CONST truncate_branch_split_root_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres"

sepref_definition truncate_branch_split_root_impl [llvm_code] is
  "uncurry9 truncate_branch_split_root_monadic" ::
  "[\<lambda>(((((((((todo, qtodo), _), acc), _), _), _), k), _), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_state_assn"
  unfolding truncate_branch_split_root_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma truncate_branch_split_root_impl_hnr[sepref_fr_rules]:
  "(uncurry9 truncate_branch_split_root_impl,
    uncurry9 (PR_CONST truncate_branch_split_root_monadic)) \<in>
    [\<lambda>(((((((((todo, qtodo), _), acc), _), _), _), k), _), Q).
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_state_assn"
  using truncate_branch_split_root_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The mid test is now the GUARDED @{const truncate_mid_test_monadic} (fix B,
  see its section note) — its result tuple carries the possibly-escalated node
  \<open>Q'\<close>/\<open>g'\<close>/\<open>rp'\<close>, destructured via the same flat bind idiom as the after-pop's
  count-escalate (the proven shape).\<close>
definition truncate_branch_split_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres" where
"truncate_branch_split_monadic todo qtodo gs acc rp l_num r_num k g Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length rp);
  ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
  (is_root, Q', g', rp') \<leftarrow>
    (PR_CONST truncate_mid_test_monadic) rp l_num r_num k g Q;
  ASSERT (0 < length Q');
  ASSERT (length Q' + 1 < max_snat LENGTH(gmp_poly_len));
  if is_root then
    (PR_CONST truncate_branch_split_root_monadic)
      todo qtodo gs acc rp' l_num r_num k g' Q'
  else
    (PR_CONST truncate_branch_split_nonroot_monadic)
      todo qtodo gs acc rp' l_num r_num k g' Q'
}"

sepref_register "PR_CONST truncate_branch_split_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres"

sepref_definition truncate_branch_split_impl [llvm_code] is
  "uncurry9 truncate_branch_split_monadic" ::
  "[\<lambda>(((((((((todo, qtodo), _), acc), rp), _), _), k), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_state_assn"
  unfolding truncate_branch_split_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma truncate_branch_split_impl_hnr[sepref_fr_rules]:
  "(uncurry9 truncate_branch_split_impl,
    uncurry9 (PR_CONST truncate_branch_split_monadic)) \<in>
    [\<lambda>(((((((((todo, qtodo), _), acc), rp), _), _), k), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_state_assn"
  using truncate_branch_split_impl.refine
  by (simp add: PR_CONST_def)

section \<open>The dense after-pop dispatch\<close>

text \<open>Clone of @{const bisection_after_pop_monadic} (\<open>Bisection.thy\<close>): count
  FIRST (guarded + escalating), then dispatch on the returned \<open>cnt\<close> — mirroring the
  bisection solver's \<open>cnt = 0\<close>/\<open>cnt = 1\<close>/else structure exactly, just with the guard \<open>g\<close> and root
  \<open>rp\<close> threaded through every branch. Takes \<open>todo qtodo gs\<close> SEPARATELY (see the
  state note above) so its OWN caller never needs to reconstruct them either.\<close>
text \<open>Split off the CNT-DISPATCH from the count+escalate call — the SAME "split
  further" pattern that resolved every other stall in this file/theory (the
  case-match, the pop chain, the tuple-construction traps): a genuine internal
  Sepref exception (\<open>THM 0\<close> in \<open>INTRO_KD\<close>/\<open>SPEC_RES_ASSN\<close>, not a normal unsolved
  goal) hit when count-escalate's 4-tuple bind and the 3-way branch dispatch into
  the BIG \<open>truncate_state_assn\<close> return type were combined in ONE
  \<open>sepref_definition\<close> — isolating the dispatch (which ALREADY has \<open>cnt\<close>/\<open>Q\<close>/\<open>g\<close>/
  \<open>rp\<close> as plain bound args, no count call inside) into its own op resolves it.\<close>
text \<open>\<open>k\<close> and \<open>g\<close> are separate arguments, for the reason given above: a nested \<open>(snat\<times>snat)\<close> pair
  arriving as a destructured bind result at the after-pop/dispatch boundary is tracked twice (both
  \<open>(kg,rp)\<close> invalidated and \<open>kg\<close> individually), and the recombiner cannot discharge it. Separate
  scalars flow through as plain arguments, like \<open>k e s c\<close> in the Newton solver.\<close>
definition truncate_dispatch_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> truncate_state nres" where
"truncate_dispatch_monadic todo qtodo gs acc rp l_num r_num k g Q cnt \<equiv> doN {
  if cnt = 0 then
    (PR_CONST truncate_branch_zero_monadic) todo qtodo gs acc rp l_num r_num k Q
  else if cnt = 1 then
    (PR_CONST truncate_branch_one_monadic) todo qtodo gs acc rp l_num r_num k Q
  else
    (PR_CONST truncate_branch_split_monadic) todo qtodo gs acc rp l_num r_num k g Q
}"

sepref_register "PR_CONST truncate_dispatch_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> truncate_state nres"

sepref_definition truncate_dispatch_impl [llvm_code] is
  "uncurry10 truncate_dispatch_monadic" ::
  "[\<lambda>((((((((((todo, qtodo), _), acc), rp), _), _), k), _), Q), _).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      truncate_state_assn"
  unfolding truncate_dispatch_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma truncate_dispatch_impl_hnr[sepref_fr_rules]:
  "(uncurry10 truncate_dispatch_impl,
    uncurry10 (PR_CONST truncate_dispatch_monadic)) \<in>
    [\<lambda>((((((((((todo, qtodo), _), acc), rp), _), _), k), _), Q), _).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      truncate_state_assn"
  using truncate_dispatch_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The dense after-pop: count-escalate FIRST (guarded count with exact-rebuild
  escalation), destructure its flat 4-tuple result, then dispatch on \<open>cnt\<close> — a direct
  clone of the bisection solver's @{const bisection_after_pop_monadic} structure, extended only
  by the guard \<open>g\<close> (in) / \<open>g'\<close> (out) and the root \<open>rp\<close>/\<open>rp'\<close> threading. \<open>k\<close>/\<open>g\<close> stay
  SEPARATE (see the dispatch note): the count result \<open>(cnt, Q', g', rp')\<close> is a flat
  bind-result tuple destructured via the standard idiom (exactly like a pop), and its
  pieces flow to \<open>dispatch\<close> as plain args — no nested pair anywhere, matching the
  Newton after-pop (which reaches \<open>uncurry12\<close> the same way). The \<open>Q'\<close>/\<open>rp'\<close>
  facts are ASSERTed right after the bind that produces them (a Sepref composability
  requirement — count-escalate may return a FRESH escalated \<open>Q'\<close>, unlike the bisection solver
  whose count borrows the same \<open>Q\<close>; the refinement proof shows it never returns an empty poly).\<close>
definition truncate_after_pop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres" where
"truncate_after_pop_monadic todo qtodo gs acc rp l_num r_num k g Q \<equiv> doN {
  ASSERT (0 < length Q);
  ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
  (cnt, Q', g', rp') \<leftarrow>
    (PR_CONST truncate_count_escalate_monadic) Q g l_num r_num k rp;
  ASSERT (0 < length Q');
  ASSERT (length Q' + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length rp');
  ASSERT (length rp' + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp' - 1) < max_snat LENGTH(gmp_poly_len));
  (PR_CONST truncate_dispatch_monadic)
    todo qtodo gs acc rp' l_num r_num k g' Q' cnt
}"

sepref_register "PR_CONST truncate_after_pop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres"

text \<open>Precondition = the union of everything the body's callees need: count-escalate's
  \<open>rp\<close>/\<open>Q\<close> facts, PLUS dispatch's split-branch \<open>todo\<close>/\<open>acc\<close>/\<open>qtodo\<close> facts (the dispatch
  facts about the FRESH \<open>Q'\<close>/\<open>rp'\<close> are ASSERTed in-body after the count bind).\<close>
sepref_definition truncate_after_pop_impl [llvm_code] is
  "uncurry9 truncate_after_pop_monadic" ::
  "[\<lambda>(((((((((todo, qtodo), _), acc), rp), _), _), k), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_state_assn"
  unfolding truncate_after_pop_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma truncate_after_pop_impl_hnr[sepref_fr_rules]:
  "(uncurry9 truncate_after_pop_impl,
    uncurry9 (PR_CONST truncate_after_pop_monadic)) \<in>
    [\<lambda>(((((((((todo, qtodo), _), acc), rp), _), _), k), _), Q).
      0 < length Q \<and>
      length Q + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len) \<and>
      dyadic_interval_vec_pushable2 todo \<and>
      dyadic_interval_vec_pushable acc \<and>
      length qtodo + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow>
      truncate_state_assn"
  using truncate_after_pop_impl.refine
  by (simp add: PR_CONST_def)

section \<open>The dense loop step: pop (todo, qtodo, gs in lockstep) \<Rightarrow> dispatch\<close>

text \<open>Clone of \<open>bisection_loop_step_args_monadic\<close> (\<open>Bisection.thy-1083\<close>): pop the
  interval, THEN the poly, THEN the guard — same lockstep order as the Newton loop's
  \<open>es\<close>/\<open>ss\<close>/\<open>cs\<close> pops (\<open>Newton.thy-2495\<close>), reusing the SAME
  @{const dyadic_exp_pop_last_monadic} primitive for \<open>gs\<close> (a plain \<open>nat list\<close>, same
  assn as \<open>es\<close>/\<open>ss\<close>/\<open>cs\<close>).\<close>
text \<open>The pop chain, split into TWO ops mirroring the bisection solver's structure
  (\<open>Bisection.thy\<close>): \<open>loop_step_args\<close> pops the INTERVAL, then delegates to
  \<open>pop_poly_args\<close> which pops the POLY + GUARD and calls after-pop. Each pop is bound to a
  fresh name and destructured in a NESTED \<open>case … of\<close> (the
  \<open>qpop \<leftarrow> pop; case qpop of (Q, qtodo) \<Rightarrow> …\<close> idiom — NOT a bind-with-pattern
  \<open>(Q, qtodo) \<leftarrow> pop\<close>, which leaves a raw \<open>case_prod\<close> the trans phase cannot see
  through when a NESTED-triple pop result like \<open>((l_num, r_num, k), todo)\<close> is also in
  play). Both ops use an explicit \<open>supply [sepref_fr_rules] = …\<close> +
  \<open>sepref_dbg_trans\<close> (not \<open>_keep\<close>) + \<open>sepref_dbg_cons_solve_cp\<close> recipe. Keeping the
  nested-triple interval pop in its OWN op (isolated from the poly pop) is what lets
  trans handle it — combining both pops in one flat op fails at \<open>trans\<close> on the triple.\<close>
definition truncate_pop_poly_args_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
    truncate_state nres" where
"truncate_pop_poly_args_monadic todo qtodo gs acc rp l_num r_num k \<equiv> doN {
  ASSERT (qtodo \<noteq> []);
  qpop \<leftarrow> (PR_CONST poly_vec_pop_last_monadic) qtodo;
  case qpop of (Q, qtodo) \<Rightarrow> doN {
    ASSERT (gs \<noteq> []);
    gpop \<leftarrow> (PR_CONST dyadic_exp_pop_last_monadic) gs;
    case gpop of (g, gs) \<Rightarrow> doN {
      ASSERT (0 < length Q);
      ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
      ASSERT (k + 1 < max_snat LENGTH(gmp_poly_len));
      ASSERT (0 < length rp);
      ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
      ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
      ASSERT (dyadic_interval_vec_pushable2 todo);
      ASSERT (dyadic_interval_vec_pushable acc);
      ASSERT (length qtodo + 2 < max_snat LENGTH(gmp_poly_len));
      (PR_CONST truncate_after_pop_monadic)
        todo qtodo gs acc rp l_num r_num k g Q
    }
  }
}"

sepref_register "PR_CONST truncate_pop_poly_args_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      truncate_state nres"

sepref_definition truncate_pop_poly_args_impl [llvm_code] is
  "uncurry7 truncate_pop_poly_args_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    truncate_state_assn"
  unfolding truncate_pop_poly_args_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] =
    poly_vec_pop_last_impl_hnr
    dyadic_exp_pop_last_impl_hnr
    truncate_after_pop_impl_hnr
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

lemma truncate_pop_poly_args_impl_hnr[sepref_fr_rules]:
  "(uncurry7 truncate_pop_poly_args_impl,
    uncurry7 (PR_CONST truncate_pop_poly_args_monadic)) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
      truncate_state_assn"
  using truncate_pop_poly_args_impl.refine
  by (simp add: PR_CONST_def)

definition truncate_loop_step_args_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres" where
"truncate_loop_step_args_monadic todo qtodo gs acc rp \<equiv> doN {
  \<comment> \<open>The HNR rule of \<open>dyadic_interval_vec_pop_last_monadic\<close> is conditional on
     \<open>dyadic_interval_vec_invar todo\<close> and a non-empty \<open>lns\<close> column; they are asserted at the call site
     so the conditional rule fires in \<open>trans\<close>.\<close>
  ASSERT (dyadic_interval_vec_invar todo);
  ASSERT (case todo of (lns, _, _) \<Rightarrow> lns \<noteq> []);
  ((l_num, r_num, k), todo) \<leftarrow>
    (PR_CONST dyadic_interval_vec_pop_last_monadic) todo;
  (PR_CONST truncate_pop_poly_args_monadic)
    todo qtodo gs acc rp l_num r_num k
}"

sepref_register "PR_CONST truncate_loop_step_args_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres"

sepref_definition truncate_loop_step_args_impl [llvm_code] is
  "uncurry4 truncate_loop_step_args_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
    truncate_state_assn"
  unfolding truncate_loop_step_args_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] =
    dyadic_interval_vec_pop_last_impl_hnr
    truncate_pop_poly_args_impl_hnr
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

lemma truncate_loop_step_args_impl_hnr[sepref_fr_rules]:
  "(uncurry4 truncate_loop_step_args_impl,
    uncurry4 (PR_CONST truncate_loop_step_args_monadic)) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
      truncate_state_assn"
  using truncate_loop_step_args_impl.refine
  by (simp add: PR_CONST_def)

definition truncate_loop_step_monadic ::
  "truncate_state \<Rightarrow> truncate_state nres" where
"truncate_loop_step_monadic S \<equiv>
  (case S of ((todo, qtodo, gs, rp), acc) \<Rightarrow>
    (PR_CONST truncate_loop_step_args_monadic) todo qtodo gs acc rp)"

sepref_register "PR_CONST truncate_loop_step_monadic"
  :: "truncate_state \<Rightarrow> truncate_state nres"

text \<open>Every precondition the step's body needs is discharged from an ASSERT immediately preceding the
  call that needs it, not from a stated loop invariant. So the step, condition, body and loop Sepref
  definitions below carry no stated precondition (\<open>\<lambda>_. True\<close>): Sepref's WHILET rule needs only that
  \<open>cond_impl\<close> and \<open>body_impl\<close> share a consistent type, and the ASSERT-before-call idiom lets
  \<open>sepref_dbg_cons_solve\<close> discharge each callee's precondition locally. The correctness invariant is
  stated in the loop refinement.\<close>
sepref_definition truncate_loop_step_impl [llvm_code] is
  "truncate_loop_step_monadic" ::
  "truncate_state_assn\<^sup>d \<rightarrow>\<^sub>a truncate_state_assn"
  unfolding truncate_loop_step_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma truncate_loop_step_impl_hnr[sepref_fr_rules]:
  "(truncate_loop_step_impl, PR_CONST truncate_loop_step_monadic) \<in>
    truncate_state_assn\<^sup>d \<rightarrow>\<^sub>a truncate_state_assn"
  using truncate_loop_step_impl.refine
  by (simp add: PR_CONST_def)

definition truncate_loop_cond :: "truncate_state \<Rightarrow> bool" where
"truncate_loop_cond S \<equiv>
  (case S of ((todo, _, _, _), _) \<Rightarrow>
    (case todo of (lns, _, _) \<Rightarrow> lns \<noteq> []))"

sepref_register "PR_CONST truncate_loop_cond"
  :: "truncate_state \<Rightarrow> bool"

text \<open>Heap-owning state (\<open>gmp_dyadic_interval_vec_assn\<close> etc.) must be read through a
  registered length op, not a bare pattern match — clone of
  @{const bisection_loop_cond_mop_monadic} (\<open>Bisection.thy-1190\<close>).\<close>
definition truncate_loop_cond_mop_monadic ::
  "truncate_state \<Rightarrow> bool nres" where
"truncate_loop_cond_mop_monadic S \<equiv>
  (case S of ((todo, _, _, _), _) \<Rightarrow> (PR_CONST gmp_dyadic_interval_vec_nonempty) todo)"

lemma truncate_loop_cond_mop_monadic_eq:
  "truncate_loop_cond_mop_monadic = RETURN o truncate_loop_cond"
  unfolding truncate_loop_cond_mop_monadic_def
    gmp_dyadic_interval_vec_nonempty_def truncate_loop_cond_def
    dyadic_interval_vec_length_monadic_def poly_length_monadic_def PR_CONST_def
  by (auto intro!: ext split: prod.splits)

sepref_definition truncate_loop_cond_impl [llvm_inline] is
  "truncate_loop_cond_mop_monadic" ::
  "truncate_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding truncate_loop_cond_mop_monadic_def
  by sepref

lemma truncate_loop_cond_impl_hnr[sepref_fr_rules]:
  "(truncate_loop_cond_impl, RETURN o (PR_CONST truncate_loop_cond)) \<in>
    truncate_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using truncate_loop_cond_impl.refine
  by (simp add: truncate_loop_cond_mop_monadic_eq PR_CONST_def)

definition truncate_loop_body_checked_monadic ::
  "truncate_state \<Rightarrow> truncate_state nres" where
"truncate_loop_body_checked_monadic S \<equiv>
  (if (PR_CONST truncate_loop_cond) S then
    (PR_CONST truncate_loop_step_monadic) S
   else RETURN S)"

sepref_register "PR_CONST truncate_loop_body_checked_monadic"
  :: "truncate_state \<Rightarrow> truncate_state nres"

sepref_definition truncate_loop_body_checked_impl [llvm_code] is
  "truncate_loop_body_checked_monadic" ::
  "truncate_state_assn\<^sup>d \<rightarrow>\<^sub>a truncate_state_assn"
  unfolding truncate_loop_body_checked_monadic_def
  supply [sepref_fr_rules] =
    truncate_loop_cond_impl_hnr
    truncate_loop_step_impl_hnr
  by sepref

lemma truncate_loop_body_checked_impl_hnr[sepref_fr_rules]:
  "(truncate_loop_body_checked_impl,
    PR_CONST truncate_loop_body_checked_monadic) \<in>
    truncate_state_assn\<^sup>d \<rightarrow>\<^sub>a truncate_state_assn"
  using truncate_loop_body_checked_impl.refine
  by (simp add: PR_CONST_def)

definition truncate_loop_stateful_monadic ::
  "truncate_state \<Rightarrow> truncate_state nres" where
"truncate_loop_stateful_monadic S0 \<equiv>
  WHILET
    (\<lambda>S. (PR_CONST truncate_loop_cond) S)
    (\<lambda>S. (PR_CONST truncate_loop_body_checked_monadic) S)
    S0"

sepref_register "PR_CONST truncate_loop_stateful_monadic"
  :: "truncate_state \<Rightarrow> truncate_state nres"

sepref_definition truncate_loop_stateful_impl [llvm_code] is
  "truncate_loop_stateful_monadic" ::
  "truncate_state_assn\<^sup>d \<rightarrow>\<^sub>a truncate_state_assn"
  unfolding truncate_loop_stateful_monadic_def
  supply [sepref_fr_rules] =
    truncate_loop_cond_impl_hnr
    truncate_loop_body_checked_impl_hnr
  by sepref_dbg_keep

lemma truncate_loop_stateful_impl_hnr[sepref_fr_rules]:
  "(truncate_loop_stateful_impl, PR_CONST truncate_loop_stateful_monadic) \<in>
    truncate_state_assn\<^sup>d \<rightarrow>\<^sub>a truncate_state_assn"
  using truncate_loop_stateful_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Outer curried wrapper — clone of the bisection solver's
  \<open>bisection_loop_monadic\<close>/\<open>bisection_loop_stateful_monadic\<close> split
  (\<open>Bisection.thy\<close>): takes \<open>todo qtodo gs acc rp\<close> SEPARATELY (avoiding
  the same inline-tuple-into-call trap at the CALLER's side, i.e. \<open>main_list\<close>) and
  builds the bundled state ONCE, internally, to call the stateful WHILET wrapper.\<close>
definition truncate_loop_monadic ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
    gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres" where
"truncate_loop_monadic todo qtodo gs acc rp \<equiv> doN {
  (PR_CONST truncate_loop_stateful_monadic) ((todo, qtodo, gs, rp), acc)
}"

sepref_register "PR_CONST truncate_loop_monadic"
  :: "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
      gmp_dyadic_interval_vec \<Rightarrow> gmp_poly \<Rightarrow> truncate_state nres"

sepref_definition truncate_loop_impl [llvm_code] is
  "uncurry4 truncate_loop_monadic" ::
  "gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
    gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
    truncate_state_assn"
  unfolding truncate_loop_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma truncate_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry4 truncate_loop_impl, uncurry4 (PR_CONST truncate_loop_monadic)) \<in>
    gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_vec_assn\<^sup>d *\<^sub>a
      gmp_dyadic_exp_list_assn\<^sup>d *\<^sub>a
      gmp_dyadic_interval_vec_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>\<^sub>a
      truncate_state_assn"
  using truncate_loop_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Main list: initialize the worklist (root pushed BOTH as node 0 and kept as \<open>rp\<close>)\<close>

text \<open>Clone of @{const bisection_main_list} (\<open>Bisection.thy-1331\<close>): the input
  poly \<open>P\<close> is pushed once as the initial worklist node (guard \<open>0\<close> — never truncated yet)
  AND copied once more as the kept root \<open>rp\<close> for escalation. \<open>rp\<close> is freed at the very
  end, alongside the now-empty \<open>qtodo\<close>/\<open>todo\<close>.\<close>
text \<open>\<open>rp\<close>, the escalation anchor, is the original input polynomial in global coordinates. Seeding it
  from the carried-initialised root (in root-local \<open>[0,1]\<close> coordinates) would make every escalation
  compose two coordinate systems. The root node polynomial \<open>q0\<close> and the anchor \<open>rp\<close> are both built by
  the wrapper and passed separately: \<open>q0 = carried_init(input)\<close> runs directly on the caller's borrowed
  array, so the input is not copied twice through the \<open>O(deg\<^sup>2)\<close> initialisation.\<close>
definition truncate_main_list ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_dyadic_interval_vec nres" where
"truncate_main_list l_num r_num k q0 rp \<equiv> doN {
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
  ASSERT (0 < length q0);
  ASSERT (length q0 + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (0 < length rp);
  ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
  qtodo0 \<leftarrow> (PR_CONST poly_vec_empty_sz_monadic) 1;
  ASSERT (length qtodo0 + 1 < max_snat LENGTH(gmp_poly_len));
  qtodo1 \<leftarrow> (PR_CONST poly_vec_push_monadic) qtodo0 q0;
  let gs0 = (op_al_empty TYPE(gmp_poly_len) :: nat list);
  ASSERT (length gs0 + 1 < max_snat LENGTH(gmp_poly_len));
  gs1 \<leftarrow> mop_list_append gs0 (0::nat);
  acc0 \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 1;
  S \<leftarrow> (PR_CONST truncate_loop_monadic) todo1 qtodo1 gs1 acc0 rp;
  let ((todo, qtodo, gs, rpx), acc) = S;
  ASSERT (qtodo = []);
  (PR_CONST poly_vec_free_empty_monadic) qtodo;
  (PR_CONST dyadic_interval_vec_free_monadic) todo;
  (PR_CONST poly_free_monadic) rpx;
  RETURN acc
}"

sepref_register "PR_CONST truncate_main_list"
  :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow>
      gmp_dyadic_interval_vec nres"

sepref_definition truncate_main_list_impl [llvm_code] is
  "uncurry4 truncate_main_list" ::
  "[\<lambda>((((_, _), k), q0), rp).
      0 < length q0 \<and>
      length q0 + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  unfolding truncate_main_list_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [simp] =
    truncate_loop_cond_def
    dyadic_interval_vec_invar_def
    dyadic_interval_vec_pushable_def
    dyadic_interval_vec_pushable2_def
  supply [sepref_fr_rules] =
    truncate_loop_impl_hnr
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

lemma truncate_main_list_impl_hnr[sepref_fr_rules]:
  "(uncurry4 truncate_main_list_impl,
    uncurry4 (PR_CONST truncate_main_list)) \<in>
    [\<lambda>((((_, _), k), q0), rp).
      0 < length q0 \<and>
      length q0 + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_dyadic_interval_vec_assn"
  using truncate_main_list_impl.refine
  by (simp add: PR_CONST_def)

(*FASTLOOP_FREEZE_ABOVE*)


end
