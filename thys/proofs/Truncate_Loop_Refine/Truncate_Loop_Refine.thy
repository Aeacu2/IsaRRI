theory Truncate_Loop_Refine
  imports
    IsaRRI_LLVM.Truncate_Solver
    IsaRRI_LLVM.Bisection_Refine
begin

text \<open>The loop-level keystone for the truncating solver.

  \<^bold>\<open>Goal\<close>: the truncating solver's program @{const truncate_main_list} refines the bisection solver's program
  @{const bisection_main_list}: \<open>truncate_main_list l r k q0 rp \<le> \<Down>Id (bisection_main_list l r k P)\<close> under the
  seeding hypotheses. So the two solvers return identical output.

  \<^bold>\<open>Approach.\<close> \<open>bisection_loop_step_monadic\<close>/\<open>bisection_loop_monadic\<close>/\<open>bisection_loop_cond\<close>/\<open>bisection_main_list\<close>,
  the bisection solver's programs before Sepref, are defined in \<open>Bisection\<close>, which this theory imports, so the
  truncating program is refined directly to the bisection program rather than to a pure model. The bisection
  solver's own correctness (\<open>bisection_main_list \<le> dsc_int\<close>, proved in \<open>Bisection_Loop_Refine\<close>) is used as a premise
  of the final capstone.

  \<^bold>\<open>Structure\<close> (a relational simulation over the two loops):
  \<^item> The truncating loop state is \<open>truncate_state\<close> = \<open>((todo,qtodo,gs,rp),acc)\<close>; the bisection loop state is
    \<open>bisection_loop_state\<close> = \<open>((todo,qtodo),acc)\<close>. The coupling \<open>truncate_state_rel\<close> keeps \<open>todo\<close> and \<open>acc\<close> identical and
    relates each truncated worklist polynomial \<open>dqtodo!i\<close> (guard \<open>gs!i\<close>) to the exact one \<open>pqtodo!i\<close> by
    @{const node_frame}.
  \<^item> @{text truncate_loop_step_refine}: one truncating step simulates one bisection step under the coupling. The
    guarded count agrees with the exact count when decisive
    (@{thm [source] carried_descartes_count_g_monadic_classify}); otherwise escalation rebuilds the exact
    polynomial (@{thm [source] carried_escalate_exact_monadic_correct}) and the count then agrees; the
    re-truncated children frame-refine the exact children (@{thm [source] carried_retrunc_mop_frame}). The same
    branch is taken, so the same \<open>acc\<close> is appended.
  \<^item> @{text truncate_loop_refine}: lifts the step refinement to the whole \<open>WHILEIT\<close>.
  \<^item> @{text truncate_main_list_refine}: the wrapper refinement.
  \<^item> @{text truncate_main_list_mset_dsc_int}: composes the wrapper refinement with the bisection solver's
    correctness to conclude that the output multiset equals @{term "dsc_int"}.\<close>

section \<open>The coupling relation between the dense and plain loop states\<close>

text \<open>Per-worklist-node coupling: the dense node poly \<open>dq\<close> with guard \<open>g\<close> is a
  @{const node_frame} stand-in for the exact plain node poly \<open>pq\<close>. (\<open>g = 0\<close> forces
  \<open>pq = dq\<close> — exact; \<open>g \<ge> 1\<close> allows the one-sided truncation slack the guards track.)\<close>
definition truncate_node_rel :: "((gmp_poly \<times> nat) \<times> gmp_poly) set" where
  "truncate_node_rel = {((dq, g), pq) | dq g pq. node_frame pq dq g}"

text \<open>The two worklists run in lockstep: identical \<open>todo\<close> interval vector, the truncating \<open>qtodo\<close>/\<open>gs\<close>
  columns refine the exact \<open>qtodo\<close> pointwise by @{const node_frame}, and the accumulator \<open>acc\<close> is identical.

  The relation is parameterised by the root \<open>P\<close> (\<open>rp\<close>'s intended value) and also requires every exact worklist
  entry to equal its recomputation from the root, \<open>carried_init_same_den l (2^k) r P\<close>, at its own triple \<open>(l,r,k)\<close>
  (the \<open>i\<close>-th columns of \<open>ptodo = (lns,rns,ks)\<close>). This is the invariant escalation needs: it identifies the output
  of \<open>carried_escalate_keep_monadic_correct\<close> with the true node polynomial for whichever triple was popped.
  Maintaining it across a split uses @{text carried_left_right_reconstruct}.\<close>
text \<open>The EXACT-LOCK sentinel (\<open>Truncate_Solver.thy\<close>'s \<open>4398046511104 = 2^42\<close>): once a
  node's guard reaches it, every dense op (retrunc, children) treats the poly as exact and
  never truncates it again (\<open>carried_retrunc_mop\<close>'s \<open>g \<ge> 2^42\<close> branch is a literal no-op).
  This is NOT implied by @{const node_frame} at a nonzero guard (\<open>gframe\<close> only asserts
  SOME error bound, not zero error) — it is a genuinely separate invariant the lock design
  relies on, needed by the mid-test's \<open>g \<ge> EXACT_LOCK\<close> branch (which reuses the plain exact
  mid test verbatim, sound only because the dense poly IS the exact one at that point).\<close>
definition truncate_state_rel :: "gmp_poly \<Rightarrow> (truncate_state \<times> bisection_loop_state) set" where
  "truncate_state_rel P =
     {(((dtodo, dqtodo, gs, rp), dacc), ((ptodo, pqtodo), pacc)) |
        dtodo dqtodo gs rp dacc ptodo pqtodo pacc.
        dtodo = ptodo \<and> dacc = pacc \<and> rp = P \<and>
        length dqtodo = length pqtodo \<and> length gs = length pqtodo \<and>
        (case ptodo of (lns, rns, ks) \<Rightarrow>
           length lns = length pqtodo \<and> length rns = length pqtodo \<and>
             length ks = length pqtodo \<and>
           (\<forall>i < length pqtodo.
              pqtodo ! i = carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) P)) \<and>
        (\<forall>i < length pqtodo. node_frame (pqtodo ! i) (dqtodo ! i) (gs ! i)) \<and>
        (\<forall>i < length pqtodo. 4398046511104 \<le> gs ! i \<longrightarrow> dqtodo ! i = pqtodo ! i) \<and>
        (\<forall>i < length pqtodo. gs ! i \<le> 4398046511104)}"

text \<open>An introduction rule for @{const truncate_state_rel}, proved once in a small context. Discharging a
  \<open>\<in> truncate_state_rel P\<close> goal with \<open>blast\<close>/\<open>auto\<close> inside the keystone's large context re-searches every hypothesis
  for the existential witnesses; applying this rule is a single unification.\<close>
lemma truncate_state_relI:
  assumes "dtodo = ptodo" and "dacc = pacc" and "rp = P"
    and "length dqtodo = length pqtodo" and "length gs = length pqtodo"
    and "case ptodo of (lns, rns, ks) \<Rightarrow>
           length lns = length pqtodo \<and> length rns = length pqtodo \<and>
             length ks = length pqtodo \<and>
           (\<forall>i < length pqtodo.
              pqtodo ! i = carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) P)"
    and "\<forall>i < length pqtodo. node_frame (pqtodo ! i) (dqtodo ! i) (gs ! i)"
    and "\<forall>i < length pqtodo. 4398046511104 \<le> gs ! i \<longrightarrow> dqtodo ! i = pqtodo ! i"
    and "\<forall>i < length pqtodo. gs ! i \<le> 4398046511104"
  shows "(((dtodo, dqtodo, gs, rp), dacc), ((ptodo, pqtodo), pacc)) \<in> truncate_state_rel P"
  using assms unfolding truncate_state_rel_def by blast

text \<open>The bisection/recompute agreement (@{thm [source] carried_left_right_reconstruct}, with its halves
  @{thm [source] carried_init_child_left} / @{thm [source] carried_init_child_right}) is in \<open>Bisection_Refine\<close>.\<close>

section \<open>Escalation reconstructs exactly (the \<open>_keep\<close> op-lemma, mechanical)\<close>

text \<open>@{const carried_escalate_keep_monadic} is byte-for-byte @{const carried_escalate_exact_monadic}
  except it also returns the borrowed root \<open>rp\<close> back (\<open>RETURN (qx, rp)\<close> vs plain \<open>RETURN qx\<close>);
  its correctness is the same @{thm [source] carried_init_inplace_monadic_correct} composition
  the exact variant already uses (\<open>Truncate.thy\<close>), just re-packaged. This is
  purely mechanical — no node/output-frame geometry needed, unlike the fact below.\<close>
lemma carried_escalate_keep_monadic_correct:
  assumes "0 < length rp"
    and "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "carried_escalate_keep_monadic rp l r k qt
       \<le> RETURN (carried_init_same_den l (2 ^ k) r rp, rp)"
  unfolding carried_escalate_keep_monadic_def PR_CONST_def
  apply (refine_vcg carried_init_inplace_monadic_correct[THEN order_trans])
  using assms by auto

section \<open>The count-classification agrees with the plain bisection solver's own pop-count\<close>

text \<open>The dense guarded/escalated count classifies EXACTLY as the plain bisection solver's own
  @{const carried_descartes_count_trunc_monadic} on the SAME node poly \<open>X = carried_init_same_den
  l (2^k) r P\<close> — the plain node's own poly, per \<open>truncate_state_rel\<close>'s recompute-invariant.
  Decisive case: @{thm [source] carried_descartes_count_g_monadic_classify} classifies
  the guarded count against exact \<open>carried_descartes_count X\<close>, and
  @{thm [source] carried_descartes_count_trunc_monadic_classify} (unconditional)
  classifies the plain branch's own truncated count against the SAME exact
  \<open>carried_descartes_count X\<close> — transitively they agree, without needing the same
  literal count value or return the SAME \<open>node_frame\<close>-coupled node (\<open>g\<close> unchanged).
  Ambiguous case: escalation's output is LITERALLY \<open>X\<close> (@{thm [source]
  carried_escalate_keep_monadic_correct}), so \<open>node_frame X X 0\<close> (@{thm [source]
  node_frame_exact}) and the dense branch's subsequent
  \<open>carried_descartes_count_trunc_monadic X\<close> is LITERALLY the plain branch's own call.\<close>
text \<open>@{const carried_init_same_den} preserves length (each of its three list transforms —
  @{const scale_for_fractional_shift}, @{const taylor_shift_list}, @{const scale_poly_list}
  — does, by the reachable @{thm [source] Dsc_Int.length_scale_for_fractional_shift},
  @{thm [source] Dsc_Taylor.length_taylor_shift_list},
  @{thm [source] Dsc_Taylor.length_scale_poly_list}).\<close>
lemma truncate_length_carried_init_same_den:
  "length (carried_init_same_den l d r P) = length P"
  unfolding carried_init_same_den_def
  by (simp add: Dsc_Taylor.length_scale_poly_list Dsc_Taylor.length_taylor_shift_list
      Dsc_Int.length_scale_for_fractional_shift)

text \<open>@{const node_frame} holds reflexively at ANY guard, not just \<open>g = 0\<close> (\<open>gframe\<close>'s
  \<open>s = 0\<close> witness makes the per-coefficient error term literally \<open>0\<close>, trivially inside
  \<open>[0, 2^g)\<close>). Needed for the escalation case, whose reset guard is the huge EXACT-LOCK
  sentinel, not \<open>0\<close>.\<close>
lemma node_frame_exact_any_g: "node_frame X X g"
  unfolding node_frame_def gframe_def
  by (cases "g = 0") (auto intro!: exI[of _ 0])

lemma truncate_count_escalate_agrees:
  fixes l r :: int and k :: nat and P :: gmp_poly
  defines "X \<equiv> carried_init_same_den l (2 ^ k) r P"
  assumes frame: "node_frame X Q g"
    and rp_eq: "rp = P"
    and lbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length Q * nat_bitlen (length Q) < max_snat LENGTH(gmp_poly_len)"
    and gbound: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and lock: "4398046511104 \<le> g \<longrightarrow> X = Q"
    and g_le: "g \<le> 4398046511104"
    and rpbound1: "0 < length P"
    and rpbound2: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and rpbound3: "k * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_count_escalate_monadic Q g l r k rp \<le> SPEC (\<lambda>(cnt, Q', g', rp').
           rp' = P \<and> node_frame X Q' g' \<and>
           g' \<le> 4398046511104 \<and> (4398046511104 \<le> g' \<longrightarrow> Q' = X) \<and>
           (cnt = 0) = (carried_descartes_count X = 0) \<and>
           (cnt = 1) = (carried_descartes_count X = 1) \<and>
           (2 \<le> cnt) = (2 \<le> carried_descartes_count X))"
  unfolding truncate_count_escalate_monadic_def PR_CONST_def rp_eq
  apply (refine_vcg carried_descartes_count_g_monadic_classify[
        of X Q g, THEN order_trans, unfolded X_def[symmetric]])
  subgoal using frame unfolding X_def by simp
  subgoal using lbound by simp
  subgoal using pbound by simp
  subgoal using gbound by simp
  subgoal using lock unfolding X_def by simp
  apply (all \<open>(use lock g_le in \<open>clarsimp simp: frame\<close>)?\<close>)
  apply (clarsimp simp: X_def)
  apply (refine_vcg carried_escalate_keep_monadic_correct[
        where rp = P and l = l and r = r and k = k and qt = Q, THEN order_trans])
  subgoal using rpbound1 by simp
  subgoal using rpbound2 by simp
  subgoal using rpbound3 by simp
  subgoal using rpbound2 by (clarsimp simp: truncate_length_carried_init_same_den)
  apply clarsimp
  apply (refine_vcg carried_descartes_count_trunc_monadic_classify[
        of "carried_init_same_den l (2 ^ k) r P", THEN order_trans])
  subgoal using rpbound2 by (clarsimp simp: X_def truncate_length_carried_init_same_den)
  apply (all \<open>clarsimp simp: X_def node_frame_exact_any_g\<close>)
  done

text \<open>The productivity combinators for \<open>Ex (inres \<dots>)\<close> (\<open>cdlr_ex_inres_RETURN\<close>/\<open>_ASSERT\<close>/\<open>_bind\<close>/
  \<open>_nfoldli\<close>) and @{thm [source] poly_free_monadic_ex_inres} / @{thm [source] poly_free_monadic_eq_RETURN} are in
  \<open>Array\<close>, next to @{thm [source] poly_free_monadic_nofail}; they are used below for the productivity proofs of
  WHILET, \<open>if\<close> and \<open>case_prod\<close>.\<close>

section \<open>The zero/one branches agree (pure bookkeeping, no geometry)\<close>

text \<open>@{const truncate_branch_zero_monadic}/@{const bisection_branch_zero_monadic} only
  discard two borrowed scalars and free the popped poly (both @{thm [source]
  mpzb_discard_monadic_def} and @{thm [source] poly_free_monadic_rule} are
  \<open>\<le> SPEC (\<lambda>_. True)\<close> at the abstract nres level) before returning the UNCHANGED
  remaining \<open>todo\<close>/\<open>qtodo\<close>/\<open>acc\<close> — so whatever coupling held before the branch call holds
  after it, verbatim. The popped node polys \<open>Q\<close>/\<open>Q'\<close> need not even be related — they are
  discarded, not returned.\<close>
lemma truncate_branch_zero_agrees:
  assumes rel: "(((todo, dqtodo, gs, rp), acc), ((todo, pqtodo), acc)) \<in> truncate_state_rel P"
  shows "truncate_branch_zero_monadic todo dqtodo gs acc rp l_num r_num k Q
       \<le> \<Down> (truncate_state_rel P) (bisection_branch_zero_monadic todo pqtodo acc l_num r_num k Q')"
  unfolding truncate_branch_zero_monadic_def bisection_branch_zero_monadic_def
    PR_CONST_def mpzb_discard_monadic_def
  using rel by simp

text \<open>@{const truncate_branch_one_monadic}/@{const bisection_branch_one_monadic} push the
  SAME output triple \<open>(l_num,r_num,k)\<close> onto the SAME \<open>acc\<close> columns (both call the identical
  @{const poly_push_coeff_monadic}/\<open>mop_list_append\<close> ops on the identical \<open>acc\<close>, which by
  \<open>rel\<close> is literally the same value on both sides) and otherwise leave \<open>todo\<close>/\<open>qtodo\<close>/\<open>gs\<close>
  untouched — so the coupling is preserved with the new \<open>acc\<close> value threaded through
  identically on both sides (\<open>truncate_state_rel\<close> only constrains \<open>acc\<close> by equality, so ANY
  new value both sides compute together, including this pushed one, keeps the relation).\<close>
lemma truncate_branch_one_agrees:
  assumes rel: "(((todo, dqtodo, gs, rp), acc), ((todo, pqtodo), acc)) \<in> truncate_state_rel P"
    and push_pre: "dyadic_interval_vec_pushable acc"
  shows "truncate_branch_one_monadic todo dqtodo gs acc rp l_num r_num k Q
       \<le> \<Down> (truncate_state_rel P) (bisection_branch_one_monadic todo pqtodo acc l_num r_num k Q')"
  unfolding truncate_branch_one_monadic_def bisection_branch_one_monadic_def PR_CONST_def
  apply (cases acc)
  using rel push_pre
  apply (clarsimp simp: truncate_state_rel_def)
  apply (refine_vcg)
  by (clarsimp simp: truncate_state_rel_def)

section \<open>The loop-step keystone\<close>

text \<open>The heart of the verification: one dense loop step simulates one plain loop step
  under the coupling \<open>truncate_state_rel P\<close>.

  Proof outline: both steps pop the shared LAST \<open>todo\<close> entry (same \<open>todo\<close> column)
  together with the corresponding LAST \<open>qtodo\<close>/\<open>gs\<close> resp.\ \<open>qtodo\<close> entry (coupled by
  @{const node_frame} via the relation's last-index instance, whose plain side is, by the
  relation's OWN recompute-invariant, exactly
  \<open>carried_init_same_den l_num (2^k) r_num P\<close> for the popped triple \<open>(l_num,r_num,k)\<close>).
  The count then classifies via TWO chained facts: (1) decisive case —
  @{thm [source] carried_descartes_count_g_monadic_classify} classifies the guarded count
  against the exact @{const carried_descartes_count} X, and
  @{thm [source] carried_descartes_count_trunc_monadic_classify} (unconditionally)
  classifies the PLAIN branch's own \<open>carried_descartes_count_trunc_monadic\<close> against the
  SAME exact count X — hence, transitively, the two programs' branch decisions agree
  without needing them to compute the same literal count value; (2) ambiguous case —
  escalate via @{thm [source] carried_escalate_keep_monadic_correct}, whose output is
  LITERALLY \<open>carried_init_same_den l_num (2^k) r_num P\<close> — by the relation's invariant this
  IS the plain node's own poly, so \<open>g\<close> resets to \<open>0\<close> (\<open>node_frame\<close> becomes literal
  equality) and the dense branch's subsequent \<open>carried_descartes_count_trunc_monadic qx\<close>
  is LITERALLY the plain branch's own call on the same input — trivial agreement. Either
  way the SAME branch (zero / one / split) fires, appending the SAME \<open>acc\<close> entry via the
  SAME output triple; the retruncated children re-establish @{const node_frame}
  (@{thm [source] carried_retrunc_mop_frame}), and re-establishing the SPLIT children's
  recompute-invariant is exactly where @{thm [source] carried_left_right_reconstruct} (the
  one external fact) is invoked.\<close>
text \<open>The layer BELOW the pop: once the shared \<open>todo\<close> triple \<open>(l_num,r_num,k)\<close> is popped
  (both sides pop the identical \<open>dyadic_interval_vec_pop_last_monadic\<close> call on the SAME
  \<open>todo\<close>, so this is a pure \<open>\<Down>Id\<close> step, discharged in the keystone below via
  @{thm [source] dyadic_interval_vec_pop_last_monadic_spec}), agreement continues one layer
  down through @{const truncate_pop_poly_args_monadic} vs
  @{const bisection_pop_poly_args_monadic}. This is where the REST of the branch dispatch
  (count-escalate agreement + zero/one/split) plugs in — kept as its own lemma so the
  keystone's own proof (which reduces to exactly this obligation) is complete and real.\<close>
text \<open>This lemma takes no \<open>truncate_state_rel P\<close> premise on \<open>todo\<close>: at this layer \<open>todo\<close> has already been popped while
  \<open>qtodo\<close>/\<open>pqtodo\<close> have not (their pop happens inside @{const truncate_pop_poly_args_monadic}/
  @{const bisection_pop_poly_args_monadic}), so \<open>length todo = length pqtodo\<close> is off by one here. \<open>todo\<close> passes through
  unchanged on both sides, so only the columns this layer touches (\<open>qtodo\<close>/\<open>gs\<close>/\<open>acc\<close>/\<open>rp\<close>) need the coupling.\<close>

section \<open>The tight right-child guard bound (SOUNDNESS of the \<open>g+len\<close> formula)\<close>

text \<open>\<open>truncate_child_guards_mop\<close> gives the right child the guard \<open>g+len\<close>, tighter than
  @{thm [source] node_frame_child_right}'s \<open>g+(2*len-1)\<close> (via \<open>gframe_bisect_right\<close>). \<open>g+len\<close> is also a valid bound:
  \<open>gframe_bisect_right\<close> bounds each binomial-weighted term by \<open>2^(s+g+len-1)\<close> and sums \<open>len\<close> of them, whereas the
  tight route needs the exact partial-sum identity below (a closed form proved by Pascal's rule,
  \<open>binomial_Suc_Suc\<close>).\<close>
text \<open>Pascal's rule lifted to PARTIAL row sums, in purely ADDITIVE form (no \<open>nat\<close>
  subtraction anywhere — subtraction on \<open>nat\<close> truncates, and every earlier attempt at
  this lemma that used it produced an unverifiable gap). Induction on \<open>i\<close> alone, \<open>n\<close>
  held fixed; each step only ADDS the next binomial term to both sides.\<close>
lemma pascal_partial_sum:
  "(\<Sum>j \<le> i. Suc n choose j) + (n choose i) = 2 * (\<Sum>j \<le> i. n choose j)"
proof (induction i)
  case 0
  show ?case by simp
next
  case (Suc i)
  have "(\<Sum>j \<le> Suc i. Suc n choose j) + (n choose Suc i)
      = ((\<Sum>j \<le> i. Suc n choose j) + (Suc n choose Suc i)) + (n choose Suc i)"
    by simp
  also have "\<dots> = ((\<Sum>j \<le> i. Suc n choose j) + (n choose i)) + 2 * (n choose Suc i)"
    by (simp add: binomial_Suc_Suc)
  also have "\<dots> = 2 * (\<Sum>j \<le> i. n choose j) + 2 * (n choose Suc i)"
    by (simp add: Suc.IH)
  also have "\<dots> = 2 * (\<Sum>j \<le> Suc i. n choose j)"
    by simp
  finally show ?case .
qed

lemma binom_partial_sum_id:
  fixes i n :: nat
  assumes "i < n"
  shows "(\<Sum>t = i..<n. (t choose i) * (2::nat) ^ (n - Suc t)) + (\<Sum>j \<le> i. n choose j) = 2 ^ n"
  using assms
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "i < n")
    case True
    have split: "{i..<Suc n} = insert n {i..<n}"
      using True by auto
    have pointwise: "\<And>t. t \<in> {i..<n} \<Longrightarrow>
        (t choose i) * (2::nat) ^ (Suc n - Suc t) = 2 * ((t choose i) * (2::nat) ^ (n - Suc t))"
    proof -
      fix t assume "t \<in> {i..<n}"
      hence e: "Suc n - Suc t = Suc (n - Suc t)" by auto
      show "(t choose i) * (2::nat) ^ (Suc n - Suc t)
          = 2 * ((t choose i) * (2::nat) ^ (n - Suc t))"
        unfolding e power_Suc by (simp only: mult_ac)
    qed
    have step: "(\<Sum>t = i..<Suc n. (t choose i) * (2::nat) ^ (Suc n - Suc t))
        = (n choose i) + 2 * (\<Sum>t = i..<n. (t choose i) * (2::nat) ^ (n - Suc t))"
    proof -
      have "(\<Sum>t = i..<Suc n. (t choose i) * (2::nat) ^ (Suc n - Suc t))
          = (n choose i) + (\<Sum>t = i..<n. (t choose i) * (2::nat) ^ (Suc n - Suc t))"
        unfolding split by (simp add: sum.insert_if)
      also have "(\<Sum>t = i..<n. (t choose i) * (2::nat) ^ (Suc n - Suc t))
          = (\<Sum>t = i..<n. 2 * ((t choose i) * (2::nat) ^ (n - Suc t)))"
        by (rule sum.cong[OF refl]) (rule pointwise)
      also have "\<dots> = 2 * (\<Sum>t = i..<n. (t choose i) * (2::nat) ^ (n - Suc t))"
        by (simp add: sum_distrib_left)
      finally show ?thesis .
    qed
    \<comment> \<open>The rest is LINEAR arithmetic over four shared atoms (the two sums, the two
       partial row sums): \<open>step\<close> rewrites the big sum, \<open>pascal\<close> trades the \<open>Suc n\<close> row
       for twice the \<open>n\<close> row, the IH supplies \<open>S + T = 2^n\<close>. Chained \<open>simp\<close> steps kept
       tripping over \<open>Suc\<close>-normal-form mismatches; \<open>linarith\<close> on the literal facts is
       normal-form-immune.\<close>
    have pw2: "(2::nat) ^ Suc n = 2 * 2 ^ n" by simp
    show ?thesis
      using step pascal_partial_sum[where i = i and n = n] Suc.IH[OF True] pw2 by linarith
  next
    case False
    with Suc.prems have i_eq: "i = n" by simp
    \<comment> \<open>At \<open>i = n\<close> the big sum is the single term \<open>C(n,n)\<cdot>2^0 = 1\<close>, and the partial row
       sum \<open>\<Sum>j\<le>n\<close> is the FULL \<open>Suc n\<close> row minus its last term \<open>C(Suc n, Suc n) = 1\<close>.\<close>
    have "(\<Sum>j \<le> n. Suc n choose j) + 1 = 2 ^ Suc n"
      using choose_row_sum[of "Suc n"] by simp
    then show ?thesis using i_eq by simp
  qed
qed

lemma binom_geom_sum_lt:
  fixes i n :: nat
  assumes "i < n"
  shows "(\<Sum>t = i..<n. (t choose i) * (2::nat) ^ (n - Suc t)) < 2 ^ n"
proof -
  have "(\<Sum>j \<le> i. n choose j) \<ge> n choose 0" by (rule member_le_sum) auto
  hence "(\<Sum>j \<le> i. n choose j) \<ge> 1" by simp
  with binom_partial_sum_id[OF assms] show ?thesis by linarith
qed

text \<open>The impl's @{const carried_left} and the spec's @{const dilate_list} are the SAME
  function (the impl computes it via \<open>rev \<circ> scale \<circ> rev\<close>, the spec as an indexed map) —
  the bridge the spec's child-frame lemmas need to speak about the impl's children.\<close>
lemma carried_left_eq_dilate: "carried_left xs = dilate_list xs"
proof (rule nth_equalityI)
  show "length (carried_left xs) = length (dilate_list xs)"
    by (simp add: carried_left_def length_scale_poly_list
        scale_for_fractional_shift_eq_scale_poly_list)
  fix i assume "i < length (carried_left xs)"
  hence i: "i < length xs"
    by (simp add: carried_left_def length_scale_poly_list
        scale_for_fractional_shift_eq_scale_poly_list)
  have "carried_left xs ! i
      = scale_poly_list 2 (rev xs) ! (length xs - Suc i)"
    using i by (simp add: carried_left_def scale_for_fractional_shift_eq_scale_poly_list
        rev_nth length_scale_poly_list)
  also have "\<dots> = rev xs ! (length xs - Suc i) * 2 ^ (length xs - Suc i)"
    using i by (simp add: length_scale_poly_list)
  also have "\<dots> = xs ! i * 2 ^ (length xs - Suc i)"
    using i by (simp add: rev_nth)
  finally show "carried_left xs ! i = dilate_list xs ! i"
    using i by (simp add: dilate_list_def)
qed

text \<open>THE TIGHT RIGHT-CHILD FRAME (the fact @{const truncate_child_guards_mop}'s
  \<open>g+len\<close> formula needs; the existing @{thm [source] node_frame_child_right} only gives
  the loose \<open>g+(2len-1)\<close>). Integer-friendly route: each dilated per-coefficient error is
  \<open>\<le> 2^(len-1-t)\<cdot>(2^(s+g)-1)\<close>, the binomial-weighted sum of the \<open>2^(len-1-t)\<close> factors is
  \<open>\<le> 2^len - 1\<close> (@{thm [source] binom_geom_sum_lt}), and
  \<open>(2^len-1)\<cdot>(2^(s+g)-1) < 2^(s+g+len)\<close> strictly.\<close>
lemma gframe_carried_right_tight:
  assumes f: "gframe s g X Y"
  shows "gframe s (g + length Y) (carried_right X) (carried_right Y)"
proof -
  have lenXY: "length X = length Y" using f unfolding gframe_def by simp
  define n where "n = length Y"
  have lenX: "length X = n" and lenY: "length Y = n" using lenXY n_def by simp_all
  show ?thesis
  proof (cases "n = 0")
    case True
    hence "X = []" "Y = []" using lenX lenY by simp_all
    thus ?thesis
      by (simp add: carried_right_def carried_left_eq_dilate dilate_list_def gframe_def)
  next
    case False
    hence npos: "0 < n" by simp
    have dil_err: "\<And>t. t < n \<Longrightarrow>
        dilate_list X ! t - 2 ^ s * dilate_list Y ! t
          = 2 ^ (n - Suc t) * (X ! t - 2 ^ s * Y ! t)"
      by (simp add: dilate_list_def lenX lenY algebra_simps)
    have err_lb: "\<And>t. t < n \<Longrightarrow> 0 \<le> X ! t - 2 ^ s * Y ! t"
      and err_ub: "\<And>t. t < n \<Longrightarrow> X ! t - 2 ^ s * Y ! t < 2 ^ (s + g)"
      using f unfolding gframe_def lenY by auto
    have len_r: "length (carried_right Z) = length Z" for Z :: "int list"
      by (simp add: carried_right_def carried_left_eq_dilate dilate_list_def)
    show ?thesis
      unfolding gframe_def
    proof (intro conjI allI impI)
      show "length (carried_right X) = length (carried_right Y)"
        by (simp add: len_r lenX lenY)
      fix j assume "j < length (carried_right Y)"
      hence j: "j < n" by (simp add: len_r lenY)
      have nthX: "carried_right X ! j
          = (\<Sum>t = j..<n. int (t choose j) * dilate_list X ! t)"
        using j by (simp add: carried_right_def carried_left_eq_dilate
            taylor_shift_list_nth_binom dilate_list_def lenX)
      have nthY: "carried_right Y ! j
          = (\<Sum>t = j..<n. int (t choose j) * dilate_list Y ! t)"
        using j by (simp add: carried_right_def carried_left_eq_dilate
            taylor_shift_list_nth_binom dilate_list_def lenY)
      have E: "carried_right X ! j - 2 ^ s * carried_right Y ! j
          = (\<Sum>t = j..<n. int (t choose j) * (dilate_list X ! t - 2 ^ s * dilate_list Y ! t))"
        unfolding nthX nthY
        by (simp add: sum_distrib_left sum_subtractf algebra_simps)
      have term_lb: "\<And>t. t \<in> {j..<n} \<Longrightarrow>
          0 \<le> int (t choose j) * (dilate_list X ! t - 2 ^ s * dilate_list Y ! t)"
      proof -
        fix t assume "t \<in> {j..<n}"
        hence tn: "t < n" by simp
        have nn1: "(0::int) \<le> int (t choose j)" by simp
        have nn2: "(0::int) \<le> dilate_list X ! t - 2 ^ s * dilate_list Y ! t"
          unfolding dil_err[OF tn]
          by (rule mult_nonneg_nonneg[OF _ err_lb[OF tn]]) simp
        from mult_nonneg_nonneg[OF nn1 nn2]
        show "0 \<le> int (t choose j) * (dilate_list X ! t - 2 ^ s * dilate_list Y ! t)" .
      qed
      show "0 \<le> carried_right X ! j - 2 ^ s * carried_right Y ! j"
        unfolding E by (rule sum_nonneg) (rule term_lb)
      have term_ub: "\<And>t. t \<in> {j..<n} \<Longrightarrow>
          int (t choose j) * (dilate_list X ! t - 2 ^ s * dilate_list Y ! t)
            \<le> int (t choose j) * 2 ^ (n - Suc t) * (2 ^ (s + g) - 1)"
      proof -
        fix t assume t: "t \<in> {j..<n}"
        hence tn: "t < n" by simp
        have "X ! t - 2 ^ s * Y ! t \<le> 2 ^ (s + g) - 1"
          using err_ub[OF tn] by simp
        hence "dilate_list X ! t - 2 ^ s * dilate_list Y ! t
            \<le> 2 ^ (n - Suc t) * (2 ^ (s + g) - 1)"
          unfolding dil_err[OF tn]
          by (intro mult_left_mono) simp_all
        thus "int (t choose j) * (dilate_list X ! t - 2 ^ s * dilate_list Y ! t)
            \<le> int (t choose j) * 2 ^ (n - Suc t) * (2 ^ (s + g) - 1)"
          by (simp add: mult.assoc mult_left_mono)
      qed
      have sum_ub: "(\<Sum>t = j..<n. int (t choose j) * 2 ^ (n - Suc t)) \<le> 2 ^ n - 1"
      proof -
        have nat_lt: "(\<Sum>t = j..<n. (t choose j) * 2 ^ (n - Suc t)) < 2 ^ n"
          using binom_geom_sum_lt[of j n] j by simp
        have cast: "(\<Sum>t = j..<n. int (t choose j) * 2 ^ (n - Suc t))
            = int (\<Sum>t = j..<n. (t choose j) * 2 ^ (n - Suc t))"
          by (simp add: of_nat_sum)
        have suc_le: "Suc (\<Sum>t = j..<n. (t choose j) * 2 ^ (n - Suc t)) \<le> 2 ^ n"
          using nat_lt by simp
        have "int (Suc (\<Sum>t = j..<n. (t choose j) * 2 ^ (n - Suc t))) \<le> int (2 ^ n)"
          using suc_le by (simp only: of_nat_le_iff)
        thus ?thesis
          unfolding cast by simp
      qed
      have pos_fac: "(0::int) \<le> 2 ^ (s + g) - 1" by simp
      have "carried_right X ! j - 2 ^ s * carried_right Y ! j
          \<le> (\<Sum>t = j..<n. int (t choose j) * 2 ^ (n - Suc t) * (2 ^ (s + g) - 1))"
        unfolding E by (rule sum_mono) (rule term_ub)
      also have "\<dots> = (\<Sum>t = j..<n. int (t choose j) * 2 ^ (n - Suc t)) * (2 ^ (s + g) - 1)"
        by (simp add: sum_distrib_right)
      also have "\<dots> \<le> (2 ^ n - 1) * (2 ^ (s + g) - 1)"
        using sum_ub pos_fac by (intro mult_right_mono) simp_all
      also have "\<dots> < 2 ^ (s + (g + n))"
      proof -
        have "(2 ^ n - 1) * ((2::int) ^ (s + g) - 1)
            = 2 ^ (n + (s + g)) - 2 ^ n - 2 ^ (s + g) + 1"
          by (simp add: algebra_simps power_add)
        also have "\<dots> < 2 ^ (n + (s + g))"
        proof -
          have p1: "(1::int) \<le> 2 ^ (s + g)" by simp
          have p2: "(1::int) \<le> 2 ^ n" by simp
          show ?thesis using p1 p2 by linarith
        qed
        also have "(2::int) ^ (n + (s + g)) = 2 ^ (s + (g + n))"
          by (simp add: add.commute add.left_commute)
        finally show ?thesis .
      qed
      finally show "carried_right X ! j - 2 ^ s * carried_right Y ! j
          < 2 ^ (s + (g + length Y))"
        by (simp add: lenY)
    qed
  qed
qed

text \<open>node_frame is MONOTONE in the guard (a larger guard is a weaker claim); needed to
  cover @{const truncate_child_guards_mop}'s clamp branches, which return \<open>2^41\<close>-style
  OVER-approximations of the exact child guards.\<close>
text \<open>@{const node_frame} version of @{thm [source] gframe_carried_right_tight}, matching
  @{thm [source] node_frame_child_left}'s shape but with the TIGHT \<open>g+len\<close> right guard
  (@{const carried_right} \<open>= taylor_shift_list 1 \<circ> dilate_list\<close> via
  @{thm [source] carried_right_def} and @{thm [source] carried_left_eq_dilate}, so no
  separate impl/spec bridging is needed).\<close>
lemma node_frame_child_right_tight:
  assumes "node_frame X Y g"
  shows "node_frame (carried_right X) (carried_right Y) (g + length Y)"
proof (cases "g = 0")
  case True
  hence XY: "X = Y" using assms unfolding node_frame_def by simp
  show ?thesis unfolding XY by (rule node_frame_exact_any_g)
next
  case False
  then obtain s where s: "gframe s g X Y" using assms unfolding node_frame_def by auto
  have "gframe s (g + length Y) (carried_right X) (carried_right Y)"
    using gframe_carried_right_tight[OF s] .
  thus ?thesis using False unfolding node_frame_def by auto
qed

text \<open>@{const carried_left}'s impl form of @{thm [source] node_frame_child_left}, via
  @{thm [source] carried_left_eq_dilate}: the LEFT guard @{const truncate_child_guards_mop}
  ships (\<open>g+(len-1)\<close>) is exactly @{const child_g_left} at \<open>g \<noteq> 0\<close>.\<close>
lemma node_frame_child_left_impl:
  assumes "node_frame X Y g" and "g \<noteq> 0"
  shows "node_frame (carried_left X) (carried_left Y) (g + (length Y - 1))"
  using node_frame_child_left[OF assms(1)] assms(2)
  by (simp add: carried_left_eq_dilate child_g_left_def)

lemma node_frame_mono:
  assumes "node_frame X Y g" and "g \<le> g'"
  shows "node_frame X Y g'"
proof (cases "g' = 0")
  case True
  with assms show ?thesis by (simp add: node_frame_def)
next
  case False
  show ?thesis
  proof (cases "g = 0")
    case True
    hence "X = Y" using assms unfolding node_frame_def by simp
    thus ?thesis using False
      unfolding node_frame_def gframe_def
      by (auto intro!: exI[of _ 0])
  next
    case False'': False
    then obtain s where s: "gframe s g X Y"
      using assms unfolding node_frame_def by auto
    have "gframe s g' X Y"
      using s assms(2) unfolding gframe_def
      by (auto elim!: order.strict_trans2 intro!: power_increasing)
    thus ?thesis using \<open>g' \<noteq> 0\<close> unfolding node_frame_def by auto
  qed
qed

text \<open>Guard-RANGE + lock-passthrough companion to @{thm [source] carried_retrunc_mop_frame}
  (which covers only \<open>node_frame\<close>): retruncation never RAISES a guard above the EXACT-LOCK
  sentinel (identity branches keep \<open>g\<close>; the truncating branch's reset returns \<open>1\<close> or
  \<open>g - t + 1 \<le> g\<close>), and a \<open>\<ge>\<close>-LOCK output can only come from a \<ge>-LOCK INPUT, whose branch
  returns the poly verbatim. Both facts are pure branch bookkeeping — no \<open>gframe\<close> content —
  so this is a separate, simpler lemma rather than a re-clone of the frame proof; callers
  conjoin the two SPECs via @{text cdlr_SPEC_conj} below.\<close>
lemma cdlr_retrunc_range:
  assumes gbound: "g \<le> 4398046511104"
  shows "carried_retrunc_mop xs g \<le> SPEC (\<lambda>(ys, g').
           g' \<le> 4398046511104 \<and>
           (4398046511104 \<le> g' \<longrightarrow> ys = xs \<and> 4398046511104 \<le> g))"
  unfolding carried_retrunc_mop_def poly_length_monadic_def
    retrunc_attempt_guard_mop_def retrunc_reset_mop_def trunc_gap_mop_def PR_CONST_def
  apply (refine_vcg poly_trunc_in_place_correct[THEN order_trans]
      lead_budget_mop_nofail[THEN order_trans])
  apply (all \<open>(simp; fail)?\<close>)
  using gbound by (auto simp: max_snat_def)

text \<open>Conjoin two \<open>\<le> SPEC\<close> facts about the same program (pointwise).\<close>
lemma cdlr_SPEC_conj:
  assumes "m \<le> SPEC \<Phi>" and "m \<le> SPEC \<Psi>"
  shows "m \<le> SPEC (\<lambda>x. \<Phi> x \<and> \<Psi> x)"
  using assms by (auto simp: pw_le_iff)

text \<open>The truncated-count threshold-cap arithmetic bound, discharged from the benign
  \<open>length P < 2\<^sup>4\<^sup>0\<close> input cap (\<open>P_small\<close>): \<open>nat_bitlen n \<le> 40\<close> for \<open>n < 2\<^sup>4\<^sup>0\<close> by
  @{thm [source] Least_le}, so the product is \<open>< 2\<^sup>4\<^sup>0 \<cdot> 40 < 2\<^sup>4\<^sup>6 \<ll> max_snat\<close>.\<close>
lemma cdlr_pbound_from_small:
  assumes "n < 1099511627776"
  shows "n * nat_bitlen n < max_snat LENGTH(gmp_poly_len)"
proof -
  have bl: "nat_bitlen n \<le> 40"
    unfolding nat_bitlen_def
    by (rule Least_le) (use assms in simp)
  have "n * nat_bitlen n \<le> n * 40" using bl by simp
  also have "\<dots> < 1099511627776 * 40" using assms by simp
  also have "\<dots> < max_snat LENGTH(gmp_poly_len)" unfolding max_snat_def by simp
  finally show ?thesis .
qed

lemma cdlr_length_carried_right[simp]:
  "length (carried_right Z) = length Z"
  by (simp add: carried_right_def carried_left_eq_dilate dilate_list_def)

subsection \<open>Plain-leaf PRODUCTIVITY (the \<open>\<noteq> RES {}\<close> facts \<Down>-refinement needs)\<close>

text \<open>Coupling a dense leaf against a DIFFERENT plain program under \<open>\<Down>R\<close> requires the
  plain side to actually PRODUCE a result — \<open>m \<le> RETURN v\<close> alone still allows the miracle
  \<open>RES {}\<close>, into which nothing refines (the same issue @{thm [source]
  poly_free_monadic_eq_RETURN} already solved for the free op). For the WHILET-based
  leaves we get the missing LOWER bound from the framework's own determinization
  machinery: \<open>refine_transfer\<close> synthesizes a plain HOL function \<open>f\<close> with
  \<open>RETURN (f x) \<le> prog x\<close> (ASSERTs erased, \<open>WHILET\<close> \<rightarrow> @{const while}), and antisym
  against the existing \<open>\<le> RETURN\<close> upper bound turns the leaf into a literal \<open>RETURN\<close>.\<close>

schematic_goal cdlr_half_eval_plain:
  "RETURN (?f xs) \<le> half_eval_zero_monadic xs"
  unfolding half_eval_zero_monadic_def poly_length_monadic_def
    poly_copy_coeff_monadic_def mpz_of_snat_monadic_def
    half_eval_body_mop_monadic_def half_eval_cond_def half_eval_finish_monadic_def
    mpz_shift_left_snat_monadic_def poly_acc_add_coeff_monadic_def
    mpzb_discard_monadic_def
    snat_sint_cast.mop_def snat_unat_cast.mop_def
    mpz_mul_2exp.amop_r1_def PR_CONST_def
  by refine_transfer

text \<open>The full leaf equality: productivity (above) + the proven upper bound + antisym.\<close>
lemma cdlr_half_eval_eq_RETURN:
  assumes ne: "0 < length xs"
    and lb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "half_eval_zero_monadic xs
       = RETURN (poly (map_poly rat_of_int (Poly xs)) (1 / 2) = 0)"
proof -
  obtain v where lo: "RETURN v \<le> half_eval_zero_monadic xs"
    using cdlr_half_eval_plain by blast
  have hi: "half_eval_zero_monadic xs
      \<le> RETURN (poly (map_poly rat_of_int (Poly xs)) (1 / 2) = 0)"
    using half_eval_zero_monadic_correct[OF ne lb] by simp
  have veq: "v = (poly (map_poly rat_of_int (Poly xs)) (1 / 2) = 0)"
    using order_trans[OF lo hi] by (auto simp: pw_le_iff)
  show ?thesis
    using lo hi unfolding veq by (rule order.antisym[rotated])
qed

lemma cdlr_mid_zero_eq_RETURN:
  assumes ne: "0 < length xs"
    and lb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_mid_zero_monadic xs
       = RETURN (poly (map_poly rat_of_int (Poly xs)) (1 / 2) = 0)"
  unfolding bisection_mid_zero_monadic_def PR_CONST_def
  by (rule cdlr_half_eval_eq_RETURN[OF ne lb])

text \<open>The remaining productivity combinators (extending the file's proven
  \<open>cdlr_ex_inres_*\<close> family): \<open>if\<close>, \<open>case_prod\<close>, satisfiable \<open>SPEC\<close>, and — the
  substantial one — \<open>WHILET\<close> along a wf measure. (The \<open>refine_transfer\<close> engine handled
  the plain \<open>WHILET\<close>-only @{const half_eval_zero_monadic} above, but chokes on the
  \<open>for\<close>/nfoldli-nested leaves with deep flex-applied continuations, so the loop-bearing
  leaves go through these combinators instead.)\<close>

lemma cdlr_ex_inres_if:
  assumes "c \<Longrightarrow> Ex (inres a)" and "\<not> c \<Longrightarrow> Ex (inres b)"
  shows "Ex (inres (if c then a else b))"
  using assms by (cases c) auto

lemma cdlr_ex_inres_case_prod:
  assumes "\<And>a b. st = (a, b) \<Longrightarrow> Ex (inres (f a b))"
  shows "Ex (inres (case_prod f st))"
  using assms by (cases st) auto

lemma cdlr_ex_inres_SPEC:
  assumes "\<Phi> x"
  shows "Ex (inres (SPEC \<Phi>))"
  using assms by (auto intro: exI[of _ x])

lemma cdlr_ex_inres_bitlen2:
  "Ex (inres (mpz_bitlen2_monadic m))"
proof (cases "m = 0")
  case True
  show ?thesis
    unfolding mpz_bitlen2_monadic_def
    by (rule cdlr_ex_inres_SPEC[of _ 1]) (simp add: True)
next
  case False
  have h1: "nat \<bar>m\<bar> < 2 ^ nat \<bar>m\<bar>" by (rule less_exp)
  have h3: "\<bar>m\<bar> < int (2 ^ nat \<bar>m\<bar>)"
    using h1 nat_less_iff[OF abs_ge_zero, of m "2 ^ nat \<bar>m\<bar>"] by blast
  have ex: "\<exists>b. \<bar>m\<bar> < 2 ^ b"
    using h3 by (intro exI[of _ "nat \<bar>m\<bar>"]) simp
  define r where "r \<equiv> LEAST b. \<bar>m\<bar> < 2 ^ b"
  have up: "\<bar>m\<bar> < 2 ^ r" unfolding r_def using LeastI_ex[OF ex] .
  have rpos: "0 < r"
  proof (rule ccontr)
    assume "\<not> 0 < r"
    hence "r = 0" by simp
    with up have "\<bar>m\<bar> < 1" by simp
    with False show False by simp
  qed
  have lo: "2 ^ (r - 1) \<le> \<bar>m\<bar>"
  proof (rule ccontr)
    assume "\<not> 2 ^ (r - 1) \<le> \<bar>m\<bar>"
    hence "\<bar>m\<bar> < 2 ^ (r - 1)" by simp
    hence "r \<le> r - 1" unfolding r_def by (rule Least_le)
    with rpos show False by simp
  qed
  \<comment> \<open>\<open>1 \<le> r\<close> is the first conjunct of the guarded specification; \<open>rpos\<close> supplies it as \<open>0 < r\<close>, which \<open>blast\<close>
     alone does not bridge, hence the explicit restatement. The remaining conjuncts come from \<open>lo\<close>, from \<open>False\<close>
     (the \<open>m = 0\<close> case is vacuous here), and from \<open>up\<close>, whose unconditional bound implies the \<open>size_t\<close>-guarded one.\<close>
  have rge1: "1 \<le> r" using rpos by simp
  show ?thesis
    unfolding mpz_bitlen2_monadic_def
    by (rule cdlr_ex_inres_SPEC[of _ r]) (use rge1 up lo False in blast)
qed

text \<open>WHILET productivity along a wf measure: if every reachable body application has a
  result and every (non-failing) body result strictly decreases the measure, the loop has
  a result — a terminating run ends in \<open>RETURN\<close>; a failing body or nontermination is FAIL,
  which contains EVERYTHING (\<open>not_nofail_inres\<close>), so only the miracle is excluded.\<close>
lemma cdlr_ex_inres_WHILET:
  assumes wf: "wf V"
    and step_ex: "\<And>s. c s \<Longrightarrow> Ex (inres (f s))"
    and step_dec: "\<And>s s'. c s \<Longrightarrow> nofail (f s) \<Longrightarrow> inres (f s) s' \<Longrightarrow> (s', s) \<in> V"
  shows "Ex (inres (WHILET c f s))"
proof (induction s rule: wf_induct_rule[OF wf])
  case (1 s)
  show ?case
  proof (cases "c s")
    case False
    hence "WHILET c f s = RETURN s" by (subst WHILET_unfold) simp
    thus ?thesis by (auto intro: exI[of _ s])
  next
    case True
    have unf: "WHILET c f s = f s \<bind> WHILET c f"
      by (subst WHILET_unfold) (simp add: True)
    show ?thesis
    proof (cases "nofail (f s)")
      case False
      hence "\<not> nofail (WHILET c f s)"
        unfolding unf by (auto simp: refine_pw_simps)
      thus ?thesis by (meson not_nofail_inres)
    next
      case nf: True
      obtain s' where s': "inres (f s) s'" using step_ex[OF True] by blast
      obtain w where w: "inres (WHILET c f s') w"
        using 1[OF step_dec[OF True nf s']] by blast
      have "inres (WHILET c f s) w"
        unfolding unf using nf s' w by (auto simp: refine_pw_simps)
      thus ?thesis by blast
    qed
  qed
qed

text \<open>Productivity of the plain bisection solver's children op (pure \<open>for\<close>-loops — the
  combinators cover it directly), then the leaf equality via nofail + productivity +
  the proven upper bound, exactly the @{thm [source] poly_free_monadic_eq_RETURN} recipe.\<close>
lemma cdlr_ex_inres_left_right:
  "Ex (inres (carried_left_right_monadic xs))"
  unfolding carried_left_right_monadic_def
    poly_shift_pow_in_place_monadic_def poly_shift_pow_loop_monadic_def
    poly_shift_coeff_monadic_def
    poly_copy_monadic_def poly_copy_loop_monadic_def poly_copy_coeff_monadic_def
    poly_empty_sz_monadic_def poly_push_coeff_monadic_def
    poly_taylor_shift_one_in_place_monadic_def poly_taylor_one_inner_loop_monadic_def
    poly_add_coeff_monadic_def
    poly_length_monadic_def mop_list_length_def mop_def o_def
    for_def PR_CONST_def Let_def
  by (intro cdlr_ex_inres_bind cdlr_ex_inres_nfoldli cdlr_ex_inres_if
      cdlr_ex_inres_case_prod cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN)

lemma cdlr_left_right_eq_RETURN:
  assumes ne: "0 < length xs"
    and lb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_left_right_monadic xs = RETURN (carried_left xs, carried_right xs)"
  using carried_left_right_monadic_correct[OF ne lb] cdlr_ex_inres_left_right[of xs]
  by (auto simp: pw_eq_iff pw_le_iff)

text \<open>Productivity of the plain bisection solver's pop count. Its three \<open>WHILET\<close>s (the reverse
  loop, the exact ET kernel, the truncated ET kernel) each go through
  @{thm [source] cdlr_ex_inres_WHILET} with their own index measure; every other
  constituent is \<open>ASSERT\<close>/\<open>RETURN\<close>/\<open>for\<close>/\<open>if\<close>-composed (+ the satisfiable
  @{const mpz_bitlen2_monadic} SPEC). Body productivity and body index-increment are
  derived pointwise from the bodies' own structure.\<close>
lemma cdlr_ex_inres_snat_bitlen:
  "Ex (inres (snat_bitlen_monadic m))"
  unfolding snat_bitlen_monadic_def
  apply (intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_RETURN
      cdlr_ex_inres_WHILET[where V = "measure fst"])
  apply (all \<open>(simp; fail)?\<close>)
  apply (all \<open>(intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_if
      cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN cdlr_ex_inres_nfoldli; fail)?\<close>)
  apply (all \<open>(fastforce simp: refine_pw_simps split: prod.splits)?\<close>)
  done

lemma cdlr_ex_inres_poly_reverse:
  "Ex (inres (poly_reverse_monadic xs))"
  unfolding poly_reverse_monadic_def poly_reverse_cond_def
    poly_reverse_loop_body_mop_monadic_def poly_reverse_step_mop_monadic_def
    poly_reverse_result_mop_monadic_def
    poly_length_monadic_def poly_empty_sz_monadic_def poly_copy_coeff_monadic_def
    poly_push_coeff_monadic_def PR_CONST_def Let_def
  apply (intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_ASSERT
      cdlr_ex_inres_RETURN
      cdlr_ex_inres_WHILET[where V = "measure (\<lambda>(i, dst). length xs - i)"])
  apply (all \<open>(simp; fail)?\<close>)
  apply (all \<open>(intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_if
      cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN cdlr_ex_inres_nfoldli; fail)?\<close>)
  apply (all \<open>(fastforce simp: refine_pw_simps split: prod.splits)?\<close>)
  done

text \<open>Predicate preservation along nfoldli results (needed to carry the length of the
  ET kernels' in-place-updated poly through the inner shift loop, so the OUTER loop's
  measure can live on the STATE's own poly component).\<close>
lemma cdlr_inres_nfoldli_pres:
  assumes "inres (nfoldli l c f s) s'"
    and "nofail (nfoldli l c f s)"
    and "P s"
    and pres: "\<And>x s s'. P s \<Longrightarrow> nofail (f x s) \<Longrightarrow> inres (f x s) s' \<Longrightarrow> P s'"
  shows "P s'"
  using assms(1-3)
proof (induction l arbitrary: s)
  case Nil
  thus ?case by simp
next
  case (Cons a l)
  show ?case
  proof (cases "c s")
    case False
    thus ?thesis using Cons.prems by simp
  next
    case True
    from Cons.prems(2) True have nfa: "nofail (f a s)"
      by (auto simp: refine_pw_simps)
    from Cons.prems(1) True nfa obtain t where
      t: "inres (f a s) t" and rest: "inres (nfoldli l c f t) s'"
      by (auto simp: refine_pw_simps)
    have nfr: "nofail (nfoldli l c f t)"
      using Cons.prems(2) True nfa t by (auto simp: refine_pw_simps)
    show ?thesis
      by (rule Cons.IH[OF rest nfr pres[OF Cons.prems(3) nfa t]])
  qed
qed

text \<open>The exact ET kernel's loop, productivity as a standalone fact (the outer measure
  lives on the STATE's poly component; the inner shift loop preserves its length —
  every step is a list UPDATE).\<close>
lemma cdlr_ex_inres_ethorner_loop:
  fixes init :: "(nat \<times> int \<times> nat) \<times> gmp_poly"
  shows "Ex (inres (WHILET (\<lambda>st. poly_ethorner_count_cond limit st)
       (\<lambda>st. poly_ethorner_count_body_mop_monadic len st) init))"
proof (rule cdlr_ex_inres_WHILET[where
      V = "measure (\<lambda>((i, ls, ch), ys). length ys - i)"])
  show "wf (measure (\<lambda>((i, ls, ch), ys). length ys - i))" by simp
next
  fix s assume "poly_ethorner_count_cond limit s"
  show "Ex (inres (poly_ethorner_count_body_mop_monadic len s))"
    unfolding poly_ethorner_count_body_mop_monadic_def
      poly_ethorner_inner_loop_monadic_def poly_coeff_sgn_monadic_def
      poly_add_coeff_monadic_def for_def PR_CONST_def Let_def
    by (intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_if
        cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN cdlr_ex_inres_nfoldli)
next
  fix s s'
  assume nof: "nofail (poly_ethorner_count_body_mop_monadic len s)"
    and ir: "inres (poly_ethorner_count_body_mop_monadic len s) s'"
  obtain i ls ch ys where s: "s = ((i, ls, ch), ys)" by (cases s) auto
  have lys: "length ys = len" and ibound: "i + 1 < len" and len2: "1 < len"
    using nof unfolding s poly_ethorner_count_body_mop_monadic_def PR_CONST_def
    by (auto simp: refine_pw_simps)
  have row: "poly_ethorner_inner_loop_monadic len i ys
      \<le> RETURN (ethorner_row_fun i ys)"
    using poly_ethorner_inner_loop_monadic_row lys len2 ibound by simp
  from ir nof obtain ys' where
    irl: "inres (poly_ethorner_inner_loop_monadic len i ys) ys'"
    and nfl: "nofail (poly_ethorner_inner_loop_monadic len i ys)"
    and fst_s': "fst (fst s') = i + 1 \<and> snd s' = ys'"
    unfolding s poly_ethorner_count_body_mop_monadic_def poly_coeff_sgn_monadic_def
      PR_CONST_def Let_def
    by (auto simp: refine_pw_simps split: if_splits)
  have ys'_eq: "ys' = ethorner_row_fun i ys"
    using irl nfl row by (auto simp: pw_le_iff)
  have lpres: "length ys' = length ys" by (simp add: ys'_eq)
  show "(s', s) \<in> measure (\<lambda>((i, ls, ch), ys). length ys - i)"
    using fst_s' lpres lys ibound unfolding s
    by (cases s') auto
qed

lemma cdlr_ex_inres_ethorner_count:
  "Ex (inres (poly_ethorner_count_monadic xs))"
  unfolding poly_ethorner_count_monadic_def
    poly_ethorner_count_result_mop_monadic_def
    poly_coeff_sgn_monadic_def poly_length_monadic_def PR_CONST_def Let_def
  by (intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_if
      cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN cdlr_ex_inres_ethorner_loop
      poly_free_monadic_ex_inres)

text \<open>Same architecture for the truncated ET kernel's loop (its body additionally reads
  a coefficient bit length — the satisfiable SPEC — and threads the ambiguity flag).\<close>
lemma cdlr_ex_inres_ethorner_trunc_loop:
  fixes init :: "(nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly"
  shows "Ex (inres (WHILET (\<lambda>st. ethorner_count_trunc_cond limit st)
       (\<lambda>st. ethorner_count_trunc_body_mop_monadic len bthr st) init))"
proof (rule cdlr_ex_inres_WHILET[where
      V = "measure (\<lambda>((i, ls, ch, amb), ys). length ys - i)"])
  show "wf (measure (\<lambda>((i, ls, ch, amb), ys). length ys - i))" by simp
next
  fix s assume "ethorner_count_trunc_cond limit s"
  show "Ex (inres (ethorner_count_trunc_body_mop_monadic len bthr s))"
    unfolding ethorner_count_trunc_body_mop_monadic_def
      poly_ethorner_inner_loop_monadic_def poly_coeff_sgn_monadic_def
      poly_coeff_bitlen2_monadic_def poly_add_coeff_monadic_def
      for_def PR_CONST_def Let_def
    by (intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_if
        cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN cdlr_ex_inres_nfoldli
        cdlr_ex_inres_bitlen2)
next
  fix s s'
  assume nof: "nofail (ethorner_count_trunc_body_mop_monadic len bthr s)"
    and ir: "inres (ethorner_count_trunc_body_mop_monadic len bthr s) s'"
  obtain i ls ch amb ys where s: "s = ((i, ls, ch, amb), ys)" by (cases s) auto
  have lys: "length ys = len" and ibound: "i + 1 < len" and len2: "1 < len"
    using nof unfolding s ethorner_count_trunc_body_mop_monadic_def PR_CONST_def
    by (auto simp: refine_pw_simps)
  have row: "poly_ethorner_inner_loop_monadic len i ys
      \<le> RETURN (ethorner_row_fun i ys)"
    using poly_ethorner_inner_loop_monadic_row lys len2 ibound by simp
  from ir nof obtain ys' where
    irl: "inres (poly_ethorner_inner_loop_monadic len i ys) ys'"
    and nfl: "nofail (poly_ethorner_inner_loop_monadic len i ys)"
    and fst_s': "fst (fst s') = i + 1 \<and> snd s' = ys'"
    unfolding s ethorner_count_trunc_body_mop_monadic_def poly_coeff_sgn_monadic_def
      poly_coeff_bitlen2_monadic_def PR_CONST_def Let_def
    by (auto simp: refine_pw_simps)
  have ys'_eq: "ys' = ethorner_row_fun i ys"
    using irl nfl row by (auto simp: pw_le_iff)
  have lpres: "length ys' = length ys" by (simp add: ys'_eq)
  show "(s', s) \<in> measure (\<lambda>((i, ls, ch, amb), ys). length ys - i)"
    using fst_s' lpres lys ibound unfolding s
    by (cases s') auto
qed

lemma cdlr_ex_inres_ethorner_count_trunc:
  "Ex (inres (poly_ethorner_count_trunc_monadic xs))"
  unfolding poly_ethorner_count_trunc_monadic_def
    ethorner_count_trunc_result_mop_monadic_def
    poly_coeff_sgn_monadic_def snat_bitlen_monadic_def
    poly_length_monadic_def PR_CONST_def Let_def
  apply (intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_if
      cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN
      cdlr_ex_inres_ethorner_trunc_loop poly_free_monadic_ex_inres
      cdlr_ex_inres_WHILET[where V = "measure fst"])
  apply (all \<open>(simp; fail)?\<close>)
  apply (all \<open>(intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_if
      cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN; fail)?\<close>)
  apply (all \<open>(fastforce simp: refine_pw_simps split: prod.splits)?\<close>)
  done

(*FASTLOOP_FREEZE_ABOVE*)

text \<open>The count begins with the \<open>(0,\<infinity>)\<close> prune, so productivity factors into the sign scan (a WHILET on the
  index shape of @{const poly_reverse_monadic}) and the body.\<close>
lemma cdlr_ex_inres_poly_sign_changes:
  "Ex (inres (poly_sign_changes_monadic xs))"
  unfolding poly_sign_changes_monadic_def sign_changes_cond_def
    sign_changes_init_mop_monadic_def sign_changes_body_mop_monadic_def
    sign_changes_result_mop_monadic_def sign_step_from_sgn_mop_monadic_def
    poly_length_monadic_def poly_coeff_sgn_monadic_def PR_CONST_def Let_def
  apply (intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_ASSERT
      cdlr_ex_inres_RETURN
      cdlr_ex_inres_WHILET[where V = "measure (\<lambda>(i, _ :: int, _ :: nat). length xs - i)"])
  apply (all \<open>(simp; fail)?\<close>)
  apply (all \<open>(intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_if
      cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN cdlr_ex_inres_nfoldli; fail)?\<close>)
  apply (all \<open>(fastforce simp: refine_pw_simps split: prod.splits)?\<close>)
  \<comment> \<open>The step-decrease survives the blanket closers: unlike @{const poly_reverse_monadic}'s
     two-component state, the sign scan's body ends behind \<open>sign_step_from_sgn_mop_monadic\<close>'s
     four-way \<open>if\<close>-chain, so the tail \<open>RETURN (i + 1, _, _)\<close> is too deep for \<open>fastforce\<close> to
     reach without the state destructured first. \<open>i < length xs\<close> comes from the body's own
     ASSERTs via \<open>nofail\<close>.\<close>
  subgoal for x xa xb s s'
    by (cases s rule: prod_cases3; cases s' rule: prod_cases3)
       (auto simp: refine_pw_simps split: if_splits)
  done

lemma cdlr_ex_inres_count_trunc_body:
  "Ex (inres (carried_descartes_count_trunc_body_monadic xs))"
  unfolding carried_descartes_count_trunc_body_monadic_def
    lead_budget_mop_def poly_coeff_bitlen2_monadic_def
    poly_trunc_in_place_monadic_def poly_trunc_loop_monadic_def
    poly_trunc_coeff_monadic_def
    poly_length_monadic_def for_def PR_CONST_def Let_def
  by (intro cdlr_ex_inres_bind cdlr_ex_inres_case_prod cdlr_ex_inres_if
      cdlr_ex_inres_ASSERT cdlr_ex_inres_RETURN cdlr_ex_inres_nfoldli
      cdlr_ex_inres_poly_reverse cdlr_ex_inres_ethorner_count
      cdlr_ex_inres_ethorner_count_trunc cdlr_ex_inres_snat_bitlen
      poly_free_monadic_ex_inres
      cdlr_ex_inres_bitlen2)

lemma cdlr_ex_inres_count_trunc:
  "Ex (inres (carried_descartes_count_trunc_monadic xs))"
  unfolding carried_descartes_count_trunc_monadic_def PR_CONST_def
  by (intro cdlr_ex_inres_bind cdlr_ex_inres_if cdlr_ex_inres_RETURN
      cdlr_ex_inres_poly_sign_changes cdlr_ex_inres_count_trunc_body)

text \<open>Bundled productivity form for the count coupling (existence only — the VALUE is
  characterized separately by @{thm [source] carried_descartes_count_trunc_monadic_classify}).\<close>
lemma cdlr_count_trunc_ex:
  "\<exists>v. inres (carried_descartes_count_trunc_monadic xs) v"
  using cdlr_ex_inres_count_trunc by blast

text \<open>The push ops as literal RETURN equalities (all ASSERT/RETURN-composed; the two GMP
  amops involved — add and mul-2exp — have trivial \<open>top\<close> preconditions). These let the
  PLAIN side of the split branch be evaluated wholesale to \<open>RETURN\<close>, turning the
  \<open>\<Down>\<close>-refinement into a one-sided SPEC goal about the dense program.\<close>
lemma cdlr_push2_eq:
  assumes "length qs + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_vec_push2_monadic qs q1 q2 = RETURN (qs @ [q1, q2])"
  using assms
  unfolding poly_vec_push2_monadic_def poly_vec_push_monadic_def PR_CONST_def
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma cdlr_append_eq:
  "mop_list_append xs x = RETURN (xs @ [x])"
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma cdlr_push_children_eq:
  assumes "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and "Suc k < max_snat LENGTH(gmp_poly_len)"
  shows "dyadic_interval_vec_push_children_monadic (lns, rns, ks) l_num r_num k
       = RETURN (lns @ [2 * l_num, l_num + r_num], rns @ [l_num + r_num, 2 * r_num],
                 ks @ [k + 1, k + 1])"
  using assms
  unfolding dyadic_interval_vec_push_children_monadic_def
    poly_push2_coeffs_monadic_def poly_push_coeff_monadic_def
    dyadic_exp_push2_monadic_def mpz_double_shift_monadic_def
    mpz_add.amop_r1_def mpz_mul_2exp.amop_r1_def
    dyadic_interval_vec_pushable2_def PR_CONST_def Let_def
  by (auto simp: pw_eq_iff refine_pw_simps cdlr_append_eq shiftl_def
      push_bit_eq_mult algebra_simps)

lemma cdlr_push_mid_eq:
  assumes "dyadic_interval_vec_pushable (al, ar, ak)"
  shows "carried_push_mid_monadic (al, ar, ak) l_num r_num k
       = RETURN (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1])"
  using assms
  unfolding carried_push_mid_monadic_def poly_push_coeff_monadic_def
    mpz_add.amop_r1_def dyadic_interval_vec_pushable_def PR_CONST_def Let_def
  by (auto simp: pw_eq_iff refine_pw_simps cdlr_append_eq)

text \<open>The per-child retruncation contract, all three output facts at once (frame + range
  + lock-passthrough), with every hypothesis explicit so the caller can instantiate it
  UNAMBIGUOUSLY per call site (the frame reference \<open>XL\<close> is a ghost — it does not appear in
  the program text, so \<open>refine_vcg\<close> cannot infer it by unification; each of the two child
  retrunc calls needs its own explicitly-\<open>OF\<close>-ed instance).\<close>
lemma cdlr_retrunc_child:
  assumes frame: "node_frame XL child gin"
    and lbound: "length child + 1 < max_snat LENGTH(gmp_poly_len)"
    and gin_le: "gin \<le> 4398046511104"
    and lock_in: "4398046511104 \<le> gin \<longrightarrow> child = XL"
  shows "carried_retrunc_mop child gin \<le> SPEC (\<lambda>(ys, g').
           node_frame XL ys g' \<and> g' \<le> 4398046511104 \<and>
           (4398046511104 \<le> g' \<longrightarrow> ys = XL))"
proof -
  have gb: "gin < max_snat LENGTH(gmp_poly_len)"
    using gin_le unfolding max_snat_def by simp
  have both: "carried_retrunc_mop child gin \<le> SPEC (\<lambda>x.
      (case x of (ys, g') \<Rightarrow> node_frame XL ys g') \<and>
      (case x of (ys, g') \<Rightarrow>
         g' \<le> 4398046511104 \<and> (4398046511104 \<le> g' \<longrightarrow> ys = child \<and> 4398046511104 \<le> gin)))"
    by (rule cdlr_SPEC_conj[OF carried_retrunc_mop_frame[OF frame lbound gb]
        cdlr_retrunc_range[OF gin_le]])
  show ?thesis
    apply (rule order_trans[OF both])
    using lock_in by auto
qed

text \<open>The truncating children op agrees with the exact children (which are \<open>carried_left X\<close>/\<open>carried_right X\<close> on
  the bisection side, by \<open>carried_left_right_monadic_correct\<close> and the midpoint test's output coupling):
  each truncated child carries a \<open>node_frame\<close> against its exact twin, stays under the exact-lock guard cap, and is
  exact when at the cap. The guard trichotomy \<open>g_tri\<close> is the midpoint test's output invariant
  (\<open>g' \<in> {0} \<union> (trust window) \<union> [lock, \<dots>]\<close>, which is why that test escalates at \<open>2\<^sup>4\<^sup>0\<close>), and it excludes the two
  clamping branches of @{const truncate_child_guards_mop}, whose \<open>2\<^sup>4\<^sup>1\<close> clamp under-approximates in \<open>[2\<^sup>4\<^sup>0, 2\<^sup>4\<^sup>2)\<close>.\<close>
lemma truncate_children_agrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_le: "g \<le> 4398046511104"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
  shows "truncate_children_monadic g Q \<le> SPEC (\<lambda>(ql, gl, qr, gr).
           node_frame (carried_left X) ql gl \<and> node_frame (carried_right X) qr gr \<and>
           gl \<le> 4398046511104 \<and> gr \<le> 4398046511104 \<and>
           (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
           (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X))"
proof -
  have lr_step: "carried_left_right_monadic Q \<bind> f
      \<le> f (carried_left Q, carried_right Q)" for f
  proof -
    have "carried_left_right_monadic Q \<bind> f
        \<le> RETURN (carried_left Q, carried_right Q) \<bind> f"
      by (rule bind_mono(1)[OF carried_left_right_monadic_correct[OF Qne Qbound]]) simp
    also have "\<dots> = f (carried_left Q, carried_right Q)" by simp
    finally show ?thesis .
  qed
  have lb_l: "length (carried_left Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lb_r: "length (carried_right Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qbound by simp_all
  show ?thesis
  proof (cases "g = 0")
    case True
    hence XQ: "X = Q" using frame unfolding node_frame_def by simp
    have fl: "node_frame (carried_left X) (carried_left Q) 0"
      and fr: "node_frame (carried_right X) (carried_right Q) 0"
      unfolding XQ by (rule node_frame_exact)+
    show ?thesis
      unfolding truncate_children_monadic_def truncate_child_guards_mop_def
        poly_length_monadic_def PR_CONST_def
      using Qne Qbound
      apply (simp add: True)
      apply (rule order_trans[OF lr_step])
      apply (simp add: lb_l)
      apply (refine_vcg cdlr_retrunc_child[OF fl lb_l, THEN order_trans])
      subgoal by simp
      subgoal by simp
      apply (clarsimp simp: lb_r)
      apply (refine_vcg cdlr_retrunc_child[OF fr lb_r, THEN order_trans])
      subgoal by simp
      subgoal by simp
      apply (all \<open>(auto; fail)?\<close>)
      done
  next
    case g_ne0: False
    show ?thesis
    proof (cases "4398046511104 \<le> g")
      case glock: True
      hence QX: "Q = X" using lock by simp
      \<comment> \<open>@{const truncate_child_guards_mop}'s lock branch returns \<open>(g, g)\<close> rather than the literal \<open>2\<^sup>4\<^sup>2\<close>, so that the
         hybrid solver can carry an exact \<open>v\<close>-bound in the guard as \<open>2\<^sup>4\<^sup>2 + v\<close>. Here this lemma's \<open>g_le\<close> invariant
         caps \<open>g\<close> at \<open>2\<^sup>4\<^sup>2\<close>, so on this branch \<open>g\<close> is the literal (\<open>gval\<close>); adding it to the \<open>simp\<close> gives the goal the
         literal form.\<close>
      have gval: "g = 4398046511104" using glock g_le by linarith
      have fl: "node_frame (carried_left X) (carried_left Q) 4398046511104"
        and fr: "node_frame (carried_right X) (carried_right Q) 4398046511104"
        unfolding QX by (rule node_frame_exact_any_g)+
      have lock_l: "4398046511104 \<le> (4398046511104::nat) \<longrightarrow> carried_left Q = carried_left X"
        and lock_r: "4398046511104 \<le> (4398046511104::nat) \<longrightarrow> carried_right Q = carried_right X"
        unfolding QX by simp_all
      show ?thesis
        unfolding truncate_children_monadic_def truncate_child_guards_mop_def
          poly_length_monadic_def PR_CONST_def
        using Qne Qbound
        apply (simp add: g_ne0 glock gval)
        apply (rule order_trans[OF lr_step])
        apply (simp add: lb_l)
        apply (refine_vcg cdlr_retrunc_child[OF fl lb_l _ lock_l, THEN order_trans])
        subgoal by simp
        apply (clarsimp simp: lb_r)
        apply (refine_vcg cdlr_retrunc_child[OF fr lb_r _ lock_r, THEN order_trans])
        subgoal by simp
        apply (all \<open>(auto; fail)?\<close>)
        done
    next
      case gsmall: False
      have g_win: "g < 1099511627776" using g_tri gsmall by simp
      have not_g40: "\<not> 1099511627776 \<le> g" using g_win by simp
      have not_len40: "\<not> 1099511627776 \<le> length Q" using Q_small by simp
      have QneL: "Q \<noteq> []" using Qne by simp
      have gplen: "g + length Q < max_snat LENGTH(gmp_poly_len)"
        using g_win Q_small unfolding max_snat_def by simp
      have fl: "node_frame (carried_left X) (carried_left Q) (g + length Q - Suc 0)"
        using node_frame_child_left_impl[OF frame g_ne0] Qne
        by (simp add: Nat.add_diff_assoc Suc_le_eq)
      have fr: "node_frame (carried_right X) (carried_right Q) (g + length Q)"
        using node_frame_child_right_tight[OF frame] .
      have gle_l: "g + length Q - Suc 0 \<le> 4398046511104"
        using g_win Q_small by linarith
      have gle_r: "g + length Q \<le> 4398046511104"
        using g_win Q_small by linarith
      have lock_l: "4398046511104 \<le> g + length Q - Suc 0 \<longrightarrow> carried_left Q = carried_left X"
        using g_win Q_small by (intro impI) linarith
      have lock_r: "4398046511104 \<le> g + length Q \<longrightarrow> carried_right Q = carried_right X"
        using g_win Q_small by (intro impI) linarith
      show ?thesis
        unfolding truncate_children_monadic_def truncate_child_guards_mop_def
          poly_length_monadic_def PR_CONST_def
        apply (simp add: g_ne0 gsmall not_g40 not_len40 QneL g_win Q_small gplen)
        apply (rule ASSERT_leI)
        subgoal using gplen by simp
        apply (rule order_trans[OF lr_step])
        apply (simp add: lb_l)
        apply (refine_vcg cdlr_retrunc_child[OF fl lb_l gle_l lock_l, THEN order_trans])
        subgoal using Qbound by simp
        apply clarsimp
        apply (refine_vcg cdlr_retrunc_child[OF fr lb_r gle_r lock_r, THEN order_trans])
        apply (all \<open>(auto; fail)?\<close>)
        done
    qed
  qed
qed

section \<open>Soundness of the guarded mid trust test (the missing eval-kernel classify)\<close>

text \<open>@{const poly_hom_eval_trust_half_monadic} (the dense mid test's trust kernel) had NO
  correctness lemma anywhere in the codebase — this section supplies it. The shape mirrors
  the count kernel's classify (@{thm [source] carried_descartes_count_g_monadic_classify})
  but for the plain Horner hom-eval at \<open>n/d = 1/2\<close>: given the node frame, \<open>tr = True\<close>
  certifies the TRUE (exact-poly) midpoint eval is nonzero. Scope note: the lemma is
  stated INSIDE the trust window \<open>g < 2^40 \<and> len < 2^40\<close>, where @{const mid_guard_mop}
  provably returns the exact \<open>g + len\<close> guard — outside the window the impl's clamped
  \<open>2^41\<close> guard genuinely under-approximates (a latent-soundness finding of this
  verification pass; the dispatch-level agreement lemma must exclude that regime via the
  worklist guard invariant, see the SCOPE FINDING note below).\<close>

text \<open>The geometric weight sum the eval-error bound needs: \<open>\<Sum>_{i<n} 2^(n-1-i) = 2^n - 1\<close>.\<close>
lemma cdlr_geom_sum: "(\<Sum>i<n. (2::int) ^ (n - Suc i)) = 2 ^ n - 1"
proof -
  have "(\<Sum>i<n. (2::int) ^ (n - Suc i)) = (\<Sum>j<n. (2::int) ^ j)"
    by (rule sum.reindex_bij_witness[where i = "\<lambda>j. n - Suc j" and j = "\<lambda>i. n - Suc i"]) auto
  also have "\<dots> = 2 ^ n - 1"
    by (induction n) simp_all
  finally show ?thesis .
qed

text \<open>The integer the Horner loop computes at \<open>1/2\<close>, in \<Sum>-form: \<open>2^(n-1)\<close> times the
  rational midpoint eval. Re-derives the two internal steps of @{thm [source]
  reverse_eval_recip} (which proves the same fact routed through \<open>Poly (rev xs)\<close>).\<close>
lemma cdlr_eval_half_scaled:
  assumes ne: "xs \<noteq> []"
  shows "rat_of_int (\<Sum>i<length xs. xs ! i * 2 ^ (length xs - Suc i))
       = 2 ^ (length xs - 1) *
           poly (map_poly rat_of_int (Poly xs)) (rat_of_int 1 / rat_of_int 2)"
proof -
  define n where "n = length xs"
  have lhs: "poly (Poly (rev xs)) (2::int) = (\<Sum>i<n. xs ! (n - 1 - i) * (2::int) ^ i)"
    unfolding poly_Poly_nth_sum n_def
    by (rule sum.cong) (auto simp: rev_nth n_def)
  have reindex: "(\<Sum>i<n. xs ! (n - 1 - i) * (2::int) ^ i)
      = (\<Sum>j<n. xs ! j * (2::int) ^ (n - 1 - j))"
    by (rule sum.reindex_bij_witness[where i = "\<lambda>i. n - 1 - i" and j = "\<lambda>j. n - 1 - j"]) auto
  have expo: "\<And>j. n - 1 - j = n - Suc j" by simp
  have "rat_of_int (\<Sum>i<n. xs ! i * 2 ^ (n - Suc i))
      = rat_of_int (poly (Poly (rev xs)) (2::int))"
    unfolding lhs reindex using expo by simp
  also have "\<dots> = 2 ^ (n - 1) * poly (map_poly rat_of_int (Poly xs)) (1 / 2)"
    using reverse_eval_recip[OF ne] n_def by simp
  finally show ?thesis by (simp add: n_def)
qed

text \<open>The arithmetic core: one-sided per-coefficient error \<open>[0, 2^(s+g))\<close> propagates
  through the \<open>2^(n-1-i)\<close>-weighted eval sum to \<open>[0, 2^(s+g+n))\<close>; a POSITIVE truncated
  eval is then sign-trusted for free, and a negative one with \<open>bitlen > g+n\<close> outweighs
  the whole error band — either way the exact eval is nonzero.\<close>
lemma cdlr_trust_arith:
  assumes f: "gframe s g X Y"
    and ne: "Y \<noteq> []"
    and acc_eq: "acc = (\<Sum>i<length Y. Y ! i * 2 ^ (length Y - Suc i))"
    and bl_lb: "acc \<noteq> 0 \<Longrightarrow> 2 ^ (bl - 1) \<le> \<bar>acc\<bar>"
    and tr: "0 < acc \<or> (acc < 0 \<and> g + length Y < bl)"
  shows "poly (map_poly rat_of_int (Poly X)) (rat_of_int 1 / rat_of_int 2) \<noteq> 0"
proof -
  define n where "n = length Y"
  have npos: "0 < n" using ne n_def by simp
  have lenX: "length X = n" using f n_def unfolding gframe_def by simp
  have Xne: "X \<noteq> []" using lenX npos by auto
  define AX where "AX = (\<Sum>i<n. X ! i * (2::int) ^ (n - Suc i))"
  have e_lb: "\<And>i. i < n \<Longrightarrow> 0 \<le> X ! i - 2 ^ s * Y ! i"
    and e_ub: "\<And>i. i < n \<Longrightarrow> X ! i - 2 ^ s * Y ! i < 2 ^ (s + g)"
    using f unfolding gframe_def n_def by auto
  have err_split: "AX - 2 ^ s * acc
      = (\<Sum>i<n. (X ! i - 2 ^ s * Y ! i) * 2 ^ (n - Suc i))"
    unfolding AX_def acc_eq n_def[symmetric]
    by (simp add: sum_subtractf sum_distrib_left algebra_simps)
  have err_nonneg: "0 \<le> AX - 2 ^ s * acc"
    unfolding err_split
    by (rule sum_nonneg) (auto intro!: mult_nonneg_nonneg e_lb)
  have err_ub: "AX - 2 ^ s * acc < 2 ^ (s + g + n)"
  proof -
    have "(\<Sum>i<n. (X ! i - 2 ^ s * Y ! i) * 2 ^ (n - Suc i))
        \<le> (\<Sum>i<n. (2 ^ (s + g) - 1) * (2::int) ^ (n - Suc i))"
    proof (rule sum_mono)
      fix i assume "i \<in> {..<n}"
      hence i: "i < n" by simp
      have "X ! i - 2 ^ s * Y ! i \<le> 2 ^ (s + g) - 1"
        using e_ub[OF i] by simp
      thus "(X ! i - 2 ^ s * Y ! i) * 2 ^ (n - Suc i)
          \<le> (2 ^ (s + g) - 1) * (2::int) ^ (n - Suc i)"
        by (intro mult_right_mono) simp_all
    qed
    also have "\<dots> = (2 ^ (s + g) - 1) * (\<Sum>i<n. (2::int) ^ (n - Suc i))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (2 ^ (s + g) - 1) * (2 ^ n - 1)"
      by (simp add: cdlr_geom_sum)
    also have "\<dots> < 2 ^ (s + g + n)"
    proof -
      have p1: "(1::int) \<le> 2 ^ (s + g)" by simp
      have p2: "(1::int) \<le> 2 ^ n" by simp
      have "(2 ^ (s + g) - 1) * ((2::int) ^ n - 1)
          = 2 ^ (s + g + n) - 2 ^ (s + g) - 2 ^ n + 1"
        by (simp add: algebra_simps power_add)
      also have "\<dots> < 2 ^ (s + g + n)" using p1 p2 by linarith
      finally show ?thesis .
    qed
    finally show ?thesis unfolding err_split .
  qed
  have AX_ne: "AX \<noteq> 0"
    using tr
  proof
    assume pos: "0 < acc"
    hence "1 \<le> acc" by simp
    hence "2 ^ s \<le> 2 ^ s * acc" by simp
    with err_nonneg have "(2::int) ^ s \<le> AX" by linarith
    moreover have "(0::int) < 2 ^ s" by simp
    ultimately show ?thesis by linarith
  next
    assume neg: "acc < 0 \<and> g + length Y < bl"
    hence acc_neg: "acc < 0" by simp
    have bl_ge: "g + n \<le> bl - 1" using neg n_def by arith
    have acc_nz: "acc \<noteq> 0" using acc_neg by simp
    have "(2::int) ^ (g + n) \<le> 2 ^ (bl - 1)"
      using bl_ge by (intro power_increasing) simp_all
    also have "\<dots> \<le> \<bar>acc\<bar>" using bl_lb[OF acc_nz] .
    finally have "2 ^ (g + n) \<le> \<bar>acc\<bar>" .
    hence "acc \<le> - (2 ^ (g + n))" using acc_neg by simp
    hence "2 ^ s * acc \<le> 2 ^ s * (- (2 ^ (g + n)))"
      by (intro mult_left_mono) simp_all
    hence "2 ^ s * acc \<le> - (2 ^ (s + g + n))"
      by (simp add: power_add)
    with err_ub have "AX < 0" by linarith
    thus ?thesis by simp
  qed
  have AX_scaled: "rat_of_int AX
      = 2 ^ (n - 1) * poly (map_poly rat_of_int (Poly X)) (rat_of_int 1 / rat_of_int 2)"
    using cdlr_eval_half_scaled[OF Xne] lenX unfolding AX_def by simp
  have "rat_of_int AX \<noteq> 0" using AX_ne by simp
  thus ?thesis using AX_scaled by auto
qed

text \<open>The Horner loop's exit value, in \<Sum>-form: reuses the framework's own
  @{const poly_hom_eval_inv} machinery (init/body-preservation lemmas), then
  converts the rational exit identity to the integer \<Sum> via
  @{thm [source] cdlr_eval_half_scaled} + injectivity.\<close>
lemma cdlr_hom_eval_loop_sum:
  assumes ne: "0 < length Y"
    and lb: "length Y + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "WHILET
      (\<lambda>st. poly_hom_eval_cond (length Y - 1) st)
      (\<lambda>st. poly_hom_eval_body_mop_monadic Y (length Y - 1) 1 2 st)
      (0, Y ! (length Y - 1), 2)
    \<le> SPEC (\<lambda>(i, acc, dpow). acc = (\<Sum>j<length Y. Y ! j * 2 ^ (length Y - Suc j)))"
proof -
  have Yne: "Y \<noteq> []" using ne by auto
  have bd1: "(length Y - 1) + 1 = length Y" using ne by simp
  have init_inv: "poly_hom_eval_inv Y (length Y - 1) 1 2 (0, Y ! (length Y - 1), 2)"
    unfolding poly_hom_eval_inv_def
    using poly_hom_eval_init[of "length Y - 1" Y 2 1] bd1 by auto
  show ?thesis
    apply (rule WHILET_rule[where
        R = "measure (\<lambda>(i, _::int, _::int). length Y - 1 - i)"
        and I = "poly_hom_eval_inv Y (length Y - 1) 1 2"])
    subgoal by simp
    subgoal by (rule init_inv)
    subgoal for st
      apply (rule order_trans[OF poly_hom_eval_body_mop_monadic_spec_decrease])
      using lb by (auto split: prod.splits)
    subgoal for st
    proof -
      assume inv: "poly_hom_eval_inv Y (length Y - 1) 1 2 st"
        and ncond: "\<not> poly_hom_eval_cond (length Y - 1) st"
      obtain i acc dpow where st_eq: "st = (i, acc, dpow)" by (cases st) auto
      have i_eq: "i = length Y - 1"
        using inv ncond unfolding poly_hom_eval_inv_def poly_hom_eval_cond_def st_eq
        by auto
      have acc_rat: "rat_of_int acc / rat_of_int ((2::int) ^ (length Y - 1))
          = poly (map_poly rat_of_int (Poly Y)) (rat_of_int 1 / rat_of_int 2)"
        using inv unfolding poly_hom_eval_inv_def st_eq i_eq by simp
      have "rat_of_int acc
          = 2 ^ (length Y - 1) * poly (map_poly rat_of_int (Poly Y)) (rat_of_int 1 / rat_of_int 2)"
        using acc_rat by (simp add: field_simps)
      also have "\<dots> = rat_of_int (\<Sum>j<length Y. Y ! j * 2 ^ (length Y - Suc j))"
        using cdlr_eval_half_scaled[OF Yne] by simp
      finally have "acc = (\<Sum>j<length Y. Y ! j * 2 ^ (length Y - Suc j))"
        by (simp only: of_int_eq_iff)
      thus "case st of (i, acc, dpow) \<Rightarrow>
          acc = (\<Sum>j<length Y. Y ! j * 2 ^ (length Y - Suc j))"
        by (simp add: st_eq)
    qed
    done
qed

text \<open>The half-loop's exit value in \<Sum>-form, for the trust op: the shift-and-add loop
  shared with @{const half_eval_zero_monadic} (seed \<open>acc = Y!0\<close>, then \<open>acc \<lless> 1\<close> + borrowed
  add) computes the integer \<open>\<Sum>_j Y!j·2^(len-1-j) = poly (Poly (rev Y)) 2\<close>, as a downward
  Horner loop would. Mirrors @{thm [source] cdlr_hom_eval_loop_sum} but for the
  @{const half_eval_cond}/@{const half_eval_body_mop_monadic} loop.\<close>
lemma cdlr_half_loop_sum:
  assumes ne: "0 < length Y"
    and lb: "length Y + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "WHILET
      (\<lambda>st. half_eval_cond (length Y) st)
      (\<lambda>st. half_eval_body_mop_monadic Y (length Y) st)
      (Suc 0, Y ! 0)
    \<le> SPEC (\<lambda>(i, acc). acc = (\<Sum>j<length Y. Y ! j * 2 ^ (length Y - Suc j)))"
proof -
  have Yne: "Y \<noteq> []" using ne by auto
  have sum_eq: "poly (Poly (rev Y)) (2::int)
      = (\<Sum>j<length Y. Y ! j * 2 ^ (length Y - Suc j))"
  proof -
    have lhs: "poly (Poly (rev Y)) (2::int) = (\<Sum>i<length Y. (rev Y) ! i * (2::int) ^ i)"
      by (simp add: poly_Poly_nth_sum)
    also have "\<dots> = (\<Sum>i<length Y. Y ! (length Y - 1 - i) * (2::int) ^ i)"
      by (rule sum.cong) (auto simp: rev_nth)
    also have "\<dots> = (\<Sum>j<length Y. Y ! j * (2::int) ^ (length Y - Suc j))"
      by (rule sum.reindex_bij_witness[where i = "\<lambda>i. length Y - 1 - i"
            and j = "\<lambda>j. length Y - 1 - j"]) auto
    finally show ?thesis .
  qed
  show ?thesis
    apply (rule WHILET_rule[where
        R = "measure (\<lambda>(i, acc::int). length Y - i)"
        and I = "\<lambda>(i, acc). 1 \<le> i \<and> i \<le> length Y
          \<and> acc = poly (Poly (rev (take i Y))) (2::int)"])
    subgoal by simp
    subgoal using ne by (simp add: take_Suc_conv_app_nth)
    subgoal for st
      unfolding half_eval_body_mop_monadic_def half_eval_cond_def
        poly_acc_add_coeff_monadic_def mpz_shift_left_snat_monadic_def
        mpz_mul_2exp.amop_r1_def mpz_mul_2exp.aop_r1_def
        snat_unat_cast.mop_def PR_CONST_def
      apply refine_vcg
      using lb
      apply (auto simp: max_snat_def max_unat_def take_Suc_conv_app_nth)
      done
    subgoal by (auto simp: take_all half_eval_cond_def sum_eq split: prod.splits)
    done
qed

text \<open>\<^bold>\<open>Soundness of the trust kernel\<close>: inside the trust window \<open>g < 2^40 \<and> len < 2^40\<close>, a \<open>True\<close> from
  @{const poly_hom_eval_trust_half_monadic} on the truncated polynomial \<open>Y\<close> certifies that the exact polynomial
  \<open>X\<close>'s midpoint value is nonzero, which the agreement of \<open>is_root\<close> needs on the trust path.\<close>
lemma poly_hom_eval_trust_half_monadic_sound:
  assumes f: "gframe s g X Y"
    and ne: "0 < length Y"
    and lb: "length Y + 1 < max_snat LENGTH(gmp_poly_len)"
    and g_win: "g < 1099511627776"
    and len_win: "length Y < 1099511627776"
  shows "poly_hom_eval_trust_half_monadic g Y
       \<le> SPEC (\<lambda>tr. tr \<longrightarrow>
           poly (map_poly rat_of_int (Poly X)) (rat_of_int 1 / rat_of_int 2) \<noteq> 0)"
proof -
  have Yne: "Y \<noteq> []" using ne by auto
  show ?thesis
    unfolding poly_hom_eval_trust_half_monadic_def
      poly_length_monadic_def poly_copy_coeff_monadic_def
      mid_guard_mop_def lead_trust_mop_def mpz_sgn_mop_def
      mpz_bitlen2_monadic_def mpzb_discard_monadic_def
      op_snat_unat_conv_def PR_CONST_def
    apply refine_vcg
    apply (all \<open>(clarsimp simp: ne lb)?\<close>)
    subgoal using Yne by simp
    subgoal using lb by simp
    apply (intro conjI impI)
    subgoal \<comment> \<open>the \<open>len \<ge> 2^40\<close> clamp branch — excluded by the window hypothesis\<close>
      using len_win by linarith
    subgoal
      apply (rule order_trans[OF cdlr_half_loop_sum[OF ne lb]])
      using g_win len_win
      apply (clarsimp simp: pw_le_iff refine_pw_simps max_snat_def split: prod.splits)
      subgoal for y using cdlr_trust_arith[OF f Yne refl, of y] by auto
      done
    done
qed

text \<open>A standalone bridge for the tail call of the trust-or-escalate branches: composed inline inside a larger
  tactic script, a \<open>half_eval_zero_monadic xs \<le> RES {\<dots>}\<close> goal meets a fresh-variable mismatch between \<open>refine_vcg\<close> and
  \<open>simp\<close>; stated standalone, with no ambient closure over \<open>X\<close>/\<open>P\<close>/\<open>Q\<close>, it does not.\<close>
lemma half_eval_zero_agrees:
  assumes ne: "0 < length (xs :: gmp_poly)"
    and lb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "half_eval_zero_monadic xs \<le>
    RES {poly (map_poly rat_of_int (Poly xs)) (1 / 2) = 0}"
  using half_eval_zero_monadic_correct[OF ne lb] by (simp add: RETURN_def)

text \<open>@{const truncate_mid_test_monadic} agrees with the plain solver's bare
  @{const bisection_mid_zero_monadic} call: \<open>g=0\<close> is literal equality (\<open>node_frame\<close>'s own
  clause); \<open>g\<ge>EXACT_LOCK\<close> uses the \<open>lock\<close> hypothesis (same pattern as
  @{thm [source] truncate_count_escalate_agrees}); the trust-or-escalate branch uses
  @{thm [source] poly_hom_eval_trust_half_monadic_sound} when trusted, or an inline
  \<open>carried_escalate_keep_monadic_correct\<close>-composition plus the \<open>recompute\<close> hypothesis
  (the popped node equals its own root-recompute, from @{const truncate_state_rel}'s
  invariant) when escalating — either way the ESCALATED poly is LITERALLY \<open>X\<close>, so the
  dense side's own \<open>bisection_mid_zero_monadic\<close> call becomes the SAME call the plain side
  makes.\<close>
lemma truncate_mid_test_agrees:
  assumes frame: "node_frame X Q g"
    and rp_eq: "rp = P"
    and recompute: "X = carried_init_same_den l (2 ^ k) r P"
    and lock: "4398046511104 \<le> g \<longrightarrow> X = Q"
    and g_le: "g \<le> 4398046511104"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_small: "length P < 1099511627776"
    and k_safe: "Suc k * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_mid_test_monadic rp l r k g Q \<le>
    SPEC (\<lambda>(is_root, Q', g', rp').
      rp' = P \<and> node_frame X Q' g' \<and>
      g' \<le> 4398046511104 \<and> (4398046511104 \<le> g' \<longrightarrow> Q' = X) \<and>
      (g' < 1099511627776 \<or> 4398046511104 \<le> g') \<and>
      is_root = (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0))"
proof -
  have k_safe': "k * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
    using k_safe by simp
  have escalate_bound: "carried_escalate_keep_monadic rp l r k Q \<le> RETURN (X, P)"
    using carried_escalate_keep_monadic_correct[OF P_len P_bound k_safe'] recompute rp_eq
    by simp
  have esc_nofail: "nofail (carried_escalate_keep_monadic rp l r k Q)"
    and esc_val: "\<And>y. inres (carried_escalate_keep_monadic rp l r k Q) y \<Longrightarrow> y = (X, P)"
    using escalate_bound by (auto simp: pw_le_iff refine_pw_simps)
  have escalate_step: "carried_escalate_keep_monadic rp l r k Q \<bind> f \<le> f (X, P)" for f
  proof -
    have "carried_escalate_keep_monadic rp l r k Q \<bind> f \<le> RETURN (X, P) \<bind> f"
      by (rule bind_mono(1)[OF escalate_bound]) simp
    also have "\<dots> = f (X, P)" by simp
    finally show ?thesis .
  qed
  have escalate_step_P: "carried_escalate_keep_monadic P l r k Q \<bind> f \<le> f (X, P)" for f
    using escalate_step rp_eq by simp
  have escalate_bound_P: "carried_escalate_keep_monadic P l r k Q \<le> RETURN (X, P)"
    using escalate_bound rp_eq by simp
  have Xne: "0 < length X"
    using recompute P_len truncate_length_carried_init_same_den by simp
  have Xbound: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    using recompute P_bound truncate_length_carried_init_same_den by simp
  have Xne': "0 < length (carried_init_same_den l (2 ^ k) r P)"
    using P_len truncate_length_carried_init_same_den by simp
  have Xbound': "length (carried_init_same_den l (2 ^ k) r P) + 1 < max_snat LENGTH(gmp_poly_len)"
    using P_bound truncate_length_carried_init_same_den by simp
  have half_eval_bound: "half_eval_zero_monadic X \<le>
      RETURN (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)"
    using half_eval_zero_monadic_correct[OF Xne Xbound] by simp
  have half_eval_step: "half_eval_zero_monadic X \<bind> f \<le>
      f (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)" for f
  proof -
    have "half_eval_zero_monadic X \<bind> f \<le>
        RETURN (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0) \<bind> f"
      by (rule bind_mono(1)[OF half_eval_bound]) simp
    also have "\<dots> = f (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)"
      by simp
    finally show ?thesis .
  qed
  have escalate_mid_agrees: "carried_escalate_keep_monadic P l r k Q \<bind> (\<lambda>(qx, rp2). doN {
      ASSERT (qx \<noteq> []);
      ASSERT (Suc (length qx) < max_snat LENGTH(gmp_poly_len));
      is_root \<leftarrow> half_eval_zero_monadic qx;
      RETURN (is_root, qx, 0, rp2)
    }) \<le> SPEC (\<lambda>(is_root, Q', g', rp').
      rp' = P \<and> node_frame X Q' g' \<and>
      g' \<le> 4398046511104 \<and> (4398046511104 \<le> g' \<longrightarrow> Q' = X) \<and>
      (g' < 1099511627776 \<or> 4398046511104 \<le> g') \<and>
      is_root = (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0))"
    apply (rule order_trans[OF escalate_step_P])
    apply simp
    apply refine_vcg
    subgoal using Xne by simp
    subgoal using Xbound by simp
    apply (rule order_trans[OF half_eval_zero_agrees[OF Xne Xbound]])
    apply (auto simp: node_frame_exact)
    done
  show ?thesis
proof (cases "g = 0")
  case True
  hence XQ: "X = Q" using frame unfolding node_frame_def by simp
  show ?thesis
    unfolding truncate_mid_test_monadic_def PR_CONST_def True
      bisection_mid_zero_monadic_def
    using rp_eq XQ Qne Qbound
    by (refine_vcg half_eval_zero_monadic_correct[OF Qne Qbound, THEN order_trans])
      (auto simp: node_frame_exact)
next
  case False
  show ?thesis
  proof (cases "4398046511104 \<le> g")
    case True
    hence XQ: "X = Q" using lock by simp
    have gL: "g = 4398046511104" using True g_le by simp
    show ?thesis
      unfolding truncate_mid_test_monadic_def PR_CONST_def
        bisection_mid_zero_monadic_def
      using rp_eq XQ Qne Qbound gL
      apply (simp add: False gL)
      by (refine_vcg half_eval_zero_monadic_correct[OF Qne Qbound, THEN order_trans])
        (auto simp: node_frame_exact_any_g)
  next
    case gnlock: False
    have Xlen: "length X = length Q" using frame node_frameE gframe_length by blast
    show ?thesis
    proof (cases "g < 1099511627776")
      case g_win: True
      have len_win: "length Q < 1099511627776"
        using Xlen recompute P_small truncate_length_carried_init_same_den by simp
      obtain s where gf: "gframe s g X Q" using node_frameE[OF frame] by blast
      have not_toobig: "\<not> 1099511627776 \<le> g" using g_win by simp
      show ?thesis
        unfolding truncate_mid_test_monadic_def PR_CONST_def bisection_mid_zero_monadic_def
        using False gnlock g_win Qne Qbound not_toobig g_le
        apply (simp add: False gnlock g_win not_toobig)
        apply (refine_vcg poly_hom_eval_trust_half_monadic_sound[OF gf Qne Qbound g_win len_win,
              THEN order_trans])
        apply (all \<open>(clarsimp simp: rp_eq frame)?\<close>)
        apply (all \<open>(rule order_trans[OF escalate_bound_P])?\<close>)
        apply (all \<open>(rule RETURN_rule)?\<close>)
        apply (all \<open>(simp)?\<close>)
        apply (all \<open>(refine_vcg)?\<close>)
        apply (all \<open>(use Xne in simp)?\<close>)
        apply (all \<open>(use Xbound in simp)?\<close>)
        apply (all \<open>(rule order_trans[OF half_eval_zero_agrees[OF Xne Xbound]])?\<close>)
        apply (all \<open>(auto simp: node_frame_exact)?\<close>)
        apply (all \<open>(use lock in simp)?\<close>)
        apply (all \<open>(use g_win in simp)?\<close>)
        done
    next
      case g_toobig: False
      have really_toobig: "1099511627776 \<le> g" using gnlock g_toobig by simp
      show ?thesis
        unfolding truncate_mid_test_monadic_def PR_CONST_def bisection_mid_zero_monadic_def
        using False gnlock g_toobig Qne Qbound really_toobig rp_eq
        apply (simp add: False gnlock g_toobig really_toobig rp_eq)
        by (rule escalate_mid_agrees[simplified])
    qed
  qed
qed
qed

section \<open>The split branch agrees (mid test, children geometry, pushes)\<close>

text \<open>The dense split branch \<Down>-refines the plain one. Architecture: the PLAIN side is
  deterministic end-to-end (mid-zero and children by the productivity equalities above,
  pushes by the push-op equalities), so it EVALUATES to a literal \<open>RETURN pfin\<close> — turning
  the \<Down>-refinement into a one-sided SPEC goal about the dense program, which composes
  @{thm [source] truncate_mid_test_agrees} and @{thm [source]
  truncate_children_agrees} with the same push evaluations, and closes with
  @{thm [source] truncate_state_relI} (old indices from the input relation via
  \<open>nth_append\<close>; the two new indices from the children facts +
  @{thm [source] carried_left_right_reconstruct}).\<close>
lemma truncate_branch_split_agrees:
  fixes l_num r_num :: int and k g :: nat and Q Qp P :: gmp_poly
  assumes rel: "(((todo, dqtodo, gs, rp), acc), ((todo, pqtodo), acc)) \<in> truncate_state_rel P"
    and frame: "node_frame Qp Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Qp = Q"
    and g_le: "g \<le> 4398046511104"
    and recompute: "Qp = carried_init_same_den l_num (2 ^ k) r_num P"
    and rp_eq: "rp = P"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and kbound: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_small: "length P < 1099511627776"
    and k_safe: "Suc k * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
    and todo_pushable2: "dyadic_interval_vec_pushable2 todo"
    and acc_pushable: "dyadic_interval_vec_pushable acc"
    and dq_bound: "length dqtodo + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_branch_split_monadic todo dqtodo gs acc rp l_num r_num k g Q
       \<le> \<Down> (truncate_state_rel P)
           (bisection_branch_split_monadic todo pqtodo acc l_num r_num k Qp)"
proof -
  \<comment> \<open>Facts about the plain node and the input relation's conjuncts.\<close>
  have Qp_len: "length Qp = length P"
    by (simp add: recompute truncate_length_carried_init_same_den)
  have Qpne: "0 < length Qp" and Qpbound: "length Qp + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qp_len P_len P_bound by simp_all
  obtain lns rns ks where todo_eq: "todo = (lns, rns, ks)" by (cases todo) auto
  obtain al ar ak where acc_eq: "acc = (al, ar, ak)" by (cases acc) auto
  have relD:
    "length dqtodo = length pqtodo" "length gs = length pqtodo" "rp = P"
    "length lns = length pqtodo" "length rns = length pqtodo" "length ks = length pqtodo"
    "\<forall>i < length pqtodo.
       pqtodo ! i = carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) P"
    "\<forall>i < length pqtodo. node_frame (pqtodo ! i) (dqtodo ! i) (gs ! i)"
    "\<forall>i < length pqtodo. 4398046511104 \<le> gs ! i \<longrightarrow> dqtodo ! i = pqtodo ! i"
    "\<forall>i < length pqtodo. gs ! i \<le> 4398046511104"
    using rel unfolding truncate_state_rel_def todo_eq by auto
  have pq_bound: "length pqtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    using dq_bound relD(1) by simp
  define pr where "pr \<equiv> poly (map_poly rat_of_int (Poly Qp)) (1 / 2) = 0"
  define todo' where "todo' \<equiv> (lns @ [2 * l_num, l_num + r_num],
      rns @ [l_num + r_num, 2 * r_num], ks @ [Suc k, Suc k])"
  define acc' where "acc' \<equiv> (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [Suc k])"
  define cl where "cl \<equiv> carried_left Qp"
  define cr where "cr \<equiv> carried_right Qp"
  define pfin where "pfin \<equiv> ((todo', pqtodo @ [cl, cr]), if pr then acc' else acc)"
  have twol: "2 * l_num = l_num + l_num" and twor: "2 * r_num = r_num + r_num"
    by (rule mult_2)+
  have cl_init: "cl = carried_init_same_den (2 * l_num) (2 ^ (k + 1)) (l_num + r_num) P"
    unfolding cl_def recompute twol by (rule carried_left_right_reconstruct(1))
  have cr_init: "cr = carried_init_same_den (l_num + r_num) (2 ^ (k + 1)) (2 * r_num) P"
    unfolding cr_def recompute twor by (rule carried_left_right_reconstruct(2))
  \<comment> \<open>The plain side evaluates to a literal RETURN.\<close>
  have plain_eq: "bisection_branch_split_monadic todo pqtodo acc l_num r_num k Qp
      = RETURN pfin"
  proof (cases pr)
    case True
    show ?thesis
      unfolding bisection_branch_split_monadic_def bisection_branch_split_root_monadic_def
        bisection_branch_split_nonroot_monadic_def bisection_split_pair_state_monadic_def
        bisection_push_children_monadic_def PR_CONST_def Let_def
        todo_eq acc_eq pfin_def todo'_def acc'_def cl_def cr_def
      apply (simp add: cdlr_mid_zero_eq_RETURN[OF Qpne Qpbound, folded pr_def] True
          cdlr_left_right_eq_RETURN[OF Qpne Qpbound]
          cdlr_push_children_eq[OF todo_pushable2[unfolded todo_eq] kbound]
          cdlr_push_mid_eq[OF acc_pushable[unfolded acc_eq]]
          cdlr_push2_eq[OF pq_bound]
          Qpbound kbound pq_bound todo_pushable2[unfolded todo_eq]
          acc_pushable[unfolded acc_eq])
      using Qpne Qpbound[simplified] kbound[simplified] pq_bound[simplified]
      by (auto simp: pw_eq_iff refine_pw_simps)
  next
    case False
    show ?thesis
      unfolding bisection_branch_split_monadic_def bisection_branch_split_root_monadic_def
        bisection_branch_split_nonroot_monadic_def bisection_split_pair_state_monadic_def
        bisection_push_children_monadic_def PR_CONST_def Let_def
        todo_eq acc_eq pfin_def todo'_def acc'_def cl_def cr_def
      apply (simp add: cdlr_mid_zero_eq_RETURN[OF Qpne Qpbound, folded pr_def] False
          cdlr_left_right_eq_RETURN[OF Qpne Qpbound]
          cdlr_push_children_eq[OF todo_pushable2[unfolded todo_eq] kbound]
          cdlr_push2_eq[OF pq_bound]
          Qpbound kbound pq_bound todo_pushable2[unfolded todo_eq])
      using Qpne Qpbound[simplified] kbound[simplified] pq_bound[simplified]
      by (auto simp: pw_eq_iff refine_pw_simps)
  qed
  \<comment> \<open>Relation membership of the dense final state against pfin, parameterized by the
     children facts (shared between the root/nonroot arms).\<close>
  have relI: "(((todo', dqtodo @ [ql, qr], gs @ [gl, gr], P), af),
               ((todo', pqtodo @ [cl, cr]), af')) \<in> truncate_state_rel P"
    if ch: "node_frame cl ql gl" "node_frame cr qr gr"
        "gl \<le> 4398046511104" "gr \<le> 4398046511104"
        "4398046511104 \<le> gl \<longrightarrow> ql = cl" "4398046511104 \<le> gr \<longrightarrow> qr = cr"
      and af_eq: "af = af'"
    for ql qr gl gr af af'
    unfolding af_eq
    apply (rule truncate_state_relI)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal using relD(1) by simp
    subgoal using relD(2) by simp
    subgoal
      unfolding todo'_def
      using relD(7) relD(4,5,6) relD(1) cl_init cr_init
      by (auto simp: nth_append nth_Cons split: nat.split)
    subgoal
      apply (intro allI impI)
      subgoal for i
        apply (cases "i < length pqtodo")
        subgoal using relD(8) relD(1,2) by (simp add: nth_append)
        subgoal using ch(1,2) relD(1,2) by (cases "i = length pqtodo") (simp_all add: nth_append)
        done
      done
    subgoal
      apply (intro allI impI)
      subgoal for i
        apply (cases "i < length pqtodo")
        subgoal using relD(9) relD(1,2) by (simp add: nth_append)
        subgoal using ch(5,6) relD(1,2) by (cases "i = length pqtodo") (simp_all add: nth_append)
        done
      done
    subgoal
      apply (intro allI impI)
      subgoal for i
        apply (cases "i < length pqtodo")
        subgoal using relD(10) relD(1,2) by (simp add: nth_append)
        subgoal using ch(3,4) relD(1,2) by (cases "i = length pqtodo") (simp_all add: nth_append)
        done
      done
    done
  \<comment> \<open>The one-sided dense goal.\<close>
  have main: "truncate_branch_split_monadic todo dqtodo gs acc rp l_num r_num k g Q
      \<le> SPEC (\<lambda>x. (x, pfin) \<in> truncate_state_rel P)"
    unfolding truncate_branch_split_monadic_def PR_CONST_def
    using Qne Qbound kbound P_len P_bound k_safe rp_eq
    apply (simp add: Qne Qbound kbound P_len P_bound k_safe rp_eq)
    apply (refine_vcg truncate_mid_test_agrees[where X = Qp and P = P,
          THEN order_trans])
    apply (all \<open>(use frame lock g_le recompute Qne Qbound P_len P_bound P_small
        k_safe in \<open>simp; fail\<close>)?\<close>)
    apply (clarsimp simp: pr_def[symmetric])
    subgoal premises prems1 for g''
    proof -
      from prems1 have nf: "node_frame Qp [] g''" by auto
      have "length Qp = length ([] :: gmp_poly)"
        using nf node_frameE gframe_length by blast
      thus ?thesis using Qpne by simp
    qed
    subgoal premises prems2 for x a b Q'' ba g'' rp''
    proof -
      from prems2 have nf: "node_frame Qp Q'' g''" by auto
      have "length Qp = length Q''" using nf node_frameE gframe_length by blast
      thus ?thesis using Qpbound by simp
    qed
    subgoal premises prems for x a b Q'' ba g'' rp''
    proof -
      from prems have caseF: "rp'' = P" "node_frame Qp Q'' g''"
          "g'' \<le> 4398046511104" "4398046511104 \<le> g'' \<longrightarrow> Q'' = Qp"
          "g'' < 1099511627776 \<or> 4398046511104 \<le> g''"
          "a = pr"
        unfolding pr_def by auto
      have prT: "pr" using prems caseF(6) by simp
      have Q''_len0: "length Qp = length Q''"
        using caseF(2) node_frameE gframe_length by blast
      have Q''_len: "length Q'' = length Qp" using Q''_len0 by simp
      have Q''ne: "0 < length Q''" and Q''bound: "length Q'' + 1 < max_snat LENGTH(gmp_poly_len)"
        and Q''small: "length Q'' < 1099511627776"
        using Q''_len Qpne Qpbound Qp_len P_small by simp_all
      have ch_rule: "truncate_children_monadic g'' Q'' \<le> SPEC (\<lambda>(ql, gl, qr, gr).
           node_frame cl ql gl \<and> node_frame cr qr gr \<and>
           gl \<le> 4398046511104 \<and> gr \<le> 4398046511104 \<and>
           (4398046511104 \<le> gl \<longrightarrow> ql = cl) \<and>
           (4398046511104 \<le> gr \<longrightarrow> qr = cr))"
        unfolding cl_def cr_def
        apply (rule truncate_children_agrees[where X = Qp])
        using caseF Q''ne Q''bound Q''small by auto
      show ?thesis
        unfolding truncate_branch_split_root_monadic_def PR_CONST_def
          todo_eq acc_eq caseF(1)
        using Q''ne Q''bound
        apply (simp add: Q''ne Q''bound dq_bound
            todo_pushable2[unfolded todo_eq] acc_pushable[unfolded acc_eq]
            cdlr_push_children_eq[OF todo_pushable2[unfolded todo_eq] kbound]
            cdlr_push_mid_eq[OF acc_pushable[unfolded acc_eq]]
            todo'_def[symmetric] acc'_def[symmetric])
        apply (refine_vcg ch_rule[THEN order_trans])
        apply (all \<open>(use dq_bound relD(1,2) in simp; fail)?\<close>)
        apply (clarsimp simp: cdlr_push2_eq[OF dq_bound] cdlr_append_eq relD(1,2)
            dq_bound[simplified] pfin_def prT)
        apply (all \<open>(rule order_trans[OF _ RETURN_rule], rule relI)?\<close>)
        apply (all \<open>(rule relI)?\<close>)
        by (auto simp: pfin_def prT acc_eq[symmetric])
    qed
    subgoal premises prems for x a b Q'' ba g'' rp''
    proof -
      from prems have caseF: "rp'' = P" "node_frame Qp Q'' g''"
          "g'' \<le> 4398046511104" "4398046511104 \<le> g'' \<longrightarrow> Q'' = Qp"
          "g'' < 1099511627776 \<or> 4398046511104 \<le> g''"
          "a = pr"
        unfolding pr_def by auto
      have prF: "\<not> pr" using prems caseF(6) by simp
      have Q''_len0: "length Qp = length Q''"
        using caseF(2) node_frameE gframe_length by blast
      have Q''_len: "length Q'' = length Qp" using Q''_len0 by simp
      have Q''ne: "0 < length Q''" and Q''bound: "length Q'' + 1 < max_snat LENGTH(gmp_poly_len)"
        and Q''small: "length Q'' < 1099511627776"
        using Q''_len Qpne Qpbound Qp_len P_small by simp_all
      have ch_rule: "truncate_children_monadic g'' Q'' \<le> SPEC (\<lambda>(ql, gl, qr, gr).
           node_frame cl ql gl \<and> node_frame cr qr gr \<and>
           gl \<le> 4398046511104 \<and> gr \<le> 4398046511104 \<and>
           (4398046511104 \<le> gl \<longrightarrow> ql = cl) \<and>
           (4398046511104 \<le> gr \<longrightarrow> qr = cr))"
        unfolding cl_def cr_def
        apply (rule truncate_children_agrees[where X = Qp])
        using caseF Q''ne Q''bound Q''small by auto
      show ?thesis
        unfolding truncate_branch_split_nonroot_monadic_def PR_CONST_def
          todo_eq acc_eq caseF(1)
        using Q''ne Q''bound
        apply (simp add: Q''ne Q''bound dq_bound
            todo_pushable2[unfolded todo_eq]
            cdlr_push_children_eq[OF todo_pushable2[unfolded todo_eq] kbound]
            todo'_def[symmetric])
        apply (refine_vcg ch_rule[THEN order_trans])
        apply (all \<open>(use dq_bound relD(1,2) in simp; fail)?\<close>)
        apply (clarsimp simp: cdlr_push2_eq[OF dq_bound] cdlr_append_eq relD(1,2)
            dq_bound[simplified] pfin_def prF)
        apply (all \<open>(rule order_trans[OF _ RETURN_rule], rule relI)?\<close>)
        apply (all \<open>(rule relI)?\<close>)
        by (auto simp: pfin_def prF acc_eq[symmetric])
    qed
    done
  show ?thesis
    using main unfolding plain_eq
    by (cases pr) (auto simp: pw_le_iff refine_pw_simps pfin_def todo'_def acc'_def acc_eq)
qed

text \<open>\<^bold>\<open>The split branch.\<close> The chain pop, after-pop, dispatch decomposes: count-escalate agreement is
  @{thm [source] truncate_count_escalate_agrees}; zero/one branch agreement is
  @{thm [source] truncate_branch_zero_agrees}/\<open>truncate_branch_one_agrees\<close>; the split branch's child
  geometry is @{thm [source] node_frame_child_right_tight}/@{thm [source] node_frame_child_left_impl} (the exact guards of
  @{const truncate_child_guards_mop} before re-truncation) together with \<open>carried_retrunc_mop_frame\<close>.

  The root/non-root dispatch differs between the solvers: the bisection solver tests \<open>is_root\<close> with
  @{const bisection_mid_zero_monadic} on the exact \<open>Q\<close>, while the truncating solver uses
  @{const truncate_mid_test_monadic}, whose \<open>0 < g < lock\<close> branch calls @{const poly_hom_eval_trust_half_monadic} to decide
  whether the truncated polynomial's midpoint value already certifies non-rootness. Its three branches are handled by:
  \<open>g = 0\<close> directly; \<open>g \<ge> lock\<close> by the lock-exactness conjunct of @{const truncate_state_rel}
  (\<open>g \<ge> lock \<longrightarrow> dqtodo!i = pqtodo!i\<close>, which @{const node_frame} does not imply at a nonzero guard); and otherwise
  @{thm [source] poly_hom_eval_trust_half_monadic_sound} within the trust window (the test escalates for \<open>g \<ge> 2^40\<close>).

  Escalation needs \<open>k * (length P - 1) < max_snat\<close> for the current node's \<open>k\<close>, a multiplicative bound
  (\<open>carried_init_inplace_monadic\<close>'s precondition) that the bisection solver's invariant does not provide, since that
  solver calls \<open>carried_init_inplace_monadic\<close> only once, at the seed. It is a hypothesis here and is established by the
  loop invariant.\<close>
text \<open>The k-depth-safety hypothesis (\<open>k_safe\<close> below, and its callers' \<open>k_depth_safe\<close>):
  stated as an EXTERNAL fact, the same kind of dependency as \<open>plain_correct\<close> on the final
  capstone. Content: for THIS run's root \<open>P\<close>, every node the plain loop's OWN
  reachable states ever pop keeps \<open>k\<close> within the range escalation's GMP op
  (\<open>carried_init_inplace_monadic\<close>, \<open>Carried_Kernel.thy\<close>) needs. It is not provable
  inline: the plain bisection loop invariant bounds \<open>k\<close> only
  ADDITIVELY (\<open>last ks+1<max_snat\<close>, \<open>bisection_loop_step_pre\<close>) since it never calls the op
  requiring the PRODUCT bound past its own wrapper seed; \<open>dyadic_interval_vec_pushable2\<close>
  bounds vector LENGTHS, not \<open>k\<close>'s value. The justification is a well-founded
  DECREASING companion measure — the one \<open>Bisection_Loop_Refine.thy\<close> proves via
  \<open>k+\<mu>(node_iv)+1<max_snat\<close> (\<open>carried_step_preserves_depth\<close>) for a different purpose;
  re-deriving it here needs the root-bound separation theory that motivates \<open>\<mu>\<close>.
  Isabelle's refinement combinators (\<open>WHILET_refine'\<close>,
  \<open>WHILEI_refine_new_invar\<close>) cannot bootstrap an unboundedly-growing quantity into a bounded
  one without such a measure: both variants' \<open>STEP_REF\<close>/\<open>STEP_INV\<close> obligations require
  exactly the fact being proven as their own hypothesis one level up. Violating the bound
  needs bisection depth \<open>max_snat/(length P-1)\<close>, i.e. thousands of trillions of levels.\<close>
text \<open>The two worklist pops as literal RETURN equalities (ASSERT/RETURN-composed).\<close>
lemma cdlr_poly_vec_pop_eq:
  assumes "qs \<noteq> []"
  shows "poly_vec_pop_last_monadic qs = RETURN (last qs, butlast qs)"
  using assms unfolding poly_vec_pop_last_monadic_def
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma cdlr_exp_pop_eq:
  assumes "ks \<noteq> []"
  shows "dyadic_exp_pop_last_monadic ks = RETURN (last ks, butlast ks)"
  using assms unfolding dyadic_exp_pop_last_monadic_def mop_list_pop_last_alt
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma cdlr_node_frame_len:
  assumes "node_frame X Y g"
  shows "length X = length Y"
  using assms node_frameE gframe_length by blast

lemma cdlr_todo_pop_eq:
  assumes "lns \<noteq> []" "length rns = length lns" "length ks = length lns"
  shows "dyadic_interval_vec_pop_last_monadic (lns, rns, ks)
       = RETURN ((last lns, last rns, last ks), butlast lns, butlast rns, butlast ks)"
  using assms
  unfolding dyadic_interval_vec_pop_last_monadic_def poly_pop_coeff_monadic_def
    dyadic_exp_pop_last_monadic_def mop_list_pop_last_alt
    dyadic_interval_vec_invar_def PR_CONST_def Let_def
  by (auto simp: pw_eq_iff refine_pw_simps)

text \<open>The after-pop chains agree: the dense count-escalate couples against the plain
  truncated count via their SHARED exact-count classification (the plain side is
  productive but its value opaque — a genuine two-sided coupling, unlike the
  deterministic split leaves), and the three dispatch arms delegate to their proven
  per-branch agreements.\<close>
lemma truncate_after_pop_agrees:
  fixes l_num r_num :: int and k g :: nat and Q Qp P :: gmp_poly
  assumes rel: "(((todo, dqtodo, gs, rp), acc), ((todo, pqtodo), acc)) \<in> truncate_state_rel P"
    and frame: "node_frame Qp Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Qp = Q"
    and g_le: "g \<le> 4398046511104"
    and recompute: "Qp = carried_init_same_den l_num (2 ^ k) r_num P"
    and rp_eq: "rp = P"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and kbound: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_small: "length P < 1099511627776"
    and k_safe: "Suc k * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
    and todo_pushable2: "dyadic_interval_vec_pushable2 todo"
    and acc_pushable: "dyadic_interval_vec_pushable acc"
    and dq_bound: "length dqtodo + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_after_pop_monadic todo dqtodo gs acc rp l_num r_num k g Q
       \<le> \<Down> (truncate_state_rel P) (bisection_after_pop_monadic todo pqtodo acc l_num r_num k Qp)"
proof -
  have k_safe': "k * (length P - 1) < max_snat LENGTH(gmp_poly_len)" using k_safe by simp
  have Qp_len: "length Qp = length P"
    by (simp add: recompute truncate_length_carried_init_same_den)
  have Q_len: "length Qp = length Q" using frame node_frameE gframe_length by blast
  have QlenP: "length Q = length P" using Q_len Qp_len by simp
  have Qpne: "0 < length Qp" and Qpbound: "length Qp + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qp_len P_len P_bound by simp_all
  have pbound: "length Q * nat_bitlen (length Q) < max_snat LENGTH(gmp_poly_len)"
    using cdlr_pbound_from_small QlenP P_small by simp
  have gbound: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    using g_le QlenP P_small unfolding max_snat_def by simp
  \<comment> \<open>The dense count-escalate against the plain truncated count, coupled by the
     shared classification against @{const carried_descartes_count} of the SAME node.\<close>
  have truncate_count: "truncate_count_escalate_monadic Q g l_num r_num k rp
      \<le> SPEC (\<lambda>(cnt, Q', g', rp').
           rp' = P \<and> node_frame Qp Q' g' \<and>
           g' \<le> 4398046511104 \<and> (4398046511104 \<le> g' \<longrightarrow> Q' = Qp) \<and>
           (cnt = 0) = (carried_descartes_count Qp = 0) \<and>
           (cnt = 1) = (carried_descartes_count Qp = 1) \<and>
           (2 \<le> cnt) = (2 \<le> carried_descartes_count Qp))"
    using truncate_count_escalate_agrees[where l = l_num and r = r_num and k = k
        and P = P and Q = Q and g = g and rp = rp,
        folded recompute]
    using frame rp_eq Qbound pbound gbound lock g_le P_len P_bound k_safe'
    by (simp add: recompute[symmetric])
  have plain_count: "carried_descartes_count_trunc_monadic Qp \<le> SPEC (\<lambda>cnt'.
           (cnt' = 0) = (carried_descartes_count Qp = 0) \<and>
           (cnt' = 1) = (carried_descartes_count Qp = 1) \<and>
           (2 \<le> cnt') = (2 \<le> carried_descartes_count Qp))"
    using carried_descartes_count_trunc_monadic_classify[OF Qpbound] .
  obtain cv where cv: "inres (carried_descartes_count_trunc_monadic Qp) cv"
    using cdlr_ex_inres_count_trunc by blast
  have nfp: "nofail (carried_descartes_count_trunc_monadic Qp)"
    using plain_count by (auto simp: pw_le_iff)
  have cvF: "(cv = 0) = (carried_descartes_count Qp = 0)"
      "(cv = 1) = (carried_descartes_count Qp = 1)"
      "(2 \<le> cv) = (2 \<le> carried_descartes_count Qp)"
    using plain_count nfp cv by (auto simp: pw_le_iff)
  have lowp: "RETURN cv \<le> carried_descartes_count_trunc_monadic Qp"
    using nfp cv by (simp add: pw_le_iff)
  have count_cpl: "truncate_count_escalate_monadic Q g l_num r_num k rp
      \<le> \<Down> {((cnt, Q', g', rp'), cnt').
            rp' = P \<and> node_frame Qp Q' g' \<and>
            g' \<le> 4398046511104 \<and> (4398046511104 \<le> g' \<longrightarrow> Q' = Qp) \<and>
            (cnt = 0) = (cnt' = 0) \<and> (cnt = 1) = (cnt' = 1) \<and> (2 \<le> cnt) = (2 \<le> cnt')}
          (carried_descartes_count_trunc_monadic Qp)"
  proof -
    have step1: "truncate_count_escalate_monadic Q g l_num r_num k rp
        \<le> \<Down> {((cnt, Q', g', rp'), cnt').
              rp' = P \<and> node_frame Qp Q' g' \<and>
              g' \<le> 4398046511104 \<and> (4398046511104 \<le> g' \<longrightarrow> Q' = Qp) \<and>
              (cnt = 0) = (cnt' = 0) \<and> (cnt = 1) = (cnt' = 1) \<and> (2 \<le> cnt) = (2 \<le> cnt')}
            (RETURN cv)"
      apply (rule order_trans[OF truncate_count])
      using cvF by (auto simp: pw_le_iff refine_pw_simps)
    have step2: "\<Down> {((cnt, Q', g', rp'), cnt').
              rp' = P \<and> node_frame Qp Q' g' \<and>
              g' \<le> 4398046511104 \<and> (4398046511104 \<le> g' \<longrightarrow> Q' = Qp) \<and>
              (cnt = 0) = (cnt' = 0) \<and> (cnt = 1) = (cnt' = 1) \<and> (2 \<le> cnt) = (2 \<le> cnt')}
            (RETURN cv)
        \<le> \<Down> {((cnt, Q', g', rp'), cnt').
              rp' = P \<and> node_frame Qp Q' g' \<and>
              g' \<le> 4398046511104 \<and> (4398046511104 \<le> g' \<longrightarrow> Q' = Qp) \<and>
              (cnt = 0) = (cnt' = 0) \<and> (cnt = 1) = (cnt' = 1) \<and> (2 \<le> cnt) = (2 \<le> cnt')}
            (carried_descartes_count_trunc_monadic Qp)"
      using lowp by (auto simp: pw_le_iff refine_pw_simps)
    show ?thesis by (rule order_trans[OF step1 step2])
  qed
  show ?thesis
    unfolding truncate_after_pop_monadic_def bisection_after_pop_monadic_def
      truncate_dispatch_monadic_def PR_CONST_def
    using Qne Qbound kbound Qpne Qpbound
    apply (simp add: Qne Qbound kbound Qpne Qpbound)
    apply (refine_vcg count_cpl)
    subgoal using Qpne by (auto dest: cdlr_node_frame_len)
    subgoal using Qpbound[simplified] by (auto dest: cdlr_node_frame_len)
    subgoal using P_len by auto
    subgoal using P_bound[simplified] by auto
    subgoal using k_safe'[simplified] by auto
    subgoal by auto
    subgoal using rel rp_eq by (auto intro!: truncate_branch_zero_agrees)
    subgoal by auto
    subgoal using rel rp_eq acc_pushable by (auto intro!: truncate_branch_one_agrees)
    subgoal premises prems for x cnt x1 x2 x1a x2a x1b x2b
    proof -
      have relP: "(((todo, dqtodo, gs, P), acc), ((todo, pqtodo), acc)) \<in> truncate_state_rel P"
        using rel rp_eq by simp
      have mem: "x2b = P" "node_frame Qp x1a x1b" "x1b \<le> 4398046511104"
          "4398046511104 \<le> x1b \<longrightarrow> x1a = Qp"
        using prems by auto
      have Qne'': "0 < length x1a" using prems by simp
      have Qbound'': "length x1a + 1 < max_snat LENGTH(gmp_poly_len)"
        using prems by simp
      show ?thesis
        unfolding mem(1)
        apply (rule truncate_branch_split_agrees[OF relP mem(2) _ mem(3) recompute])
        subgoal using mem(4) by auto
        using Qne'' Qbound'' kbound P_len P_bound P_small k_safe
          todo_pushable2 acc_pushable dq_bound by auto
    qed
    done
qed

lemma truncate_pop_poly_args_agrees:
  assumes dqtodo_len: "length dqtodo = length pqtodo"
    and gs_len: "length gs = length pqtodo"
    and frame: "\<forall>i < length pqtodo. node_frame (pqtodo ! i) (dqtodo ! i) (gs ! i)"
    and lock_all: "\<forall>i < length pqtodo. 4398046511104 \<le> gs ! i \<longrightarrow> dqtodo ! i = pqtodo ! i"
    and gs_bound_all: "\<forall>i < length pqtodo. gs ! i \<le> 4398046511104"
    and recompute_rest: "case todo of (lns, rns, ks) \<Rightarrow>
        length lns = length pqtodo - 1 \<and> length rns = length pqtodo - 1 \<and>
        length ks = length pqtodo - 1 \<and>
        (\<forall>i < length pqtodo - 1.
           pqtodo ! i = carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) P)"
    and recompute_last: "last pqtodo = carried_init_same_den l_num (2 ^ k) r_num P"
    and rp_eq: "rp = P"
    and pop_pre: "bisection_pop_poly_args_pre todo pqtodo acc k"
    and qne: "pqtodo \<noteq> []"
    and last_ne: "last pqtodo \<noteq> []"
    and last_bound: "Suc (length (last pqtodo)) < max_snat LENGTH(gmp_poly_len)"
    and kbound: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and todo_pushable2: "dyadic_interval_vec_pushable2 todo"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_small: "length P < 1099511627776"
    and k_safe: "Suc k * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_pop_poly_args_monadic todo dqtodo gs acc rp l_num r_num k
       \<le> \<Down> (truncate_state_rel P) (bisection_pop_poly_args_monadic todo pqtodo acc l_num r_num k)"
proof -
  have len_pos: "0 < length pqtodo" using qne by simp
  have dq_ne: "dqtodo \<noteq> []" and gs_ne: "gs \<noteq> []"
    using qne dqtodo_len gs_len by auto
  define Q where "Q \<equiv> last dqtodo"
  define Qp where "Qp \<equiv> last pqtodo"
  define g where "g \<equiv> last gs"
  have Q_nth: "Q = dqtodo ! (length pqtodo - 1)"
    unfolding Q_def using dqtodo_len last_conv_nth[OF dq_ne] by simp
  have Qp_nth: "Qp = pqtodo ! (length pqtodo - 1)"
    unfolding Qp_def using last_conv_nth[OF qne] by simp
  have g_nth: "g = gs ! (length pqtodo - 1)"
    unfolding g_def using gs_len last_conv_nth[OF gs_ne] by simp
  have frame_last: "node_frame Qp Q g"
    using frame[rule_format, of "length pqtodo - 1"] len_pos
    unfolding Q_nth Qp_nth g_nth by simp
  have lock_last: "4398046511104 \<le> g \<longrightarrow> Qp = Q"
    using lock_all[rule_format, of "length pqtodo - 1"] len_pos
    unfolding Q_nth Qp_nth g_nth by auto
  have g_le_last: "g \<le> 4398046511104"
    using gs_bound_all[rule_format, of "length pqtodo - 1"] len_pos
    unfolding g_nth by simp
  have rec_last: "Qp = carried_init_same_den l_num (2 ^ k) r_num P"
    unfolding Qp_def by (rule recompute_last)
  have Qp_len: "length Qp = length P"
    by (simp add: rec_last truncate_length_carried_init_same_den)
  have Q_lenQp: "length Qp = length Q" using frame_last cdlr_node_frame_len by blast
  have Qne: "0 < length Q" and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    using Q_lenQp Qp_len P_len P_bound by simp_all
  \<comment> \<open>The residual (post-pop) states are coupled.\<close>
  have popD: "bisection_pop_poly_args_pre todo pqtodo acc k"
    using pop_pre .
  have acc_pushable: "dyadic_interval_vec_pushable acc"
    and dq_bound0: "length (butlast pqtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    using pop_pre unfolding bisection_pop_poly_args_pre_def by auto
  have dq_bound: "length (butlast dqtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    using dq_bound0 dqtodo_len by simp
  have rel_rest: "(((todo, butlast dqtodo, butlast gs, P), acc),
                   ((todo, butlast pqtodo), acc)) \<in> truncate_state_rel P"
  proof -
    obtain lns rns ks where todo_eq: "todo = (lns, rns, ks)" by (cases todo) auto
    show ?thesis
      unfolding todo_eq
      apply (rule truncate_state_relI)
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal using dqtodo_len by simp
      subgoal using gs_len by simp
      subgoal using recompute_rest unfolding todo_eq
        by (auto simp: nth_butlast)
      subgoal using frame dqtodo_len gs_len
        by (auto simp: nth_butlast)
      subgoal using lock_all dqtodo_len gs_len
        by (auto simp: nth_butlast)
      subgoal using gs_bound_all gs_len
        by (auto simp: nth_butlast)
      done
  qed
  have after: "truncate_after_pop_monadic todo (butlast dqtodo) (butlast gs) acc P
        l_num r_num k g Q
      \<le> \<Down> (truncate_state_rel P)
          (bisection_after_pop_monadic todo (butlast pqtodo) acc l_num r_num k Qp)"
    apply (rule truncate_after_pop_agrees[OF rel_rest frame_last lock_last g_le_last
          rec_last])
    using Qne Qbound kbound P_len P_bound P_small k_safe todo_pushable2 acc_pushable
      dq_bound by auto
  show ?thesis
    unfolding truncate_pop_poly_args_monadic_def bisection_pop_poly_args_monadic_def
      PR_CONST_def
    apply (simp add: cdlr_poly_vec_pop_eq[OF dq_ne] cdlr_poly_vec_pop_eq[OF qne]
        cdlr_exp_pop_eq[OF gs_ne] pop_pre dq_ne gs_ne
        Q_def[symmetric] Qp_def[symmetric] g_def[symmetric])
    using Qne Qbound kbound P_len P_bound P_small k_safe todo_pushable2 acc_pushable
      dq_bound rp_eq
    apply (simp add: rp_eq)
    using after k_safe dqtodo_len dq_bound0
    by (auto simp: pw_le_iff refine_pw_simps)
qed

text \<open>\<^bold>\<open>The step precondition.\<close> The truncating step asserts \<open>dyadic_interval_vec_invar todo\<close> and \<open>lns \<noteq> []\<close> before
  the pop, while the bisection step (\<open>bisection_pop_poly_args_monadic\<close>) asserts a longer chain after the pop
  (\<open>pqtodo \<noteq> []\<close>, length and budget bounds, \<open>bisection_pop_poly_args_pre\<close>), which comes from
  \<open>bisection_loop_step_pre ps\<close>, i.e. from the bisection loop's \<open>bisection_loop_safe_invar\<close>, and does not follow from
  \<open>truncate_state_rel\<close>. So \<open>truncate_loop_step_refine\<close> takes \<open>bisection_loop_step_pre ps\<close> as a hypothesis; the
  truncating side's own assertions follow from \<open>ptodo = dtodo\<close>. The branch dispatch matches one to one
  (\<open>truncate_branch_zero/one/split_monadic\<close> against \<open>carried_branch_zero/one/split_monadic\<close>, with \<open>split\<close> forking into
  \<open>_root\<close>/\<open>_nonroot\<close> on both sides); in the split branch, @{thm [source] carried_left_right_reconstruct} re-establishes the
  children's recompute invariant and @{thm [source] carried_retrunc_mop_frame} their \<open>node_frame\<close>.\<close>
lemma truncate_loop_step_refine:
  assumes rel: "(ds, ps) \<in> truncate_state_rel P"
    and pre: "bisection_loop_step_pre ps"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_small: "length P < 1099511627776"
    and k_depth_safe: "\<And>tD qD acD kD.
        bisection_pop_poly_args_pre tD qD acD kD \<Longrightarrow>
        Suc kD * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_loop_step_monadic ds \<le> \<Down> (truncate_state_rel P) (bisection_loop_step_monadic ps)"
  using rel[unfolded truncate_state_rel_def]
  unfolding truncate_loop_step_monadic_def bisection_loop_step_monadic_def
  apply clarsimp
  unfolding truncate_loop_step_args_monadic_def bisection_loop_step_args_monadic_def
    PR_CONST_def
  using pre k_depth_safe
  unfolding bisection_loop_step_pre_def bisection_loop_state_invar_def bisection_loop_cond_def
  apply (clarsimp simp: dyadic_interval_vec_invar_def)
  apply (simp add: cdlr_todo_pop_eq)
  apply (refine_vcg)
  apply (rule truncate_pop_poly_args_agrees)
  apply (all \<open>(assumption; fail)?\<close>)
  apply (all \<open>(rule k_depth_safe; assumption; fail)?\<close>)
  using P_len P_bound P_small
  apply (all \<open>(simp; fail)?\<close>)
  apply (all \<open>(auto simp: nth_butlast last_conv_nth list_all_length; fail)?\<close>)
  subgoal premises p for a aa b dqtodo gs ab ac ba pqtodo
  proof -
    have bne: "b \<noteq> []" and aane: "aa \<noteq> []"
      using p by auto
    show ?thesis
      using p by (simp add: last_conv_nth bne aane)
  qed
  done

text \<open>The loop condition agrees on coupled states (both test the shared \<open>todo\<close> column's
  first component being nonempty).\<close>
lemma truncate_loop_cond_agree:
  assumes "(ds, ps) \<in> truncate_state_rel P"
  shows "truncate_loop_cond ds = bisection_loop_cond ps"
  using assms
  unfolding truncate_state_rel_def truncate_loop_cond_def bisection_loop_cond_def
  by (auto split: prod.splits)

section \<open>Lifting the step refinement over the WHILEIT\<close>

text \<open>@{const truncate_loop_monadic} refines @{const bisection_loop_monadic} under the
  coupling, via \<open>WHILEIT_refine\<close> fed the step keystone + cond agreement + a related
  initial state. The seed's \<open>bisection_loop_safe_invar\<close> is exactly what supplies
  \<open>truncate_loop_step_refine\<close>'s \<open>bisection_loop_step_pre\<close> premise at each iteration
  (\<open>bisection_loop_safe_invar\<close>'s own definition is \<open>bisection_loop_state_invar st \<and>
  (bisection_loop_cond st \<longrightarrow> bisection_loop_step_pre st)\<close> — precisely the per-iteration
  obligation \<open>WHILEIT_refine\<close> re-establishes from the invariant argument).\<close>
lemma truncate_loop_refine:
  assumes rel: "((dtodo, dqtodo, dgs, drp), dacc) \<in>
             {s. \<exists>p. (s, p) \<in> truncate_state_rel P \<and> p = ((ptodo, pqtodo), pacc)}"
    and safe: "bisection_loop_safe_invar ((ptodo, pqtodo), pacc)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_small: "length P < 1099511627776"
    and k_depth_safe_all: "\<And>tD qD acD kD. bisection_pop_poly_args_pre tD qD acD kD \<Longrightarrow>
        Suc kD * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_loop_monadic dtodo dqtodo dgs dacc drp
       \<le> \<Down> (truncate_state_rel P) (bisection_loop_monadic ptodo pqtodo pacc)"
  using rel
  unfolding truncate_loop_monadic_def bisection_loop_monadic_def
    truncate_loop_stateful_monadic_def bisection_loop_stateful_monadic_def
    truncate_loop_body_checked_monadic_def bisection_loop_body_checked_monadic_def
    PR_CONST_def
  apply clarsimp
  apply (rule WHILET_refine'[where R = "truncate_state_rel P"])
  subgoal using safe by simp
  subgoal using truncate_loop_cond_agree by blast
  subgoal for a aa b ab ac ba x x'
    using truncate_loop_step_refine[of x x' P] P_len P_bound P_small k_depth_safe_all
    unfolding bisection_loop_safe_invar_def
    by auto
  done

section \<open>The wrapper refinement + the inherited dsc_int capstone\<close>

text \<open>The main-list wrapper refines the bisection solver's wrapper. The bisection wrapper also initialises the root
  node before calling \<open>bisection_main_list\<close> (\<open>carried_init_inplace\<close> of the input, then the loop), so the comparison target
  is \<open>bisection_main_list l_num r_num k q0\<close> with the same initialised \<open>q0\<close>, not \<open>bisection_main_list l_num r_num k P\<close>
  (\<open>carried_init_same_den\<close> is a Taylor shift and scaling, not an identity, on a non-trivial box). \<open>P\<close>/\<open>rp\<close> are needed only to
  define \<open>q0\<close> and to anchor escalations through \<open>truncate_state_rel\<close>'s recompute invariant.

  Under \<open>q0 = carried_init_same_den l_num (2^k) r_num P\<close> and \<open>rp = P\<close>, the seeded worklists are @{const node_frame}-coupled at
  \<open>g = 0\<close> (where \<open>node_frame\<close> is equality), and the result \<open>acc\<close> is identical (\<open>\<Down>Id\<close>, since \<open>truncate_state_rel\<close> forces
  \<open>dacc = pacc\<close>).\<close>
text \<open>\<^bold>\<open>Proof strategy.\<close> Every prefix operation in both wrappers is deterministic (\<open>poly_empty_sz\<close>/
  \<open>poly_vec_empty_sz\<close> are unconditional \<open>RETURN\<close>s; the pushes and appends are \<open>ASSERT + RETURN\<close> with numeric assertions on
  the concrete seeds; \<open>COPY\<close> is the identity; the cleanup frees are \<open>RETURN ()\<close>, including
  @{thm [source] poly_free_monadic_eq_RETURN}). So both programs are simp-evaluated down to their concrete seed states
  (the construction of \<open>gs\<close> evaluates away), leaving the truncating loop call against \<open>ASSERT safe_invar\<close>, the bisection
  loop call and coupled cleanups. @{thm [source] truncate_loop_refine} closes the loop, and the cleanup closes pointwise
  from the relation's \<open>todo\<close>/\<open>acc\<close> equalities and the length of \<open>qtodo\<close>. The three extra hypotheses cover the truncating
  program's own \<open>rp\<close> assertions (\<open>0 < length P\<close> etc.), which the bisection side never sees; they are the Sepref
  implementation's preconditions.\<close>
lemma truncate_main_list_refine:
  assumes q0_eq: "q0 = carried_init_same_den l_num (2 ^ k) r_num P"
    and rp_eq: "rp = P"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_small: "length P < 1099511627776"
    and k_bound: "k * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
    and k_depth_safe_all: "\<And>tD qD acD kD. bisection_pop_poly_args_pre tD qD acD kD \<Longrightarrow>
        Suc kD * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_main_list l_num r_num k q0 rp
       \<le> \<Down> Id (bisection_main_list l_num r_num k q0)"
proof -
  have len_q0: "length q0 = length P"
    by (simp add: q0_eq truncate_length_carried_init_same_den)
  have loopref: "truncate_loop_monadic ([l_num], [r_num], [k]) [q0] [0] ([], [], []) P
      \<le> \<Down> (truncate_state_rel P) (bisection_loop_monadic ([l_num], [r_num], [k]) [q0] ([], [], []))"
    if safe: "bisection_loop_safe_invar ((([l_num], [r_num], [k]), [q0]), ([], [], []))"
  proof (rule truncate_loop_refine)
    show "((([l_num], [r_num], [k]), [q0], [0], P), ([], [], []))
        \<in> {s. \<exists>p. (s, p) \<in> truncate_state_rel P \<and>
             p = ((([l_num], [r_num], [k]), [q0]), ([], [], []))}"
      apply (intro CollectI exI conjI)
       apply (rule truncate_state_relI)
      by (simp_all add: q0_eq node_frame_exact)
    show "bisection_loop_safe_invar ((([l_num], [r_num], [k]), [q0]), ([], [], []))"
      by (rule safe)
    show "0 < length P" by (rule P_len)
    show "length P + 1 < max_snat LENGTH(gmp_poly_len)" by (rule P_bound)
    show "length P < 1099511627776" by (rule P_small)
    show "\<And>tD qD acD kD. bisection_pop_poly_args_pre tD qD acD kD \<Longrightarrow>
        Suc kD * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
      by (rule k_depth_safe_all)
  qed
  show ?thesis
    unfolding truncate_main_list_def bisection_main_list_def
      dyadic_interval_vec_empty_sz_monadic_def poly_empty_sz_monadic_def
      poly_push_coeff_monadic_def poly_vec_empty_sz_monadic_def poly_vec_push_monadic_def
      poly_vec_free_empty_monadic_def dyadic_interval_vec_free_monadic_def
      mop_free_def mop_list_append_alt COPY_def PR_CONST_def
    using P_len P_bound k_bound len_q0 rp_eq
    apply (simp add: max_snat_def Let_def dyadic_interval_vec_pushable_def)
    apply (rule assert.le_ASSERTI)
    apply (rule refine_IdD)
    apply (rule bind_refine[where R' = "truncate_state_rel P"])
     apply (rule loopref)
     apply assumption
    apply (auto simp: truncate_state_rel_def pw_le_iff refine_pw_simps split: prod.splits)
    done
qed

text \<open>CAPSTONE: the dense solver's output multiset equals @{term dsc_int} — the same
  guarantee the plain bisection solver carries. Composes the wrapper refinement above with the
  plain solver's own correctness fact, taken here as an EXTERNAL premise
  \<open>plain_correct\<close> (proved as \<open>bilr_main_list_impl_refine_dsc_int\<close> /
  \<open>carried_gmp_main_seed_mset_dsc_int\<close> in \<open>Bisection_Loop_Refine.thy\<close>, which this theory
  does not import). This external fact is about \<open>bisection_main_list\<close> applied to WHATEVER poly
  the caller passes (\<open>carried_gmp_main_seed_mset_dsc_int\<close>'s own shape targets \<open>dsc_int 0 1 (Poly
  <argument>)\<close>, with \<open>l_num\<close>/\<open>r_num\<close>/\<open>k\<close> only labelling the OUTPUT triples via \<open>phi\<close>/
  \<open>node_iv\<close>, not selecting which polynomial's roots are computed) — so instantiating it
  at \<open>q0\<close> (matching the real wrapper's own call, see the note above) is the correct use.\<close>
lemma truncate_main_list_mset_dsc_int:
  assumes q0_eq: "q0 = carried_init_same_den l_num (2 ^ k) r_num P"
    and rp_eq: "rp = P"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_small: "length P < 1099511627776"
    and k_bound: "k * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
    and k_depth_safe_all: "\<And>tD qD acD kD. bisection_pop_poly_args_pre tD qD acD kD \<Longrightarrow>
        Suc kD * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
    and plain_correct:
      "bisection_main_list l_num r_num k q0 \<le> SPEC (\<lambda>acc. Q acc)"
  shows "truncate_main_list l_num r_num k q0 rp \<le> SPEC (\<lambda>acc. Q acc)"
  using truncate_main_list_refine[OF q0_eq rp_eq P_len P_bound P_small k_bound
    k_depth_safe_all] plain_correct
  by (simp add: pw_le_iff refine_pw_simps)

end
