theory Hybrid_Loop_Refine
  imports "IsaRRI_Refine.Bail_Loop_Refine"
          "IsaRRI_Refine.Truncate_Loop_Refine"
          "IsaRRI_LLVM.Hybrid_Solver_Pipeline"
begin

text \<open>The \<open>\<exists>pol\<close> loop refinement for the hybrid solver.

  \<^bold>\<open>Why the hybrid loop is not refined step for step against the bail solver.\<close> The hybrid loop
  pushes an ambiguous child with the sentinel class \<open>4\<close> and resolves it only at pop
  (@{const hybrid_resolve_count_monadic}); but the push-time sentinel already feeds
  @{const hybrid_split_run_len} (in @{const hybrid_split_pair_state_monadic}; the shared
  @{const newton_split_run_len} keeps the plain nonzero test), so the hybrid solver's \<open>\<sigma>\<close>, hence its
  gate decisions, hence its tree, can diverge from the bail solver's whenever an ambiguous child's true
  count is \<open>0\<close>. That is real information loss in the cheap \<open>g\<close>-count (the classification contract gives
  no guarantee at \<open>dec = False\<close>), so neither \<open>lazy \<le> \<Down>Id bail\<close> nor an eager-escalation equivalence can
  hold literally.

  \<^bold>\<open>Why an existential policy works instead\<close>:
  \<^enum> In @{const newdsc_pol_bail}'s recursion, the threaded \<open>s\<close> affects the output only through \<open>pol\<close>'s
    inputs (it is passed to \<open>pol\<close> and recomputed for children via @{const split_run_len_real}). A policy
    that ignores its \<open>s\<close> argument makes the \<open>\<sigma>\<close>-divergence irrelevant.
  \<^enum> @{thm [source] newdsc_pol_bail_sound}, @{thm [source] newdsc_pol_bail_complete}, domain totality,
    and the int/real bridge @{thm [source] newdsc_pol_bail_int_eq_newdsc_pol_bail} all hold for every
    \<open>pol\<close>, so an existential keystone composes with them as the bail solver's \<open>pol_final\<close> one does.
  \<^enum> Every node of one run's tree has a unique \<open>(a, b)\<close> view (widths strictly shrink along every edge,
    and sibling subtrees have disjoint interiors), so the solver's actual gate decisions can always be
    recorded as some policy.

  \<^bold>\<open>Proof architecture.\<close> The pure LIFO driver and order-agnostic tree decomposition of the bail
  refinement are reused with \<open>pol\<close> free, and the bail invariant's \<open>\<sigma>\<close>-alignment conjunct is replaced by a
  partial decision map \<open>D\<close>: the invariant quantifies over every \<open>pol\<close> extending \<open>D\<close>, and each pop extends
  \<open>D\<close> at the popped node's fresh view with the decision the implementation took. The truncation coupling
  (node polynomials against their exact versions, the guard column, escalation from \<open>rp\<close>) reuses the
  devices of the truncating loop (@{term truncate_state_rel}'s conjuncts, the escalation correctness and
  \<open>g\<close>-count classification contracts).\<close>

section \<open>The compatible-interval-family device (well-definedness of the
  run-derived policy)\<close>

text \<open>\<^bold>\<open>Why this section exists.\<close> The \<open>\<exists>pol\<close> keystone's witness policy is built by RECORDING,
  for every node the impl actually visits, the decision it took, keyed by the node's
  \<open>(a,b)\<close> view (a policy that ignores its \<open>e\<close>/\<open>dk\<close>/\<open>(s,v)\<close> arguments — see the file header
  — sidesteps the \<open>\<sigma>\<close> divergence entirely, since the abstract recursion's OWN \<open>s\<close>-thread
  never needs to match the impl's). For this lookup to be well-defined, no two DISTINCT
  pop events may ever record the SAME \<open>(a,b)\<close> view. This section proves that: it tracks a
  PAIRWISE-COMPATIBLE family of intervals (properly nested or interior-disjoint, which for
  proper \<open>a<b\<close> intervals excludes equality) across \<open>D\<close> (already-decided views) and
  \<open>todo\<close> (still-live views), and shows the invariant survives every one of the three loop
  transitions (discard/accept \<open>\<Rightarrow>\<close> move to \<open>D\<close>, no new todo; window-accept \<open>\<Rightarrow>\<close> move to
  \<open>D\<close> + push ONE strictly-narrower child; split \<open>\<Rightarrow>\<close> move to \<open>D\<close> + push TWO
  strictly-narrower, mutually-disjoint children). Pure \<open>rat \<times> rat\<close> combinatorics —
  independent of any concrete GMP state; the concrete sections below instantiate it via
  @{const dyadic_iv_node_iv_of}.\<close>

subsection \<open>Interval algebra\<close>

definition alr_ivl_disjoint :: "rat \<times> rat \<Rightarrow> rat \<times> rat \<Rightarrow> bool" where
  "alr_ivl_disjoint X Y \<longleftrightarrow> snd X \<le> fst Y \<or> snd Y \<le> fst X"

definition alr_ivl_subset :: "rat \<times> rat \<Rightarrow> rat \<times> rat \<Rightarrow> bool" where
  "alr_ivl_subset X Y \<longleftrightarrow> fst Y \<le> fst X \<and> snd X \<le> snd Y"

text \<open>Proper (strict) subset: @{const alr_ivl_subset} plus \<open>X \<noteq> Y\<close> — equivalently, at least one
  bound is a strict inequality (immediate from @{const alr_ivl_subset}'s two \<open>\<le>\<close>s).\<close>
definition alr_ivl_pss :: "rat \<times> rat \<Rightarrow> rat \<times> rat \<Rightarrow> bool" where
  "alr_ivl_pss X Y \<longleftrightarrow> alr_ivl_subset X Y \<and> X \<noteq> Y"

definition alr_ivl_compat :: "rat \<times> rat \<Rightarrow> rat \<times> rat \<Rightarrow> bool" where
  "alr_ivl_compat X Y \<longleftrightarrow> alr_ivl_pss X Y \<or> alr_ivl_pss Y X \<or> alr_ivl_disjoint X Y"

lemma alr_ivl_subset_refl: "alr_ivl_subset X X" by (simp add: alr_ivl_subset_def)

lemma alr_ivl_subset_trans:
  assumes "alr_ivl_subset X V" and "alr_ivl_subset V Y" shows "alr_ivl_subset X Y"
  using assms by (auto simp: alr_ivl_subset_def)

text \<open>Under the \<open>alr_ivl_subset\<close> bound inequalities, \<open>X \<noteq> V\<close> forces a strict inequality on at least one
  coordinate (\<open>X = V\<close> would need both coordinates equal).\<close>
lemma alr_ivl_subset_neq_strict:
  fixes X V :: "rat \<times> rat"
  assumes "fst V \<le> fst X" and "snd X \<le> snd V" and "X \<noteq> V"
  shows "fst V < fst X \<or> snd X < snd V"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence neg1: "\<not> fst V < fst X" and neg2: "\<not> snd X < snd V" by simp_all
  have f1: "fst V = fst X" using assms(1) neg1 by linarith
  have f2: "snd X = snd V" using assms(2) neg2 by linarith
  from f1 f2 have "X = V" by (metis prod_eqI)
  thus False using assms(3) by simp
qed

lemma alr_ivl_pss_subset_trans:
  assumes "alr_ivl_pss X V" and "alr_ivl_subset V Y" shows "alr_ivl_pss X Y"
proof -
  have sub: "alr_ivl_subset X Y" using assms by (auto simp: alr_ivl_pss_def alr_ivl_subset_def)
  have neq: "X \<noteq> Y"
  proof
    assume eq: "X = Y"
    from assms(1) have xv: "fst V \<le> fst X" "snd X \<le> snd V" "X \<noteq> V"
      by (auto simp: alr_ivl_pss_def alr_ivl_subset_def)
    have strict: "fst V < fst X \<or> snd X < snd V" by (rule alr_ivl_subset_neq_strict[OF xv])
    from assms(2) have "fst Y \<le> fst V" "snd V \<le> snd Y" by (auto simp: alr_ivl_subset_def)
    with eq xv have "fst V = fst X \<and> snd X = snd V" by auto
    with strict show False by auto
  qed
  from sub neq show ?thesis by (simp add: alr_ivl_pss_def)
qed

lemma alr_ivl_subset_pss_trans:
  assumes "alr_ivl_subset X V" and "alr_ivl_pss V Y" shows "alr_ivl_pss X Y"
proof -
  have sub: "alr_ivl_subset X Y" using assms by (auto simp: alr_ivl_pss_def alr_ivl_subset_def)
  have neq: "X \<noteq> Y"
  proof
    assume eq: "X = Y"
    from assms(1) have xv: "fst V \<le> fst X" "snd X \<le> snd V" by (auto simp: alr_ivl_subset_def)
    from assms(2) have vy: "fst Y \<le> fst V" "snd V \<le> snd Y" "V \<noteq> Y"
      by (auto simp: alr_ivl_pss_def alr_ivl_subset_def)
    from vy(1,2) xv eq have "fst V = fst Y" "snd V = snd Y" by auto
    hence "V = Y" by (metis prod_eqI)
    thus False using vy(3) by simp
  qed
  from sub neq show ?thesis by (simp add: alr_ivl_pss_def)
qed

lemma alr_ivl_subset_disjoint:
  assumes "alr_ivl_subset X V" and "alr_ivl_disjoint V Y" shows "alr_ivl_disjoint X Y"
  using assms by (auto simp: alr_ivl_subset_def alr_ivl_disjoint_def)

lemma alr_ivl_disjoint_sym: "alr_ivl_disjoint X Y = alr_ivl_disjoint Y X"
  by (auto simp: alr_ivl_disjoint_def)

lemma alr_ivl_disjoint_neq:
  fixes X Y :: "rat \<times> rat"
  assumes "fst X < snd X" and "fst Y < snd Y" and "alr_ivl_disjoint X Y"
  shows "X \<noteq> Y"
proof
  assume eq: "X = Y"
  from assms(3) have "snd X \<le> fst Y \<or> snd Y \<le> fst X" by (simp add: alr_ivl_disjoint_def)
  with eq assms(1) show False by auto
qed

text \<open>The corollary this whole device exists for: two distinct-by-construction PROPER
  intervals related by @{const alr_ivl_compat} are never literally equal.\<close>
lemma alr_ivl_compat_neq:
  assumes X0: "fst X < snd X" and Y0: "fst Y < snd Y" and c: "alr_ivl_compat X Y"
  shows "X \<noteq> Y"
proof -
  consider (sub) "alr_ivl_pss X Y" | (sup) "alr_ivl_pss Y X" | (dis) "alr_ivl_disjoint X Y"
    using c by (auto simp: alr_ivl_compat_def)
  then show ?thesis
  proof cases
    case sub thus ?thesis by (simp add: alr_ivl_pss_def)
  next
    case sup thus ?thesis by (auto simp: alr_ivl_pss_def)
  next
    case dis thus ?thesis using alr_ivl_disjoint_neq[OF X0 Y0] by simp
  qed
qed

subsection \<open>The pairwise-compatible family invariant\<close>

text \<open>\<^bold>\<open>Design\<close>: SET-quantified clauses (\<open>X \<noteq> Y \<longrightarrow> \<dots>\<close> over \<open>set L\<close>) plus an EXPLICIT
  \<open>distinct\<close> conjunct — not index-quantified. A set-only formulation (no \<open>distinct\<close>) would
  be vacuously satisfied by a list secretly containing a repeated value (nothing to say
  about a value vs itself), which is exactly the bad case this device exists to exclude —
  so \<open>distinct\<close> is carried directly, proven fresh at each step alongside the compat
  clauses, rather than derived post-hoc.

  \<^bold>\<open>The loop invariant\<close> (four clauses, over the count-frame \<open>(a,b)\<close> views of the
  already-decided list \<open>D\<close> and the still-live \<open>todo\<close> stack):
  \<^enum> \<open>todo\<close> is DISTINCT and pairwise DISJOINT (the standard "frontier of an unexplored
    tree" property: no live node is ever a descendant of another live node, since
    descendants are created only by POPPING their ancestor, which removes it from
    \<open>todo\<close>);
  \<^enum> every \<open>D\<close>-entry is, relative to every \<open>todo\<close>-entry, EITHER disjoint OR a proper
    ANCESTOR (never a descendant — a live node's own descendants do not exist yet) —
    this ALSO forces \<open>set D \<inter> set todo = {}\<close> for free (neither disjunct can hold of
    \<open>Z\<close> vs itself for a proper interval), so no extra "D/todo disjoint as sets" clause
    is needed;
  \<^enum> \<open>D\<close> itself is DISTINCT and pairwise @{const alr_ivl_compat} (nested-or-disjoint,
    accumulated ancestor chains).\<close>
definition alr_ivl_todo_ok :: "(rat \<times> rat) list \<Rightarrow> bool" where
  "alr_ivl_todo_ok todo \<longleftrightarrow>
     distinct todo \<and> (\<forall>X \<in> set todo. \<forall>Y \<in> set todo. X \<noteq> Y \<longrightarrow> alr_ivl_disjoint X Y)"

definition alr_ivl_D_todo_ok :: "(rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow> bool" where
  "alr_ivl_D_todo_ok D todo \<longleftrightarrow>
     (\<forall>Z \<in> set D. \<forall>Y \<in> set todo. alr_ivl_disjoint Z Y \<or> alr_ivl_pss Y Z)"

definition alr_ivl_D_ok :: "(rat \<times> rat) list \<Rightarrow> bool" where
  "alr_ivl_D_ok D \<longleftrightarrow>
     distinct D \<and> (\<forall>X \<in> set D. \<forall>Y \<in> set D. X \<noteq> Y \<longrightarrow> alr_ivl_compat X Y)"

definition alr_ivl_run_invar :: "(rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow> bool" where
  "alr_ivl_run_invar D todo \<longleftrightarrow>
     alr_ivl_todo_ok todo \<and> alr_ivl_D_todo_ok D todo \<and> alr_ivl_D_ok D"

lemma alr_ivl_run_invar_init:
  assumes "fst v < snd v"
  shows "alr_ivl_run_invar [] [v]"
  using assms
  by (simp add: alr_ivl_run_invar_def alr_ivl_todo_ok_def alr_ivl_D_todo_ok_def alr_ivl_D_ok_def
      alr_ivl_disjoint_def)

text \<open>Core preservation fact, shared by all three steps: moving \<open>v\<close> (the last live
  element, hence — by @{const alr_ivl_todo_ok}'s pairwise-disjoint clause — disjoint from
  every OTHER \<open>todo\<close> element, and — by @{const alr_ivl_D_todo_ok} — either disjoint from or
  a proper superset of every \<open>D\<close> element) from \<open>todo\<close> into \<open>D\<close> preserves ALL FOUR
  clauses, provided no NEW children are pushed yet.\<close>
lemma alr_ivl_run_invar_move_last:
  assumes inv: "alr_ivl_run_invar D (todo @ [v])" and vprop: "fst v < snd v"
  shows "alr_ivl_todo_ok todo"
    and "alr_ivl_D_todo_ok (D @ [v]) todo"
    and "alr_ivl_D_ok (D @ [v])"
proof -
  from inv have todo_ok: "alr_ivl_todo_ok (todo @ [v])"
    and Dtodo_ok: "alr_ivl_D_todo_ok D (todo @ [v])"
    and D_ok: "alr_ivl_D_ok D"
    by (simp_all add: alr_ivl_run_invar_def)
  show todo_ok': "alr_ivl_todo_ok todo"
    using todo_ok by (auto simp: alr_ivl_todo_ok_def)
  have v_disj_todo: "\<forall>Y \<in> set todo. alr_ivl_disjoint v Y"
    using todo_ok by (auto simp: alr_ivl_todo_ok_def)
  have v_fresh_todo: "v \<notin> set todo"
    using todo_ok by (simp add: alr_ivl_todo_ok_def)
  show "alr_ivl_D_todo_ok (D @ [v]) todo"
    unfolding alr_ivl_D_todo_ok_def
  proof (intro ballI)
    fix Z Y assume Z: "Z \<in> set (D @ [v])" and Y: "Y \<in> set todo"
    show "alr_ivl_disjoint Z Y \<or> alr_ivl_pss Y Z"
    proof (cases "Z \<in> set D")
      case True
      then show ?thesis using Dtodo_ok Y by (auto simp: alr_ivl_D_todo_ok_def)
    next
      case False
      with Z have "Z = v" by simp
      with v_disj_todo Y show ?thesis by auto
    qed
  qed
  have v_fresh_D: "v \<notin> set D"
  proof
    assume "v \<in> set D"
    then have "alr_ivl_disjoint v v \<or> alr_ivl_pss v v" using Dtodo_ok
      by (auto simp: alr_ivl_D_todo_ok_def)
    then show False using vprop by (auto simp: alr_ivl_disjoint_def alr_ivl_pss_def)
  qed
  show "alr_ivl_D_ok (D @ [v])"
    unfolding alr_ivl_D_ok_def
  proof (intro conjI)
    show "distinct (D @ [v])" using D_ok v_fresh_D by (simp add: alr_ivl_D_ok_def)
  next
    show "\<forall>X \<in> set (D @ [v]). \<forall>Y \<in> set (D @ [v]). X \<noteq> Y \<longrightarrow> alr_ivl_compat X Y"
    proof (intro ballI impI)
      fix X Y assume X: "X \<in> set (D @ [v])" and Y: "Y \<in> set (D @ [v])" and XY: "X \<noteq> Y"
      consider (DD) "X \<in> set D \<and> Y \<in> set D"
        | (Dv) "X \<in> set D \<and> Y = v" | (vD) "X = v \<and> Y \<in> set D"
        using X Y XY by auto
      then show "alr_ivl_compat X Y"
      proof cases
        case DD thus ?thesis using D_ok XY by (auto simp: alr_ivl_D_ok_def)
      next
        case Dv
        have "alr_ivl_disjoint X v \<or> alr_ivl_pss v X" using Dtodo_ok Dv
          by (auto simp: alr_ivl_D_todo_ok_def)
        with Dv show ?thesis by (auto simp: alr_ivl_compat_def)
      next
        case vD
        have "alr_ivl_disjoint Y v \<or> alr_ivl_pss v Y" using Dtodo_ok vD
          by (auto simp: alr_ivl_D_todo_ok_def)
        with vD show ?thesis by (auto simp: alr_ivl_compat_def alr_ivl_disjoint_sym)
      qed
    qed
  qed
qed

text \<open>Step 1: DISCARD/ACCEPT — pop \<open>v\<close> = last element of \<open>todo\<close>, move it to \<open>D\<close>, push no
  children.\<close>
lemma alr_ivl_run_invar_leaf:
  assumes inv: "alr_ivl_run_invar D (todo @ [v])" and vprop: "fst v < snd v"
  shows "alr_ivl_run_invar (D @ [v]) todo"
  using alr_ivl_run_invar_move_last[OF inv vprop] by (simp add: alr_ivl_run_invar_def)

text \<open>Every element of \<open>todo\<close> is, by @{const alr_ivl_run_invar}, either disjoint from \<open>v\<close> or
  a proper ancestor of \<open>v\<close> — used by both child-pushing steps to show a strictly-narrower
  child \<open>w\<close> of \<open>v\<close> stays compatible with the rest of \<open>todo\<close>.\<close>
lemma alr_ivl_run_invar_child_vs_todo:
  assumes inv: "alr_ivl_run_invar D (todo @ [v])" and wv: "alr_ivl_subset w v"
  shows "\<forall>Y \<in> set todo. alr_ivl_disjoint w Y"
proof
  fix Y assume Y: "Y \<in> set todo"
  from inv have distn: "distinct (todo @ [v])"
    and pairw: "\<forall>X \<in> set (todo @ [v]). \<forall>X' \<in> set (todo @ [v]). X \<noteq> X' \<longrightarrow> alr_ivl_disjoint X X'"
    by (simp_all add: alr_ivl_run_invar_def alr_ivl_todo_ok_def)
  have "v \<noteq> Y" using distn Y by auto
  hence "alr_ivl_disjoint v Y" using pairw Y by auto
  thus "alr_ivl_disjoint w Y" using wv alr_ivl_subset_disjoint by blast
qed

text \<open>...and every \<open>D\<close>-entry, relative to \<open>v\<close>, is disjoint or a proper ancestor —
  inherited by any child \<open>w \<sqsubseteq> v\<close> via @{thm alr_ivl_subset_disjoint} /
  @{thm alr_ivl_subset_pss_trans}.\<close>
lemma alr_ivl_run_invar_child_vs_D:
  assumes inv: "alr_ivl_run_invar D (todo @ [v])" and wv: "alr_ivl_subset w v"
  shows "\<forall>Z \<in> set D. alr_ivl_disjoint Z w \<or> alr_ivl_pss w Z"
proof
  fix Z assume Z: "Z \<in> set D"
  from inv have "alr_ivl_disjoint Z v \<or> alr_ivl_pss v Z"
    by (simp add: alr_ivl_run_invar_def alr_ivl_D_todo_ok_def) (use Z in blast)
  then show "alr_ivl_disjoint Z w \<or> alr_ivl_pss w Z"
  proof
    assume "alr_ivl_disjoint Z v"
    hence "alr_ivl_disjoint v Z" by (simp add: alr_ivl_disjoint_sym)
    hence "alr_ivl_disjoint w Z" using wv alr_ivl_subset_disjoint by blast
    thus ?thesis by (simp add: alr_ivl_disjoint_sym)
  next
    assume vZ: "alr_ivl_pss v Z"
    hence vZsub: "alr_ivl_subset v Z" and vZne: "v \<noteq> Z" by (auto simp: alr_ivl_pss_def)
    hence wZsub: "alr_ivl_subset w Z" using wv alr_ivl_subset_trans by blast
    have "w \<noteq> Z"
    proof
      assume wZ: "w = Z"
      with wv have Zv: "alr_ivl_subset Z v" by simp
      have "fst v = fst Z" "snd Z = snd v"
        using Zv vZsub by (auto simp: alr_ivl_subset_def)
      hence "Z = v" by (metis prod_eqI)
      with vZne show False by simp
    qed
    with wZsub show ?thesis by (simp add: alr_ivl_pss_def)
  qed
qed

text \<open>Step 2: ONE child \<open>w\<close>, strictly narrower than \<open>v\<close> (@{term "alr_ivl_pss w v"}).\<close>
lemma alr_ivl_run_invar_window:
  assumes inv: "alr_ivl_run_invar D (todo @ [v])" and wv: "alr_ivl_pss w v"
    and vprop: "fst v < snd v" and wprop: "fst w < snd w"
  shows "alr_ivl_run_invar (D @ [v]) (todo @ [w])"
proof -
  have base: "alr_ivl_todo_ok todo" "alr_ivl_D_todo_ok (D @ [v]) todo" "alr_ivl_D_ok (D @ [v])"
    using alr_ivl_run_invar_move_last[OF inv vprop] by simp_all
  have wsub: "alr_ivl_subset w v" using wv by (simp add: alr_ivl_pss_def)
  have w_vs_todo: "\<forall>Y \<in> set todo. alr_ivl_disjoint w Y"
    using alr_ivl_run_invar_child_vs_todo[OF inv wsub] .
  have w_fresh_todo: "w \<notin> set todo"
  proof
    assume "w \<in> set todo"
    hence "alr_ivl_disjoint w w" using w_vs_todo by blast
    thus False using wprop by (auto simp: alr_ivl_disjoint_def)
  qed
have w_ne_v: "w \<noteq> v" using wv by (simp add: alr_ivl_pss_def)
  have todo_ok': "alr_ivl_todo_ok (todo @ [w])"
    unfolding alr_ivl_todo_ok_def
  proof (intro conjI)
    show "distinct (todo @ [w])" using base(1) w_fresh_todo by (simp add: alr_ivl_todo_ok_def)
  next
    show "\<forall>X \<in> set (todo @ [w]). \<forall>Y \<in> set (todo @ [w]). X \<noteq> Y \<longrightarrow> alr_ivl_disjoint X Y"
    proof (intro ballI impI)
      fix X Y assume X: "X \<in> set (todo @ [w])" and Y: "Y \<in> set (todo @ [w])" and XY: "X \<noteq> Y"
      consider (TT) "X \<in> set todo \<and> Y \<in> set todo" | (Tw) "X \<in> set todo \<and> Y = w"
        | (wT) "X = w \<and> Y \<in> set todo"
        using X Y XY by auto
      then show "alr_ivl_disjoint X Y"
      proof cases
        case TT thus ?thesis using base(1) XY by (auto simp: alr_ivl_todo_ok_def)
      next
        case Tw thus ?thesis using w_vs_todo by (auto simp: alr_ivl_disjoint_sym)
      next
        case wT thus ?thesis using w_vs_todo by auto
      qed
    qed
  qed
  have Dtodo_ok': "alr_ivl_D_todo_ok (D @ [v]) (todo @ [w])"
    unfolding alr_ivl_D_todo_ok_def
  proof (intro ballI)
    fix Z Y assume Z: "Z \<in> set (D @ [v])" and Y: "Y \<in> set (todo @ [w])"
    show "alr_ivl_disjoint Z Y \<or> alr_ivl_pss Y Z"
    proof (cases "Y \<in> set todo")
      case True thus ?thesis using base(2) Z by (auto simp: alr_ivl_D_todo_ok_def)
    next
      case False
      with Y have YW: "Y = w" by simp
      show ?thesis
      proof (cases "Z \<in> set D")
        case True
        have "\<forall>Z' \<in> set D. alr_ivl_disjoint Z' w \<or> alr_ivl_pss w Z'"
          using alr_ivl_run_invar_child_vs_D[OF inv wsub] .
        with True YW show ?thesis by auto
      next
        case False
        with Z have "Z = v" by simp
        with YW wv show ?thesis by auto
      qed
    qed
  qed
  show ?thesis
    unfolding alr_ivl_run_invar_def using todo_ok' Dtodo_ok' base(3) by simp
qed

text \<open>Step 3: TWO children \<open>c1\<close>, \<open>c2\<close>, each strictly narrower than \<open>v\<close> and mutually
  disjoint (the bisection-halves / dense-truncated-children shape). Same argument as Step
  2, applied to each child, plus the CONSTRUCTIVE fact \<open>c1\<close>/\<open>c2\<close> are disjoint from EACH
  OTHER (a fresh sibling pair, not derived from the invariant).\<close>
lemma alr_ivl_run_invar_split:
  assumes inv: "alr_ivl_run_invar D (todo @ [v])"
    and c1v: "alr_ivl_pss c1 v" and c2v: "alr_ivl_pss c2 v" and c12: "alr_ivl_disjoint c1 c2"
    and vprop: "fst v < snd v" and c1prop: "fst c1 < snd c1" and c2prop: "fst c2 < snd c2"
  shows "alr_ivl_run_invar (D @ [v]) (todo @ [c1, c2])"
proof -
  have step1: "alr_ivl_run_invar (D @ [v]) (todo @ [c1])"
    using alr_ivl_run_invar_window[OF inv c1v vprop c1prop] .
  have c1_ne_c2: "c1 \<noteq> c2" using c12 c1prop
    by (auto simp: alr_ivl_disjoint_def)
  have c2_sub_v: "alr_ivl_subset c2 v" using c2v by (simp add: alr_ivl_pss_def)
  have c2_vs_todo: "\<forall>Y \<in> set todo. alr_ivl_disjoint c2 Y"
    using alr_ivl_run_invar_child_vs_todo[OF inv c2_sub_v] .
  have c2_vs_D: "\<forall>Z \<in> set D. alr_ivl_disjoint Z c2 \<or> alr_ivl_pss c2 Z"
    using alr_ivl_run_invar_child_vs_D[OF inv c2_sub_v] .
  have c2_fresh_todo1: "c2 \<notin> set (todo @ [c1])"
  proof
    assume "c2 \<in> set (todo @ [c1])"
    then consider "c2 \<in> set todo" | "c2 = c1" by auto
    then show False
    proof cases
      case 1 hence "alr_ivl_disjoint c2 c2" using c2_vs_todo by blast
      thus False using c2prop by (auto simp: alr_ivl_disjoint_def)
    next
      case 2 thus False using c1_ne_c2 by simp
    qed
  qed
  have todo_ok2: "alr_ivl_todo_ok (todo @ [c1] @ [c2])"
    unfolding alr_ivl_todo_ok_def
  proof (intro conjI)
    have "alr_ivl_todo_ok (todo @ [c1])" using step1 by (simp add: alr_ivl_run_invar_def)
    thus "distinct (todo @ [c1] @ [c2])"
      using c2_fresh_todo1 c1_ne_c2 by (simp add: alr_ivl_todo_ok_def)
  next
    show "\<forall>X \<in> set (todo @ [c1] @ [c2]). \<forall>Y \<in> set (todo @ [c1] @ [c2]).
            X \<noteq> Y \<longrightarrow> alr_ivl_disjoint X Y"
    proof (intro ballI impI)
      fix X Y assume X: "X \<in> set (todo @ [c1] @ [c2])" and Y: "Y \<in> set (todo @ [c1] @ [c2])"
        and XY: "X \<noteq> Y"
      have base_todo_ok: "alr_ivl_todo_ok (todo @ [c1])" using step1 by (simp add: alr_ivl_run_invar_def)
      consider (base) "X \<in> set (todo @ [c1]) \<and> Y \<in> set (todo @ [c1])"
        | (Xc2) "X \<in> set (todo @ [c1]) \<and> Y = c2" | (c2Y) "X = c2 \<and> Y \<in> set (todo @ [c1])"
        using X Y XY by auto
      then show "alr_ivl_disjoint X Y"
      proof cases
        case base thus ?thesis using base_todo_ok XY by (auto simp: alr_ivl_todo_ok_def)
      next
        case Xc2
        then consider "X \<in> set todo" | "X = c1" by auto
        then show ?thesis
        proof cases
          case 1 thus ?thesis using c2_vs_todo Xc2 by (auto simp: alr_ivl_disjoint_sym)
        next
          case 2 thus ?thesis using c12 Xc2 by simp
        qed
      next
        case c2Y
        then consider "Y \<in> set todo" | "Y = c1" by auto
        then show ?thesis
        proof cases
          case 1 thus ?thesis using c2_vs_todo c2Y by auto
        next
          case 2 thus ?thesis using c12 c2Y by (simp add: alr_ivl_disjoint_sym)
        qed
      qed
    qed
  qed
  have Dtodo_ok2: "alr_ivl_D_todo_ok (D @ [v]) (todo @ [c1] @ [c2])"
    unfolding alr_ivl_D_todo_ok_def
  proof (intro ballI)
    fix Z Y assume Z: "Z \<in> set (D @ [v])" and Y: "Y \<in> set (todo @ [c1] @ [c2])"
    show "alr_ivl_disjoint Z Y \<or> alr_ivl_pss Y Z"
    proof (cases "Y \<in> set (todo @ [c1])")
      case True
      have "alr_ivl_D_todo_ok (D @ [v]) (todo @ [c1])" using step1 by (simp add: alr_ivl_run_invar_def)
      thus ?thesis using True Z by (auto simp: alr_ivl_D_todo_ok_def)
    next
      case False
      with Y have YC2: "Y = c2" by simp
      show ?thesis
      proof (cases "Z \<in> set D")
        case True thus ?thesis using c2_vs_D YC2 by auto
      next
        case False
        with Z have "Z = v" by simp
        with YC2 c2v show ?thesis by auto
      qed
    qed
  qed
  have D_ok2: "alr_ivl_D_ok (D @ [v])" using step1 by (simp add: alr_ivl_run_invar_def)
  show ?thesis
    using todo_ok2 Dtodo_ok2 D_ok2 by (simp add: alr_ivl_run_invar_def)
qed

text \<open>\<^bold>\<open>The payoff\<close>: under @{const alr_ivl_run_invar}, \<open>D\<close> (which accumulates every view the
  impl has ever dispatched a decision at) is already tracked \<open>distinct\<close> directly —
  making "lookup the decision by view" well-defined with no further lemma needed.\<close>
lemma alr_ivl_run_invar_D_distinct: "alr_ivl_run_invar D todo \<Longrightarrow> distinct D"
  by (simp add: alr_ivl_run_invar_def alr_ivl_D_ok_def)

text \<open>The geometry of a bisection split, in the \<open>ivl_\<close> predicates @{thm [source] alr_ivl_run_invar_split}
  consumes: the two children \<open>(a,m)\<close>, \<open>(m,b)\<close> (with \<open>m = (a+b)/2\<close>) are each a PROPER subinterval
  of the parent \<open>(a,b)\<close> and are mutually disjoint. This is what the gate-CLOSED (and, with the
  midpoint, gate-OPEN's fallback) step-preservation feeds to keep the decision-map view family
  compatible.\<close>
lemma alr_ivl_split_children_geometry:
  assumes ab: "a < b"
  shows "alr_ivl_pss (a, (a + b) / 2) (a, b)"
    and "alr_ivl_pss ((a + b) / 2, b) (a, b)"
    and "alr_ivl_disjoint (a, (a + b) / 2) ((a + b) / 2, b)"
    and "fst (a, (a + b) / 2) < snd (a, (a + b) / 2)"
    and "fst ((a + b) / 2, b) < snd ((a + b) / 2, b)"
  using ab by (auto simp: alr_ivl_pss_def alr_ivl_subset_def alr_ivl_disjoint_def)

section \<open>The free-pol abstract tree and its order-agnostic worklist
  decomposition\<close>

text \<open>Clone of \<open>Bail_Loop_Refine.thy\<close>'s "The abstract per-node tree and its
  order-agnostic worklist decomposition" section, with the fixed policy \<open>pol_final\<close>/
  \<open>pol_final_real\<close> generalized to a FREE \<open>pol\<close>/\<open>polr\<close> pair. This is a mechanical
  generalization, not a re-derivation: the two facts the bail section rests on —
  @{thm [source] newdsc_pol_bail_terminates_squarefree} (domain totality) and
  @{thm [source] newdsc_pol_bail_main_int_sim_aux} (the int/real worklist-peel
  simulation) — are ALREADY \<open>\<forall>pol\<close> theorems in \<open>Bail_Spec.thy\<close> (\<open>pol_final\<close> is
  merely their INSTANTIATION, not a hypothesis they need); the only new ingredient
  here is a free \<open>polrel\<close> hypothesis in place of the concrete \<open>pol_final_real_rel\<close>
  witness. The keystone's ONLY use of this section instantiates \<open>pol\<close>/\<open>polr\<close> at the
  witness built from the compatible-family device above — never at \<open>pol_final\<close>.\<close>

definition hybrid_tree1 ::
  "newton_pol \<Rightarrow> int poly \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (rat \<times> rat) list" where
"hybrid_tree1 pol P a b e dk s = newdsc_pol_bail_main_int (pol (degree P)) P [(a, b, e, dk, s)] []"

definition hybrid_tree_mset ::
  "newton_pol \<Rightarrow> int poly \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> (rat \<times> rat) multiset" where
"hybrid_tree_mset pol P nodes =
  sum_list (map (\<lambda>(a, b, e, dk, s). mset (hybrid_tree1 pol P a b e dk s)) nodes)"

lemma hybrid_tree_mset_Nil[simp]: "hybrid_tree_mset pol P [] = {#}"
  by (simp add: hybrid_tree_mset_def)

lemma hybrid_tree_mset_append[simp]:
  "hybrid_tree_mset pol P (xs @ ys) = hybrid_tree_mset pol P xs + hybrid_tree_mset pol P ys"
  by (simp add: hybrid_tree_mset_def)

lemma hybrid_tree_mset_Cons:
  "hybrid_tree_mset pol P ((a, b, e, dk, s) # xs)
     = mset (hybrid_tree1 pol P a b e dk s) + hybrid_tree_mset pol P xs"
  by (simp add: hybrid_tree_mset_def)

text \<open>Domain totality, free in \<open>polr\<close> — the same instantiation of the already-\<open>\<forall>pol\<close>
  @{thm [source] newdsc_pol_bail_terminates_squarefree} that
  @{thm [source] newdsc_pol_bail_pol_final_dom} performs, just without fixing \<open>polr\<close>.\<close>
lemma hybrid_pol_dom:
  fixes P :: "int poly" and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "newdsc_pol_bail_dom (polr, degree P, a, b, e, dk, s, map_poly of_int P)"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  show ?thesis by (rule newdsc_pol_bail_terminates_squarefree[OF dne dle p0 sf ab])
qed

lemma hybrid_pol_dom_rat:
  fixes polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "newdsc_pol_bail_dom
           (polr, degree P, of_rat a, of_rat b, e, dk, s, map_poly of_int P)"
  using hybrid_pol_dom[OF P0 p0 sf, of "of_rat a" "of_rat b" polr e dk s] ab
  by (simp add: of_rat_less)

text \<open>The worklist-peel keystone, free in \<open>pol\<close>/\<open>polr\<close> under an explicit \<open>polrel\<close>
  hypothesis (in place of the concrete \<open>pol_final_real_rel\<close> witness
  @{thm [source] newton_worklist_cons_bl} composes with).\<close>
lemma hybrid_worklist_cons:
  fixes pol :: newton_pol and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = pol (degree P) a2 b2 e2 dk2 (s2, v)"
  shows "newdsc_pol_bail_main_int (pol (degree P)) P ((a, b, e, dk, s) # todo) acc
       = newdsc_pol_bail_main_int (pol (degree P)) P todo (hybrid_tree1 pol P a b e dk s @ acc)"
proof -
  have dom: "newdsc_pol_bail_dom (polr, degree P, of_rat a, of_rat b, e, dk, s, map_poly of_int P)"
    by (rule hybrid_pol_dom_rat[OF P0 p0 sf ab])
  let ?sub = "map real_to_rat_pair
                (rev (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk s
                        (map_poly of_int P)))"
  have gen: "\<And>td ac. newdsc_pol_bail_main_int (pol (degree P)) P ((a, b, e, dk, s) # td) ac
               = newdsc_pol_bail_main_int (pol (degree P)) P td (?sub @ ac)"
    by (rule newdsc_pol_bail_main_int_sim_aux[OF dom refl refl refl refl P0 ab polrel])
  have tree1: "hybrid_tree1 pol P a b e dk s = ?sub"
    unfolding hybrid_tree1_def by (subst gen) (simp add: newdsc_pol_bail_main_int.simps)
  show ?thesis by (subst gen) (simp add: tree1)
qed

text \<open>Hence the order-agnostic multiset decomposition, free in \<open>pol\<close>/\<open>polr\<close>.\<close>
lemma hybrid_worklist_decomp:
  fixes pol :: newton_pol and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and nodes: "\<forall>(a, b, e, dk, s) \<in> set todo. a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = pol (degree P) a2 b2 e2 dk2 (s2, v)"
  shows "mset (newdsc_pol_bail_main_int (pol (degree P)) P todo acc)
       = mset acc + hybrid_tree_mset pol P todo"
  using nodes
proof (induction todo arbitrary: acc)
  case Nil
  show ?case by (simp add: newdsc_pol_bail_main_int.simps)
next
  case (Cons nd todo)
  obtain a b e dk s where nd: "nd = (a, b, e, dk, s)" by (cases nd) auto
  have ab: "a < b" using Cons.prems nd by auto
  have step: "newdsc_pol_bail_main_int (pol (degree P)) P ((a, b, e, dk, s) # todo) acc
      = newdsc_pol_bail_main_int (pol (degree P)) P todo (hybrid_tree1 pol P a b e dk s @ acc)"
  proof (rule hybrid_worklist_cons)
    show "P \<noteq> 0" by (rule P0)
    show "degree P \<noteq> 0" by (rule p0)
    show "square_free (map_poly of_int P :: real poly)" by (rule sf)
    show "a < b" by (rule ab)
    show "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
            = pol (degree P) a2 b2 e2 dk2 (s2, v)"
      by (rule polrel)
  qed
  have "mset (newdsc_pol_bail_main_int (pol (degree P)) P (nd # todo) acc)
      = mset (newdsc_pol_bail_main_int (pol (degree P)) P todo (hybrid_tree1 pol P a b e dk s @ acc))"
    unfolding nd by (simp only: step)
  also have "\<dots> = mset (hybrid_tree1 pol P a b e dk s @ acc) + hybrid_tree_mset pol P todo"
    using Cons.prems nd by (subst Cons.IH) auto
  also have "\<dots> = mset acc + hybrid_tree_mset pol P (nd # todo)"
    unfolding nd by (simp add: hybrid_tree_mset_Cons)
  finally show ?case .
qed

text \<open>\<^bold>\<open>The pol-parameterised ONE-STEP tree unfold\<close> (the analog of
  bail's @{thm [source] newton_gmp_step_bail_tree_preservation}, but free in \<open>pol\<close> and expressed
  on @{const hybrid_tree1} directly). It is @{thm [source] newdsc_pol_bail_main_int.simps} (the
  \<open>[code]\<close> tailrec unfolds the front node) composed with @{thm [source] hybrid_worklist_decomp} for
  the two-child bisection arm. It discharges the per-step accounting obligation of the keystone's
  WHILEIT invariant: \<open>mset (hybrid_tree1 pol n) = mset (leaf n) + \<Sum> mset (hybrid_tree1 pol child)\<close>, where
  leaf/children are exactly what @{const newdsc_pol_bail}'s recursion produces under
  \<open>pol (degree P) a b e dk (s, v)\<close> at the EXACT count \<open>v\<close>. The keystone reads it right-to-left at
  the popped node with \<open>pol\<close> instantiated to any policy AGREEING with the impl's recorded decision
  there (the decision map above), so the window/bisection branch it unfolds along is the one
  the impl actually took.\<close>
lemma hybrid_tree1_unfold:
  fixes pol :: newton_pol and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and ab: "a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = pol (degree P) a2 b2 e2 dk2 (s2, v)"
  defines "v \<equiv> descartes_list_int a b (coeffs P)"
  shows "mset (hybrid_tree1 pol P a b e dk s) =
    (if v = 0 then {#}
     else if v = 1 then {#(a, b)#}
     else (case try_window_bail_int (snd (pol (degree P) a b e dk (s, v))) a b (N_of e) P v of
             Some I \<Rightarrow> mset (hybrid_tree1 pol P (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s)
           | None \<Rightarrow>
               (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                then {#((a + b) / 2, (a + b) / 2)#} else {#})
               + mset (hybrid_tree1 pol P a ((a + b) / 2) (max 1 (e - 1)) (dk + 1)
                         (split_run_len_int P a b s))
               + mset (hybrid_tree1 pol P ((a + b) / 2) b (max 1 (e - 1)) (dk + 1)
                         (split_run_len_int P a b s))))"
proof -
  let ?m = "(a + b) / 2"
  let ?g = "pol (degree P) a b e dk (s, v)"
  have am: "a < ?m" and mb: "?m < b" using ab by (auto)
  have t1: "hybrid_tree1 pol P a b e dk s
      = newdsc_pol_bail_main_int (pol (degree P)) P [(a, b, e, dk, s)] []"
    by (simp add: hybrid_tree1_def)
  have step: "newdsc_pol_bail_main_int (pol (degree P)) P [(a, b, e, dk, s)] []
      = (if v = 0 then []
         else if v = 1 then [(a, b)]
         else (case try_window_bail_int (snd ?g) a b (N_of e) P v of
                 Some I \<Rightarrow> newdsc_pol_bail_main_int (pol (degree P)) P
                             [accept_child_int I e dk s] []
               | None \<Rightarrow> newdsc_pol_bail_main_int (pol (degree P)) P
                           (bisect_children_int P a b e dk s)
                           (if poly (map_poly of_int P :: rat poly) ?m = 0
                            then [(?m, ?m)] else [])))"
    unfolding v_def
    by (subst newdsc_pol_bail_main_int.simps)
       (simp add: Let_def newdsc_pol_bail_main_int.simps split: option.split)
  show ?thesis
  proof (cases "v = 0")
    case True thus ?thesis unfolding t1 step by simp
  next
    case v1: False
    show ?thesis
    proof (cases "v = 1")
      case True thus ?thesis unfolding t1 step using v1 by simp
    next
      case v2: False
      show ?thesis
      proof (cases "try_window_bail_int (snd ?g) a b (N_of e) P v")
        case None
        have dec: "mset (newdsc_pol_bail_main_int (pol (degree P)) P
                     (bisect_children_int P a b e dk s)
                     (if poly (map_poly of_int P :: rat poly) ?m = 0 then [(?m, ?m)] else []))
            = mset (if poly (map_poly of_int P :: rat poly) ?m = 0 then [(?m, ?m)] else [])
              + hybrid_tree_mset pol P (bisect_children_int P a b e dk s)"
        proof (rule hybrid_worklist_decomp[OF P0 p0 sf])
          show "\<forall>(a', b', e', dk', s') \<in> set (bisect_children_int P a b e dk s). a' < b'"
            using am mb by (auto simp: bisect_children_int_def Let_def)
        next
          show "\<And>a2 b2 e2 dk2 s2 v.
                  polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = pol (degree P) a2 b2 e2 dk2 (s2, v)"
            by (rule polrel)
        qed
        \<comment> \<open>the two-child mset of the folded bisect list — kept SEPARATE so the final step can
           apply \<open>dec\<close> with @{const bisect_children_int} still folded (unfolding it first would
           stop \<open>dec\<close> from matching).\<close>
        have cm: "hybrid_tree_mset pol P (bisect_children_int P a b e dk s)
            = mset (hybrid_tree1 pol P a ?m (max 1 (e - 1)) (dk + 1) (split_run_len_int P a b s))
              + mset (hybrid_tree1 pol P ?m b (max 1 (e - 1)) (dk + 1) (split_run_len_int P a b s))"
          by (simp add: bisect_children_int_def Let_def hybrid_tree_mset_Cons)
        show ?thesis unfolding t1 step using v1 v2 None
          by (simp add: dec cm add.assoc)
      next
        case (Some I)
        have "newdsc_pol_bail_main_int (pol (degree P)) P [accept_child_int I e dk s] []
            = hybrid_tree1 pol P (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s"
          by (simp add: hybrid_tree1_def accept_child_int_def)
        thus ?thesis unfolding t1 step using v1 v2 Some by simp
      qed
    qed
  qed
qed

text \<open>The two trivial-arm rewrites of @{const hybrid_tree1} (discard/accept), branch-independent
  (they do not consult \<open>pol\<close>) — directly discharge \<open>hybrid_acc_invar_step\<close>'s
  \<open>branch\<close> obligation for the \<open>v = 0\<close> and \<open>v = 1\<close> dispatch arms. Definitional via
  @{thm [source] newdsc_pol_bail_main_int.simps} (no domain/polrel hypotheses needed).\<close>
lemma hybrid_tree1_discard:
  assumes "descartes_list_int a b (coeffs P) = 0"
  shows "hybrid_tree1 pol P a b e dk s = []"
  unfolding hybrid_tree1_def
  by (subst newdsc_pol_bail_main_int.simps) (simp add: assms newdsc_pol_bail_main_int.simps)

lemma hybrid_tree1_accept:
  assumes "descartes_list_int a b (coeffs P) = 1"
  shows "hybrid_tree1 pol P a b e dk s = [(a, b)]"
  unfolding hybrid_tree1_def
  by (subst newdsc_pol_bail_main_int.simps)
     (simp add: assms newdsc_pol_bail_main_int.simps)

text \<open>With the window gate off, no window try fires (immediate from @{const try_window_bail_int}'s
  definition).\<close>
lemma try_window_bail_int_off: "try_window_bail_int False a b N P v = None"
  by (simp add: try_window_bail_int_def)

text \<open>\<^bold>\<open>The split branch equation, keyed on the window missing.\<close> The implementation reaches the split
  arm by two routes: the gate-closed dispatch (\<open>\<not> gate\<close>), and the gate-open arm whose Newton probe was
  rejected (\<open>is_None wc\<close> in @{const hybrid_gate_open_monadic}). Only the first records \<open>(False, False)\<close>;
  the reject route records \<open>dec = (True, True)\<close> so that the policy-free window correspondence
  \<open>newton_window_pick_bail_abs\<close> applies, and there the \<open>None\<close> comes from that correspondence rather than
  from @{thm [source] try_window_bail_int_off}. Taking the \<open>None\<close> itself as the premise covers both
  routes; the gate-closed form is the corollary \<open>hybrid_tree1_split\<close> below.

  When the window misses and the exact count is \<open>\<ge> 2\<close>, the node's subtree splits into the midpoint leaf
  and the two bisection children, the shape the implementation's truncated split produces (its children
  have the same split points \<open>(a,m),(m,b)\<close>, since truncation changes coefficients, not geometry). A
  specialisation of @{thm [source] hybrid_tree1_unfold} to the \<open>None\<close> case.\<close>
lemma hybrid_tree1_split_off:
  fixes pol :: newton_pol and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and ab: "a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = pol (degree P) a2 b2 e2 dk2 (s2, v)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and off: "try_window_bail_int
                (snd (pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P))))
                a b (N_of e) P (descartes_list_int a b (coeffs P)) = None"
  shows "mset (hybrid_tree1 pol P a b e dk s) =
      (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
       then {#((a + b) / 2, (a + b) / 2)#} else {#})
      + mset (hybrid_tree1 pol P a ((a + b) / 2) (max 1 (e - 1)) (dk + 1)
                (split_run_len_int P a b s))
      + mset (hybrid_tree1 pol P ((a + b) / 2) b (max 1 (e - 1)) (dk + 1)
                (split_run_len_int P a b s))"
proof -
  have v0: "descartes_list_int a b (coeffs P) \<noteq> 0" using v2 by simp
  have v1: "descartes_list_int a b (coeffs P) \<noteq> 1" using v2 by simp
  have unf: "mset (hybrid_tree1 pol P a b e dk s) =
    (if descartes_list_int a b (coeffs P) = 0 then {#}
     else if descartes_list_int a b (coeffs P) = 1 then {#(a, b)#}
     else (case try_window_bail_int
                  (snd (pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P))))
                  a b (N_of e) P (descartes_list_int a b (coeffs P)) of
             Some I \<Rightarrow> mset (hybrid_tree1 pol P (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s)
           | None \<Rightarrow>
               (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                then {#((a + b) / 2, (a + b) / 2)#} else {#})
               + mset (hybrid_tree1 pol P a ((a + b) / 2) (max 1 (e - 1)) (dk + 1)
                         (split_run_len_int P a b s))
               + mset (hybrid_tree1 pol P ((a + b) / 2) b (max 1 (e - 1)) (dk + 1)
                         (split_run_len_int P a b s))))"
    by (rule hybrid_tree1_unfold[where P = P and pol = pol and polr = polr
              and a = a and b = b and e = e and dk = dk and s = s,
              OF P0 p0 sf ab polrel])
  show ?thesis using unf v0 v1 off by simp
qed

text \<open>\<^bold>\<open>The gate-closed corollary\<close>: at a node whose recorded decision is \<open>(False, False)\<close>, what the
  dispatch's \<open>\<not> gate\<close> arm records, no window try fires (@{thm [source] try_window_bail_int_off}), so
  @{thm [source] hybrid_tree1_split_off} applies.\<close>
lemma hybrid_tree1_split:
  fixes pol :: newton_pol and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and ab: "a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = pol (degree P) a2 b2 e2 dk2 (s2, v)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and dec: "pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P)) = (False, False)"
  shows "mset (hybrid_tree1 pol P a b e dk s) =
      (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
       then {#((a + b) / 2, (a + b) / 2)#} else {#})
      + mset (hybrid_tree1 pol P a ((a + b) / 2) (max 1 (e - 1)) (dk + 1)
                (split_run_len_int P a b s))
      + mset (hybrid_tree1 pol P ((a + b) / 2) b (max 1 (e - 1)) (dk + 1)
                (split_run_len_int P a b s))"
  \<comment> \<open>pin EVERY variable with \<open>where\<close> before \<open>OF\<close>: \<open>polrel\<close> is higher-order and a bare
     \<open>OF \<dots> polrel\<close> against a schematic \<open>?P\<close>/\<open>?a\<close>/\<open>?b\<close> raises \<open>OF: multiple unifiers\<close>. Same
     idiom @{thm [source] hybrid_tree1_unfold}'s call sites already use.\<close>
proof (rule hybrid_tree1_split_off[where P = P and pol = pol and polr = polr
          and a = a and b = b and e = e and dk = dk and s = s,
          OF P0 p0 sf ab polrel v2])
  show "try_window_bail_int
          (snd (pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P))))
          a b (N_of e) P (descartes_list_int a b (coeffs P)) = None"
    using dec by (simp add: try_window_bail_int_off)
qed

text \<open>\<^bold>\<open>The gate-open window branch equation\<close>: when the recorded decision \<open>dec\<close> makes the window try
  fire (\<open>try_window_bail_int (newton?) = Some I\<close>; \<open>fst dec\<close> is read only by the plain Newton route), the
  node's subtree is exactly its single window child's subtree. This matches the implementation's
  gate-open arm, which escalates to exact and then runs the bail window machinery, so the chosen window
  is \<open>Some I\<close> under the same recorded gates. A specialisation of @{thm [source] hybrid_tree1_unfold} to
  the \<open>Some\<close> case.\<close>
lemma hybrid_tree1_window:
  fixes pol :: newton_pol and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and ab: "a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = pol (degree P) a2 b2 e2 dk2 (s2, v)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and win: "try_window_bail_int
                (snd (pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P))))
                a b (N_of e) P (descartes_list_int a b (coeffs P)) = Some I"
  shows "mset (hybrid_tree1 pol P a b e dk s)
       = mset (hybrid_tree1 pol P (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s)"
proof -
  have v0: "descartes_list_int a b (coeffs P) \<noteq> 0" using v2 by simp
  have v1: "descartes_list_int a b (coeffs P) \<noteq> 1" using v2 by simp
  have unf: "mset (hybrid_tree1 pol P a b e dk s) =
    (if descartes_list_int a b (coeffs P) = 0 then {#}
     else if descartes_list_int a b (coeffs P) = 1 then {#(a, b)#}
     else (case try_window_bail_int
                  (snd (pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P))))
                  a b (N_of e) P (descartes_list_int a b (coeffs P)) of
             Some I \<Rightarrow> mset (hybrid_tree1 pol P (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s)
           | None \<Rightarrow>
               (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                then {#((a + b) / 2, (a + b) / 2)#} else {#})
               + mset (hybrid_tree1 pol P a ((a + b) / 2) (max 1 (e - 1)) (dk + 1)
                         (split_run_len_int P a b s))
               + mset (hybrid_tree1 pol P ((a + b) / 2) b (max 1 (e - 1)) (dk + 1)
                         (split_run_len_int P a b s))))"
    by (rule hybrid_tree1_unfold[where P = P and pol = pol and polr = polr
              and a = a and b = b and e = e and dk = dk and s = s,
              OF P0 p0 sf ab polrel])
  show ?thesis using unf v0 v1 win by simp
qed

section \<open>The g-aware cached-class invariant\<close>

text \<open>The hybrid's per-node cached class \<open>c\<close> (column \<open>cs\<close>) relative to the EXACT count
  \<open>cnt\<close> of the node's exact polynomial: either the fully-unknown ambiguous sentinel
  (\<open>c = 4\<close> on a still-truncated node, \<open>g < 2^42\<close>) — carrying NO count information — or a
  trustworthy class in bail's own sense (@{const dyadic_iv_cs_invar}: classify trichotomy plus
  the W1 \<open>c = cnt + 2\<close> decode for \<open>4 \<le> c\<close>). A LOCKed node (\<open>2^42 \<le> g\<close>) is always in the
  second disjunct — @{const carried_descartes_count_g_monadic} treats \<open>g \<ge> 2^42\<close> as
  always-decisive, and window-pushed children (which carry \<open>g = 2^42\<close>) cache \<open>v + 2\<close>.\<close>
definition hybrid_cs_ok :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hybrid_cs_ok g c cnt \<equiv> (c = 4 \<and> g < 4398046511104) \<or> dyadic_iv_cs_invar c cnt"

lemma hybrid_cs_ok_locked: "4398046511104 \<le> g \<Longrightarrow> hybrid_cs_ok g c cnt \<Longrightarrow> dyadic_iv_cs_invar c cnt"
  by (auto simp: hybrid_cs_ok_def)

text \<open>\<^bold>\<open>The \<open>g\<close>-count kernel returns at most 3.\<close> The loop condition @{const ethorner_count_trunc_cond}
  requires \<open>cnt < 2\<close>, @{const trunc_update_mop} increases \<open>cnt\<close> by at most one, and the boundary \<open>extra_f\<close>
  adds at most one, so \<open>cnt \<le> 3\<close>. The WHILET invariant is \<open>cnt \<le> 2\<close> plus the length bound the body's
  coefficient reads need (@{thm [source] length_ethorner_row_fun} keeps the length clause free).\<close>
lemma trunc_update_mop_cnt_le:
  assumes "cnt < 2"
  shows "trunc_update_mop s bl bt last_s cnt amb \<le> SPEC (\<lambda>(_, nc, _). nc \<le> Suc cnt)"
  using assms unfolding trunc_update_mop_def by (refine_vcg) auto

text \<open>\<^bold>\<open>Why \<open>pbound\<close>/\<open>gbound\<close> are premises.\<close> With only \<open>lb\<close> the lemma is false. The kernel's \<open>else\<close> branch
  executes \<open>ASSERT (len * bthr < max_snat \<dots>)\<close> and \<open>ASSERT (g + len < max_snat \<dots>)\<close> with \<open>g\<close> free, so
  \<open>length ys = 2\<close>, \<open>g = 2\<^sup>6\<^sup>3 - 1\<close> satisfies \<open>lb\<close>, fails the ASSERT and makes the program \<open>FAIL\<close>, and
  \<open>FAIL \<le> SPEC P\<close> is \<open>False\<close>. The two premises are the ones
  @{thm [source] poly_ethorner_count_gtrunc_monadic_classify} carries, and the consumers
  (\<open>carried_descartes_count_g_hybrid_cs_ok\<close>, \<open>hybrid_resolve_count_monadic_classify\<close>, below) have them.

  The proof reuses @{thm [source] poly_ethorner_count_gtrunc_loop_spec} (\<open>Truncate\<close>) rather than a new
  WHILET invariant: its seed \<open>amb0\<close> is a lemma parameter (the kernel's own lead-trust boolean, which an
  inline invariant cannot name), its \<open>\<le> SPEC\<close> gives \<open>cnt \<le> 2\<close> at exit, and the boundary \<open>extra_f \<le> 1\<close> lifts
  that to \<open>\<le> 3\<close>. The loop lemma is stated with \<open>ethorner_count_trunc_cond\<close> folded, so
  \<open>ethorner_count_trunc_cond_def\<close> must not be in the \<open>unfolding\<close> list.\<close>
lemma poly_ethorner_count_gtrunc_monadic_le3:
  assumes lb: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length ys * nat_bitlen (length ys) < max_snat LENGTH(gmp_poly_len)"
    and gbound: "g + length ys < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_ethorner_count_gtrunc_monadic g ys \<le> SPEC (\<lambda>(cnt, amb). cnt \<le> 3)"
proof -
  have snatlen: "length ys < max_snat LENGTH(gmp_poly_len)" using lb by simp
  show ?thesis
    unfolding truncate_ethorner_count_gtrunc_monadic_def
      ethorner_count_trunc_result_mop_monadic_def poly_length_monadic_def
      poly_coeff_sgn_monadic_def poly_coeff_bitlen2_monadic_def mpz_bitlen2_monadic_def
      lead_trust_mop_def bool_not_mop_def op_snat_unat_conv_def PR_CONST_def Let_def
    apply (refine_vcg snat_bitlen_monadic_correct[THEN order_trans]
        poly_ethorner_count_gtrunc_loop_spec[THEN order_trans])
    \<comment> \<open>\<^bold>\<open>INSERT the word bounds, do not pass them as simp RULES.\<close> Several residual goals have
       \<open>lb\<close>/\<open>gbound\<close> as their literal conclusion, and \<open>simp add: lb gbound\<close> does not close them;
       as inserted PREMISES they close by assumption after normalization. Same idiom as
       @{thm [source] poly_ethorner_count_gtrunc_monadic_classify}'s per-subgoal
       \<open>using \<dots> by simp\<close>. @{thm [source] small_lt_max_snat} is conditional (\<open>n \<le> 3\<close>) and gets
       its \<open>cnt \<le> 2\<close> from the loop lemma's exit conjunct, which simp splits.\<close>
    apply (all \<open>insert lb pbound gbound snatlen\<close>)
    apply (simp_all add: small_lt_max_snat)
    done
qed

text \<open>Hence the OUTER g-count caps at 3 too: the \<open>g = 0\<close> and \<open>g \<ge> 2\<^sup>4\<^sup>2\<close> branches run the plain
  \<open>count_trunc\<close> (@{thm [source] carried_descartes_count_trunc_monadic_classify_le3}), the middle
  branch the gtrunc kernel just bounded.\<close>
lemma carried_descartes_count_g_monadic_le3:
  assumes lb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length xs * nat_bitlen (length xs) < max_snat LENGTH(gmp_poly_len)"
    and gbound: "g + length xs < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_g_monadic xs g \<le> SPEC (\<lambda>(cnt, dec). cnt \<le> 3)"
  \<comment> \<open>\<open>pbound\<close>/\<open>gbound\<close> are the \<open>gtrunc\<close> kernel's own ASSERTs, as in
     @{thm [source] poly_ethorner_count_gtrunc_monadic_le3}. The kernel runs on \<open>rev xs\<close>, so \<open>length_rev\<close>
     normalises both to \<open>xs\<close> form.\<close>
  unfolding carried_descartes_count_g_monadic_def PR_CONST_def
  apply (refine_vcg carried_descartes_count_trunc_monadic_classify_le3[THEN order_trans]
      poly_reverse_monadic_correct[THEN order_trans]
      poly_ethorner_count_gtrunc_monadic_le3[THEN order_trans])
  using lb pbound gbound by (auto simp: length_rev)

text \<open>And \<open>\<not> dec \<Longrightarrow> g < 2\<^sup>4\<^sup>2\<close>: the two decisive branches (\<open>g = 0\<close>, \<open>g \<ge> 2\<^sup>4\<^sup>2\<close>) always
  return \<open>dec = True\<close>, so \<open>\<not> dec\<close> can only arise in the \<open>0 < g < 2\<^sup>4\<^sup>2\<close> branch.\<close>
lemma carried_descartes_count_g_monadic_notdec:
  assumes lb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length xs * nat_bitlen (length xs) < max_snat LENGTH(gmp_poly_len)"
    and gbound: "g + length xs < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_g_monadic xs g
       \<le> SPEC (\<lambda>(cnt, dec). \<not> dec \<longrightarrow> g < 4398046511104)"
  \<comment> \<open>the same premises as @{thm [source] carried_descartes_count_g_monadic_le3}.\<close>
  unfolding carried_descartes_count_g_monadic_def PR_CONST_def
  apply (refine_vcg carried_descartes_count_trunc_monadic_classify_le3[THEN order_trans]
      poly_reverse_monadic_correct[THEN order_trans]
      poly_ethorner_count_gtrunc_monadic_le3[THEN order_trans])
  using lb pbound gbound by (auto simp: length_rev)

text \<open>\<^bold>\<open>The pushed-child cache class is always @{const hybrid_cs_ok}\<close> against the node's EXACT count.
  Combines the g-count classify (trichotomy when \<open>dec\<close>) with the two bounds above and
  @{const hybrid_class_of}: \<open>dec\<close> \<Rightarrow> the class is \<open>cnt \<le> 3\<close>, a @{const dyadic_iv_cs_invar} (its
  \<open>4 \<le> c \<Longrightarrow> c = cnt + 2\<close> conjunct is vacuous at \<open>cnt \<le> 3\<close>); \<open>\<not> dec\<close> \<Rightarrow> the class is the sentinel
  \<open>4\<close> and \<open>g < 2\<^sup>4\<^sup>2\<close> hits @{const hybrid_cs_ok}'s first disjunct. What
  @{const hybrid_classify_prebuilt_monadic} needs for the two pushed children's \<open>cs\<close>-coupling.\<close>
lemma carried_descartes_count_g_hybrid_cs_ok:
  assumes frame: "node_frame X xs g"
    and lbound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length xs * nat_bitlen (length xs) < max_snat LENGTH(gmp_poly_len)"
    and gbound: "g + length xs < max_snat LENGTH(gmp_poly_len)"
    and lock: "4398046511104 \<le> g \<longrightarrow> X = xs"
  shows "carried_descartes_count_g_monadic xs g \<le> SPEC (\<lambda>(cnt, dec).
      hybrid_cs_ok g (hybrid_class_of dec cnt) (carried_descartes_count X))"
  using carried_descartes_count_g_monadic_classify[OF frame lbound pbound gbound lock]
        carried_descartes_count_g_monadic_le3[OF lbound pbound gbound]
        carried_descartes_count_g_monadic_notdec[OF lbound pbound gbound]
  by (fastforce simp: pw_le_iff refine_pw_simps hybrid_cs_ok_def hybrid_class_of_def dyadic_iv_cs_invar_def)

section \<open>Split-arm lemmas\<close>

text \<open>\<^bold>\<open>The exact-guard midpoint decision is decisive.\<close> @{const truncate_mid_decide_monadic} returns a
  three-way code: \<open>0\<close> not a root, \<open>1\<close> the midpoint is an exact root, \<open>2\<close> ambiguous. The ambiguous arm of
  @{const hybrid_branch_split_monadic} (\<open>code = 2\<close>) frees the truncated children, rebuilds the node exact
  from \<open>rp\<close>, decides again at guard \<open>0\<close>, and branches on \<open>code2 = 1\<close> versus \<open>else\<close>, treating a second \<open>2\<close>
  as not a root. That is sound only because \<open>2\<close> cannot arise at guard \<open>0\<close>: the \<open>g = 0\<close> branch is the
  unguarded sign test \<open>if 0 < mids \<or> mids < 0 then 0 else 1\<close>, with no @{const mid_guard_mop} cascade.
  This lemma justifies the \<open>else\<close> arm of that rebuild.\<close>
lemma truncate_mid_decide_monadic_exact_decisive:
  "truncate_mid_decide_monadic 0 len mids midbl \<le> SPEC (\<lambda>code. code \<noteq> 2)"
  unfolding truncate_mid_decide_monadic_def by simp

text \<open>The same fact for a LOCKed node (\<open>2\<^sup>4\<^sup>2 \<le> g\<close>), which takes the identical unguarded branch —
  the window-pushed children carry \<open>g = 2\<^sup>4\<^sup>2\<close>, so the split arm can be re-entered on them.\<close>
lemma truncate_mid_decide_monadic_locked_decisive:
  assumes "4398046511104 \<le> g"
  shows "truncate_mid_decide_monadic g len mids midbl \<le> SPEC (\<lambda>code. code \<noteq> 2)"
  using assms unfolding truncate_mid_decide_monadic_def by simp

section \<open>Pop-time resolution yields a bail-trustworthy class (dense coupling)\<close>

text \<open>The dense-coupling anchor: at pop, @{const hybrid_resolve_count_monadic} converts ANY
  \<open>hybrid_cs_ok\<close> cache entry into a @{const dyadic_iv_cs_invar} one against the node's EXACT
  polynomial \<open>X\<close> (= what escalation from the retained root \<open>rp\<close> rebuilds), locking the
  node iff it escalated. Proof: the \<open>c = 4 \<and> g < 2^42\<close> branch composes the dense
  escalation-correctness fact (escalate-from-\<open>rp\<close> \<open>=\<close> the exact carried init at the node
  frame) with the plain truncated count's classify contract; the else branch is the
  hypothesis verbatim. This is the ONLY place the sentinel is consumed at pop — \<open>\<sigma>\<close>'s
  push-time consumption of the sentinel is deliberately NOT bridged (the \<open>\<exists>pol\<close> keystone
  absorbs it).\<close>
lemma hybrid_resolve_count_monadic_classify:
  assumes rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the two word-arithmetic bounds of the kernel on the escalated polynomial \<open>X\<close>: the op's resolve arm
       calls @{const carried_descartes_count_g_monadic}, whose classification contract carries them.
       They are preconditions of the \<open>g\<close>-count kernel, as in
       @{thm [source] carried_descartes_count_g_hybrid_cs_ok}.\<close>
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_eq: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and cache: "hybrid_cs_ok g c (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> g \<Longrightarrow> Q = X"
  shows "hybrid_resolve_count_monadic Q g l_num r_num k rp c \<le> SPEC (\<lambda>(c', Q', g', rp').
      dyadic_iv_cs_invar c' (carried_descartes_count X) \<and>
      rp' = rp \<and>
      (4398046511104 \<le> g' \<longrightarrow> Q' = X) \<and>
      (g' < 4398046511104 \<longrightarrow> Q' = Q \<and> g' = g))"
proof (cases "c = 4 \<and> g < 4398046511104")
  case cond: False
  have invc: "dyadic_iv_cs_invar c (carried_descartes_count X)"
    using cache cond by (auto simp: hybrid_cs_ok_def)
  show ?thesis
    unfolding hybrid_resolve_count_monadic_def PR_CONST_def
    apply (simp add: cond)
    using invc locked_exact
    apply (simp add: pw_le_iff refine_pw_simps)
    done
next
  case cond: True
  have escalate: "carried_escalate_keep_monadic rp l_num r_num k Q
       \<le> RETURN (X, rp)"
    using rp_len rp_bound k_bound
    by (simp only: X_eq) (rule carried_escalate_keep_monadic_correct)
  have qxlen: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    using rp_bound unfolding X_eq by (simp add: truncate_length_carried_init_same_den)
  \<comment> \<open>The escalated poly is its own exact frame at ANY guard: \<open>gframe 0 0 X X\<close>
     (@{thm [source] gframe_exact}) lifted by @{thm [source] gframe_mono}. So the LOCK
     value \<open>2\<^sup>4\<^sup>2\<close> the op writes satisfies @{const node_frame}, and the classify's
     \<open>LOCK \<longrightarrow> X = xs\<close> side condition is reflexive here.\<close>
  have frameX: "node_frame X X 4398046511104"
    using gframe_mono[OF gframe_exact, of 4398046511104 X]
    by (auto simp: node_frame_def)
  \<comment> \<open>At \<open>g = 2\<^sup>4\<^sup>2\<close> the count is DECISIVE: @{thm [source] carried_descartes_count_g_monadic_notdec}
     says \<open>\<not> dec \<longrightarrow> g < 2\<^sup>4\<^sup>2\<close>, so the ambiguous arm is unreachable and the classify
     trichotomy applies — which is exactly what upgrades @{const hybrid_cs_ok} to the stronger
     @{const dyadic_iv_cs_invar} this lemma must produce. Same three facts, same order, as the
     working analog @{thm [source] carried_descartes_count_g_hybrid_cs_ok}.\<close>
  have gcls: "carried_descartes_count_g_monadic X 4398046511104 \<le> SPEC (\<lambda>(cnt, dec).
           (2 \<le> cnt \<longrightarrow> 2 \<le> carried_descartes_count X) \<and>
           (dec \<longrightarrow>
              (cnt = 0) = (carried_descartes_count X = 0) \<and>
              (cnt = 1) = (carried_descartes_count X = 1) \<and>
              (2 \<le> cnt) = (2 \<le> carried_descartes_count X)))"
    by (rule carried_descartes_count_g_monadic_classify[OF frameX qxlen X_pbound X_gbound])
       simp
  \<comment> \<open>\<^bold>\<open>Collapse the escalate binder FIRST, then reason at \<open>X\<close>.\<close> Neither \<open>refine_vcg\<close> nor a
     pointwise \<open>auto\<close> works directly on the two-op tail: the post-condition factorizes, so
     phase 1 turns it into a \<open>RES (\<dots> \<times> \<dots>)\<close> product and \<open>refine_vcg\<close>'s bind rule (which needs
     a genuine \<open>SPEC\<close> head) never fires, while \<open>auto\<close>
     leaves the \<open>4 \<le> c \<Longrightarrow> c = cnt + 2\<close> cache conjunct open because that goal mentions the
     BOUND variable and will not chain \<open>inres escalate (qx, _)\<close> into \<open>qx = X\<close> to match the
     \<open>X\<close>-stated facts. @{thm [source] bind_mono} does exactly that rewriting as a refinement
     step: \<open>escalate \<le> RETURN (X, rp)\<close> lifts through the bind, and \<open>RETURN\<close>-bind then reduces
     syntactically — after which \<open>le3\<close> makes the cache conjunct vacuous.\<close>
  have collapse:
    "hybrid_resolve_count_monadic Q g l_num r_num k rp c
       \<le> doN { ASSERT (length X + 1 < max_snat LENGTH(gmp_poly_len));
                (cx, _) \<leftarrow> carried_descartes_count_g_monadic X 4398046511104;
                RETURN (cx, X, 4398046511104, rp) }"
    unfolding hybrid_resolve_count_monadic_def PR_CONST_def
    apply (simp add: cond)
    apply (rule order_trans[OF bind_mono(1)[OF escalate]])
     \<comment> \<open>\<open>order_refl\<close>, not \<open>simp\<close>: the continuation \<open>?f'\<close> is still SCHEMATIC here, and \<open>simp\<close>
        cannot invent it. \<open>order_refl\<close> instantiates it to the continuation itself by
        higher-order pattern unification (\<open>?f' x\<close> against a \<open>case x of \<dots>\<close> body, \<open>x\<close> bound —
        a Miller pattern), which is precisely the \<open>same continuation on both sides\<close>
        reading of @{thm [source] bind_mono} we want.\<close>
     apply (rule order_refl)
    apply simp
    done
  show ?thesis
    apply (rule order_trans[OF collapse])
    \<comment> \<open>\<open>qxlen\<close> itself must be in scope, not only as the \<open>[OF \<dots>]\<close> argument of the two count
       facts: the pointwise unfolding of the surviving \<open>ASSERT\<close> splits on its condition, and
       every failed-\<open>ASSERT\<close> branch carries \<open>\<not> Suc (length X) < max_snat 64\<close> as a hypothesis —
       vacuous under \<open>qxlen\<close>, unprovable without it.\<close>
    using qxlen gcls
      carried_descartes_count_g_monadic_le3[OF qxlen X_pbound X_gbound]
      carried_descartes_count_g_monadic_notdec[OF qxlen X_pbound X_gbound]
    \<comment> \<open>\<open>fastforce\<close>, not \<open>auto\<close>, for the last two: both need TWO \<open>\<forall>\<close>-premises instantiated at
       the SAME witness \<open>(a, b)\<close> — decisiveness (\<open>notdec\<close> at \<open>g = 2\<^sup>4\<^sup>2\<close> forces \<open>b\<close>) and then the
       trichotomy under that \<open>b\<close>. \<open>auto\<close> does not chain \<open>\<forall>\<close>-premises through a shared witness;
       this is the same shape @{thm [source] carried_descartes_count_g_hybrid_cs_ok} closes with
       \<open>fastforce\<close> just above.\<close>
    by (fastforce simp: pw_le_iff refine_pw_simps dyadic_iv_cs_invar_def split: if_splits)
qed

section \<open>View freshness (widths strictly shrink down every tree edge)\<close>

text \<open>The support fact for the partial decision map: an accepted window is a strict subinterval, so
  (with bisection halving) interval widths strictly shrink along every edge of @{const newdsc_pol_bail}'s
  recursion tree, which makes every node's \<open>(a, b)\<close> view unique within one run, so extending the decision
  map at a popped node never conflicts. The window case follows from the same geometry that gives the
  \<open>\<mu>\<close>-decrease in @{thm [source] newdsc_pol_bail_domI_general}; this restates the width inequality in the
  form the freshness invariant consumes.\<close>
lemma try_window_bail_Some_width_lt:
  assumes TW: "try_window_bail gn p a b (N_of e) P v = Some I"
    and ab: "a < b"
  shows "snd I - fst I < b - a"
proof -
  have N2: "N_of e \<ge> 2" using N_of_ge_2 by simp
  have Npos: "N_of e > 0" using N2 by simp
  have w: "snd I - fst I = (b - a) / of_nat (N_of e)"
    using try_window_bail_SomeD(3)[OF TW ab Npos] .
  have "(b - a) / of_nat (N_of e) < (b - a) / 1"
    using ab N2 by (intro divide_strict_left_mono) auto
  thus ?thesis using w by simp
qed

section \<open>Free-pol sound/complete and \<open>\<exists>pol\<close> consumption packaging\<close>

text \<open>Clone of \<open>Kiou_Bound_Bail_Reflect.thy\<close>'s \<open>newdsc_pol_bail_pol_final_sound\<close>/
  \<open>_complete\<close> and \<open>newdsc_pol_bail_int_pol_final_sound_real_image'\<close>/\<open>_complete_real_image'\<close>,
  generalized to a free \<open>pol\<close>/\<open>polr\<close> pair (in place of \<open>pol_final\<close>/\<open>pol_final_real\<close>). Every
  underlying fact — @{thm [source] newdsc_pol_bail_sound}, @{thm [source]
  newdsc_pol_bail_complete}, @{thm [source] newdsc_pol_bail_int_eq_newdsc_pol_bail} — is
  already \<open>\<forall>pol\<close>; only the packaging (composing them with \<open>hybrid_pol_dom\<close> instead of
  the concrete \<open>newdsc_pol_bail_pol_final_dom\<close>) needs restating.\<close>

lemma hybrid_pol_sound:
  fixes P :: "int poly" and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "\<forall>I \<in> set (newdsc_pol_bail polr (degree P) a b e dk s (map_poly of_int P)).
           dsc_pair_ok (map_poly of_int P) I"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  show ?thesis
    by (rule newdsc_pol_bail_sound[OF hybrid_pol_dom[OF P0 p0 sf ab] dle dne ab])
qed

lemma hybrid_pol_complete:
  fixes P :: "int poly" and polr :: newton_pol_real
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "\<And>x. poly (map_poly of_int P :: real poly) x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol_bail polr (degree P) a b e dk s (map_poly of_int P)).
              fst I \<le> x \<and> x \<le> snd I)"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  show "\<And>x. poly (map_poly of_int P :: real poly) x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol_bail polr (degree P) a b e dk s (map_poly of_int P)).
              fst I \<le> x \<and> x \<le> snd I)"
    by (rule newdsc_pol_bail_complete[OF hybrid_pol_dom[OF P0 p0 sf ab] dle dne])
qed

text \<open>The \<open>\<exists>pol\<close> packaging: given ANY \<open>pol\<close>/\<open>polr\<close> pair related by \<open>polrel\<close>, the int-level
  \<open>newdsc_pol_bail_int pol\<close> is sound/complete — the keystone only ever needs to supply ONE
  concrete witness (the run-derived lookup policy above) to both of these.\<close>
lemma hybrid_pol_int_sound_real_image':
  fixes P :: "int poly" and pol :: newton_pol and polr :: newton_pol_real
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0" and sf: "square_free P_real" and ab: "a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = pol (degree P) a2 b2 e2 dk2 (s2, v)"
  shows "\<forall>I \<in> set (newdsc_pol_bail_int pol a b e dk P).
    \<exists>J \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real).
      I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
proof -
  have abr: "(of_rat a :: real) < of_rat b" using ab by (simp add: of_rat_less)
  have dom: "newdsc_pol_bail_dom (polr, degree P, of_rat a, of_rat b, e, dk, 0, P_real)"
    unfolding P_real_def
  proof (rule hybrid_pol_dom_rat)
    show "P \<noteq> 0" by (rule P0)
    show "degree P \<noteq> 0" by (rule p0)
    show "square_free (map_poly of_int P :: real poly)" using sf by (simp add: P_real_def)
    show "a < b" by (rule ab)
  qed
  have eqbridge: "rev (newdsc_pol_bail_int pol a b e dk P)
      = map real_to_rat_pair (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real)"
    unfolding P_real_def
  proof (rule newdsc_pol_bail_int_eq_newdsc_pol_bail)
    show "newdsc_pol_bail_dom (polr, degree P, of_rat a, of_rat b, e, dk, 0,
            map_poly of_int P)" using dom by (simp add: P_real_def)
    show "degree P = degree P" by (rule refl)
    show "P \<noteq> 0" by (rule P0)
    show "a < b" by (rule ab)
    show "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
            = pol (degree P) a2 b2 e2 dk2 (s2, v)" by (rule polrel)
  qed
  have set_eq: "set (newdsc_pol_bail_int pol a b e dk P)
      = real_to_rat_pair ` set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real)"
    using eqbridge by (metis set_map set_rev)
  have sound: "\<forall>J \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real).
      dsc_pair_ok P_real J"
    unfolding P_real_def by (rule hybrid_pol_sound[OF P0 p0 sf[unfolded P_real_def] abr])
  show ?thesis using set_eq sound by auto
qed

lemma hybrid_pol_int_complete_real_image':
  fixes P :: "int poly" and pol :: newton_pol and polr :: newton_pol_real
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0" and sf: "square_free P_real"
    and root: "poly P_real x = 0" and ax: "of_rat a < x" and xb: "x < of_rat b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = pol (degree P) a2 b2 e2 dk2 (s2, v)"
  shows "\<exists>I \<in> set (newdsc_pol_bail_int pol a b e dk P).
    \<exists>J \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real).
      I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
proof -
  have ab: "a < b" using ax xb by (meson less_trans of_rat_less)
  have abr: "(of_rat a :: real) < of_rat b" using ab by (simp add: of_rat_less)
  have dom: "newdsc_pol_bail_dom (polr, degree P, of_rat a, of_rat b, e, dk, 0, P_real)"
    unfolding P_real_def
  proof (rule hybrid_pol_dom_rat)
    show "P \<noteq> 0" by (rule P0)
    show "degree P \<noteq> 0" by (rule p0)
    show "square_free (map_poly of_int P :: real poly)" using sf by (simp add: P_real_def)
    show "a < b" by (rule ab)
  qed
  have eqbridge: "rev (newdsc_pol_bail_int pol a b e dk P)
      = map real_to_rat_pair (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real)"
    unfolding P_real_def
  proof (rule newdsc_pol_bail_int_eq_newdsc_pol_bail)
    show "newdsc_pol_bail_dom (polr, degree P, of_rat a, of_rat b, e, dk, 0,
            map_poly of_int P)" using dom by (simp add: P_real_def)
    show "degree P = degree P" by (rule refl)
    show "P \<noteq> 0" by (rule P0)
    show "a < b" by (rule ab)
    show "\<And>a2 b2 e2 dk2 s2 v. polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
            = pol (degree P) a2 b2 e2 dk2 (s2, v)" by (rule polrel)
  qed
  have set_eq: "set (newdsc_pol_bail_int pol a b e dk P)
      = real_to_rat_pair ` set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real)"
    using eqbridge by (metis set_map set_rev)
  have completeP: "\<And>x. poly (map_poly of_int P :: real poly) x = 0 \<Longrightarrow> of_rat a < x \<Longrightarrow>
           x < of_rat b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0
                        (map_poly of_int P)). fst I \<le> x \<and> x \<le> snd I)"
    using hybrid_pol_complete[OF P0 p0 sf[unfolded P_real_def] abr, where e = e and dk = dk and s = 0]
    by simp
  have ex_step: "\<exists>I \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real).
      fst I \<le> x \<and> x \<le> snd I"
    using completeP[of x] root[unfolded P_real_def] ax xb
    by (simp add: P_real_def)
  obtain J where J_in: "J \<in> set (newdsc_pol_bail polr (degree P) (of_rat a) (of_rat b) e dk 0 P_real)"
    and J_cov: "fst J \<le> x \<and> x \<le> snd J"
    using ex_step by blast
  then have "real_to_rat_pair J \<in> set (newdsc_pol_bail_int pol a b e dk P)" using set_eq by blast
  thus ?thesis using J_in J_cov by blast
qed

section \<open>The \<open>\<exists>pol\<close>-from-decision-map extraction (the keystone's exit device)\<close>

text \<open>The run-derived witness policy: ignore \<open>e\<close>/\<open>dk\<close>/\<open>(s,v)\<close> entirely and look the decision up
  by the node's \<open>(a,b)\<close> view in the accumulated decision list \<open>D\<close> (default \<open>(False, False)\<close> =
  bisect, off the domain). The degree argument is also ignored — the hybrid solve is
  degree-constant. This is the concrete form of the \<open>pol_witness\<close> the keystone builds from
  \<open>D_final\<close>.\<close>
definition hybrid_pol_of_D :: "((rat \<times> rat) \<times> (bool \<times> bool)) list \<Rightarrow> newton_pol" where
  "hybrid_pol_of_D D = (\<lambda>_ a b _ _ _. case map_of D (a, b) of Some d \<Rightarrow> d | None \<Rightarrow> (False, False))"

text \<open>\<^bold>\<open>From every extending policy to one policy.\<close> If the implementation's accumulator multiset equals
  \<open>hybrid_tree1\<close> of the seed for every policy that agrees with the recorded decision map \<open>D\<close> on \<open>dom D\<close>
  (the WHILEIT invariant's accounting clause, read off at \<open>todo = []\<close>), then some policy realises it:
  @{const hybrid_pol_of_D}, which extends \<open>D\<close> by construction (well defined because \<open>D\<close>'s keys are
  @{const distinct}, @{thm [source] alr_ivl_run_invar_D_distinct}). This turns the run-dependent tree into
  the \<open>\<exists>pol\<close> shape that the theorems quantified over every policy consume.\<close>
lemma hybrid_expol_from_decisions:
  fixes D :: "((rat \<times> rat) \<times> (bool \<times> bool)) list" and P :: "int poly"
  assumes dist: "distinct (map fst D)"
    and acc: "\<And>pol. (\<forall>(v, d) \<in> set D. \<forall>e2 dk2 s2 w2.
                 pol (degree P) (fst v) (snd v) e2 dk2 (s2, w2) = d)
              \<Longrightarrow> mset ACC = mset (hybrid_tree1 pol P a b e0 dk0 0)"
  shows "\<exists>pol. mset ACC = mset (newdsc_pol_bail_int pol a b e0 dk0 P)"
proof -
  let ?pol = "hybrid_pol_of_D D"
  have extends: "\<forall>(v, d) \<in> set D. \<forall>e2 dk2 s2 w2.
      ?pol (degree P) (fst v) (snd v) e2 dk2 (s2, w2) = d"
  proof (intro ballI allI, clarify)
    fix v :: "rat \<times> rat" and d :: "bool \<times> bool" and e2 dk2 s2 w2
    assume vd: "(v, d) \<in> set D"
    have "map_of D v = Some d" using dist vd by (rule map_of_is_SomeI)
    thus "?pol (degree P) (fst v) (snd v) e2 dk2 (s2, w2) = d"
      by (simp add: hybrid_pol_of_D_def)
  qed
  have "mset ACC = mset (hybrid_tree1 ?pol P a b e0 dk0 0)"
    by (rule acc[where pol = ?pol, OF extends])
  also have "hybrid_tree1 ?pol P a b e0 dk0 0 = newdsc_pol_bail_int ?pol a b e0 dk0 P"
    by (simp add: hybrid_tree1_def newdsc_pol_bail_int_def)
  finally show ?thesis by blast
qed

section \<open>The abstract accounting engine (\<open>\<forall>pol\<close>-extending-\<open>D\<close> worklist decomposition)\<close>

text \<open>\<^bold>\<open>The accounting invariant\<close> that replaces bail's \<open>newton_gmp_main_bail (\<alpha> st) = \<dots>\<close>
  invariant clause (@{text blr_refine_invar}, \<open>Bail_Loop_Refine.thy\<close>) — the one
  clause the hybrid CANNOT carry (its \<open>\<sigma>\<close> diverges from bail's fixed pure driver). It states, for
  EVERY policy \<open>pol\<close> agreeing with the recorded decision map \<open>D\<close> on \<open>dom D\<close>, that the accepted
  multiset plus the still-pending worklist's subtree multiset equals the seed subtree — the
  order-agnostic worklist decomposition (@{const hybrid_tree_mset} / @{thm [source] hybrid_worklist_decomp})
  carried as a loop invariant. At \<open>todo = []\<close> it collapses (via @{thm [source]
  hybrid_expol_from_decisions}) to the keystone's \<open>\<exists>pol\<close> conclusion. It is entirely ABSTRACT — pure
  rat/multiset bookkeeping over @{const hybrid_tree1}, independent of the concrete truncation/guard
  coupling (which is a SEPARATE conjunct of the full WHILEIT invariant, cloned from
  @{term truncate_state_rel}).\<close>
definition hybrid_acc_invar ::
  "int poly \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) \<Rightarrow> ((rat \<times> rat) \<times> (bool \<times> bool)) list
     \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> bool" where
  "hybrid_acc_invar P seed D ACC todo \<longleftrightarrow>
     (\<forall>pol. (\<forall>(v, d) \<in> set D. \<forall>e2 dk2 s2 w2.
                pol (degree P) (fst v) (snd v) e2 dk2 (s2, w2) = d) \<longrightarrow>
            mset ACC + hybrid_tree_mset pol P todo = hybrid_tree_mset pol P [seed])"

text \<open>Seeding: the initial worklist \<open>[seed]\<close> with empty acc and empty decision map — the
  accounting holds trivially (\<open>{#} + tree(seed) = tree(seed)\<close>).\<close>
lemma hybrid_acc_invar_init: "hybrid_acc_invar P seed [] [] [seed]"
  by (simp add: hybrid_acc_invar_def)

text \<open>\<^bold>\<open>Exit\<close>: at \<open>todo = []\<close> with a distinct-keyed decision map, the accounting collapses to the
  keystone's \<open>\<exists>pol\<close> conclusion. The seed's run-length component must be \<open>0\<close> (the top-level entry
  point's, so @{const hybrid_tree1} at \<open>s = 0\<close> equals @{const newdsc_pol_bail_int}).\<close>
lemma hybrid_acc_invar_exit:
  assumes inv: "hybrid_acc_invar P (a, b, e0, dk0, 0) D ACC []"
    and dist: "distinct (map fst D)"
  shows "\<exists>pol. mset ACC = mset (newdsc_pol_bail_int pol a b e0 dk0 P)"
proof (rule hybrid_expol_from_decisions[OF dist])
  fix pol :: newton_pol
  assume ext: "\<forall>(v, d) \<in> set D. \<forall>e2 dk2 s2 w2.
      pol (degree P) (fst v) (snd v) e2 dk2 (s2, w2) = d"
  from inv[unfolded hybrid_acc_invar_def] ext
  have "mset ACC + hybrid_tree_mset pol P [] = hybrid_tree_mset pol P [(a, b, e0, dk0, 0)]" by blast
  thus "mset ACC = mset (hybrid_tree1 pol P a b e0 dk0 0)"
    by (simp add: hybrid_tree_mset_Cons)
qed

text \<open>\<^bold>\<open>Step\<close>: pop the LAST worklist node \<open>(a,b,e,dk,s)\<close> (LIFO), record its decision \<open>dec\<close> at
  view \<open>(a,b)\<close>, append leaf list \<open>L\<close> to acc and push children nodes \<open>C\<close>. Provided the abstract
  ONE-STEP unfold holds along the recorded branch (\<open>branch\<close> — discharged per-arm by @{thm [source]
  hybrid_tree1_unfold} once the concrete impl's leaf/children are shown to match what
  @{const newdsc_pol_bail}'s recursion produces under \<open>pol (\<dots>) = dec\<close>), the accounting invariant
  is preserved. Freshness of \<open>(a,b)\<close> in \<open>D\<close> is NOT needed here (it is tracked separately by
  @{const alr_ivl_run_invar} for the \<open>distinct\<close> the EXIT needs) — the accounting holds regardless,
  vacuously if \<open>D\<close> were made inconsistent.\<close>
lemma hybrid_acc_invar_step:
  assumes inv: "hybrid_acc_invar P seed D ACC (rest @ [(a, b, e, dk, s)])"
    and branch: "\<And>pol. pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P)) = dec
                   \<Longrightarrow> mset (hybrid_tree1 pol P a b e dk s) = mset L + hybrid_tree_mset pol P C"
  shows "hybrid_acc_invar P seed (D @ [((a, b), dec)]) (ACC @ L) (rest @ C)"
  unfolding hybrid_acc_invar_def
proof (intro allI impI)
  fix pol :: newton_pol
  assume ext: "\<forall>(v, d) \<in> set (D @ [((a, b), dec)]). \<forall>e2 dk2 s2 w2.
      pol (degree P) (fst v) (snd v) e2 dk2 (s2, w2) = d"
  have extD: "\<forall>(v, d) \<in> set D. \<forall>e2 dk2 s2 w2.
      pol (degree P) (fst v) (snd v) e2 dk2 (s2, w2) = d"
    using ext by auto
  have deceq: "pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P)) = dec"
    using ext by auto
  have base: "mset ACC + hybrid_tree_mset pol P (rest @ [(a, b, e, dk, s)])
      = hybrid_tree_mset pol P [seed]"
    using inv[unfolded hybrid_acc_invar_def] extD by blast
  have "mset (ACC @ L) + hybrid_tree_mset pol P (rest @ C)
      = mset ACC + (mset L + hybrid_tree_mset pol P C) + hybrid_tree_mset pol P rest"
    by (simp add: hybrid_tree_mset_append add.assoc add.left_commute)
  also have "mset L + hybrid_tree_mset pol P C = mset (hybrid_tree1 pol P a b e dk s)"
    using branch[where pol = pol, OF deceq] by simp
  also have "mset ACC + mset (hybrid_tree1 pol P a b e dk s) + hybrid_tree_mset pol P rest
      = mset ACC + hybrid_tree_mset pol P (rest @ [(a, b, e, dk, s)])"
    by (simp add: hybrid_tree_mset_append hybrid_tree_mset_Cons add.assoc add.left_commute)
  also have "\<dots> = hybrid_tree_mset pol P [seed]" by (rule base)
  finally show "mset (ACC @ L) + hybrid_tree_mset pol P (rest @ C) = hybrid_tree_mset pol P [seed]" .
qed

section \<open>The \<open>\<alpha>\<close>-projection to abstract count-frame nodes\<close>

text \<open>The concrete hybrid loop state carries the parallel columns \<open>todo\<close> (dyadic interval
  vector), \<open>es\<close> (NewDsc exponents) and \<open>ss\<close> (run-length counters). This projects them to the
  abstract count-frame nodes @{typ "(rat \<times> rat \<times> nat \<times> nat \<times> nat)"} that the accounting engine
  (@{const hybrid_acc_invar} / @{const hybrid_tree_mset}) consumes: each todo triple \<open>t = ((l,r),k)\<close>
  maps to \<open>(a, b) = @{term "dyadic_iv_node_iv_of l0 r0 k0 t"}\<close> (its count-frame interval, anchored at
  the run's \<open>(l0,r0,k0)\<close>), with \<open>e\<close> from \<open>es\<close>, the depth tag \<open>dk = k = snd t\<close>, and \<open>s\<close> from
  \<open>ss\<close>. (Under the run-derived policy \<open>e\<close> drives \<open>try_window_bail_int\<close>'s grid; \<open>dk\<close>/\<open>s\<close> feed
  only \<open>pol\<close>, which the witness ignores — see the file header — so their concrete values are
  harmless.) The \<open>qtodo\<close>/\<open>cs\<close>/\<open>gs\<close> columns do NOT enter this projection; they are coupled
  separately (truncation/guard coupling and the cache coupling).\<close>
definition hybrid_alpha_nodes ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> nat list \<Rightarrow> nat list
     \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list" where
  "hybrid_alpha_nodes l0 r0 k0 todo es ss =
     map (\<lambda>(t, e, s). (fst (dyadic_iv_node_iv_of l0 r0 k0 t), snd (dyadic_iv_node_iv_of l0 r0 k0 t),
                       e, snd t, s))
         (zip (dyadic_interval_vec_triples todo) (zip es ss))"

text \<open>The \<open>(a,b)\<close> views of the abstract nodes — the family @{const alr_ivl_run_invar} tracks
  compatible.\<close>
definition hybrid_alpha_views ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> (rat \<times> rat) list" where
  "hybrid_alpha_views l0 r0 k0 todo = map (dyadic_iv_node_iv_of l0 r0 k0) (dyadic_interval_vec_triples todo)"

text \<open>Under aligned column lengths, the views are exactly the first two components of the
  abstract nodes (the shape @{const alr_ivl_run_invar}'s clauses need to line up with the accounting
  engine's node list).\<close>
lemma hybrid_alpha_views_eq_map:
  assumes "length es = length (dyadic_interval_vec_triples todo)"
    and "length ss = length (dyadic_interval_vec_triples todo)"
  shows "hybrid_alpha_views l0 r0 k0 todo
     = map (\<lambda>nd. (fst nd, fst (snd nd))) (hybrid_alpha_nodes l0 r0 k0 todo es ss)"
proof -
  have lenz: "length (dyadic_interval_vec_triples todo) = length (zip es ss)"
    using assms by simp
  have key: "map fst (zip (dyadic_interval_vec_triples todo) (zip es ss))
      = dyadic_interval_vec_triples todo"
    by (rule map_fst_zip[OF lenz])
  have "map (\<lambda>nd. (fst nd, fst (snd nd))) (hybrid_alpha_nodes l0 r0 k0 todo es ss)
      = map (\<lambda>t. dyadic_iv_node_iv_of l0 r0 k0 t)
          (map fst (zip (dyadic_interval_vec_triples todo) (zip es ss)))"
    by (simp add: hybrid_alpha_nodes_def case_prod_beta comp_def dyadic_iv_node_iv_of_def)
  also have "\<dots> = hybrid_alpha_views l0 r0 k0 todo"
    by (simp add: key hybrid_alpha_views_def)
  finally show ?thesis ..
qed

lemma hybrid_alpha_nodes_length:
  assumes "length es = length (dyadic_interval_vec_triples todo)"
    and "length ss = length (dyadic_interval_vec_triples todo)"
  shows "length (hybrid_alpha_nodes l0 r0 k0 todo es ss) = length (dyadic_interval_vec_triples todo)"
  using assms by (simp add: hybrid_alpha_nodes_def)

text \<open>\<^bold>\<open>Pop-last (LIFO) behavior of the \<open>\<alpha>\<close>-projection\<close>: popping the concrete todo's last node
  (and the parallel \<open>es\<close>/\<open>ss\<close> columns) is @{term butlast} on the abstract node/view lists. Reuses
  bail's @{thm [source] blr_triples_butlast_bl}; the double-zip commutes with @{term butlast} via
  @{thm [source] butlast_conv_take} under the aligned column lengths. Needed by the step-preservation
  to relate the popped concrete state to the abstract worklist decomposition.\<close>
lemma hybrid_alpha_views_butlast:
  assumes inv: "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
       = butlast (hybrid_alpha_views l0 r0 k0 (lns, rns, ks))"
  unfolding hybrid_alpha_views_def
  by (simp add: blr_triples_butlast_bl[OF inv] map_butlast)

text \<open>@{term butlast} commutes with @{const zip} under equal lengths. Proven by @{thm [source]
  list_induct2}, NOT with @{thm butlast_conv_take} in a simp set, which rewrites every
  @{term butlast} to a @{const take} and then churns on the \<open>length _ - 1\<close> / @{const min}
  arithmetic.\<close>
lemma butlast_zip_eq:
  "length xs = length ys \<Longrightarrow> butlast (zip xs ys) = zip (butlast xs) (butlast ys)"
proof (induction xs ys rule: list_induct2)
  case (Cons x xs y ys)
  show ?case by (cases "xs = []") (use Cons in auto)
qed simp

lemma hybrid_alpha_nodes_butlast:
  assumes inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and les: "length es = length (dyadic_interval_vec_triples (lns, rns, ks))"
    and lss: "length ss = length (dyadic_interval_vec_triples (lns, rns, ks))"
  shows "hybrid_alpha_nodes l0 r0 k0 (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
       = butlast (hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss)"
proof -
  let ?tr = "dyadic_interval_vec_triples (lns, rns, ks)"
  let ?f = "\<lambda>(t, e, s). (fst (dyadic_iv_node_iv_of l0 r0 k0 t), snd (dyadic_iv_node_iv_of l0 r0 k0 t),
                        e, snd t, s)"
  have tb: "dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) = butlast ?tr"
    by (rule blr_triples_butlast_bl[OF inv])
  have z1: "butlast (zip es ss) = zip (butlast es) (butlast ss)"
    by (rule butlast_zip_eq) (use les lss in simp)
  have lz: "length ?tr = length (zip es ss)" using les lss by simp
  have z2: "butlast (zip ?tr (zip es ss)) = zip (butlast ?tr) (butlast (zip es ss))"
    by (rule butlast_zip_eq[OF lz])
  \<comment> \<open>explicit chain: only the specific equations \<open>z1\<close>/\<open>z2\<close> (via \<open>simp only\<close>) and
     @{thm map_butlast} (via \<open>rule\<close>) — no @{thm butlast_conv_take} and no \<open>subst\<close> on the big
     projection lambda, both of which caused runaway/slow builds.\<close>
  have "hybrid_alpha_nodes l0 r0 k0 (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
      = map ?f (zip (butlast ?tr) (zip (butlast es) (butlast ss)))"
    by (simp add: hybrid_alpha_nodes_def tb)
  also have "\<dots> = map ?f (butlast (zip ?tr (zip es ss)))"
    by (simp only: z1[symmetric] z2[symmetric])
  also have "\<dots> = butlast (map ?f (zip ?tr (zip es ss)))"
    by (rule map_butlast)
  also have "\<dots> = butlast (hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss)"
    by (simp add: hybrid_alpha_nodes_def)
  finally show ?thesis .
qed

text \<open>The root triple projects to the normalized count-frame interval \<open>(0, 1)\<close> (the seed view).\<close>
lemma dyadic_iv_node_iv_root:
  assumes "l0 < r0"
  shows "dyadic_iv_node_iv l0 r0 k0 l0 r0 k0 = (0, 1)"
proof -
  have lt: "dyadic_rat l0 k0 < dyadic_rat r0 k0"
    using assms by (simp add: dyadic_rat_def divide_strict_right_mono)
  hence ne: "dyadic_rat r0 k0 - dyadic_rat l0 k0 \<noteq> 0"
    and ne2: "dyadic_rat r0 k0 \<noteq> dyadic_rat l0 k0" by simp_all
  show ?thesis unfolding dyadic_iv_node_iv_def Let_def by (simp add: ne ne2)
qed

text \<open>\<^bold>\<open>The abstract-side WHILEIT invariant\<close>: existentially carry the ghost decision map \<open>D\<close>
  (a proof artifact, not in the concrete state) with BOTH the freshness/distinctness device
  (@{const alr_ivl_run_invar} over the recorded views vs the live @{const hybrid_alpha_views}) AND the
  \<open>\<forall>pol\<close>-extending-\<open>D\<close> accounting (@{const hybrid_acc_invar} over the projected acc-intervals and the
  live @{const hybrid_alpha_nodes}). This is the pair of clauses that REPLACE bail's
  \<open>newton_gmp_main_bail\<close>-alignment clause; the full concrete WHILEIT invariant is this CONJOINED
  with the (separate) truncation/guard coupling + word bounds cloned from \<open>truncate_state_rel\<close> and
  bail's own budget clauses.\<close>
definition hybrid_abs_invar ::
  "int poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat)
     \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "hybrid_abs_invar P l0 r0 k0 seed todo es ss acc \<longleftrightarrow>
     (\<exists>D. alr_ivl_run_invar (map fst D) (hybrid_alpha_views l0 r0 k0 todo) \<and>
          hybrid_acc_invar P seed D (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc))
            (hybrid_alpha_nodes l0 r0 k0 todo es ss))"

text \<open>\<^bold>\<open>Exit\<close>: at empty todo the abstract invariant yields the keystone's \<open>\<exists>pol\<close> conclusion
  directly — the recorded map is distinct (@{thm [source] alr_ivl_run_invar_D_distinct}), so the
  accounting collapses via @{thm [source] hybrid_acc_invar_exit}.\<close>
lemma hybrid_abs_invar_exit:
  assumes inv: "hybrid_abs_invar P l0 r0 k0 (a, b, e0, dk0, 0) todo es ss acc"
    and empty: "dyadic_interval_vec_triples todo = []"
  shows "\<exists>pol. mset (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc))
              = mset (newdsc_pol_bail_int pol a b e0 dk0 P)"
proof -
  from inv obtain D
    where run: "alr_ivl_run_invar (map fst D) (hybrid_alpha_views l0 r0 k0 todo)"
      and acc: "hybrid_acc_invar P (a, b, e0, dk0, 0) D
                  (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc))
                  (hybrid_alpha_nodes l0 r0 k0 todo es ss)"
    by (auto simp: hybrid_abs_invar_def)
  have nodes_empty: "hybrid_alpha_nodes l0 r0 k0 todo es ss = []"
    using empty by (simp add: hybrid_alpha_nodes_def)
  have dist: "distinct (map fst D)" using run by (rule alr_ivl_run_invar_D_distinct)
  have acc0: "hybrid_acc_invar P (a, b, e0, dk0, 0) D
                (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)) []"
    using acc by (simp add: nodes_empty)
  show ?thesis by (rule hybrid_acc_invar_exit[OF acc0 dist])
qed

text \<open>\<^bold>\<open>Init\<close>: the seed state — a single root node (triple \<open>((l0,r0),k0)\<close>, exponent \<open>e0\<close>, run-length
  \<open>0\<close>), empty acc — satisfies the abstract invariant with the empty decision map. The seed abstract
  node is \<open>(0, 1, e0, k0, 0)\<close> (the root view is \<open>(0,1)\<close>, @{thm [source] dyadic_iv_node_iv_root}). The
  concrete seed's \<open>dyadic_interval_vec_triples\<close> shape is supplied by the keystone assembly (as in
  bail's \<open>bail_main_list_correct\<close> seeding).\<close>
lemma hybrid_abs_invar_init:
  assumes triples: "dyadic_interval_vec_triples todo = [((l0, r0), k0)]"
    and lr: "l0 < r0"
    and es: "es = [e0]" and ss: "ss = [0]"
    and acc_empty: "dyadic_interval_vec_triples acc = []"
  shows "hybrid_abs_invar P l0 r0 k0 (0, 1, e0, k0, 0) todo es ss acc"
  unfolding hybrid_abs_invar_def
proof (intro exI[of _ "[]"] conjI)
  have view: "hybrid_alpha_views l0 r0 k0 todo = [(0, 1)]"
    by (simp add: hybrid_alpha_views_def triples dyadic_iv_node_iv_of_def dyadic_iv_node_iv_root[OF lr])
  show "alr_ivl_run_invar (map fst []) (hybrid_alpha_views l0 r0 k0 todo)"
    by (simp add: view alr_ivl_run_invar_init)
  have nodes: "hybrid_alpha_nodes l0 r0 k0 todo es ss = [(0, 1, e0, k0, 0)]"
    by (simp add: hybrid_alpha_nodes_def triples es ss dyadic_iv_node_iv_of_def dyadic_iv_node_iv_root[OF lr])
  show "hybrid_acc_invar P (0, 1, e0, k0, 0) []
          (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc))
          (hybrid_alpha_nodes l0 r0 k0 todo es ss)"
    by (simp add: nodes acc_empty dyadic_iv_acc_ivs_def hybrid_acc_invar_init)
qed

section \<open>Dispatch-arm correctness (\<open>\<le> RETURN/SPEC\<close>)\<close>

text \<open>The discard arm (\<open>v = 0\<close>): frees the popped endpoints and node poly, returns the
  already-popped state UNCHANGED. Clone of bail's @{thm [source] blr_branch_zero_refine_bl} with
  the \<open>gs\<close>/\<open>rp\<close> columns; the frees are \<open>\<le> SPEC (\<lambda>_. True)\<close> (their \<open>[refine_vcg]\<close> rules,
  @{thm [source] poly_free_monadic_rule}), so the tail RETURN survives. This is the abstract
  \<open>v = 0\<close> branch: no new todo, acc unchanged (matches @{thm [source] hybrid_tree1_discard}: the node's
  subtree is empty).\<close>
lemma hybrid_branch_zero_correct:
  "hybrid_branch_zero_monadic todo qtodo es ss cs gs rp acc l_num r_num Q
     \<le> RETURN ((todo, qtodo, es, ss, cs, gs, rp), acc)"
  unfolding hybrid_branch_zero_monadic_def mpzb_discard_monadic_def PR_CONST_def
  by refine_vcg simp

text \<open>The acc push helper appends the accepted interval's endpoints/exponent (clone of the push
  half of bail's @{thm [source] blr_branch_one_refine_bl}).\<close>
lemma hybrid_acc_push_iv_correct:
  assumes "dyadic_interval_vec_pushable (lns, rns, ks)"
  shows "hybrid_acc_push_iv_monadic (lns, rns, ks) l_num r_num k
       \<le> RETURN (lns @ [l_num], rns @ [r_num], ks @ [k])"
  using assms
  unfolding hybrid_acc_push_iv_monadic_def poly_push_coeff_monadic_def PR_CONST_def
    dyadic_interval_vec_pushable_def
  by refine_vcg auto

text \<open>The accept arm (\<open>v = 1\<close>): push \<open>(l_num, r_num, k)\<close> onto acc and free \<open>Q\<close>. Matches the
  abstract \<open>v = 1\<close> branch (@{thm [source] hybrid_tree1_accept}: the node's subtree is the singleton
  \<open>[(a, b)]\<close>, whose count-frame projection is the pushed endpoint pair).\<close>
lemma hybrid_branch_one_correct:
  assumes "dyadic_interval_vec_pushable (lns, rns, ks)"
  shows "hybrid_branch_one_monadic todo qtodo es ss cs gs rp (lns, rns, ks) l_num r_num k Q
       \<le> RETURN ((todo, qtodo, es, ss, cs, gs, rp), (lns @ [l_num], rns @ [r_num], ks @ [k]))"
  unfolding hybrid_branch_one_monadic_def PR_CONST_def
  apply (refine_vcg hybrid_acc_push_iv_correct[OF assms, THEN order_trans])
  apply simp
  done

text \<open>The keystone itself, @{text hybrid_main_list_correct}, and the capstones are in
  \<open>Hybrid_Keystone\<close> and \<open>Hybrid_Capstone\<close>.\<close>

end
