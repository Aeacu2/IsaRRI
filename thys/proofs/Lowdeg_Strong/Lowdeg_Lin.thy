theory Lowdeg_Lin
  imports
    IsaRRI_Refine.Stack_Bound
    IsaRRI_Refine.Lowdeg_Reflect
begin

text \<open>\<^bold>\<open>The degree \<open>\<le> 8\<close> path's bisection loop, with a word budget linear in \<open>\<mu>\<close>.\<close>

  @{const bilr_refine_invar} bounds the worklist and the accumulator by charging every pending node
  a complete binary tree below it (\<open>2\<^sup>\<mu>\<^sup>+\<^sup>1\<close> entries), so its seed needs
  \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 + 1 < 2\<^sup>6\<^sup>3\<close>. Here the two budgets are replaced:

  \<^item> the worklist is a depth-first stack (@{const bisection_gmp_step} pops the last node and pushes
    its two halves), so @{const stack_ok} bounds it by \<open>\<mu>(0,1) + 1\<close> entries;
  \<^item> the accumulator only grows, so at every state it is a prefix of the pure driver's final
    accumulator (\<open>carried_gmp_main_acc_prefix\<close>), which the invariant already pins;
    that final accumulator is the Descartes output, at most one window per root.

  The loop, the code and every other conjunct are those of \<open>Bisection_Loop_Refine\<close>; this theory
  re-assembles its step and capstone lemmas around the new invariant.\<close>

section \<open>The pure driver only appends to the accumulator\<close>

lemma bisection_gmp_step_acc_ext:
  "\<exists>zs. snd (bisection_gmp_step st) = snd st @ zs"
  by (cases st) (auto simp: bisection_gmp_step_def Let_def split: prod.splits)

lemma carried_gmp_main_acc_prefix:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and P_len: "0 < length P"
  shows "(\<forall>nd \<in> set (fst st). gmp_node_inv P l0 r0 k0 nd)
           \<Longrightarrow> \<exists>ys. snd (carried_gmp_main st) = snd st @ ys"
proof (induct st rule: wf_induct[OF bilr_abs_mu_mset_rel_wf[of \<delta> l0 r0 k0]])
  case (1 st)
  show ?case
  proof (cases "fst st = []")
    case True
    obtain a b where st: "st = (a, b)" by (cases st)
    then have "carried_gmp_main st = st" using True by (simp add: carried_gmp_main_Nil)
    then show ?thesis by simp
  next
    case ne: False
    obtain x xs where fx: "fst st = x # xs" using ne by (cases "fst st") auto
    have eq: "carried_gmp_main st = carried_gmp_main (bisection_gmp_step st)"
      using fx by (cases st) (simp add: carried_gmp_main.simps)
    have ninv': "\<forall>nd \<in> set (fst (bisection_gmp_step st)). gmp_node_inv P l0 r0 k0 nd"
      by (rule gmp_node_inv_preserved[OF P_len "1.prems"])
    have meas: "rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st)))
        < rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st))"
      by (rule bisection_gmp_step_mu_decreases[OF \<delta>_pos small_fast ne "1.prems"])
    obtain ys where ys: "snd (carried_gmp_main (bisection_gmp_step st)) = snd (bisection_gmp_step st) @ ys"
      using "1.hyps"[rule_format, of "bisection_gmp_step st"] meas ninv' by auto
    obtain zs where zs: "snd (bisection_gmp_step st) = snd st @ zs"
      using bisection_gmp_step_acc_ext by blast
    show ?thesis using eq ys zs by auto
  qed
qed

section \<open>The worklist is a depth-first stack\<close>

lemma carried_step_preserves_stack:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and inv: "\<forall>e \<in> set (fst st). gmp_node_inv P l0 r0 k0 e"
    and st0: "stack_ok M (map (rational_interval_mu \<delta>) (todo_ivs l0 r0 k0 (fst st)))"
  shows "stack_ok M (map (rational_interval_mu \<delta>) (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st))))"
proof (cases "fst st = []")
  case True thus ?thesis using st0 by (cases st) (simp add: bisection_gmp_step_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain t Q where tQ: "last todo = (t, Q)" by (cases "last todo")
  obtain lr k where lrk: "t = (lr, k)" by (cases t)
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), Q)" using tQ lrk lr_eq by simp
  have inv': "\<forall>e \<in> set todo. gmp_node_inv P l0 r0 k0 e" using inv by (simp add: st)
  have ninv: "gmp_node_inv P l0 r0 k0 (((l, r), k), Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (node_iv l0 r0 k0 l r k)"
  define b where "b = snd (node_iv l0 r0 k0 l r k)"
  have ab: "a < b" using gmp_node_inv_ordered[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using gmp_node_inv_count[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have niv: "node_iv_of l0 r0 k0 ((l, r), k) = (a, b)" by (simp add: node_iv_of_def a_def b_def)
  let ?m = "(a + b) / 2"
  let ?mu = "rational_interval_mu \<delta>"
  have todo_split: "todo = butlast todo @ [(((l, r), k), Q)]"
    using todo_ne last_eq by (metis append_butlast_last_id)
  have old_ivs: "todo_ivs l0 r0 k0 todo = todo_ivs l0 r0 k0 (butlast todo) @ [(a, b)]"
    by (subst todo_split) (simp add: todo_ivs_def niv)
  have S: "stack_ok M (map ?mu (todo_ivs l0 r0 k0 (butlast todo)) @ [?mu (a, b)])"
    using st0 unfolding st fst_conv old_ivs by simp
  show ?thesis
  proof (cases "carried_descartes_count Q = 0 \<or> carried_descartes_count Q = 1")
    case True
    have stf: "fst (bisection_gmp_step st) = butlast todo"
      using todo_ne last_eq True by (auto simp: st bisection_gmp_step_def Let_def)
    show ?thesis unfolding stf by (rule stack_ok_pop[OF S])
  next
    case False
    have v0: "descartes_list_int a b P \<noteq> 0" and v1: "descartes_list_int a b P \<noteq> 1"
      using False count by auto
    have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
    proof (rule ccontr)
      assume "\<not> \<delta> < of_rat b - of_rat a"
      then have "of_rat b - of_rat a \<le> \<delta>" by linarith
      then have "descartes_list_int a b P \<le> 1" using small_fast[OF ab] by simp
      with v0 v1 show False by simp
    qed
    have left_lt: "rational_interval_mu \<delta> (a, ?m) < rational_interval_mu \<delta> (a, b)"
      using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def by (simp add: of_rat_add of_rat_divide)
    have right_lt: "rational_interval_mu \<delta> (?m, b) < rational_interval_mu \<delta> (a, b)"
      using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def by (simp add: of_rat_add of_rat_divide)
    have nl: "node_iv_of l0 r0 k0 ((l + l, l + r), k + 1) = (a, ?m)"
      using node_iv_bisect_left[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
    have nr: "node_iv_of l0 r0 k0 ((l + r, r + r), k + 1) = (?m, b)"
      using node_iv_bisect_right[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
    have stf: "fst (bisection_gmp_step st)
        = butlast todo @ [(((l + l, l + r), k + 1), carried_left Q),
                          (((l + r, r + r), k + 1), carried_right Q)]"
      using todo_ne last_eq v0 v1 count by (auto simp: st bisection_gmp_step_def Let_def)
    have new_ivs: "todo_ivs l0 r0 k0 (fst (bisection_gmp_step st))
        = todo_ivs l0 r0 k0 (butlast todo) @ [(a, ?m), (?m, b)]"
      by (simp only: stf todo_ivs_def map_append list.map fst_conv nl nr)
    show ?thesis
      unfolding new_ivs using stack_ok_push2[OF S left_lt right_lt] by simp
  qed
qed

lemma rational_interval_mu_ge_1: "1 \<le> rational_interval_mu \<delta> I"
  unfolding rational_interval_mu_def mu_def by simp

lemma stack_ok_todo_len:
  assumes s: "stack_ok (rational_interval_mu \<delta> (0, 1))
                (map (rational_interval_mu \<delta>) (todo_ivs l0 r0 k0 todo))"
  shows "length todo \<le> Suc (rational_interval_mu \<delta> (0, 1))"
proof -
  have "length (map (rational_interval_mu \<delta>) (todo_ivs l0 r0 k0 todo))
          \<le> Suc (rational_interval_mu \<delta> (0, 1))"
    by (rule stack_ok_length[OF s]) (auto simp: rational_interval_mu_def mu_def)
  then show ?thesis by (simp add: todo_ivs_def)
qed

section \<open>The refinement invariant, with the two budgets replaced\<close>

definition bilr_refine_invar_lin ::
  "real \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bisection_gmp_state \<Rightarrow>
    bisection_loop_state \<Rightarrow> bool" where
"bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 st \<equiv>
  bisection_loop_safe_invar st \<and>
  (\<forall>nd \<in> set (bilr_alpha_todo st). gmp_node_inv P l0 r0 k0 nd) \<and>
  carried_gmp_main (bilr_alpha st) = carried_gmp_main st0 \<and>
  stack_ok (rational_interval_mu \<delta> (0, 1))
    (map (rational_interval_mu \<delta>) (todo_ivs l0 r0 k0 (bilr_alpha_todo st))) \<and>
  (\<forall>nd \<in> set (bilr_alpha_todo st).
     snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1
       < max_snat LENGTH(gmp_poly_len)) \<and>
  (\<forall>nd \<in> set (bilr_alpha_todo st). length (snd nd) = length P)"

text \<open>\<^bold>\<open>The accumulator bound, read off the invariant\<close>: the state's accumulator is a prefix of
  the driver's final one, which is the reference state's.\<close>

lemma bilr_lin_acc_le:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and P_len: "0 < length P"
    and ndinv: "\<forall>nd \<in> set (bilr_alpha_todo st). gmp_node_inv P l0 r0 k0 nd"
    and main: "carried_gmp_main (bilr_alpha st) = carried_gmp_main st0"
  shows "length (bilr_alpha_acc st) \<le> length (snd (carried_gmp_main st0))"
proof -
  have "\<forall>nd \<in> set (fst (bilr_alpha st)). gmp_node_inv P l0 r0 k0 nd"
    using ndinv by (simp add: bilr_alpha_def)
  then obtain ys where "snd (carried_gmp_main (bilr_alpha st)) = snd (bilr_alpha st) @ ys"
    using carried_gmp_main_acc_prefix[OF \<delta>_pos small_fast P_len] by blast
  then show ?thesis using main by (simp add: bilr_alpha_def)
qed

lemma bilr_imp_step_pre_lin:
  fixes \<delta> :: real
  assumes si: "bisection_loop_state_invar st"
    and cond: "bisection_loop_cond st"
    and tcap: "length (bilr_alpha_todo st) + 2 < max_snat LENGTH(gmp_poly_len)"
    and accb: "length (bilr_alpha_acc st) + 1 < max_snat LENGTH(gmp_poly_len)"
    and depth: "\<forall>nd \<in> set (bilr_alpha_todo st).
        snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1
          < max_snat LENGTH(gmp_poly_len)"
    and plen: "\<forall>nd \<in> set (bilr_alpha_todo st). length (snd nd) = length P"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_loop_step_pre st"
proof -
  obtain todo qtodo acc where st0: "st = ((todo, qtodo), acc)" by (cases st) auto
  obtain lns rns ks where todo: "todo = (lns, rns, ks)" by (cases todo) auto
  obtain alns arns aks where acc: "acc = (alns, arns, aks)" by (cases acc) auto
  note dstr = st0 todo acc
  from si have ivT: "dyadic_interval_vec_invar (lns, rns, ks)"
    and ivA: "dyadic_interval_vec_invar (alns, arns, aks)"
    and ltq: "length qtodo = length lns"
    by (auto simp: dstr bisection_loop_state_invar_def)
  from ivT have llr: "length lns = length rns" and llk: "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  from cond have ne: "lns \<noteq> []" by (simp add: dstr bisection_loop_cond_def)
  have lenAt: "length (bilr_alpha_todo st) = length lns"
    using bilr_alpha_todo_length[OF si] by (simp add: dstr)
  have Atne: "bilr_alpha_todo st \<noteq> []" using bilr_alpha_cond[OF si] cond by simp
  have lastA: "last (bilr_alpha_todo st) = (((last lns, last rns), last ks), last qtodo)"
    using bilr_alpha_todo_last[OF si[unfolded dstr] ne] by (simp add: dstr)
  have lastA_in: "last (bilr_alpha_todo st) \<in> set (bilr_alpha_todo st)" using Atne by simp
  have iv_bl: "dyadic_interval_vec_invar (butlast lns, butlast rns, butlast ks)"
    using ivT by (auto simp: dyadic_interval_vec_invar_def llr llk)
  have push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
  proof (rule dyadic_interval_vec_pushable2_from_budget[where B = 0, OF iv_bl _ order_refl])
    show "int (length (butlast lns)) + 0 + 2 < int (max_snat LENGTH(gmp_poly_len))"
      using tcap lenAt by (simp add: length_butlast)
  qed
  have lenAa: "length (bilr_alpha_acc st) = length alns"
    using ivA by (simp add: dstr bilr_alpha_acc_def dyadic_interval_vec_triples_length)
  have pushA: "dyadic_interval_vec_pushable (alns, arns, aks)"
  proof (rule dyadic_interval_vec_pushable_from_budget[where B = 0, OF ivA _ order_refl])
    show "int (length alns) + 0 + 1 < int (max_snat LENGTH(gmp_poly_len))"
      using accb lenAa by simp
  qed
  have qne: "qtodo \<noteq> []" using ne ltq by (cases qtodo) auto
  have blq: "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "length (butlast qtodo) + 1 = length lns"
      using qne ltq ne by (cases lns) (auto simp: length_butlast)
    thus ?thesis using tcap lenAt by linarith
  qed
  have qmap: "map snd (bilr_alpha_todo st) = qtodo"
    using ltq llr llk
    by (simp add: dstr bilr_alpha_todo_def dyadic_interval_vec_triples_simps map_snd_zip)
  have listall: "list_all (\<lambda>Q. 0 < length Q
        \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)) qtodo"
    unfolding list_all_iff
  proof (intro ballI)
    fix Q assume "Q \<in> set qtodo"
    then have "Q \<in> set (map snd (bilr_alpha_todo st))" using qmap by simp
    then obtain nd where "nd \<in> set (bilr_alpha_todo st)" and "Q = snd nd" by auto
    then have "length Q = length P" using plen by auto
    thus "0 < length Q \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)"
      using P_len P_bound by simp
  qed
  have lastk: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "snd (fst (last (bilr_alpha_todo st)))
        + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst (last (bilr_alpha_todo st)))) + 1
        < max_snat LENGTH(gmp_poly_len)"
      using depth lastA_in by blast
    then have "last ks
        + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + 1
        < max_snat LENGTH(gmp_poly_len)" by (simp add: lastA)
    thus ?thesis by simp
  qed
  show ?thesis
    unfolding bisection_loop_step_pre_def
    using si cond push2 pushA blq listall lastk
    by (simp add: dstr)
qed

text \<open>The two capacities, from the invariant and the two global premises.\<close>

lemma bilr_lin_caps:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and P_len: "0 < length P"
    and capl: "rational_interval_mu \<delta> (0, 1) + 3 < max_snat LENGTH(gmp_poly_len)"
    and accN: "length (snd (carried_gmp_main st0)) + 1 < max_snat LENGTH(gmp_poly_len)"
    and inv: "bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 st"
  shows "length (bilr_alpha_todo st) + 2 < max_snat LENGTH(gmp_poly_len)"
    and "length (bilr_alpha_acc st) + 1 < max_snat LENGTH(gmp_poly_len)"
proof -
  from inv have ndinv: "\<forall>nd \<in> set (bilr_alpha_todo st). gmp_node_inv P l0 r0 k0 nd"
    and main: "carried_gmp_main (bilr_alpha st) = carried_gmp_main st0"
    and stk: "stack_ok (rational_interval_mu \<delta> (0, 1))
                (map (rational_interval_mu \<delta>) (todo_ivs l0 r0 k0 (bilr_alpha_todo st)))"
    unfolding bilr_refine_invar_lin_def by blast+
  show "length (bilr_alpha_todo st) + 2 < max_snat LENGTH(gmp_poly_len)"
    using stack_ok_todo_len[OF stk] capl by linarith
  show "length (bilr_alpha_acc st) + 1 < max_snat LENGTH(gmp_poly_len)"
    using bilr_lin_acc_le[OF \<delta>_pos small_fast P_len ndinv main] accN by linarith
qed


section \<open>The step rule, re-assembled\<close>

text \<open>@{thm [source] bilr_step_result_invar} with the two budget conjuncts replaced: the stack is
  preserved by @{thm [source] carried_step_preserves_stack}, and the next state's \<open>step_pre\<close> reads
  its capacities off the new invariant through @{thm [source] bilr_lin_caps}.\<close>

lemma bilr_step_result_invar_lin:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and capl: "rational_interval_mu \<delta> (0, 1) + 3 < max_snat LENGTH(gmp_poly_len)"
    and accN: "length (snd (carried_gmp_main st0)) + 1 < max_snat LENGTH(gmp_poly_len)"
    and inv: "bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 (((lns, rns, ks), qtodo), (alns, arns, aks))"
    and ne: "lns \<noteq> []"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and vt': "dyadic_interval_vec_invar todo'"
    and tt': "dyadic_interval_vec_triples todo' =
        (if 2 \<le> carried_descartes_count (last qtodo)
         then dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) @
                [((last lns + last lns, last lns + last rns), last ks + 1),
                 ((last lns + last rns, last rns + last rns), last ks + 1)]
         else dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))"
    and qt': "qtodo' = (if 2 \<le> carried_descartes_count (last qtodo)
                then butlast qtodo @
                       [carried_left (last qtodo), carried_right (last qtodo)]
                else butlast qtodo)"
    and at': "acc' = (if carried_descartes_count (last qtodo) = 0 then (alns, arns, aks)
              else if carried_descartes_count (last qtodo) = 1
                   then (alns @ [last lns], arns @ [last rns], aks @ [last ks])
              else if bisection_mid_is_root (last qtodo)
                   then (alns @ [last lns + last rns], arns @ [last lns + last rns], aks @ [last ks + 1])
                   else (alns, arns, aks))"
  shows "bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 ((todo', qtodo'), acc')
       \<and> bilr_alpha ((todo', qtodo'), acc')
           = bisection_gmp_step (bilr_alpha (((lns, rns, ks), qtodo), (alns, arns, aks)))
       \<and> rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo ((todo', qtodo'), acc')))
         < rational_todo_mu_mset \<delta>
             (todo_ivs l0 r0 k0 (bilr_alpha_todo (((lns, rns, ks), qtodo), (alns, arns, aks))))"
proof -
  let ?st = "(((lns, rns, ks), qtodo), (alns, arns, aks))"
  let ?st' = "((todo', qtodo'), acc')"
  from inv have safe: "bisection_loop_safe_invar ?st"
    and ndinv: "\<forall>nd \<in> set (bilr_alpha_todo ?st). gmp_node_inv P l0 r0 k0 nd"
    and main_eq: "carried_gmp_main (bilr_alpha ?st) = carried_gmp_main st0"
    and stk: "stack_ok (rational_interval_mu \<delta> (0, 1))
                (map (rational_interval_mu \<delta>) (todo_ivs l0 r0 k0 (bilr_alpha_todo ?st)))"
    and depth: "\<forall>nd \<in> set (bilr_alpha_todo ?st).
        snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1
          < max_snat LENGTH(gmp_poly_len)"
    and plen: "\<forall>nd \<in> set (bilr_alpha_todo ?st). length (snd nd) = length P"
    unfolding bilr_refine_invar_lin_def by blast+
  from safe have si: "bisection_loop_state_invar ?st"
    by (simp add: bisection_loop_safe_invar_def)
  have cond: "bisection_loop_cond ?st"
    by (simp add: bisection_loop_cond_def ne)
  have At_ne: "bilr_alpha_todo ?st \<noteq> []" using bilr_alpha_cond[OF si] cond by simp
  have fcl: "fst (bilr_alpha ?st) = bilr_alpha_todo ?st" by (simp add: bilr_alpha_def)
  have scl: "snd (bilr_alpha ?st) = bilr_alpha_acc ?st" by (simp add: bilr_alpha_def)
  have alpha: "bilr_alpha ?st' = bisection_gmp_step (bilr_alpha ?st)"
    by (rule bilr_step_alpha_eq[OF si ne tt' qt' at'])
  have at_eq: "bilr_alpha_todo ?st' = fst (bisection_gmp_step (bilr_alpha ?st))"
    using arg_cong[OF alpha, of fst] by (simp add: bilr_alpha_def)
  have ndinv_a: "\<forall>e \<in> set (fst (bilr_alpha ?st)). gmp_node_inv P l0 r0 k0 e"
    using ndinv by (simp add: fcl)
  have ndinv': "\<forall>nd \<in> set (bilr_alpha_todo ?st'). gmp_node_inv P l0 r0 k0 nd"
    using gmp_node_inv_preserved[OF P_len ndinv_a] by (simp add: at_eq)
  have main': "carried_gmp_main (bilr_alpha ?st') = carried_gmp_main st0"
  proof -
    obtain x xs where ct: "bilr_alpha_todo ?st = x # xs"
      using At_ne by (cases "bilr_alpha_todo ?st") auto
    have "bilr_alpha ?st = (x # xs, bilr_alpha_acc ?st)" using ct by (simp add: bilr_alpha_def)
    hence "carried_gmp_main (bilr_alpha ?st) = carried_gmp_main (bisection_gmp_step (bilr_alpha ?st))"
      by (simp add: carried_gmp_main.simps)
    thus ?thesis using alpha main_eq by simp
  qed
  have stk': "stack_ok (rational_interval_mu \<delta> (0, 1))
                (map (rational_interval_mu \<delta>) (todo_ivs l0 r0 k0 (bilr_alpha_todo ?st')))"
    using carried_step_preserves_stack[OF \<delta>_pos small_fast ndinv_a] stk
    by (simp add: at_eq fcl)
  have depth': "\<forall>nd \<in> set (bilr_alpha_todo ?st').
      snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1
        < max_snat LENGTH(gmp_poly_len)"
    using carried_step_preserves_depth[OF \<delta>_pos small_fast ndinv_a, where B = "max_snat LENGTH(gmp_poly_len)"]
          depth by (simp add: at_eq fcl)
  have plen': "\<forall>nd \<in> set (bilr_alpha_todo ?st'). length (snd nd) = length P"
    using carried_step_preserves_polylen[where st = "bilr_alpha ?st" and n = "length P"] plen
    by (simp add: at_eq fcl)
  from si have ivA: "dyadic_interval_vec_invar (alns, arns, aks)"
    and ivT: "dyadic_interval_vec_invar (lns, rns, ks)"
    and ltq: "length qtodo = length lns"
    by (auto simp: bisection_loop_state_invar_def)
  from ivT have llr: "length lns = length rns" and llk: "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  have ivA': "dyadic_interval_vec_invar acc'"
    using at' ivA by (auto simp: dyadic_interval_vec_invar_def split: if_splits)
  have lqt': "length qtodo' = length (dyadic_interval_vec_triples todo')"
  proof -
    have blq_len: "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
        = length (butlast qtodo)"
      using llr llk ltq by (simp add: dyadic_interval_vec_triples_simps length_zip)
    show ?thesis using tt' qt' blq_len by (simp split: if_splits)
  qed
  obtain tlns trns tks where todo'_eq: "todo' = (tlns, trns, tks)" by (cases todo')
  have siv': "bisection_loop_state_invar ?st'"
    using vt' ivA' lqt'
    by (simp add: bisection_loop_state_invar_def todo'_eq
        dyadic_interval_vec_triples_length[OF vt'[unfolded todo'_eq]])
  \<comment> \<open>\<^bold>\<open>The next state's capacities\<close>, from the invariant it is about to satisfy. The \<open>safe\<close>
     conjunct is the only one that needs them, so the invariant is assembled WITHOUT it first.\<close>
  have tcap': "length (bilr_alpha_todo ?st') + 2 < max_snat LENGTH(gmp_poly_len)"
    using stack_ok_todo_len[OF stk'] capl by linarith
  have accb': "length (bilr_alpha_acc ?st') + 1 < max_snat LENGTH(gmp_poly_len)"
    using bilr_lin_acc_le[OF \<delta>_pos small_fast P_len ndinv' main'] accN by linarith
  have steppre': "bisection_loop_cond ?st' \<Longrightarrow> bisection_loop_step_pre ?st'"
    by (rule bilr_imp_step_pre_lin[OF siv' _ tcap' accb' depth' plen' P_len P_bound])
  have safe': "bisection_loop_safe_invar ?st'"
    using siv' steppre' by (simp add: bisection_loop_safe_invar_def)
  have invar': "bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 ?st'"
    unfolding bilr_refine_invar_lin_def
    using safe' ndinv' main' stk' depth' plen' by blast
  have meas: "rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo ?st'))
       < rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo ?st))"
    using bisection_gmp_step_mu_decreases[OF \<delta>_pos small_fast _ ndinv_a] At_ne
    by (simp add: at_eq fcl)
  show ?thesis using invar' alpha meas by blast
qed

lemma bilr_step_refine_lin:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and capl: "rational_interval_mu \<delta> (0, 1) + 3 < max_snat LENGTH(gmp_poly_len)"
    and accN: "length (snd (carried_gmp_main st0)) + 1 < max_snat LENGTH(gmp_poly_len)"
    and inv: "bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 st"
    and cond: "bisection_loop_cond st"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_loop_step_monadic st \<le> SPEC (\<lambda>st'.
      bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 st' \<and>
      bilr_alpha st' = bisection_gmp_step (bilr_alpha st) \<and>
      rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st'))
        < rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st)))"
proof -
  obtain todo qd acc where st1: "st = ((todo, qd), acc)" by (cases st) auto
  obtain lns rns ks where todoeq: "todo = (lns, rns, ks)" by (cases todo) auto
  obtain alns arns aks where acceq: "acc = (alns, arns, aks)" by (cases acc) auto
  have st: "st = (((lns, rns, ks), qd), (alns, arns, aks))" by (simp add: st1 todoeq acceq)
  from inv have safe: "bisection_loop_safe_invar st"
    and depth: "\<forall>nd \<in> set (bilr_alpha_todo st).
        snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1
          < max_snat LENGTH(gmp_poly_len)"
    and plen: "\<forall>nd \<in> set (bilr_alpha_todo st). length (snd nd) = length P"
    unfolding bilr_refine_invar_lin_def by blast+
  from safe have si: "bisection_loop_state_invar st"
    by (simp add: bisection_loop_safe_invar_def)
  have caps: "length (bilr_alpha_todo st) + 2 < max_snat LENGTH(gmp_poly_len)"
             "length (bilr_alpha_acc st) + 1 < max_snat LENGTH(gmp_poly_len)"
    using bilr_lin_caps[OF \<delta>_pos small_fast P_len capl accN inv] by auto
  have steppre: "bisection_loop_step_pre st"
    by (rule bilr_imp_step_pre_lin[OF si cond caps(1) caps(2) depth plen P_len P_bound])
  have ivT: "dyadic_interval_vec_invar (lns, rns, ks)" and lq: "length qd = length lns"
    using si by (auto simp: st bisection_loop_state_invar_def)
  have ne: "lns \<noteq> []" using cond by (simp add: st bisection_loop_cond_def)
  have qne: "qd \<noteq> []" using ne lq by (cases qd) auto
  have lqin: "last qd \<in> set qd" using qne by simp
  from steppre have push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    and pushA: "dyadic_interval_vec_pushable (alns, arns, aks)"
    and blq: "length (butlast qd) + 2 < max_snat LENGTH(gmp_poly_len)"
    and listall: "list_all (\<lambda>Q. 0 < length Q \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)) qd"
    and lastk: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
    by (simp_all add: st bisection_loop_step_pre_def)
  have lqp: "0 < length (last qd) \<and> length (last qd) + 1 < max_snat LENGTH(gmp_poly_len)"
    using listall[unfolded list_all_iff, rule_format, OF lqin] .
  have argspec: "bisection_loop_step_monadic st \<le> SPEC (\<lambda>((todo', qtodo'), acc').
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        (if 2 \<le> carried_descartes_count (last qd)
         then dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) @
                [((last lns + last lns, last lns + last rns), last ks + 1),
                 ((last lns + last rns, last rns + last rns), last ks + 1)]
         else dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)) \<and>
      qtodo' = (if 2 \<le> carried_descartes_count (last qd)
                then butlast qd @
                       [carried_left (last qd), carried_right (last qd)]
                else butlast qd) \<and>
      acc' = (if carried_descartes_count (last qd) = 0 then (alns, arns, aks)
              else if carried_descartes_count (last qd) = 1
                   then (alns @ [last lns], arns @ [last rns], aks @ [last ks])
              else if bisection_mid_is_root (last qd)
                   then (alns @ [last lns + last rns], arns @ [last lns + last rns], aks @ [last ks + 1])
                   else (alns, arns, aks)))"
    unfolding st bisection_loop_step_monadic_def PR_CONST_def prod.case
    by (rule bilr_step_args_spec[OF ivT ne lq lqp[THEN conjunct1] lqp[THEN conjunct2]
          lastk push2 blq pushA])
  show ?thesis
    unfolding st
  proof (rule SPEC_cons_rule[OF argspec[unfolded st]], goal_cases)
    case (1 r)
    obtain todo' qtodo' acc' where r: "r = ((todo', qtodo'), acc')" by (cases r) auto
    from "1" have
      vt': "dyadic_interval_vec_invar todo'" and
      tt': "dyadic_interval_vec_triples todo' =
        (if 2 \<le> carried_descartes_count (last qd)
         then dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) @
                [((last lns + last lns, last lns + last rns), last ks + 1),
                 ((last lns + last rns, last rns + last rns), last ks + 1)]
         else dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))" and
      qt': "qtodo' = (if 2 \<le> carried_descartes_count (last qd)
                then butlast qd @ [carried_left (last qd), carried_right (last qd)]
                else butlast qd)" and
      at': "acc' = (if carried_descartes_count (last qd) = 0 then (alns, arns, aks)
              else if carried_descartes_count (last qd) = 1
                   then (alns @ [last lns], arns @ [last rns], aks @ [last ks])
              else if bisection_mid_is_root (last qd)
                   then (alns @ [last lns + last rns], arns @ [last lns + last rns], aks @ [last ks + 1])
                   else (alns, arns, aks))"
      by (simp_all add: r)
    show ?case
      unfolding r
      by (rule bilr_step_result_invar_lin[OF \<delta>_pos small_fast capl accN inv[unfolded st] ne
            P_len P_bound vt' tt' qt' at'])
  qed
qed

section \<open>The loop, the seed, and the capstone\<close>

lemma bilr_loop_stateful_dref_lin:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and capl: "rational_interval_mu \<delta> (0, 1) + 3 < max_snat LENGTH(gmp_poly_len)"
    and accN: "length (snd (carried_gmp_main st0)) + 1 < max_snat LENGTH(gmp_poly_len)"
    and init: "bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 s0"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_loop_stateful_monadic s0
       \<le> \<Down>(br bilr_alpha (bilr_refine_invar_lin \<delta> P l0 r0 k0 st0)) (bilr_loop_abs (bilr_alpha s0))"
  unfolding loop_stateful_unfold bilr_loop_abs_def WHILET_def
  apply (rule WHILEIT_refine[where R="br bilr_alpha (bilr_refine_invar_lin \<delta> P l0 r0 k0 st0)"])
  subgoal using init by (simp add: in_br_conv)
  subgoal by (auto simp: in_br_conv bilr_refine_invar_lin_def)
  subgoal for s s'
  proof -
    assume R: "(s, s') \<in> br bilr_alpha (bilr_refine_invar_lin \<delta> P l0 r0 k0 st0)"
    from R have sa: "s' = bilr_alpha s" and inv_s: "bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 s"
      by (auto simp: in_br_conv)
    from inv_s have si: "bisection_loop_state_invar s"
      by (simp add: bilr_refine_invar_lin_def bisection_loop_safe_invar_def)
    show "bisection_loop_cond s = (fst s' \<noteq> [])"
      using bilr_alpha_cond[OF si] by (simp add: sa bilr_alpha_def)
  qed
  subgoal for s s'
  proof -
    assume R: "(s, s') \<in> br bilr_alpha (bilr_refine_invar_lin \<delta> P l0 r0 k0 st0)"
      and bs: "bisection_loop_cond s"
    from R have sa: "s' = bilr_alpha s" and inv_s: "bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 s"
      by (auto simp: in_br_conv)
    have bc: "bisection_loop_body_checked_monadic s = bisection_loop_step_monadic s"
      using bs by (simp add: bisection_loop_body_checked_monadic_def PR_CONST_def)
    have "bisection_loop_step_monadic s \<le> SPEC (\<lambda>c.
        bisection_gmp_step (bilr_alpha s) = bilr_alpha c \<and> bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 c)"
      using bilr_step_refine_lin[OF \<delta>_pos small_fast capl accN inv_s bs P_len P_bound]
      by (auto simp: pw_le_iff refine_pw_simps)
    thus "bisection_loop_body_checked_monadic s
        \<le> \<Down>(br bilr_alpha (bilr_refine_invar_lin \<delta> P l0 r0 k0 st0)) (RETURN (bisection_gmp_step s'))"
      unfolding bc sa by (simp add: conc_fun_RETURN in_br_conv)
  qed
  done

lemma bilr_loop_stateful_spec_lin:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and capl: "rational_interval_mu \<delta> (0, 1) + 3 < max_snat LENGTH(gmp_poly_len)"
    and accN: "length (snd (carried_gmp_main st0)) + 1 < max_snat LENGTH(gmp_poly_len)"
    and init: "bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 s0"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_loop_stateful_monadic s0 \<le> SPEC (\<lambda>c.
      bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 c \<and> bilr_alpha_todo c = []
      \<and> bilr_alpha_acc c = snd (carried_gmp_main (bilr_alpha s0)))"
proof -
  have ninv0: "\<forall>nd \<in> set (fst (bilr_alpha s0)). gmp_node_inv P l0 r0 k0 nd"
    using init by (auto simp: bilr_refine_invar_lin_def bilr_alpha_def)
  have "bisection_loop_stateful_monadic s0
      \<le> \<Down>(br bilr_alpha (bilr_refine_invar_lin \<delta> P l0 r0 k0 st0)) (bilr_loop_abs (bilr_alpha s0))"
    by (rule bilr_loop_stateful_dref_lin[OF \<delta>_pos small_fast capl accN init P_len P_bound])
  also have "\<dots> \<le> \<Down>(br bilr_alpha (bilr_refine_invar_lin \<delta> P l0 r0 k0 st0))
      (SPEC (\<lambda>st. fst st = [] \<and> snd st = snd (carried_gmp_main (bilr_alpha s0))))"
    by (rule monoD[OF conc_fun_mono]) (rule bilr_loop_abs_spec[OF \<delta>_pos small_fast P_len ninv0])
  also have "\<dots> \<le> SPEC (\<lambda>c. bilr_refine_invar_lin \<delta> P l0 r0 k0 st0 c \<and> bilr_alpha_todo c = []
      \<and> bilr_alpha_acc c = snd (carried_gmp_main (bilr_alpha s0)))"
    by (auto simp: pw_le_iff refine_pw_simps in_br_conv bilr_alpha_def)
  finally show ?thesis .
qed

lemma bilr_seed_invar_lin:
  fixes \<delta> :: real
  assumes lr: "l_num < r_num"
    and len: "0 < length P"
    and lenb: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and capl: "rational_interval_mu \<delta> (0, 1) + 3 < max_snat LENGTH(gmp_poly_len)"
  shows "bilr_refine_invar_lin \<delta> P l_num r_num k
           (bilr_alpha (((([l_num], [r_num], [k]), [P]), ([], [], [])) :: bisection_loop_state))
           ((([l_num], [r_num], [k]), [P]), ([], [], []))"
proof -
  let ?s0 = "((([l_num], [r_num], [k]), [P]), ([], [], [])) :: bisection_loop_state"
  have at0: "bilr_alpha_todo ?s0 = [(((l_num, r_num), k), P)]"
    by (simp add: bilr_alpha_todo_def dyadic_interval_vec_triples_simps)
  have aa0: "bilr_alpha_acc ?s0 = []"
    by (simp add: bilr_alpha_acc_def dyadic_interval_vec_triples_simps)
  have node01: "node_iv l_num r_num k l_num r_num k = (0, 1)"
  proof -
    have "dyadic_rat l_num k < dyadic_rat r_num k"
      using lr by (simp add: dyadic_rat_def divide_strict_right_mono)
    hence "dyadic_rat r_num k - dyadic_rat l_num k \<noteq> 0" by simp
    thus ?thesis by (simp add: node_iv_def Let_def)
  qed
  have niv0: "node_iv_of l_num r_num k ((l_num, r_num), k) = (0, 1)"
    by (simp add: node_iv_of_def node01)
  have unit01: "unit_dyadic (0 :: rat, 1 :: rat)"
    unfolding unit_dyadic_def by (auto intro!: exI[of _ "0 :: int"] exI[of _ "0 :: nat"])
  have ndinv: "\<forall>nd \<in> set (bilr_alpha_todo ?s0). gmp_node_inv P l_num r_num k nd"
    by (simp add: at0 gmp_node_inv_def niv0 carried_repr_init unit01)
  have tivs0: "todo_ivs l_num r_num k [(((l_num, r_num), k), P)] = [(0, 1)]"
    by (simp add: todo_ivs_def niv0)
  have si: "bisection_loop_state_invar ?s0"
    by (simp add: bisection_loop_state_invar_def dyadic_interval_vec_invar_def)
  have stk: "stack_ok (rational_interval_mu \<delta> (0, 1))
               (map (rational_interval_mu \<delta>) (todo_ivs l_num r_num k (bilr_alpha_todo ?s0)))"
    by (simp add: at0 tivs0 stack_ok_seed)
  have depth: "\<forall>nd \<in> set (bilr_alpha_todo ?s0).
      snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l_num r_num k (fst nd)) + 1
        < max_snat LENGTH(gmp_poly_len)"
    using dcap by (simp add: at0 niv0)
  have plen: "\<forall>nd \<in> set (bilr_alpha_todo ?s0). length (snd nd) = length P"
    by (simp add: at0)
  have cond: "bisection_loop_cond ?s0"
    by (simp add: bisection_loop_cond_def)
  have tcap: "length (bilr_alpha_todo ?s0) + 2 < max_snat LENGTH(gmp_poly_len)"
    using capl by (simp add: at0)
  have accb: "length (bilr_alpha_acc ?s0) + 1 < max_snat LENGTH(gmp_poly_len)"
    using capl by (simp add: aa0)
  have steppre: "bisection_loop_step_pre ?s0"
    by (rule bilr_imp_step_pre_lin[OF si cond tcap accb depth plen len lenb])
  have safe: "bisection_loop_safe_invar ?s0"
    by (simp add: bisection_loop_safe_invar_def si steppre)
  show ?thesis
    unfolding bilr_refine_invar_lin_def
    using safe ndinv stk depth plen by (simp add: bilr_alpha_def)
qed

text \<open>\<^bold>\<open>The capstone\<close>, @{thm [source] bisection_main_list_spec} with its exponential \<open>cap\<close>
  replaced by two linear premises: \<open>\<mu>(0,1) + 3 < 2\<^sup>6\<^sup>3\<close>, and room for the Descartes output
  itself --- which the caller bounds by the number of roots.\<close>

lemma bisection_main_list_spec_lin:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and lenb: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and capl: "rational_interval_mu \<delta> (0, 1) + 3 < max_snat LENGTH(gmp_poly_len)"
    and accD: "length (dsc_int 0 1 (Poly P)) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lr: "l_num < r_num"
    and dom: "dsc_dom (degree (Poly P), of_rat 0, of_rat 1, map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
  shows "bisection_main_list l_num r_num k P \<le> SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      mset (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
        = mset (dsc_int 0 1 (Poly P)))"
proof -
  let ?s0 = "((([l_num], [r_num], [k]), [P]), ([], [], [])) :: bisection_loop_state"
  have aseed: "bilr_alpha ?s0 = ([(((l_num, r_num), k), P)], [])"
    by (simp add: bilr_alpha_def bilr_alpha_todo_def bilr_alpha_acc_def
        dyadic_interval_vec_triples_simps)
  have l8: "mset (acc_ivs l_num r_num k (snd (carried_gmp_main (bilr_alpha ?s0))))
          = mset (dsc_int 0 1 (Poly P))"
    using carried_gmp_main_seed_mset_dsc_int[OF \<delta>_pos len small_fast dom P0 canon lr]
    by (simp add: aseed)
  have accN: "length (snd (carried_gmp_main (bilr_alpha ?s0))) + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "length (acc_ivs l_num r_num k (snd (carried_gmp_main (bilr_alpha ?s0))))
          = length (dsc_int 0 1 (Poly P))"
      using arg_cong[OF l8, of size] by simp
    then show ?thesis using accD by (simp add: acc_ivs_def)
  qed
  have inv0: "bilr_refine_invar_lin \<delta> P l_num r_num k (bilr_alpha ?s0) ?s0"
    by (rule bilr_seed_invar_lin[OF lr len lenb dcap capl])
  have loop: "bisection_loop_stateful_monadic ?s0 \<le> SPEC (\<lambda>c.
      bilr_refine_invar_lin \<delta> P l_num r_num k (bilr_alpha ?s0) c \<and> bilr_alpha_todo c = []
      \<and> bilr_alpha_acc c = snd (carried_gmp_main (bilr_alpha ?s0)))"
    by (rule bilr_loop_stateful_spec_lin[OF \<delta>_pos small_fast capl accN inv0 len lenb])
  have loopC: "bisection_loop_monadic ([l_num], [r_num], [k]) [P] ([], [], []) \<le> SPEC (\<lambda>c.
      bisection_loop_safe_invar c \<and> bilr_alpha_todo c = []
      \<and> mset (acc_ivs l_num r_num k (bilr_alpha_acc c)) = mset (dsc_int 0 1 (Poly P)))"
    unfolding bisection_loop_monadic_def PR_CONST_def
    using l8 by (rule_tac order_trans[OF loop])
                (auto simp: pw_le_iff refine_pw_simps bilr_refine_invar_lin_def)
  have seed_safe: "bisection_loop_safe_invar ?s0"
    using inv0 by (simp add: bilr_refine_invar_lin_def)
  have phi: "\<And>c. inres (bisection_loop_monadic ([l_num], [r_num], [k]) [P] ([], [], [])) c \<Longrightarrow>
      bisection_loop_safe_invar c \<and> bilr_alpha_todo c = []
      \<and> mset (acc_ivs l_num r_num k (bilr_alpha_acc c)) = mset (dsc_int 0 1 (Poly P))"
    using loopC by (auto simp: pw_le_iff refine_pw_simps)
  have free_d: "\<And>v. dyadic_interval_vec_free_monadic v \<le> SPEC (\<lambda>_. True)"
    unfolding dyadic_interval_vec_free_monadic_def PR_CONST_def
    by (refine_vcg) (auto simp: pw_le_iff refine_pw_simps mop_free_def)
  have free_d_nofail: "\<And>v. nofail (dyadic_interval_vec_free_monadic v)"
    using free_d by (auto simp: pw_le_iff refine_pw_simps)
  have loop_nofail: "nofail (bisection_loop_monadic ([l_num], [r_num], [k]) [P] ([], [], []))"
    using loopC by (auto simp: pw_le_iff refine_pw_simps)
  have max1: "Suc 0 < max_snat LENGTH(gmp_poly_len)" using len lenb by linarith
  have seed_steppre: "bisection_loop_step_pre ?s0"
    using seed_safe
    by (simp add: bisection_loop_safe_invar_def bisection_loop_cond_def)
  show ?thesis
    unfolding bisection_main_list_def PR_CONST_def COPY_def
      dyadic_interval_vec_empty_sz_monadic_def poly_empty_sz_monadic_def
      poly_push_coeff_monadic_def poly_vec_empty_sz_monadic_def poly_vec_push_monadic_def
      poly_vec_free_empty_monadic_def
    apply (refine_vcg free_d)
    apply (all \<open>(rule order_trans[OF loopC])?\<close>)
    apply (auto simp: pw_le_iff refine_pw_simps dyadic_interval_vec_pushable_def
        bilr_alpha_acc_def bilr_alpha_todo_def bisection_loop_safe_invar_def
        bisection_loop_state_invar_def dyadic_interval_vec_invar_def
        dyadic_interval_vec_triples_simps zip_eq_Nil_iff length_zip seed_safe free_d_nofail
        loop_nofail max1 seed_steppre
        dest!: phi dest: bilr_exit_qtodo_empty)
    apply (simp add: max_snat_def)
    done
qed


section \<open>The degree \<open>\<le> 8\<close> path's precondition, without the exponential clause\<close>

text \<open>\<open>bisect_cap_lin\<close> is @{const split_cap} with its \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 + 1 < 2\<^sup>6\<^sup>3\<close> clause dropped and the
  depth clause widened by two (the stack has \<open>\<mu> + 1\<close> entries and must fit two more). It is
  verbatim the deflating chain's \<open>split_cap_lin\<close> (\<open>Kiou_Bound_Defl_Reflect\<close>), which this graph
  cannot see; \<open>Isarri_Paths\<close> equates the two.\<close>

definition bisect_cap_lin :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"bisect_cap_lin ys k \<longleftrightarrow>
  k * length ys < max_snat LENGTH(gmp_poly_len) \<and>
  (let Yinit = scale_poly_list (2 ^ k) ys;
       \<delta> = delta_P (map_poly of_int (Poly Yinit) :: real poly) in
     k + rational_interval_mu \<delta> (0, 1) + 3 < max_snat LENGTH(gmp_poly_len))"

definition lowdeg_lin_pre :: "int list \<Rightarrow> bool" where
"lowdeg_lin_pre xs \<longleftrightarrow>
  2 \<le> length xs \<and> last xs \<noteq> 0 \<and> kiou_headroom xs \<and>
  coeffs (Poly xs) = xs \<and>
  square_free (map_poly of_int (Poly xs) :: real poly) \<and>
  kiou_bound_k_monadic xs \<le> SPEC (bisect_cap_lin xs) \<and>
  kiou_bound_k_monadic (refl_list xs) \<le> SPEC (bisect_cap_lin (refl_list xs))"

lemma lowdeg_lin_pre_basic:
  assumes "lowdeg_lin_pre xs"
  shows "lowdeg_basic_pre xs"
  using assms unfolding lowdeg_lin_pre_def lowdeg_basic_pre_def
  by (auto elim!: order_trans intro!: SPEC_rule simp: bisect_cap_lin_def)

lemma kiou_bound_k_monadic_spec_capped_bisect_lin:
  fixes ys :: "int list"
  assumes len2: "2 \<le> length ys" and lastnz: "last ys \<noteq> 0"
    and hr: "kiou_headroom ys"
    and capY: "kiou_bound_k_monadic ys \<le> SPEC (bisect_cap_lin ys)"
  shows "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k.
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k) \<and>
      k * length ys < max_snat LENGTH(gmp_poly_len) \<and> k < max_snat LENGTH(gmp_poly_len) \<and>
      bisect_cap_lin ys k)"
proof -
  have len1: "1 \<le> length ys" using len2 by linarith
  have kcap: "\<And>k. k * length ys < max_snat LENGTH(gmp_poly_len) \<Longrightarrow>
      k < max_snat LENGTH(gmp_poly_len)"
  proof -
    fix k assume h: "k * length ys < max_snat LENGTH(gmp_poly_len)"
    have "k * 1 \<le> k * length ys" by (rule mult_le_mono2[OF len1])
    hence "k \<le> k * length ys" by linarith
    thus "k < max_snat LENGTH(gmp_poly_len)" using h by linarith
  qed
  have both: "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k.
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k) \<and> bisect_cap_lin ys k)"
    by (rule kiou_le_SPEC_conj[OF kiou_bound_k_monadic_sound[OF len2 lastnz hr] capY])
  show ?thesis
    by (rule order_trans[OF both]) (use kcap in \<open>auto simp: bisect_cap_lin_def\<close>)
qed

text \<open>\<^bold>\<open>The seed facts of one half\<close>, at any list \<open>ys\<close> the half runs on: @{thm [source]
  bisection_isolate_all_split_pos_pre} followed by @{thm [source]
  bilr_dsc_squarefree_pre_imp_int_pre}, with the exponential clause replaced by the linear one.\<close>

lemma bisection_seed_facts_lin:
  fixes ys :: "int list" and k :: nat
  assumes len2: "2 \<le> length ys" and lastnz: "last ys \<noteq> 0"
    and sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and hr: "kiou_headroom ys"
    and cap_at: "bisect_cap_lin ys k"
  defines "Pinit \<equiv> scale_poly_list (2 ^ k) ys"
  defines "d \<equiv> delta_P (map_poly of_int (Poly Pinit) :: real poly)"
  shows "d > 0" and "0 < length Pinit"
    and "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> d \<Longrightarrow> descartes_list_int a b Pinit \<le> 1"
    and "length Pinit + 1 < max_snat LENGTH(gmp_poly_len)"
    and "0 + rational_interval_mu d (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and "rational_interval_mu d (0, 1) + 3 < max_snat LENGTH(gmp_poly_len)"
    and "dsc_dom (degree (Poly Pinit), of_rat 0, of_rat 1, map_poly of_int (Poly Pinit) :: real poly)"
    and "Poly Pinit \<noteq> 0" and "coeffs (Poly Pinit) = Pinit"
    and "length Pinit = length ys"
proof -
  have ne: "ys \<noteq> []" using len2 by auto
  have canon: "coeffs (Poly ys) = ys" by (rule coeffs_Poly_eq_self_of_last_nonzero[OF ne lastnz])
  have cpos: "(2::int) ^ k \<noteq> 0" by simp
  show len_eq: "length Pinit = length ys"
    unfolding Pinit_def by (simp add: scale_poly_list_eq_map_upt)
  have sfPinit: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    unfolding Pinit_def
    using square_free_pcompose_linear[OF sf, of "2 ^ k"]
    by (simp add: Poly_scale_poly_list_eq_pcompose)
  show P0init: "Poly Pinit \<noteq> 0" using sfPinit unfolding square_free_def by simp
  show canonPinit: "coeffs (Poly Pinit) = Pinit"
    unfolding Pinit_def
    using coeffs_scale_poly_list[OF canon[symmetric], of "2 ^ k"] cpos
    by (simp add: scale_poly_list_correct[symmetric, of "2 ^ k" "Poly ys"] canon)
  have degne: "degree (Poly Pinit) \<noteq> 0"
  proof -
    have "length (coeffs (Poly Pinit)) = degree (Poly Pinit) + 1"
      using P0init by (rule length_coeffs)
    thus ?thesis using len2 len_eq canonPinit by simp
  qed
  show "d > 0" unfolding d_def using P0init delta_P_pos by simp
  show "0 < length Pinit" using len2 len_eq by linarith
  show "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> d \<Longrightarrow> descartes_list_int a b Pinit \<le> 1"
    unfolding d_def
    by (rule rational_fast_descartes_list_int_delta_P_le1[OF P0init canonPinit degne sfPinit])
  have lenb: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  show "length Pinit + 1 < max_snat LENGTH(gmp_poly_len)" using lenb len_eq by simp
  have c: "k + rational_interval_mu d (0, 1) + 3 < max_snat LENGTH(gmp_poly_len)"
    using cap_at unfolding bisect_cap_lin_def Pinit_def d_def by (simp add: Let_def)
  show "0 + rational_interval_mu d (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)" using c by simp
  show "rational_interval_mu d (0, 1) + 3 < max_snat LENGTH(gmp_poly_len)" using c by simp
  have P_real0: "(map_poly of_int (Poly Pinit) :: real poly) \<noteq> 0" using P0init by simp
  have deg_le: "degree (map_poly of_int (Poly Pinit) :: real poly) \<le> degree (Poly Pinit)" by simp
  have I_less: "(of_rat 0 :: real) < of_rat 1" by simp
  show "dsc_dom (degree (Poly Pinit), of_rat 0, of_rat 1, map_poly of_int (Poly Pinit) :: real poly)"
    by (rule dsc_terminates_squarefree[OF P_real0 deg_le degne sfPinit I_less])
qed

end
