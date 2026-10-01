theory Rational_Solver
imports "IsaRRI_LLVM.Interval_Eval"
begin

text \<open>Plain Dsc loop with GMP-backed rational endpoints. Layer: SEPREF.

  This is the replacement for the signed-long endpoint worklist in
  @{text Interval_Eval}. Coefficients are still borrowed from the caller, but interval
  endpoints in todo/acc are owned GMP integer blocks stored in four parallel
  vectors. The public entry point copies the borrowed initial endpoints into
  the owned todo vector and returns an owned accumulator vector.

  Main exports: \<open>rational_loop_monadic\<close> / \<open>dsc_rational_main_list\<close>
  and their \<open>_impl\<close> Sepref definitions (the \<open>[llvm_code]\<close>-tagged
  \<open>dsc_rational_main_list_impl\<close> is the exported entry point). Proven refined
  to \<open>dsc_int\<close> in \<open>refine/rational/Rational_Refine.thy\<close>.\<close>

type_synonym rational_loop_state =
  "nat \<times> (gmp_interval_vec \<times> gmp_interval_vec)"

abbreviation rational_loop_state_assn where
"rational_loop_state_assn \<equiv>
  snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
    (gmp_interval_vec_assn \<times>\<^sub>a gmp_interval_vec_assn)"

definition rational_state_todo ::
  "rational_loop_state \<Rightarrow> (rat \<times> rat) list" where
"rational_state_todo st \<equiv>
  (let (i, todo, acc) = st in drop i (interval_vec_to_list todo))"

definition rational_state_acc ::
  "rational_loop_state \<Rightarrow> (rat \<times> rat) list" where
"rational_state_acc st \<equiv>
  (let (i, todo, acc) = st in interval_vec_to_list acc)"

lemma rational_state_todo_simps[simp]:
  "rational_state_todo (i, todo, acc) =
    drop i (interval_vec_to_list todo)"
  unfolding rational_state_todo_def by simp

lemma rational_state_acc_simps[simp]:
  "rational_state_acc (i, todo, acc) =
    interval_vec_to_list acc"
  unfolding rational_state_acc_def by simp

definition rational_queue_step_int ::
  "gmp_poly \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow>
    ((rat \<times> rat) list \<times> (rat \<times> rat) list)" where
"rational_queue_step_int P todo acc \<equiv>
  (case todo of
    [] \<Rightarrow> ([], acc)
  | I # rest \<Rightarrow>
      (let v = descartes_list_int (fst I) (snd I) P in
       if v = 0 then (rest, acc)
       else if v = 1 then (rest, acc @ [I])
       else
         (let m = (fst I + snd I) / 2 in
          (rest @ [(fst I, m), (m, snd I)],
           acc @
             (if poly (map_poly rat_of_int (Poly P)) m = 0
              then [(m, m)] else [])))))"

definition rational_stack_step_int ::
  "gmp_poly \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow>
    ((rat \<times> rat) list \<times> (rat \<times> rat) list)" where
"rational_stack_step_int P todo acc \<equiv>
  (case todo of
    [] \<Rightarrow> ([], acc)
  | I # rest \<Rightarrow>
      (let v = descartes_list_int (fst I) (snd I) P in
       if v = 0 then (rest, acc)
       else if v = 1 then (rest, I # acc)
       else
         (let m = (fst I + snd I) / 2;
              acc' =
                (if poly (map_poly rat_of_int (Poly P)) m = 0
                 then (m, m) # acc else acc)
          in ([(fst I, m), (m, snd I)] @ rest, acc'))))"

lemma rational_queue_stack_step_set:
  "set (fst (rational_queue_step_int P todo acc)) \<union>
    set (snd (rational_queue_step_int P todo acc)) =
   set (fst (rational_stack_step_int P todo acc)) \<union>
    set (snd (rational_stack_step_int P todo acc))"
  by (cases todo)
    (auto simp: rational_queue_step_int_def
      rational_stack_step_int_def Let_def split: prod.splits)

lemma rational_queue_stack_step_mset:
  "mset (fst (rational_queue_step_int P todo acc)) +
    mset (snd (rational_queue_step_int P todo acc)) =
   mset (fst (rational_stack_step_int P todo acc)) +
    mset (snd (rational_stack_step_int P todo acc))"
  by (cases todo)
    (auto simp: rational_queue_step_int_def
      rational_stack_step_int_def Let_def ac_simps split: prod.splits)

definition rational_interval_mu ::
  "real \<Rightarrow> (rat \<times> rat) \<Rightarrow> nat" where
"rational_interval_mu \<delta> I \<equiv>
  mu \<delta> (of_rat (fst I)) (of_rat (snd I))"

definition rational_todo_mu_mset ::
  "real \<Rightarrow> (rat \<times> rat) list \<Rightarrow> nat multiset" where
"rational_todo_mu_mset \<delta> todo \<equiv>
  mset (map (rational_interval_mu \<delta>) todo)"

definition rational_interval_todo_budget ::
  "real \<Rightarrow> (rat \<times> rat) \<Rightarrow> int" where
"rational_interval_todo_budget \<delta> I \<equiv>
  int ((2::nat) ^ Suc (rational_interval_mu \<delta> I)) - 2"

definition rational_todo_append_budget ::
  "real \<Rightarrow> (rat \<times> rat) list \<Rightarrow> int" where
"rational_todo_append_budget \<delta> todo \<equiv>
  sum_list (map (rational_interval_todo_budget \<delta>) todo)"

definition rational_interval_acc_budget ::
  "real \<Rightarrow> (rat \<times> rat) \<Rightarrow> int" where
"rational_interval_acc_budget \<delta> I \<equiv>
  int ((2::nat) ^ Suc (rational_interval_mu \<delta> I)) - 1"

definition rational_todo_acc_budget ::
  "real \<Rightarrow> (rat \<times> rat) list \<Rightarrow> int" where
"rational_todo_acc_budget \<delta> todo \<equiv>
  sum_list (map (rational_interval_acc_budget \<delta>) todo)"

definition rational_queue_step_todo_extra ::
  "gmp_poly \<Rightarrow> (rat \<times> rat) list \<Rightarrow> int" where
"rational_queue_step_todo_extra P todo \<equiv>
  (case todo of
    [] \<Rightarrow> 0
  | I # _ \<Rightarrow>
      (let v = descartes_list_int (fst I) (snd I) P in
       if v = 0 \<or> v = 1 then 0 else 2))"

definition rational_queue_step_acc_extra ::
  "gmp_poly \<Rightarrow> (rat \<times> rat) list \<Rightarrow> int" where
"rational_queue_step_acc_extra P todo \<equiv>
  (case todo of
    [] \<Rightarrow> 0
  | I # _ \<Rightarrow>
      (let v = descartes_list_int (fst I) (snd I) P in
       if v = 0 then 0 else 1))"

lemma rational_interval_todo_budget_nonneg[simp]:
  "0 \<le> rational_interval_todo_budget \<delta> I"
  unfolding rational_interval_todo_budget_def
  by simp

lemma rational_todo_append_budget_nonneg[simp]:
  "0 \<le> rational_todo_append_budget \<delta> todo"
  unfolding rational_todo_append_budget_def
  by (induction todo) auto

lemma rational_interval_acc_budget_pos[simp]:
  "0 < rational_interval_acc_budget \<delta> I"
proof -
  have "(1::nat) < 2 ^ Suc (rational_interval_mu \<delta> I)"
    by (rule one_less_power) simp_all
  then show ?thesis
    unfolding rational_interval_acc_budget_def by linarith
qed

lemma rational_todo_acc_budget_nonneg[simp]:
  "0 \<le> rational_todo_acc_budget \<delta> todo"
  unfolding rational_todo_acc_budget_def
proof (induction todo)
  case Nil
  then show ?case by simp
next
  case (Cons I todo)
  have "0 \<le> rational_interval_acc_budget \<delta> I"
    using rational_interval_acc_budget_pos[of \<delta> I] by linarith
  then show ?case
    using Cons.IH by simp
qed

lemma rational_budget_power_children_le:
  assumes x_lt: "x < z"
    and y_lt: "y < z"
  shows "int ((2::nat) ^ Suc x) + int ((2::nat) ^ Suc y) \<le>
    int ((2::nat) ^ Suc z)"
proof -
  have x_le: "Suc x \<le> z"
    using x_lt by simp
  have y_le: "Suc y \<le> z"
    using y_lt by simp
  have px: "(2::nat) ^ Suc x \<le> 2 ^ z"
    by (rule power_increasing[OF x_le]) simp
  have py: "(2::nat) ^ Suc y \<le> 2 ^ z"
    by (rule power_increasing[OF y_le]) simp
  have "int ((2::nat) ^ Suc x) + int ((2::nat) ^ Suc y) \<le>
    int (2 ^ z) + int (2 ^ z)"
    using px py by linarith
  also have "... = int ((2::nat) ^ Suc z)"
    by simp
  finally show ?thesis .
qed

lemma rational_todo_budget_children_le:
  assumes x_lt: "x < z"
    and y_lt: "y < z"
  shows "2 + (int ((2::nat) ^ Suc x) - 2) +
      (int ((2::nat) ^ Suc y) - 2) \<le>
    int ((2::nat) ^ Suc z) - 2"
  using rational_budget_power_children_le[OF assms]
  by linarith

lemma rational_acc_budget_children_le:
  assumes x_lt: "x < z"
    and y_lt: "y < z"
  shows "1 + (int ((2::nat) ^ Suc x) - 1) +
      (int ((2::nat) ^ Suc y) - 1) \<le>
    int ((2::nat) ^ Suc z) - 1"
  using rational_budget_power_children_le[OF assms]
  by linarith

lemma rational_queue_step_todo_budget_preserved:
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
  shows "rational_queue_step_todo_extra P todo +
      rational_todo_append_budget \<delta>
        (fst (rational_queue_step_int P todo acc)) \<le>
    rational_todo_append_budget \<delta> todo"
proof (cases todo)
  case Nil
  then show ?thesis
    unfolding rational_queue_step_todo_extra_def
      rational_queue_step_int_def
      rational_todo_append_budget_def
    by simp
next
  case (Cons I rest)
  obtain a b where I_eq: "I = (a, b)"
    by (cases I) auto
  have ab: "a < b"
    using ordered[of "(a, b)"] Cons I_eq by simp
  let ?v = "descartes_list_int a b P"
  let ?m = "(a + b) / 2"
  show ?thesis
  proof (cases "?v = 0 \<or> ?v = 1")
    case True
    then show ?thesis
      using Cons I_eq
      unfolding rational_queue_step_todo_extra_def
        rational_queue_step_int_def
        rational_todo_append_budget_def
      by (auto split: prod.splits)
  next
    case False
    have v_gt1: "\<not> ?v \<le> 1"
      using False by auto
    have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
    proof (rule ccontr)
      assume "\<not> \<delta> < of_rat b - of_rat a"
      then have "of_rat b - of_rat a \<le> \<delta>"
        by linarith
      then have "?v \<le> 1"
        using small_fast[OF ab] by simp
      with v_gt1 show False by simp
    qed
    let ?rank = "rational_interval_mu \<delta>"
    have left_lt:
      "?rank (a, ?m) < ?rank (a, b)"
      using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"]
        \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def
      by (simp add: of_rat_add of_rat_divide)
    have right_lt:
      "?rank (?m, b) < ?rank (a, b)"
      using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"]
        \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def
      by (simp add: of_rat_add of_rat_divide)
    have child_le:
      "2 + rational_interval_todo_budget \<delta> (a, ?m) +
          rational_interval_todo_budget \<delta> (?m, b) \<le>
        rational_interval_todo_budget \<delta> (a, b)"
      using rational_todo_budget_children_le[OF left_lt right_lt]
      unfolding rational_interval_todo_budget_def by simp
    show ?thesis
      using False Cons I_eq child_le
      unfolding rational_queue_step_todo_extra_def
        rational_queue_step_int_def
        rational_todo_append_budget_def
      by (simp add: Let_def ac_simps)
  qed
qed

lemma rational_queue_step_acc_budget_preserved:
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
  shows "rational_queue_step_acc_extra P todo +
      rational_todo_acc_budget \<delta>
        (fst (rational_queue_step_int P todo acc)) \<le>
    rational_todo_acc_budget \<delta> todo"
proof (cases todo)
  case Nil
  then show ?thesis
    unfolding rational_queue_step_acc_extra_def
      rational_queue_step_int_def
      rational_todo_acc_budget_def
    by simp
next
  case (Cons I rest)
  obtain a b where I_eq: "I = (a, b)"
    by (cases I) auto
  have ab: "a < b"
    using ordered[of "(a, b)"] Cons I_eq by simp
  let ?v = "descartes_list_int a b P"
  let ?m = "(a + b) / 2"
  show ?thesis
  proof (cases "?v = 0")
    case True
    have head_nonneg: "0 \<le> rational_interval_acc_budget \<delta> (a, b)"
      using rational_interval_acc_budget_pos[of \<delta> "(a, b)"] by linarith
    show ?thesis
      using True Cons I_eq head_nonneg
      unfolding rational_queue_step_acc_extra_def
        rational_queue_step_int_def
        rational_todo_acc_budget_def
      by (auto split: prod.splits)
  next
    case False
    show ?thesis
    proof (cases "?v = 1")
      case True
      have head_ge1: "1 \<le> rational_interval_acc_budget \<delta> (a, b)"
        using rational_interval_acc_budget_pos[of \<delta> "(a, b)"] by linarith
      show ?thesis
        using False True Cons I_eq head_ge1
        unfolding rational_queue_step_acc_extra_def
          rational_queue_step_int_def
          rational_todo_acc_budget_def
        by simp
    next
      case v_not1: False
      have v_gt1: "\<not> ?v \<le> 1"
        using False v_not1 by auto
      have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
      proof (rule ccontr)
        assume "\<not> \<delta> < of_rat b - of_rat a"
        then have "of_rat b - of_rat a \<le> \<delta>"
          by linarith
        then have "?v \<le> 1"
          using small_fast[OF ab] by simp
        with v_gt1 show False by simp
      qed
      let ?rank = "rational_interval_mu \<delta>"
      have left_lt:
        "?rank (a, ?m) < ?rank (a, b)"
        using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"]
          \<delta>_pos ab \<delta>_lt
        unfolding rational_interval_mu_def
        by (simp add: of_rat_add of_rat_divide)
      have right_lt:
        "?rank (?m, b) < ?rank (a, b)"
        using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"]
          \<delta>_pos ab \<delta>_lt
        unfolding rational_interval_mu_def
        by (simp add: of_rat_add of_rat_divide)
      have child_le:
        "1 + rational_interval_acc_budget \<delta> (a, ?m) +
            rational_interval_acc_budget \<delta> (?m, b) \<le>
          rational_interval_acc_budget \<delta> (a, b)"
        using rational_acc_budget_children_le[OF left_lt right_lt]
        unfolding rational_interval_acc_budget_def by simp
      show ?thesis
        using False v_not1 Cons I_eq child_le
        unfolding rational_queue_step_acc_extra_def
          rational_queue_step_int_def
          rational_todo_acc_budget_def
        by (simp add: Let_def ac_simps)
    qed
  qed
qed

lemma rational_queue_step_todo_capacity_preserved:
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and cap: "int n + rational_todo_append_budget \<delta> todo + 2 < M"
    and n'_le: "int n' \<le> int n + rational_queue_step_todo_extra P todo"
  shows "int n' + rational_todo_append_budget \<delta>
      (fst (rational_queue_step_int P todo acc)) + 2 < M"
proof -
  have budget_le:
    "rational_queue_step_todo_extra P todo +
      rational_todo_append_budget \<delta>
        (fst (rational_queue_step_int P todo acc)) \<le>
    rational_todo_append_budget \<delta> todo"
    by (rule rational_queue_step_todo_budget_preserved[
      OF \<delta>_pos ordered small_fast])
  show ?thesis
    using cap n'_le budget_le by linarith
qed

lemma rational_queue_step_acc_capacity_preserved:
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and cap: "int n + rational_todo_acc_budget \<delta> todo + 1 < M"
    and n'_le: "int n' \<le> int n + rational_queue_step_acc_extra P todo"
  shows "int n' + rational_todo_acc_budget \<delta>
      (fst (rational_queue_step_int P todo acc)) + 1 < M"
proof -
  have budget_le:
    "rational_queue_step_acc_extra P todo +
      rational_todo_acc_budget \<delta>
        (fst (rational_queue_step_int P todo acc)) \<le>
    rational_todo_acc_budget \<delta> todo"
    by (rule rational_queue_step_acc_budget_preserved[
      OF \<delta>_pos ordered small_fast])
  show ?thesis
    using cap n'_le budget_le by linarith
qed

lemma rational_queue_step_todo_capacity_preserved_eq:
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and cap: "int n + rational_todo_append_budget \<delta> todo + 2 < M"
    and n'_le: "int n' \<le> int n + rational_queue_step_todo_extra P todo"
    and todo'_eq: "todo' = fst (rational_queue_step_int P todo acc)"
  shows "int n' + rational_todo_append_budget \<delta> todo' + 2 < M"
  using rational_queue_step_todo_capacity_preserved[
    OF \<delta>_pos ordered small_fast cap n'_le] todo'_eq
  by simp

lemma rational_queue_step_acc_capacity_preserved_eq:
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and cap: "int n + rational_todo_acc_budget \<delta> todo + 1 < M"
    and n'_le: "int n' \<le> int n + rational_queue_step_acc_extra P todo"
    and todo'_eq: "todo' = fst (rational_queue_step_int P todo acc)"
  shows "int n' + rational_todo_acc_budget \<delta> todo' + 1 < M"
  using rational_queue_step_acc_capacity_preserved[
    OF \<delta>_pos ordered small_fast cap n'_le] todo'_eq
  by simp

lemma rational_queue_step_todo_capacity_preserved_pair_eq:
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and cap: "int n + rational_todo_append_budget \<delta> todo + 2 < M"
    and n'_le: "int n' \<le> int n + rational_queue_step_todo_extra P todo"
    and step_eq: "(todo', acc') = rational_queue_step_int P todo acc"
  shows "int n' + rational_todo_append_budget \<delta> todo' + 2 < M"
proof -
  have todo'_eq: "todo' = fst (rational_queue_step_int P todo acc)"
    using step_eq by (metis fst_conv)
  show ?thesis
    by (rule rational_queue_step_todo_capacity_preserved_eq[
      OF \<delta>_pos ordered small_fast cap n'_le todo'_eq])
qed

lemma rational_queue_step_acc_capacity_preserved_pair_eq:
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and cap: "int n + rational_todo_acc_budget \<delta> todo + 1 < M"
    and n'_le: "int n' \<le> int n + rational_queue_step_acc_extra P todo"
    and step_eq: "(todo', acc') = rational_queue_step_int P todo acc"
  shows "int n' + rational_todo_acc_budget \<delta> todo' + 1 < M"
proof -
  have todo'_eq: "todo' = fst (rational_queue_step_int P todo acc)"
    using step_eq by (metis fst_conv)
  show ?thesis
    by (rule rational_queue_step_acc_capacity_preserved_eq[
      OF \<delta>_pos ordered small_fast cap n'_le todo'_eq])
qed

lemma rational_todo_mu_mset_tl_less:
  "rational_todo_mu_mset \<delta> todo =
    add_mset x (rational_todo_mu_mset \<delta> rest) \<Longrightarrow>
   rational_todo_mu_mset \<delta> rest <
    rational_todo_mu_mset \<delta> todo"
  unfolding less_multiset_def
  by (simp add: subset_implies_multp)

lemma rational_todo_mu_mset_two_smaller:
  assumes x_lt: "x < z"
    and y_lt: "y < z"
  shows "mset rest + {#x, y#} < add_mset z (mset rest)"
proof -
  have "multp (<) (mset rest + {#x, y#}) (mset rest + {#z#})"
    apply (rule one_step_implies_multp[
      where I="mset rest" and J="{#z#}" and K="{#x, y#}"])
     apply simp
    using assms by auto
  then show ?thesis
    by (simp add: less_multiset_def)
qed

lemma rational_queue_step_mu_mset_decreases:
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and todo_ne: "todo \<noteq> []"
  shows "rational_todo_mu_mset \<delta>
      (fst (rational_queue_step_int P todo acc)) <
    rational_todo_mu_mset \<delta> todo"
  using todo_ne
proof (cases todo)
  case Nil
  then show ?thesis using todo_ne by simp
next
  case (Cons I rest)
  obtain a b where I_eq: "I = (a, b)"
    by (cases I) auto
  have ab: "a < b"
  proof -
    have in_todo: "(a, b) \<in> set todo"
      using Cons I_eq by simp
    then show ?thesis
      using ordered[OF in_todo] by simp
  qed
  let ?v = "descartes_list_int a b P"
  let ?m = "(a + b) / 2"
  let ?rank = "rational_interval_mu \<delta>"
  show ?thesis
  proof (cases "?v = 0 \<or> ?v = 1")
    case True
    then show ?thesis
      using Cons I_eq
      unfolding rational_queue_step_int_def
        rational_todo_mu_mset_def
      by (auto simp: rational_todo_mu_mset_tl_less
        less_multiset_def subset_implies_multp)
  next
    case False
    have v_gt1: "\<not> ?v \<le> 1"
      using False by auto
    have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
    proof (rule ccontr)
      assume "\<not> \<delta> < of_rat b - of_rat a"
      then have "of_rat b - of_rat a \<le> \<delta>"
        by linarith
      then have "?v \<le> 1"
        using small_fast[OF ab] by simp
      with v_gt1 show False by simp
    qed
    have left_lt:
      "?rank (a, ?m) < ?rank (a, b)"
      using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"]
        \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def
      by (simp add: of_rat_add of_rat_divide)
    have right_lt:
      "?rank (?m, b) < ?rank (a, b)"
      using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"]
        \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def
      by (simp add: of_rat_add of_rat_divide)
    have split_dec:
      "mset (map ?rank rest) + {#?rank (a, ?m), ?rank (?m, b)#} <
        add_mset (?rank (a, b)) (mset (map ?rank rest))"
      by (rule rational_todo_mu_mset_two_smaller[OF left_lt right_lt])
    show ?thesis
      using False Cons I_eq split_dec
      unfolding rational_queue_step_int_def
        rational_todo_mu_mset_def
      by (simp add: Let_def ac_simps)
  qed
qed

partial_function (tailrec) rational_queue_main_int ::
  "gmp_poly \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow>
    (rat \<times> rat) list" where
  [code]:
  "rational_queue_main_int P todo acc =
    (case todo of
      [] \<Rightarrow> acc
    | _ \<Rightarrow>
        (let (todo', acc') = rational_queue_step_int P todo acc in
         rational_queue_main_int P todo' acc'))"

lemma rational_queue_main_int_Nil[simp]:
  "rational_queue_main_int P [] acc = acc"
  by (subst rational_queue_main_int.simps)
    (simp add: rational_queue_step_int_def)

lemma rational_queue_main_int_Cons:
  "rational_queue_main_int P (I # todo) acc =
    (let (todo', acc') =
       rational_queue_step_int P (I # todo) acc
     in rational_queue_main_int P todo' acc')"
  by (subst rational_queue_main_int.simps) simp

lemma rational_queue_main_int_step:
  assumes "todo \<noteq> []"
  shows "rational_queue_main_int P todo acc =
    (let (todo', acc') = rational_queue_step_int P todo acc in
     rational_queue_main_int P todo' acc')"
  using assms
  by (cases todo) (simp_all add: rational_queue_main_int_Cons)

lemma rational_queue_main_int_Cons_cases:
  "rational_queue_main_int P ((a, b) # todo) acc =
    (let v = descartes_list_int a b P in
     if v = 0 then rational_queue_main_int P todo acc
     else if v = 1 then rational_queue_main_int P todo (acc @ [(a, b)])
     else
       (let m = (a + b) / 2 in
        rational_queue_main_int P
          (todo @ [(a, m), (m, b)])
          (acc @
            (if poly (map_poly rat_of_int (Poly P)) m = 0
             then [(m, m)] else []))))"
  by (subst rational_queue_main_int_Cons)
    (simp add: rational_queue_step_int_def Let_def)

partial_function (tailrec) rational_stack_main_int ::
  "gmp_poly \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow>
    (rat \<times> rat) list" where
  [code]:
  "rational_stack_main_int P todo acc =
    (case todo of
      [] \<Rightarrow> acc
    | _ \<Rightarrow>
        (let (todo', acc') = rational_stack_step_int P todo acc in
         rational_stack_main_int P todo' acc'))"

lemma rational_stack_main_int_Nil[simp]:
  "rational_stack_main_int P [] acc = acc"
  by (subst rational_stack_main_int.simps)
    (simp add: rational_stack_step_int_def)

lemma rational_stack_main_int_Cons:
  "rational_stack_main_int P (I # todo) acc =
    (let (todo', acc') =
       rational_stack_step_int P (I # todo) acc
     in rational_stack_main_int P todo' acc')"
  by (subst rational_stack_main_int.simps) simp

lemma rational_stack_main_int_step:
  assumes "todo \<noteq> []"
  shows "rational_stack_main_int P todo acc =
    (let (todo', acc') = rational_stack_step_int P todo acc in
     rational_stack_main_int P todo' acc')"
  using assms
  by (cases todo) (simp_all add: rational_stack_main_int_Cons)

lemma rational_stack_main_int_Cons_cases:
  "rational_stack_main_int P ((a, b) # todo) acc =
    (let v = descartes_list_int a b P in
     if v = 0 then rational_stack_main_int P todo acc
     else if v = 1 then rational_stack_main_int P todo ((a, b) # acc)
     else
       (let m = (a + b) / 2 in
        rational_stack_main_int P
          ([(a, m), (m, b)] @ todo)
          (if poly (map_poly rat_of_int (Poly P)) m = 0
           then (m, m) # acc else acc)))"
  by (subst rational_stack_main_int_Cons)
    (simp add: rational_stack_step_int_def Let_def)

lemma rational_stack_step_dsc_main_int:
  assumes canon: "coeffs (Poly P) = P"
  shows "dsc_main_int (Poly P) (I # todo) acc =
    (let (todo', acc') =
       rational_stack_step_int P (I # todo) acc
     in dsc_main_int (Poly P) todo' acc')"
  using assms
  by (cases I)
    (subst dsc_main_int.simps,
      simp add: rational_stack_step_int_def Let_def)

definition rational_interval_pair_ordered ::
  "(int \<times> int) \<times> (int \<times> int) \<Rightarrow> bool" where
"rational_interval_pair_ordered I \<equiv>
  (case I of ((na, da), (nb, db)) \<Rightarrow>
    0 < da \<and> 0 < db \<and> na * db < nb * da)"

definition rational_gmp_interval_vec_ordered ::
  "gmp_interval_vec \<Rightarrow> bool" where
"rational_gmp_interval_vec_ordered v \<equiv>
  (\<forall>I \<in> set (interval_vec_pairs v).
    rational_interval_pair_ordered I)"

lemma gmp_interval_vec_ordered_nthD:
  assumes "rational_gmp_interval_vec_ordered v"
    and "i < length (interval_vec_pairs v)"
  shows "rational_interval_pair_ordered (interval_vec_pairs v ! i)"
  using assms nth_mem
  unfolding rational_gmp_interval_vec_ordered_def by blast

lemma gmp_interval_vec_ordered_componentsD:
  assumes inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and ord: "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and raw: "interval_vec_pairs (lna, lda, rnb, rdb) ! i =
      ((na, da), (nb, db))"
  shows "0 < da" "0 < db" "na * db < nb * da"
proof -
  have len: "i < length (interval_vec_pairs (lna, lda, rnb, rdb))"
    using i_lt interval_vec_pairs_length[OF inv] by simp
  have "rational_interval_pair_ordered
    (interval_vec_pairs (lna, lda, rnb, rdb) ! i)"
    using gmp_interval_vec_ordered_nthD[OF ord len] .
  then show "0 < da" "0 < db" "na * db < nb * da"
    unfolding raw rational_interval_pair_ordered_def by simp_all
qed

lemma interval_pair_ordered_of_pair_less:
  assumes "rational_interval_pair_ordered I"
  shows "fst (interval_of_pair I) <
    snd (interval_of_pair I)"
proof -
  obtain na da nb db where I_eq: "I = ((na, da), (nb, db))"
    by (cases I) auto
  have da_pos: "0 < da" and db_pos: "0 < db"
    and cross: "na * db < nb * da"
    using assms unfolding I_eq rational_interval_pair_ordered_def by simp_all
  have cross_int: "db * na < da * nb"
    using cross by (simp add: mult.commute)
  have cross_rat:
    "rat_of_int db * rat_of_int na < rat_of_int da * rat_of_int nb"
    using cross_int by (simp only: of_int_mult[symmetric] of_int_less_iff)
  show ?thesis
    using da_pos db_pos cross_rat
    unfolding I_eq interval_of_pair_def
      rat_of_pair_def
    by (simp add: field_simps mult.commute)
qed

lemma interval_pair_orderedI:
  assumes da_pos: "0 < da"
    and db_pos: "0 < db"
    and less: "rat_of_pair (na, da) <
      rat_of_pair (nb, db)"
  shows "rational_interval_pair_ordered ((na, da), (nb, db))"
proof -
  have cross_rat:
    "rat_of_int db * rat_of_int na < rat_of_int da * rat_of_int nb"
    using assms
    unfolding rat_of_pair_def
    by (simp add: field_simps)
  have cross_int: "db * na < da * nb"
    using cross_rat by (simp only: of_int_mult[symmetric] of_int_less_iff)
  show ?thesis
    using da_pos db_pos cross_int
    unfolding rational_interval_pair_ordered_def
    by (simp add: mult.commute)
qed

lemma interval_pair_ordered_mid_left:
  assumes ord: "rational_interval_pair_ordered ((na, da), (nb, db))"
    and mid_twice: "rat_of_pair (mn, md) * 2 =
      rat_of_pair (na, da) +
       rat_of_pair (nb, db)"
    and md_pos: "0 < md"
  shows "rational_interval_pair_ordered ((na, da), (mn, md))"
proof -
  have da_pos: "0 < da"
    using ord unfolding rational_interval_pair_ordered_def by simp
  have less_ab:
    "rat_of_pair (na, da) < rat_of_pair (nb, db)"
    using interval_pair_ordered_of_pair_less[OF ord]
    unfolding interval_of_pair_def by simp
  have mid_less:
    "rat_of_pair (na, da) <
      (rat_of_pair (na, da) +
       rat_of_pair (nb, db)) / 2"
  proof -
    have "2 * rat_of_pair (na, da) <
      rat_of_pair (na, da) +
      rat_of_pair (nb, db)"
      using less_ab by linarith
    then show ?thesis by (simp add: field_simps)
  qed
  have mid: "rat_of_pair (mn, md) =
      (rat_of_pair (na, da) +
       rat_of_pair (nb, db)) / 2"
  proof -
    have "rat_of_pair (mn, md) * 2 / 2 =
        (rat_of_pair (na, da) +
         rat_of_pair (nb, db)) / 2"
      using mid_twice by simp
    then show ?thesis by simp
  qed
  have "rat_of_pair (na, da) < rat_of_pair (mn, md)"
    using mid_less mid by simp
  then show ?thesis
    by (rule interval_pair_orderedI[OF da_pos md_pos])
qed

lemma interval_pair_ordered_mid_right:
  assumes ord: "rational_interval_pair_ordered ((na, da), (nb, db))"
    and mid_twice: "rat_of_pair (mn, md) * 2 =
      rat_of_pair (na, da) +
       rat_of_pair (nb, db)"
    and md_pos: "0 < md"
  shows "rational_interval_pair_ordered ((mn, md), (nb, db))"
proof -
  have db_pos: "0 < db"
    using ord unfolding rational_interval_pair_ordered_def by simp
  have less_ab:
    "rat_of_pair (na, da) < rat_of_pair (nb, db)"
    using interval_pair_ordered_of_pair_less[OF ord]
    unfolding interval_of_pair_def by simp
  have less_mid:
    "(rat_of_pair (na, da) +
      rat_of_pair (nb, db)) / 2 <
     rat_of_pair (nb, db)"
  proof -
    have "rat_of_pair (na, da) +
      rat_of_pair (nb, db) <
      2 * rat_of_pair (nb, db)"
      using less_ab by linarith
    then show ?thesis by (simp add: field_simps)
  qed
  have mid: "rat_of_pair (mn, md) =
      (rat_of_pair (na, da) +
       rat_of_pair (nb, db)) / 2"
  proof -
    have "rat_of_pair (mn, md) * 2 / 2 =
        (rat_of_pair (na, da) +
         rat_of_pair (nb, db)) / 2"
      using mid_twice by simp
    then show ?thesis by simp
  qed
  have "rat_of_pair (mn, md) < rat_of_pair (nb, db)"
    using less_mid mid by simp
  then show ?thesis
    by (rule interval_pair_orderedI[OF md_pos db_pos])
qed

lemma gmp_interval_vec_ordered_to_listD:
  assumes "rational_gmp_interval_vec_ordered v"
    and "I \<in> set (interval_vec_to_list v)"
  shows "fst I < snd I"
  using assms interval_pair_ordered_of_pair_less
  unfolding rational_gmp_interval_vec_ordered_def
    interval_vec_to_list_def
  by auto

lemma rational_state_todo_orderedD:
  assumes "rational_gmp_interval_vec_ordered todo"
    and "I \<in> set (rational_state_todo (i, todo, acc))"
  shows "fst I < snd I"
proof -
  have "I \<in> set (interval_vec_to_list todo)"
    using assms(2) by (auto dest: in_set_dropD)
  then show ?thesis
    using gmp_interval_vec_ordered_to_listD[OF assms(1)] by simp
qed

lemma gmp_interval_vec_ordered_push_children:
  assumes inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and ord: "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and left: "rational_interval_pair_ordered ((na, da), (mn, md))"
    and right: "rational_interval_pair_ordered ((mn, md), (nb, db))"
  shows "rational_gmp_interval_vec_ordered
    (lna @ [na, mn], lda @ [da, md],
     rnb @ [mn, nb], rdb @ [md, db])"
  using inv ord left right
  unfolding rational_gmp_interval_vec_ordered_def
  by (simp add: interval_vec_pairs_push_children)

lemma gmp_interval_vec_ordered_push_mid:
  assumes inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and ord: "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and raw: "interval_vec_pairs (lna, lda, rnb, rdb) ! i =
      ((na, da), (nb, db))"
    and mid_twice: "rat_of_pair (mn, md) * 2 =
      rat_of_pair (na, da) +
       rat_of_pair (nb, db)"
    and md_pos: "0 < md"
  shows "rational_gmp_interval_vec_ordered
    (lna @ [na, mn], lda @ [da, md],
     rnb @ [mn, nb], rdb @ [md, db])"
proof -
  have raw_ord:
    "rational_interval_pair_ordered ((na, da), (nb, db))"
    using gmp_interval_vec_ordered_nthD[
      OF ord, of i] interval_vec_pairs_length[OF inv]
      i_lt raw
    by simp
  have left:
    "rational_interval_pair_ordered ((na, da), (mn, md))"
    by (rule interval_pair_ordered_mid_left[
      OF raw_ord mid_twice md_pos])
  have right:
    "rational_interval_pair_ordered ((mn, md), (nb, db))"
    by (rule interval_pair_ordered_mid_right[
      OF raw_ord mid_twice md_pos])
  show ?thesis
    by (rule gmp_interval_vec_ordered_push_children[
      OF inv ord left right])
qed

definition rational_zero_monadic ::
  "rational_loop_state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
    rational_loop_state nres" where
"rational_zero_monadic st na da nb db \<equiv> doN {
  let (i, todo, acc) = st;
  (PR_CONST mpzb_discard_monadic) na;
  (PR_CONST mpzb_discard_monadic) da;
  (PR_CONST mpzb_discard_monadic) nb;
  (PR_CONST mpzb_discard_monadic) db;
  RETURN (i + 1, todo, acc)
}"

lemma rational_zero_monadic_spec:
  "rational_zero_monadic (i, todo, acc) na da nb db \<le>
    RETURN (Suc i, todo, acc)"
  unfolding rational_zero_monadic_def mpzb_discard_monadic_def
    PR_CONST_def
  by simp

sepref_register "PR_CONST rational_zero_monadic"
  :: "rational_loop_state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
      rational_loop_state nres"

sepref_definition rational_zero_impl [llvm_inline] is
  "uncurry4 rational_zero_monadic" ::
  "[\<lambda>((((st, _), _), _), _). case st of (i, _, _) \<Rightarrow>
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    rational_loop_state_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      rational_loop_state_assn"
  unfolding rational_zero_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

lemma rational_zero_impl_hnr[sepref_fr_rules]:
  "(uncurry4 rational_zero_impl,
    uncurry4 (PR_CONST rational_zero_monadic)) \<in>
    [\<lambda>((((st, _), _), _), _). case st of (i, _, _) \<Rightarrow>
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      rational_loop_state_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        rational_loop_state_assn"
  using rational_zero_impl.refine
  by (simp add: PR_CONST_def)

definition rational_one_monadic ::
  "rational_loop_state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
    rational_loop_state nres" where
"rational_one_monadic st na da nb db \<equiv> doN {
  let (i, todo, acc) = st;
  let (lna, lda, rnb, rdb) = acc;
  ASSERT (interval_vec_pushable acc);
  lna \<leftarrow> (PR_CONST poly_push_coeff_monadic) lna na;
  lda \<leftarrow> (PR_CONST poly_push_coeff_monadic) lda da;
  rnb \<leftarrow> (PR_CONST poly_push_coeff_monadic) rnb nb;
  rdb \<leftarrow> (PR_CONST poly_push_coeff_monadic) rdb db;
  RETURN (i + 1, todo, (lna, lda, rnb, rdb))
}"

lemma rational_one_monadic_spec:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "interval_vec_pushable (lna, lda, rnb, rdb)"
  shows "rational_one_monadic
      (i, todo, (lna, lda, rnb, rdb)) na da nb db \<le>
    SPEC (\<lambda>st'. st' =
      (Suc i, todo, (lna @ [na], lda @ [da], rnb @ [nb], rdb @ [db])) \<and>
      rational_state_acc st' =
        rational_state_acc (i, todo, (lna, lda, rnb, rdb)) @
          [interval_of_pair ((na, da), (nb, db))])"
  using assms
  unfolding rational_one_monadic_def
    interval_vec_pushable_def
    poly_push_coeff_monadic_def PR_CONST_def
  by (simp add: refine_pw_simps interval_vec_to_list_push)

sepref_register "PR_CONST rational_one_monadic"
  :: "rational_loop_state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
      rational_loop_state nres"

sepref_definition rational_one_impl [llvm_inline] is
  "uncurry4 rational_one_monadic" ::
  "[\<lambda>((((st, _), _), _), _). case st of (i, _, acc) \<Rightarrow>
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    rational_loop_state_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      rational_loop_state_assn"
  unfolding rational_one_monadic_def
  unfolding interval_vec_pushable_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
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

lemma rational_one_impl_hnr[sepref_fr_rules]:
  "(uncurry4 rational_one_impl,
    uncurry4 (PR_CONST rational_one_monadic)) \<in>
    [\<lambda>((((st, _), _), _), _). case st of (i, _, acc) \<Rightarrow>
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      rational_loop_state_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        rational_loop_state_assn"
  using rational_one_impl.refine
  by (simp add: PR_CONST_def)

definition rational_split_nonroot_monadic ::
  "nat \<Rightarrow> gmp_interval_vec \<Rightarrow> gmp_interval_vec \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
    rational_loop_state nres" where
"rational_split_nonroot_monadic i todo acc na da nb db mn md \<equiv> doN {
  ASSERT (interval_vec_pushable2 todo);
  todo1 \<leftarrow> (PR_CONST interval_vec_push_children_monadic)
    todo na da nb db mn md;
  RETURN (i + 1, todo1, acc)
}"

lemma rational_drop_Suc_append:
  assumes "i < length xs"
  shows "drop (Suc i) (xs @ ys) = tl (drop i xs) @ ys"
  using assms
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases i) simp_all
qed

lemma rational_drop_Suc_tl:
  assumes "i < length xs"
  shows "drop (Suc i) xs = tl (drop i xs)"
  using rational_drop_Suc_append[OF assms, of "[]"] by simp

lemma rational_zero_monadic_project_spec:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "i < length lna"
  shows "rational_zero_monadic
      (i, (lna, lda, rnb, rdb), acc) na da nb db \<le>
    SPEC (\<lambda>st'.
      rational_state_todo st' =
        tl (rational_state_todo
          (i, (lna, lda, rnb, rdb), acc)) \<and>
      rational_state_acc st' =
        rational_state_acc (i, (lna, lda, rnb, rdb), acc))"
  using assms
  unfolding rational_zero_monadic_def mpzb_discard_monadic_def
    PR_CONST_def
  by (simp add: rational_drop_Suc_tl
    interval_vec_to_list_length)

lemma rational_one_monadic_project_spec:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "i < length lna"
    and "interval_vec_invar (alna, alda, arnb, ardb)"
    and "interval_vec_pushable (alna, alda, arnb, ardb)"
  shows "rational_one_monadic
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
      na da nb db \<le>
    SPEC (\<lambda>st'.
      rational_state_todo st' =
        tl (rational_state_todo
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))) \<and>
      rational_state_acc st' =
        rational_state_acc
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)) @
        [interval_of_pair ((na, da), (nb, db))])"
  using assms
  unfolding rational_one_monadic_def
    interval_vec_pushable_def
    poly_push_coeff_monadic_def PR_CONST_def
  by (simp add: refine_pw_simps rational_drop_Suc_tl
    interval_vec_to_list_length
    interval_vec_to_list_push)

lemma rational_split_nonroot_monadic_spec:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and "i < length lna"
  shows "rational_split_nonroot_monadic i (lna, lda, rnb, rdb) acc
      na da nb db mn md \<le>
    SPEC (\<lambda>st'.
      rational_state_todo st' =
        tl (rational_state_todo
          (i, (lna, lda, rnb, rdb), acc)) @
        [interval_of_pair ((na, da), (mn, md)),
         interval_of_pair ((mn, md), (nb, db))] \<and>
      rational_state_acc st' =
        rational_state_acc (i, (lna, lda, rnb, rdb), acc))"
  using assms
  unfolding rational_split_nonroot_monadic_def PR_CONST_def
  apply refine_vcg
  apply (rule order_trans[OF interval_vec_push_children_monadic_spec])
    apply simp_all
  apply (clarsimp simp: rational_drop_Suc_append
    rational_drop_Suc_tl
    interval_vec_to_list_length)
  done

lemma rational_split_nonroot_monadic_exact_spec:
  assumes "interval_vec_pushable2 (lna, lda, rnb, rdb)"
  shows "rational_split_nonroot_monadic i (lna, lda, rnb, rdb) acc
      na da nb db mn md \<le>
    RETURN (Suc i,
      (lna @ [na, mn], lda @ [da, md], rnb @ [mn, nb], rdb @ [md, db]),
      acc)"
  using assms
  unfolding rational_split_nonroot_monadic_def
    interval_vec_push_children_monadic_def
    poly_push2_coeffs_monadic_def poly_push_coeff_monadic_def
    interval_vec_pushable2_def PR_CONST_def
  by refine_vcg auto

sepref_register "PR_CONST rational_split_nonroot_monadic"
  :: "nat \<Rightarrow> gmp_interval_vec \<Rightarrow> gmp_interval_vec \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
      rational_loop_state nres"

sepref_definition rational_split_nonroot_impl [llvm_inline] is
  "uncurry8 rational_split_nonroot_monadic" ::
  "[\<lambda>((((((((i, _), _), _), _), _), _), _), _).
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_interval_vec_assn\<^sup>d *\<^sub>a gmp_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      rational_loop_state_assn"
  unfolding rational_split_nonroot_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
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

lemma rational_split_nonroot_impl_hnr[sepref_fr_rules]:
  "(uncurry8 rational_split_nonroot_impl,
    uncurry8 (PR_CONST rational_split_nonroot_monadic)) \<in>
    [\<lambda>((((((((i, _), _), _), _), _), _), _), _).
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_interval_vec_assn\<^sup>d *\<^sub>a gmp_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        rational_loop_state_assn"
  using rational_split_nonroot_impl.refine
  by (simp add: PR_CONST_def)

definition rational_split_root_monadic ::
  "nat \<Rightarrow> gmp_interval_vec \<Rightarrow> gmp_interval_vec \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
    rational_loop_state nres" where
"rational_split_root_monadic i todo acc na da nb db mn md \<equiv> doN {
  ASSERT (interval_vec_pushable acc);
  acc1 \<leftarrow> (PR_CONST interval_vec_push_point_monadic) acc mn md;
  ASSERT (interval_vec_pushable2 todo);
  todo1 \<leftarrow> (PR_CONST interval_vec_push_children_monadic)
    todo na da nb db mn md;
  RETURN (i + 1, todo1, acc1)
}"

lemma rational_split_root_monadic_spec:
  assumes "interval_vec_invar (lna, lda, rnb, rdb)"
    and "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and "i < length lna"
    and "interval_vec_invar (alna, alda, arnb, ardb)"
    and "interval_vec_pushable (alna, alda, arnb, ardb)"
  shows "rational_split_root_monadic i (lna, lda, rnb, rdb)
      (alna, alda, arnb, ardb)
      na da nb db mn md \<le>
    SPEC (\<lambda>st'.
      rational_state_todo st' =
        tl (rational_state_todo
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))) @
        [interval_of_pair ((na, da), (mn, md)),
         interval_of_pair ((mn, md), (nb, db))] \<and>
      rational_state_acc st' =
        rational_state_acc
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)) @
        [interval_of_pair ((mn, md), (mn, md))])"
  using assms
  unfolding rational_split_root_monadic_def PR_CONST_def
  apply (refine_vcg interval_vec_push_point_monadic_spec
    interval_vec_push_children_monadic_spec)
  apply (auto simp: rational_drop_Suc_append
    rational_drop_Suc_tl
    interval_vec_to_list_length)
  done

lemma rational_split_root_monadic_exact_spec:
  assumes "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and "interval_vec_pushable (alna, alda, arnb, ardb)"
  shows "rational_split_root_monadic i (lna, lda, rnb, rdb)
      (alna, alda, arnb, ardb)
      na da nb db mn md \<le>
    RETURN (Suc i,
      (lna @ [na, mn], lda @ [da, md], rnb @ [mn, nb], rdb @ [md, db]),
      (alna @ [mn], alda @ [md], arnb @ [mn], ardb @ [md]))"
  using assms
  unfolding rational_split_root_monadic_def
    interval_vec_push_point_monadic_def
    interval_vec_push_monadic_def
    interval_vec_push_children_monadic_def
    poly_push2_coeffs_monadic_def poly_push_coeff_monadic_def
    interval_vec_pushable_def
    interval_vec_pushable2_def PR_CONST_def
  by refine_vcg auto

sepref_register "PR_CONST rational_split_root_monadic"
  :: "nat \<Rightarrow> gmp_interval_vec \<Rightarrow> gmp_interval_vec \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
      rational_loop_state nres"

sepref_definition rational_split_root_impl [llvm_inline] is
  "uncurry8 rational_split_root_monadic" ::
  "[\<lambda>((((((((i, _), _), _), _), _), _), _), _).
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_interval_vec_assn\<^sup>d *\<^sub>a gmp_interval_vec_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      rational_loop_state_assn"
  unfolding rational_split_root_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
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

lemma rational_split_root_impl_hnr[sepref_fr_rules]:
  "(uncurry8 rational_split_root_impl,
    uncurry8 (PR_CONST rational_split_root_monadic)) \<in>
    [\<lambda>((((((((i, _), _), _), _), _), _), _), _).
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_interval_vec_assn\<^sup>d *\<^sub>a gmp_interval_vec_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        rational_loop_state_assn"
  using rational_split_root_impl.refine
  by (simp add: PR_CONST_def)

definition rational_split_monadic ::
  "gmp_poly \<Rightarrow> rational_loop_state \<Rightarrow>
    int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
    rational_loop_state nres" where
"rational_split_monadic P st na da nb db \<equiv> doN {
  let (i, todo, acc) = st;
  ASSERT (0 < da);
  ASSERT (0 < db);
  m \<leftarrow> (PR_CONST rat_mid_monadic) na da nb db;
  case m of (mn, md) \<Rightarrow> doN {
    ASSERT (0 < length P);
    is_root \<leftarrow> (PR_CONST poly_hom_eval_zero_mpz_monadic) mn md P;
    if is_root then
      (PR_CONST rational_split_root_monadic) i todo acc na da nb db mn md
    else
      (PR_CONST rational_split_nonroot_monadic) i todo acc na da nb db mn md
  }
}"

sepref_register "PR_CONST rational_split_monadic"
  :: "gmp_poly \<Rightarrow> rational_loop_state \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow>
      rational_loop_state nres"

sepref_definition rational_split_impl [llvm_inline] is
  "uncurry5 rational_split_monadic" ::
  "[\<lambda>(((((P, st), _), _), _), _). case st of (i, _, _) \<Rightarrow>
      0 < length P \<and> length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a rational_loop_state_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
      rational_loop_state_assn"
  unfolding rational_split_monadic_def
  unfolding interval_vec_pushable_def
    interval_vec_pushable2_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

lemma rational_split_impl_hnr[sepref_fr_rules]:
  "(uncurry5 rational_split_impl,
    uncurry5 (PR_CONST rational_split_monadic)) \<in>
    [\<lambda>(((((P, st), _), _), _), _). case st of (i, _, _) \<Rightarrow>
      0 < length P \<and> length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a rational_loop_state_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>
        rational_loop_state_assn"
  using rational_split_impl.refine
  by (simp add: PR_CONST_def)

lemma rational_mid_eq_from_twice:
  fixes a b :: rat
  assumes "0 < d"
    and "rat_of_int n * 2 / rat_of_int d = a + b"
  shows "rat_of_int n / rat_of_int d = (a + b) / 2"
  using assms by (simp add: field_simps)

lemma rational_midpoint_times_two:
  fixes a b :: rat
  shows "((a + b) / 2) * 2 = a + b"
    and "a + b = ((a + b) / 2) * 2"
  by simp_all

lemma rational_mid_eq_from_times_two:
  fixes m a b :: rat
  assumes "m * 2 = a + b"
  shows "m = (a + b) / 2"
  using assms by simp

lemma rational_split_monadic_project_spec:
  fixes na da nb db :: int
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    and da_pos: "0 < da"
    and db_pos: "0 < db"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  defines "a \<equiv> rat_of_pair (na, da)"
    and "b \<equiv> rat_of_pair (nb, db)"
  shows "rational_split_monadic P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
      na da nb db \<le>
    SPEC (\<lambda>st'. \<exists>m.
      m = (a + b) / 2 \<and>
      rational_state_todo st' =
        tl (rational_state_todo
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))) @
        [(a, m), (m, b)] \<and>
      rational_state_acc st' =
        rational_state_acc
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)) @
        (if poly (map_poly rat_of_int (Poly P)) m = 0
         then [(m, m)] else []))"
  using assms
  unfolding rational_split_monadic_def PR_CONST_def a_def b_def
  apply (refine_vcg rat_mid_monadic_spec)
    apply simp_all
  subgoal for mn md
    apply (rule order_trans)
     apply (rule poly_hom_eval_zero_mpz_monadic_spec)
       apply simp_all
    apply (simp add: refine_pw_simps)?
    apply (intro conjI impI)
    subgoal
      apply (rule order_trans)
       apply (rule rational_split_root_monadic_spec)
            apply simp_all
      apply (clarsimp simp: interval_of_pair_def
        rat_of_pair_def rational_mid_eq_from_twice)
      apply (rule_tac x="(rat_of_int na / rat_of_int da +
        rat_of_int nb / rat_of_int db) / 2" in exI)
      apply (intro conjI)
        apply assumption
       apply (rule rational_midpoint_times_two)
      apply (rule rational_midpoint_times_two)
      done
    subgoal
      apply (rule order_trans)
       apply (rule rational_split_nonroot_monadic_spec)
         apply simp_all
      apply (clarsimp simp: interval_of_pair_def
        rat_of_pair_def rational_mid_eq_from_twice)
      apply (rule_tac x="(rat_of_int na / rat_of_int da +
        rat_of_int nb / rat_of_int db) / 2" in exI)
      apply (intro conjI)
        apply assumption
       apply (rule rational_midpoint_times_two)
      apply (rule rational_midpoint_times_two)
      done
    done
  done

definition rational_step_raw_post ::
  "gmp_poly \<Rightarrow> rational_loop_state \<Rightarrow>
    rational_loop_state \<Rightarrow> bool" where
"rational_step_raw_post P st st' \<equiv>
  (let (i, todo, acc) = st;
       raw = interval_vec_pairs todo ! i;
       I = interval_of_pair raw;
       rest = tl (rational_state_todo st);
       acc0 = rational_state_acc st
   in case raw of ((na, da), (nb, db)) \<Rightarrow>
      let v = descartes_preprocess na da nb db P in
      if v = 0 then
        rational_state_todo st' = rest \<and>
        rational_state_acc st' = acc0
      else if v = 1 then
        rational_state_todo st' = rest \<and>
        rational_state_acc st' = acc0 @ [I]
      else
        (\<exists>m.
          m = (fst I + snd I) / 2 \<and>
          rational_state_todo st' =
            rest @ [(fst I, m), (m, snd I)] \<and>
          rational_state_acc st' =
            acc0 @
              (if poly (map_poly rat_of_int (Poly P)) m = 0
               then [(m, m)] else [])))"

lemma interval_vec_to_list_nth_pair:
  assumes "interval_vec_invar v"
    and "i < length (case v of (lna, _, _, _) \<Rightarrow> lna)"
  shows "interval_vec_to_list v ! i =
    interval_of_pair (interval_vec_pairs v ! i)"
  using assms
  by (cases v)
    (auto simp: interval_vec_to_list_def
      interval_vec_pairs_length)

lemma rational_state_todo_cons_raw:
  assumes inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
  shows "rational_state_todo
      (i, (lna, lda, rnb, rdb), acc) =
    interval_of_pair
      (interval_vec_pairs (lna, lda, rnb, rdb) ! i) #
    tl (rational_state_todo
      (i, (lna, lda, rnb, rdb), acc))"
proof -
  let ?todo = "interval_vec_to_list (lna, lda, rnb, rdb)"
  have len: "i < length ?todo"
    using i_lt interval_vec_to_list_length[OF inv] by simp
  have "?todo ! i =
    interval_of_pair
      (interval_vec_pairs (lna, lda, rnb, rdb) ! i)"
    using interval_vec_to_list_nth_pair[
      of "(lna, lda, rnb, rdb)" i] inv i_lt by simp
  then show ?thesis
    using hd_drop_conv_nth[OF len] len
    by (cases "drop i ?todo")
      (auto simp: rational_state_todo_def)
qed

lemma rational_step_raw_post_queue_step:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and P_len: "0 < length P"
    and post: "rational_step_raw_post P
      (i, (lna, lda, rnb, rdb), acc) st'"
  shows "(rational_state_todo st',
          rational_state_acc st') =
    rational_queue_step_int P
      (rational_state_todo
        (i, (lna, lda, rnb, rdb), acc))
      (rational_state_acc
        (i, (lna, lda, rnb, rdb), acc))"
proof -
  let ?raw = "interval_vec_pairs (lna, lda, rnb, rdb) ! i"
  have todo_cons:
    "rational_state_todo
      (i, (lna, lda, rnb, rdb), acc) =
    interval_of_pair ?raw #
      tl (rational_state_todo
        (i, (lna, lda, rnb, rdb), acc))"
    by (rule rational_state_todo_cons_raw[OF todo_inv i_lt])

  obtain na da nb db where raw:
    "?raw = ((na, da), (nb, db))"
    by (cases ?raw) auto
  have da_pos: "0 < da" and db_pos: "0 < db"
    and cross: "na * db < nb * da"
    using gmp_interval_vec_ordered_componentsD[
      OF todo_inv todo_ordered i_lt raw] by simp_all
  have count_eq:
    "descartes_preprocess na da nb db P =
      descartes_list_int
        (fst (interval_of_pair ?raw))
        (snd (interval_of_pair ?raw)) P"
    using descartes_preprocess_eq_fast[
      OF P_len da_pos db_pos cross]
    by (simp add: raw interval_of_pair_def
      rat_of_pair_def)
  have queue_step:
    "rational_queue_step_int P
      (rational_state_todo
        (i, (lna, lda, rnb, rdb), acc))
      (rational_state_acc
        (i, (lna, lda, rnb, rdb), acc)) =
    (let I = interval_of_pair ?raw;
         rest = tl (rational_state_todo
          (i, (lna, lda, rnb, rdb), acc));
         acc0 = rational_state_acc
          (i, (lna, lda, rnb, rdb), acc);
         v = descartes_list_int (fst I) (snd I) P
     in if v = 0 then (rest, acc0)
        else if v = 1 then (rest, acc0 @ [I])
        else
          (let m = (fst I + snd I) / 2 in
           (rest @ [(fst I, m), (m, snd I)],
            acc0 @
              (if poly (map_poly rat_of_int (Poly P)) m = 0
               then [(m, m)] else []))))"
    unfolding rational_queue_step_int_def
    apply (subst todo_cons)
    apply (simp add: Let_def)
    done
  show ?thesis
    using post count_eq queue_step
    unfolding rational_step_raw_post_def
    by (auto simp: raw Let_def
      dest: rational_mid_eq_from_times_two
      split: prod.splits if_splits)
qed

lemma descartes_preprocess_monadic_refine_Id:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "descartes_preprocess_monadic na da nb db xs \<le>
    \<Down>Id (RETURN (descartes_preprocess na da nb db xs))"
  using descartes_preprocess_monadic_correct[OF assms, of na da nb db]
  by simp

lemma dsc_nres_bind_RETURN_SPEC:
  assumes "m \<le> RETURN x"
    and "f x \<le> SPEC P"
  shows "Refine_Basic.bind m f \<le> SPEC P"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps)

lemma dsc_nres_SPEC_conjI:
  assumes "m \<le> SPEC P"
    and "m \<le> SPEC Q"
  shows "m \<le> SPEC (\<lambda>x. P x \<and> Q x)"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps)

lemma rational_after_get_project_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and raw: "interval_vec_pairs (lna, lda, rnb, rdb) ! i =
      ((na, da), (nb, db))"
  shows "(doN {
      v \<leftarrow> (PR_CONST descartes_preprocess_monadic)
        na da nb db P;
      if v = 0 then
        (PR_CONST rational_zero_monadic)
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
          na da nb db
      else if v = 1 then
        (PR_CONST rational_one_monadic)
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
          na da nb db
      else
        (PR_CONST rational_split_monadic) P
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
          na da nb db
    }) \<le>
    SPEC (rational_step_raw_post P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)))"
proof -
  let ?v = "descartes_preprocess na da nb db P"
  let ?st = "(i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"

  have count:
    "descartes_preprocess_monadic na da nb db P \<le>
      RETURN ?v"
    using descartes_preprocess_monadic_correct[OF P_bound] .

  have branch:
    "(if ?v = 0 then
        rational_zero_monadic ?st na da nb db
      else if ?v = 1 then
        rational_one_monadic ?st na da nb db
      else
        rational_split_monadic P ?st na da nb db) \<le>
      SPEC (rational_step_raw_post P ?st)"
    using assms
    unfolding rational_step_raw_post_def
    apply (cases "?v = 0")
    subgoal
      apply simp
      apply (rule order_trans)
       apply (rule rational_zero_monadic_project_spec
          [OF todo_inv i_lt])
      apply (clarsimp simp: raw)
      done
    subgoal
      apply (cases "?v = 1")
      subgoal
        apply simp
        apply (rule order_trans)
         apply (rule rational_one_monadic_project_spec
            [OF todo_inv i_lt acc_inv acc_push])
        apply (clarsimp simp: raw interval_of_pair_def)
        done
      subgoal
        apply simp
        apply (rule order_trans)
         apply (rule rational_split_monadic_project_spec[
            OF todo_inv todo_push2 i_lt acc_inv acc_push
              gmp_interval_vec_ordered_componentsD(1)[OF todo_inv todo_ordered i_lt raw]
              gmp_interval_vec_ordered_componentsD(2)[OF todo_inv todo_ordered i_lt raw]
              P_len P_bound])
        apply (clarsimp simp: raw interval_of_pair_def)
        done
      done
    done

  show ?thesis
    unfolding PR_CONST_def
    apply (rule dsc_nres_bind_RETURN_SPEC[where x="?v"])
     apply (rule count)
    apply (rule branch)
    done
qed

definition rational_loop_body_idx_monadic ::
  "gmp_poly \<Rightarrow> rational_loop_state \<Rightarrow>
    rational_loop_state nres" where
"rational_loop_body_idx_monadic P st \<equiv> doN {
  let (i, todo, acc) = st;
  ASSERT (interval_vec_invar todo);
  ASSERT (case todo of (lna, lda, rnb, rdb) \<Rightarrow>
    i < length lna \<and> i < length lda \<and> i < length rnb \<and> i < length rdb);
  ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
  ep \<leftarrow> (PR_CONST interval_vec_copy_get_monadic) todo i;
  case ep of (na, da, nb, db) \<Rightarrow> doN {
    v \<leftarrow> (PR_CONST descartes_preprocess_monadic) na da nb db P;
    if v = 0 then
      (PR_CONST rational_zero_monadic) (i, todo, acc) na da nb db
    else if v = 1 then
      (PR_CONST rational_one_monadic) (i, todo, acc) na da nb db
    else
      (PR_CONST rational_split_monadic) P (i, todo, acc) na da nb db
  }
}"

sepref_register "PR_CONST rational_loop_body_idx_monadic"
  :: "gmp_poly \<Rightarrow> rational_loop_state \<Rightarrow>
      rational_loop_state nres"

sepref_definition rational_loop_body_idx_impl [llvm_inline] is
  "uncurry rational_loop_body_idx_monadic" ::
  "[\<lambda>(P, i, todo, acc).
      0 < length P \<and> length P + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a rational_loop_state_assn\<^sup>d \<rightarrow>
      rational_loop_state_assn"
  unfolding rational_loop_body_idx_monadic_def
  unfolding interval_vec_invar_def
  unfolding interval_vec_pushable_def
    interval_vec_pushable2_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
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

lemma rational_loop_body_idx_impl_hnr[sepref_fr_rules]:
  "(uncurry rational_loop_body_idx_impl,
    uncurry (PR_CONST rational_loop_body_idx_monadic)) \<in>
    [\<lambda>(P, i, todo, acc).
      0 < length P \<and> length P + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a rational_loop_state_assn\<^sup>d \<rightarrow>
        rational_loop_state_assn"
  using rational_loop_body_idx_impl.refine
  by (simp add: PR_CONST_def)

lemma rational_loop_body_idx_monadic_project_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and i_bound: "i + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_loop_body_idx_monadic P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)) \<le>
    SPEC (rational_step_raw_post P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)))"
  using assms
  unfolding rational_loop_body_idx_monadic_def PR_CONST_def
  apply (refine_vcg interval_vec_copy_get_monadic_spec)
  subgoal by (clarsimp simp: interval_vec_invar_def split: prod.splits)
  subgoal by (clarsimp simp: interval_vec_invar_def split: prod.splits)
  subgoal by (clarsimp simp: interval_vec_invar_def split: prod.splits)
  subgoal by (clarsimp simp: interval_vec_invar_def split: prod.splits)
  subgoal by (clarsimp simp: interval_vec_invar_def split: prod.splits)
  subgoal by (clarsimp split: prod.splits)
  subgoal
    apply (clarsimp split: prod.splits)
    apply (rule order_trans[OF interval_vec_copy_get_monadic_spec])
      apply (clarsimp split: prod.splits)
     apply (clarsimp split: prod.splits)
    apply (clarsimp simp: refine_pw_simps split: prod.splits)
    apply (rule_tac na=ab and da=aaa and nb=aba and db=bb
      in rational_after_get_project_spec[unfolded PR_CONST_def])
            apply (clarsimp split: prod.splits)+
    done
  done

lemma rational_loop_body_idx_monadic_queue_step_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and i_bound: "i + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_loop_body_idx_monadic P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)) \<le>
    SPEC (\<lambda>st'.
      (rational_state_todo st',
       rational_state_acc st') =
        rational_queue_step_int P
          (rational_state_todo
            (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)))
          (rational_state_acc
            (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))))"
  apply (rule order_trans[
    OF rational_loop_body_idx_monadic_project_spec[
      OF todo_inv todo_ordered i_lt acc_inv acc_push todo_push2
         i_bound P_len P_bound]])
  apply (clarsimp simp: refine_pw_simps)
  apply (drule rational_step_raw_post_queue_step[
    OF todo_inv todo_ordered i_lt P_len])
  apply simp
  done

lemma rational_loop_body_idx_monadic_queue_main_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and i_bound: "i + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_loop_body_idx_monadic P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)) \<le>
    SPEC (\<lambda>st'.
      rational_queue_main_int P
        (rational_state_todo st')
        (rational_state_acc st') =
      rational_queue_main_int P
        (rational_state_todo
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)))
        (rational_state_acc
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))))"
proof -
  let ?st = "(i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
  let ?todo = "drop i (interval_vec_to_list (lna, lda, rnb, rdb))"
  let ?acc = "interval_vec_to_list (alna, alda, arnb, ardb)"
  have todo_nonempty:
    "?todo \<noteq> []"
    using i_lt interval_vec_to_list_length[OF todo_inv]
    by auto
  have step_main:
    "\<And>todo' acc'. (todo', acc') =
        rational_queue_step_int P ?todo ?acc \<Longrightarrow>
      rational_queue_main_int P todo' acc' =
      rational_queue_main_int P ?todo ?acc"
  proof -
    fix todo' acc'
    assume eq: "(todo', acc') =
      rational_queue_step_int P ?todo ?acc"
    have "rational_queue_main_int P ?todo ?acc =
      (let (todo'', acc'') =
         rational_queue_step_int P ?todo ?acc
       in rational_queue_main_int P todo'' acc'')"
      by (rule rational_queue_main_int_step[OF todo_nonempty])
    also have "... = rational_queue_main_int P todo' acc'"
      using eq by (cases "rational_queue_step_int P ?todo ?acc") auto
    finally show "rational_queue_main_int P todo' acc' =
      rational_queue_main_int P ?todo ?acc"
      by simp
  qed
  show ?thesis
    apply (rule order_trans[
      OF rational_loop_body_idx_monadic_queue_step_spec[
        OF todo_inv todo_ordered i_lt acc_inv acc_push todo_push2
           i_bound P_len P_bound]])
    apply (clarsimp simp: refine_pw_simps)
    apply (rule step_main)
    apply assumption
    done
qed

lemma rational_loop_body_idx_monadic_queue_mu_decreases:
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and i_bound: "i + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_loop_body_idx_monadic P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)) \<le>
    SPEC (\<lambda>st'.
      rational_todo_mu_mset \<delta> (rational_state_todo st') <
      rational_todo_mu_mset \<delta>
        (rational_state_todo
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))))"
proof -
  let ?st = "(i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
  let ?todo = "rational_state_todo ?st"
  let ?acc = "rational_state_acc ?st"
  have todo_ne: "?todo \<noteq> []"
    using i_lt interval_vec_to_list_length[OF todo_inv]
    by auto
  have ordered_todo: "\<And>I. I \<in> set ?todo \<Longrightarrow> fst I < snd I"
    by (rule rational_state_todo_orderedD[OF todo_ordered])
  have step_dec:
    "rational_todo_mu_mset \<delta>
        (fst (rational_queue_step_int P ?todo ?acc)) <
      rational_todo_mu_mset \<delta> ?todo"
    by (rule rational_queue_step_mu_mset_decreases[
      OF \<delta>_pos ordered_todo small_fast todo_ne])
  have spec_refine:
    "SPEC (\<lambda>st'.
      (rational_state_todo st',
       rational_state_acc st') =
        rational_queue_step_int P ?todo ?acc) \<le>
     SPEC (\<lambda>st'.
      rational_todo_mu_mset \<delta> (rational_state_todo st') <
      rational_todo_mu_mset \<delta> ?todo)"
    using step_dec
    apply (clarsimp simp: pw_le_iff refine_pw_simps)
    apply (drule arg_cong[where f=fst])
    apply simp
    done
  show ?thesis
    by (rule order_trans[
      OF rational_loop_body_idx_monadic_queue_step_spec[
        OF todo_inv todo_ordered i_lt acc_inv acc_push todo_push2
           i_bound P_len P_bound] spec_refine])
qed

definition rational_vec_len ::
  "gmp_interval_vec \<Rightarrow> nat" where
"rational_vec_len v \<equiv>
  length (fst v)"

lemma rational_vec_len_simps[simp]:
  "rational_vec_len (lna, lda, rnb, rdb) = length lna"
  unfolding rational_vec_len_def by simp

lemma interval_vec_pushable2_from_budget:
  assumes inv: "interval_vec_invar v"
    and cap: "int (rational_vec_len v) + B + 2 <
      int (max_snat LENGTH(gmp_poly_len))"
    and nonneg: "0 \<le> B"
  shows "interval_vec_pushable2 v"
  using assms
  unfolding interval_vec_invar_def
    interval_vec_pushable2_def
  by (cases v) (auto simp: Let_def)

lemma interval_vec_pushable_from_budget:
  assumes inv: "interval_vec_invar v"
    and cap: "int (rational_vec_len v) + B + 1 <
      int (max_snat LENGTH(gmp_poly_len))"
    and nonneg: "0 \<le> B"
  shows "interval_vec_pushable v"
  using assms
  unfolding interval_vec_invar_def
    interval_vec_pushable_def
  by (cases v) (auto simp: Let_def)

lemma interval_vec_pushable2_from_budget_tuple:
  assumes inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and cap: "int (length lna) + B + 2 <
      int (max_snat LENGTH(gmp_poly_len))"
    and nonneg: "0 \<le> B"
  shows "interval_vec_pushable2 (lna, lda, rnb, rdb)"
  using assms
  unfolding interval_vec_invar_def
    interval_vec_pushable2_def
  by auto

lemma interval_vec_pushable_from_budget_tuple:
  assumes inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and cap: "int (length lna) + B + 1 <
      int (max_snat LENGTH(gmp_poly_len))"
    and nonneg: "0 \<le> B"
  shows "interval_vec_pushable (lna, lda, rnb, rdb)"
  using assms
  unfolding interval_vec_invar_def
    interval_vec_pushable_def
  by auto

definition rational_loop_invar ::
  "real \<Rightarrow> gmp_poly \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow>
    rational_loop_state \<Rightarrow> bool" where
"rational_loop_invar \<delta> P todo0 acc0 st \<equiv>
  (let (i, todo, acc) = st in
    interval_vec_invar todo \<and>
    interval_vec_invar acc \<and>
    rational_gmp_interval_vec_ordered todo \<and>
    rational_queue_main_int P
      (rational_state_todo st)
      (rational_state_acc st) =
    rational_queue_main_int P todo0 acc0 \<and>
    int (rational_vec_len todo) +
      rational_todo_append_budget \<delta>
        (rational_state_todo st) + 2 <
      int (max_snat LENGTH(gmp_poly_len)) \<and>
    int (rational_vec_len acc) +
      rational_todo_acc_budget \<delta>
        (rational_state_todo st) + 1 <
      int (max_snat LENGTH(gmp_poly_len)))"

definition rational_loop_cond ::
  "rational_loop_state \<Rightarrow> bool" where
"rational_loop_cond st \<equiv>
  (let (i, todo, acc) = st in
    let (lna, _, _, _) = todo in i < length lna)"

lemma rational_loop_i_bound_from_todo_budget:
  assumes inv: "interval_vec_invar todo"
    and cond: "rational_loop_cond (i, todo, acc)"
    and cap: "int (rational_vec_len todo) + B + 2 <
      int (max_snat LENGTH(gmp_poly_len))"
    and nonneg: "0 \<le> B"
  shows "i + 1 < max_snat LENGTH(gmp_poly_len)"
  using assms
  unfolding rational_loop_cond_def
    interval_vec_invar_def
  by (cases todo) auto

lemma rational_loop_i_bound_from_todo_budget_tuple:
  assumes cond: "rational_loop_cond
      (i, (lna, lda, rnb, rdb), acc)"
    and cap: "int (length lna) + B + 2 <
      int (max_snat LENGTH(gmp_poly_len))"
    and nonneg: "0 \<le> B"
  shows "i + 1 < max_snat LENGTH(gmp_poly_len)"
proof -
  have i_lt: "i < length lna"
    using cond unfolding rational_loop_cond_def by simp
  have i_le_len: "int (i + 1) \<le> int (length lna)"
    using i_lt by simp
  have len_lt: "int (length lna) < int (max_snat LENGTH(gmp_poly_len))"
    using cap nonneg by linarith
  have "int (i + 1) < int (max_snat LENGTH(gmp_poly_len))"
    using i_le_len len_lt by linarith
  then show ?thesis by simp
qed

lemma rational_split_root_monadic_shape_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and raw: "interval_vec_pairs (lna, lda, rnb, rdb) ! i =
      ((na, da), (nb, db))"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    and mid_twice: "rat_of_pair (mn, md) * 2 =
      rat_of_pair (na, da) +
       rat_of_pair (nb, db)"
    and md_pos: "0 < md"
  shows "rational_split_root_monadic i (lna, lda, rnb, rdb)
      (alna, alda, arnb, ardb) na da nb db mn md \<le>
    SPEC (\<lambda>st'. case st' of
      (i', (tlna, tlda, trnb, trdb), (alna', alda', arnb', ardb')) \<Rightarrow>
        interval_vec_invar (tlna, tlda, trnb, trdb) \<and>
        interval_vec_invar (alna', alda', arnb', ardb') \<and>
        rational_gmp_interval_vec_ordered (tlna, tlda, trnb, trdb) \<and>
        int (length tlna) \<le> int (length lna) + 2 \<and>
        int (length alna') \<le> int (length alna) + 1)"
proof -
  have mid: "rat_of_pair (mn, md) =
      (rat_of_pair (na, da) +
       rat_of_pair (nb, db)) / 2"
    by (rule rational_mid_eq_from_times_two[OF mid_twice])
  show ?thesis
    apply (rule order_trans)
     apply (rule rational_split_root_monadic_exact_spec[
        OF todo_push2 acc_push])
    using assms mid
    apply (clarsimp simp: refine_pw_simps)
    apply (rule gmp_interval_vec_ordered_push_mid[
       OF todo_inv todo_ordered i_lt raw mid_twice md_pos])
    done
qed

lemma rational_split_nonroot_monadic_shape_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and raw: "interval_vec_pairs (lna, lda, rnb, rdb) ! i =
      ((na, da), (nb, db))"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and mid_twice: "rat_of_pair (mn, md) * 2 =
      rat_of_pair (na, da) +
       rat_of_pair (nb, db)"
    and md_pos: "0 < md"
  shows "rational_split_nonroot_monadic i (lna, lda, rnb, rdb)
      (alna, alda, arnb, ardb) na da nb db mn md \<le>
    SPEC (\<lambda>st'. case st' of
      (i', (tlna, tlda, trnb, trdb), (alna', alda', arnb', ardb')) \<Rightarrow>
        interval_vec_invar (tlna, tlda, trnb, trdb) \<and>
        interval_vec_invar (alna', alda', arnb', ardb') \<and>
        rational_gmp_interval_vec_ordered (tlna, tlda, trnb, trdb) \<and>
        int (length tlna) \<le> int (length lna) + 2 \<and>
        int (length alna') \<le> int (length alna) + 1)"
proof -
  have mid: "rat_of_pair (mn, md) =
      (rat_of_pair (na, da) +
       rat_of_pair (nb, db)) / 2"
    by (rule rational_mid_eq_from_times_two[OF mid_twice])
  show ?thesis
    apply (rule order_trans)
     apply (rule rational_split_nonroot_monadic_exact_spec[
        OF todo_push2])
    using assms mid
    apply (clarsimp simp: refine_pw_simps)
    apply (rule gmp_interval_vec_ordered_push_mid[
       OF todo_inv todo_ordered i_lt raw mid_twice md_pos])
    done
qed

lemma rational_split_monadic_shape_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and raw: "interval_vec_pairs (lna, lda, rnb, rdb) ! i =
      ((na, da), (nb, db))"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    and da_pos: "0 < da"
    and db_pos: "0 < db"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_split_monadic P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
      na da nb db \<le>
    SPEC (\<lambda>st'. case st' of
      (i', (tlna, tlda, trnb, trdb), (alna', alda', arnb', ardb')) \<Rightarrow>
        interval_vec_invar (tlna, tlda, trnb, trdb) \<and>
        interval_vec_invar (alna', alda', arnb', ardb') \<and>
        rational_gmp_interval_vec_ordered (tlna, tlda, trnb, trdb) \<and>
        int (length tlna) \<le> int (length lna) + 2 \<and>
        int (length alna') \<le> int (length alna) + 1)"
  using assms
  unfolding rational_split_monadic_def PR_CONST_def
  apply (refine_vcg rat_mid_monadic_spec)
    apply simp_all
  subgoal
    apply (rule order_trans)
    apply (rule poly_hom_eval_zero_mpz_monadic_spec)
      apply simp_all
    apply (clarsimp simp: refine_pw_simps)
    apply (intro conjI impI)
    subgoal
      apply (rule order_trans)
       apply (rule rational_split_root_monadic_shape_spec)
               apply simp_all
      done
    subgoal
      apply (rule order_trans)
       apply (rule rational_split_nonroot_monadic_shape_spec)
              apply simp_all
      done
    done
  done

lemma rational_queue_step_todo_extra_raw:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and raw: "interval_vec_pairs (lna, lda, rnb, rdb) ! i =
      ((na, da), (nb, db))"
    and P_len: "0 < length P"
  shows "rational_queue_step_todo_extra P
      (rational_state_todo
        (i, (lna, lda, rnb, rdb), acc)) =
    (let v = descartes_preprocess na da nb db P in
     if v = 0 \<or> v = 1 then 0 else 2)"
proof -
  let ?st = "(i, (lna, lda, rnb, rdb), acc)"
  have todo_cons:
    "rational_state_todo ?st =
      interval_of_pair ((na, da), (nb, db)) #
      tl (rational_state_todo ?st)"
    using rational_state_todo_cons_raw[OF todo_inv i_lt]
    by (simp add: raw)
  have da_pos: "0 < da" and db_pos: "0 < db"
    and cross: "na * db < nb * da"
    using gmp_interval_vec_ordered_componentsD[
      OF todo_inv todo_ordered i_lt raw] by simp_all
  have count_eq:
    "descartes_preprocess na da nb db P =
      descartes_list_int
        (fst (interval_of_pair ((na, da), (nb, db))))
        (snd (interval_of_pair ((na, da), (nb, db)))) P"
    using descartes_preprocess_eq_fast[
      OF P_len da_pos db_pos cross]
    by (simp add: interval_of_pair_def
      rat_of_pair_def)
  show ?thesis
    unfolding rational_queue_step_todo_extra_def
    apply (subst todo_cons)
    using count_eq
    apply (simp add: Let_def)
    done
qed

lemma rational_queue_step_acc_extra_raw:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and raw: "interval_vec_pairs (lna, lda, rnb, rdb) ! i =
      ((na, da), (nb, db))"
    and P_len: "0 < length P"
  shows "rational_queue_step_acc_extra P
      (rational_state_todo
        (i, (lna, lda, rnb, rdb), acc)) =
    (let v = descartes_preprocess na da nb db P in
     if v = 0 then 0 else 1)"
proof -
  let ?st = "(i, (lna, lda, rnb, rdb), acc)"
  have todo_cons:
    "rational_state_todo ?st =
      interval_of_pair ((na, da), (nb, db)) #
      tl (rational_state_todo ?st)"
    using rational_state_todo_cons_raw[OF todo_inv i_lt]
    by (simp add: raw)
  have da_pos: "0 < da" and db_pos: "0 < db"
    and cross: "na * db < nb * da"
    using gmp_interval_vec_ordered_componentsD[
      OF todo_inv todo_ordered i_lt raw] by simp_all
  have count_eq:
    "descartes_preprocess na da nb db P =
      descartes_list_int
        (fst (interval_of_pair ((na, da), (nb, db))))
        (snd (interval_of_pair ((na, da), (nb, db)))) P"
    using descartes_preprocess_eq_fast[
      OF P_len da_pos db_pos cross]
    by (simp add: interval_of_pair_def
      rat_of_pair_def)
  show ?thesis
    unfolding rational_queue_step_acc_extra_def
    apply (subst todo_cons)
    using count_eq
    apply (simp add: Let_def)
    done
qed

lemma rational_zero_monadic_shape_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
  shows "rational_zero_monadic
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
      na da nb db \<le>
    SPEC (\<lambda>st'. case st' of
      (i', (tlna, tlda, trnb, trdb), (alna', alda', arnb', ardb')) \<Rightarrow>
        interval_vec_invar (tlna, tlda, trnb, trdb) \<and>
        interval_vec_invar (alna', alda', arnb', ardb') \<and>
        rational_gmp_interval_vec_ordered (tlna, tlda, trnb, trdb) \<and>
        int (length tlna) \<le> int (length lna) \<and>
        int (length alna') \<le> int (length alna))"
  apply (rule order_trans)
   apply (rule rational_zero_monadic_spec)
  using assms
  apply (clarsimp simp: refine_pw_simps split: prod.splits)
  done

lemma rational_one_monadic_shape_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
  shows "rational_one_monadic
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
      na da nb db \<le>
    SPEC (\<lambda>st'. case st' of
      (i', (tlna, tlda, trnb, trdb), (alna', alda', arnb', ardb')) \<Rightarrow>
        interval_vec_invar (tlna, tlda, trnb, trdb) \<and>
        interval_vec_invar (alna', alda', arnb', ardb') \<and>
        rational_gmp_interval_vec_ordered (tlna, tlda, trnb, trdb) \<and>
        int (length tlna) \<le> int (length lna) \<and>
        int (length alna') \<le> int (length alna) + 1)"
  using assms
  unfolding rational_one_monadic_def
    interval_vec_pushable_def
    poly_push_coeff_monadic_def PR_CONST_def
  by (auto simp: refine_pw_simps)

lemma rational_after_get_shape_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and raw: "interval_vec_pairs (lna, lda, rnb, rdb) ! i =
      ((na, da), (nb, db))"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "(doN {
      v \<leftarrow> (PR_CONST descartes_preprocess_monadic)
        na da nb db P;
      if v = 0 then
        (PR_CONST rational_zero_monadic)
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
          na da nb db
      else if v = 1 then
        (PR_CONST rational_one_monadic)
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
          na da nb db
      else
        (PR_CONST rational_split_monadic) P
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))
          na da nb db
    }) \<le>
    SPEC (\<lambda>st'. case st' of
      (i', (tlna, tlda, trnb, trdb), (alna', alda', arnb', ardb')) \<Rightarrow>
        interval_vec_invar (tlna, tlda, trnb, trdb) \<and>
        interval_vec_invar (alna', alda', arnb', ardb') \<and>
        rational_gmp_interval_vec_ordered (tlna, tlda, trnb, trdb) \<and>
        int (length tlna) \<le>
          int (length lna) +
            rational_queue_step_todo_extra P
              (rational_state_todo
                (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))) \<and>
        int (length alna') \<le>
          int (length alna) +
            rational_queue_step_acc_extra P
              (rational_state_todo
                (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))))"
proof -
  let ?v = "descartes_preprocess na da nb db P"
  let ?st = "(i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
  have todo_extra:
    "rational_queue_step_todo_extra P
      (rational_state_todo ?st) =
    (if ?v = 0 \<or> ?v = 1 then 0 else 2)"
    using rational_queue_step_todo_extra_raw[
      OF todo_inv todo_ordered i_lt raw P_len] by simp
  have acc_extra:
    "rational_queue_step_acc_extra P
      (rational_state_todo ?st) =
    (if ?v = 0 then 0 else 1)"
    using rational_queue_step_acc_extra_raw[
      OF todo_inv todo_ordered i_lt raw P_len] by simp
  have da_pos: "0 < da" and db_pos: "0 < db"
    using gmp_interval_vec_ordered_componentsD[
      OF todo_inv todo_ordered i_lt raw] by simp_all
  have count:
    "descartes_preprocess_monadic na da nb db P \<le>
      RETURN ?v"
    using descartes_preprocess_monadic_correct[OF P_bound] .
  have branch:
    "(if ?v = 0 then
        rational_zero_monadic ?st na da nb db
      else if ?v = 1 then
        rational_one_monadic ?st na da nb db
      else
        rational_split_monadic P ?st na da nb db) \<le>
    SPEC (\<lambda>st'. case st' of
      (i', (tlna, tlda, trnb, trdb), (alna', alda', arnb', ardb')) \<Rightarrow>
        interval_vec_invar (tlna, tlda, trnb, trdb) \<and>
        interval_vec_invar (alna', alda', arnb', ardb') \<and>
        rational_gmp_interval_vec_ordered (tlna, tlda, trnb, trdb) \<and>
        int (length tlna) \<le>
          int (length lna) +
            rational_queue_step_todo_extra P
              (rational_state_todo ?st) \<and>
        int (length alna') \<le>
          int (length alna) +
            rational_queue_step_acc_extra P
              (rational_state_todo ?st))"
    using todo_extra acc_extra
    apply (cases "?v = 0")
    subgoal
      apply simp
      apply (rule order_trans)
       apply (rule rational_zero_monadic_shape_spec[
        OF todo_inv todo_ordered acc_inv])
      apply (simp add: refine_pw_simps)
      done
    subgoal
      apply (cases "?v = 1")
      subgoal
        apply simp
        apply (rule order_trans)
         apply (rule rational_one_monadic_shape_spec[
          OF todo_inv todo_ordered acc_inv acc_push])
        apply (simp add: refine_pw_simps)
        done
      subgoal
        apply simp
        apply (rule order_trans)
         apply (rule rational_split_monadic_shape_spec[
          OF todo_inv todo_ordered todo_push2 i_lt raw acc_inv acc_push
             da_pos db_pos P_len P_bound])
        apply (simp add: refine_pw_simps)
        done
      done
    done
  show ?thesis
    unfolding PR_CONST_def
    apply (rule dsc_nres_bind_RETURN_SPEC[where x="?v"])
     apply (rule count)
    apply (rule branch)
    done
qed

lemma rational_loop_body_idx_monadic_shape_spec:
  assumes todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and todo_ordered:
      "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and i_lt: "i < length lna"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    and todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    and i_bound: "i + 1 < max_snat LENGTH(gmp_poly_len)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_loop_body_idx_monadic P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)) \<le>
    SPEC (\<lambda>st'. case st' of
      (i', (tlna, tlda, trnb, trdb), (alna', alda', arnb', ardb')) \<Rightarrow>
        interval_vec_invar (tlna, tlda, trnb, trdb) \<and>
        interval_vec_invar (alna', alda', arnb', ardb') \<and>
        rational_gmp_interval_vec_ordered (tlna, tlda, trnb, trdb) \<and>
        int (length tlna) \<le>
          int (length lna) +
            rational_queue_step_todo_extra P
              (rational_state_todo
                (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))) \<and>
        int (length alna') \<le>
          int (length alna) +
            rational_queue_step_acc_extra P
              (rational_state_todo
                (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))))"
  using assms
  unfolding rational_loop_body_idx_monadic_def PR_CONST_def
  apply (refine_vcg interval_vec_copy_get_monadic_spec)
  subgoal by (clarsimp simp: interval_vec_invar_def split: prod.splits)
  subgoal by (clarsimp simp: interval_vec_invar_def split: prod.splits)
  subgoal by (clarsimp simp: interval_vec_invar_def split: prod.splits)
  subgoal by (clarsimp simp: interval_vec_invar_def split: prod.splits)
  subgoal by (clarsimp simp: interval_vec_invar_def split: prod.splits)
  subgoal by (clarsimp split: prod.splits)
  subgoal
    apply (clarsimp split: prod.splits)
    apply (rule order_trans[OF interval_vec_copy_get_monadic_spec])
      apply (clarsimp split: prod.splits)
     apply (clarsimp split: prod.splits)
    apply (clarsimp simp: refine_pw_simps split: prod.splits)
    apply (rule order_trans)
     apply (rule_tac na=ab and da=aaa and nb=aba and db=bb
      in rational_after_get_shape_spec[unfolded PR_CONST_def])
             apply (clarsimp split: prod.splits)+
    done
  done

lemma rational_loop_body_idx_monadic_progress_spec:
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and inv: "rational_loop_invar \<delta> P todo0 acc0
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
    and cond: "rational_loop_cond
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_loop_body_idx_monadic P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)) \<le>
    SPEC (\<lambda>st'.
      rational_queue_main_int P
        (rational_state_todo st')
        (rational_state_acc st') =
      rational_queue_main_int P todo0 acc0 \<and>
      rational_todo_mu_mset \<delta>
        (rational_state_todo st') <
      rational_todo_mu_mset \<delta>
        (rational_state_todo
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))))"
proof -
  let ?st = "(i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
  let ?todo = "rational_state_todo ?st"
  let ?acc = "rational_state_acc ?st"
  have todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and todo_ordered: "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and queue_main:
      "rational_queue_main_int P ?todo ?acc =
        rational_queue_main_int P todo0 acc0"
    and todo_cap:
      "int (length lna) + rational_todo_append_budget \<delta> ?todo + 2 <
        int (max_snat LENGTH(gmp_poly_len))"
    and acc_cap:
      "int (length alna) + rational_todo_acc_budget \<delta> ?todo + 1 <
        int (max_snat LENGTH(gmp_poly_len))"
    using inv
    unfolding rational_loop_invar_def
    by simp_all
  have i_lt: "i < length lna"
    using cond unfolding rational_loop_cond_def by simp
  have todo_budget_nonneg:
    "0 \<le> rational_todo_append_budget \<delta> ?todo"
    by simp
  have acc_budget_nonneg:
    "0 \<le> rational_todo_acc_budget \<delta> ?todo"
    by simp
  have todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    by (rule interval_vec_pushable2_from_budget_tuple[
      OF todo_inv todo_cap todo_budget_nonneg])
  have acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    by (rule interval_vec_pushable_from_budget_tuple[
      OF acc_inv acc_cap acc_budget_nonneg])
  have i_bound: "i + 1 < max_snat LENGTH(gmp_poly_len)"
    by (rule rational_loop_i_bound_from_todo_budget_tuple[
      OF cond todo_cap todo_budget_nonneg])
  have todo_ne: "?todo \<noteq> []"
    using i_lt interval_vec_to_list_length[OF todo_inv] by auto
  have ordered_todo: "\<And>I. I \<in> set ?todo \<Longrightarrow> fst I < snd I"
    by (rule rational_state_todo_orderedD[OF todo_ordered])
  have step_dec:
    "rational_todo_mu_mset \<delta>
        (fst (rational_queue_step_int P ?todo ?acc)) <
      rational_todo_mu_mset \<delta> ?todo"
    by (rule rational_queue_step_mu_mset_decreases[
      OF \<delta>_pos ordered_todo small_fast todo_ne])
  have step_main:
    "\<And>todo' acc'. (todo', acc') =
        rational_queue_step_int P ?todo ?acc \<Longrightarrow>
      rational_queue_main_int P todo' acc' =
        rational_queue_main_int P todo0 acc0"
  proof -
    fix todo' acc'
    assume eq: "(todo', acc') =
      rational_queue_step_int P ?todo ?acc"
    have "rational_queue_main_int P ?todo ?acc =
      (let (todo'', acc'') =
        rational_queue_step_int P ?todo ?acc
       in rational_queue_main_int P todo'' acc'')"
      by (rule rational_queue_main_int_step[OF todo_ne])
    also have "... = rational_queue_main_int P todo' acc'"
      using eq by (cases "rational_queue_step_int P ?todo ?acc") auto
    finally show "rational_queue_main_int P todo' acc' =
      rational_queue_main_int P todo0 acc0"
      using queue_main by simp
  qed
  let ?step = "rational_queue_step_int P ?todo ?acc"
  have post_if_step:
    "\<And>st'. (rational_state_todo st',
        rational_state_acc st') = ?step \<Longrightarrow>
      rational_queue_main_int P
        (rational_state_todo st')
        (rational_state_acc st') =
      rational_queue_main_int P todo0 acc0 \<and>
      rational_todo_mu_mset \<delta>
        (rational_state_todo st') <
      rational_todo_mu_mset \<delta> ?todo"
  proof -
    fix st'
    assume st_eq:
      "(rational_state_todo st',
        rational_state_acc st') = ?step"
    have main_pres:
      "rational_queue_main_int P
        (rational_state_todo st')
        (rational_state_acc st') =
      rational_queue_main_int P todo0 acc0"
      by (rule step_main) (simp add: st_eq)
    have todo_eq:
      "rational_state_todo st' = fst ?step"
      using st_eq by (metis fst_conv)
    have dec:
      "rational_todo_mu_mset \<delta>
        (rational_state_todo st') <
       rational_todo_mu_mset \<delta> ?todo"
      using step_dec todo_eq by simp
    show "rational_queue_main_int P
        (rational_state_todo st')
        (rational_state_acc st') =
      rational_queue_main_int P todo0 acc0 \<and>
      rational_todo_mu_mset \<delta>
        (rational_state_todo st') <
      rational_todo_mu_mset \<delta> ?todo"
      using main_pres dec by simp
  qed
  have spec_refine:
    "SPEC (\<lambda>st'.
      (rational_state_todo st',
       rational_state_acc st') = ?step) \<le>
    SPEC (\<lambda>st'.
      rational_queue_main_int P
        (rational_state_todo st')
        (rational_state_acc st') =
      rational_queue_main_int P todo0 acc0 \<and>
      rational_todo_mu_mset \<delta>
        (rational_state_todo st') <
      rational_todo_mu_mset \<delta> ?todo)"
    using post_if_step by (auto simp: pw_le_iff refine_pw_simps)
  show ?thesis
    by (rule order_trans[
      OF rational_loop_body_idx_monadic_queue_step_spec[
	        OF todo_inv todo_ordered i_lt acc_inv acc_push todo_push2
	           i_bound P_len P_bound] spec_refine])
qed

lemma rational_loop_invar_stepI:
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered_todo: "\<And>I. I \<in> set todo_abs \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and todo_cap:
      "int (length lna) + rational_todo_append_budget \<delta> todo_abs + 2 <
        int (max_snat LENGTH(gmp_poly_len))"
    and acc_cap:
      "int (length alna) + rational_todo_acc_budget \<delta> todo_abs + 1 <
        int (max_snat LENGTH(gmp_poly_len))"
    and todo_inv': "interval_vec_invar
      (tlna, tlda, trnb, trdb)"
    and acc_inv': "interval_vec_invar
      (alna', alda', arnb', ardb')"
    and todo_ordered': "rational_gmp_interval_vec_ordered
      (tlna, tlda, trnb, trdb)"
    and todo_len_le:
      "int (length tlna) \<le>
        int (length lna) + rational_queue_step_todo_extra P todo_abs"
    and acc_len_le:
      "int (length alna') \<le>
        int (length alna) + rational_queue_step_acc_extra P todo_abs"
    and step_eq:
      "(drop i' (interval_vec_to_list (tlna, tlda, trnb, trdb)),
        interval_vec_to_list (alna', alda', arnb', ardb')) =
      rational_queue_step_int P todo_abs acc_abs"
    and main_eq:
      "rational_queue_main_int P
        (drop i' (interval_vec_to_list (tlna, tlda, trnb, trdb)))
        (interval_vec_to_list (alna', alda', arnb', ardb')) =
      rational_queue_main_int P todo0 acc0"
  shows "rational_loop_invar \<delta> P todo0 acc0
    (i', (tlna, tlda, trnb, trdb), (alna', alda', arnb', ardb'))"
proof -
  let ?todo' =
    "drop i' (interval_vec_to_list (tlna, tlda, trnb, trdb))"
  have todo_cap':
    "int (length tlna) + rational_todo_append_budget \<delta> ?todo' + 2 <
      int (max_snat LENGTH(gmp_poly_len))"
    by (rule rational_queue_step_todo_capacity_preserved_pair_eq[
      OF \<delta>_pos ordered_todo small_fast todo_cap todo_len_le step_eq])
  have acc_cap':
    "int (length alna') + rational_todo_acc_budget \<delta> ?todo' + 1 <
      int (max_snat LENGTH(gmp_poly_len))"
    by (rule rational_queue_step_acc_capacity_preserved_pair_eq[
      OF \<delta>_pos ordered_todo small_fast acc_cap acc_len_le step_eq])
  show ?thesis
    using todo_inv' acc_inv' todo_ordered' main_eq todo_cap' acc_cap'
    unfolding rational_loop_invar_def
    by simp
qed

lemma rational_loop_body_idx_monadic_invar_spec:
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and inv: "rational_loop_invar \<delta> P todo0 acc0
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
    and cond: "rational_loop_cond
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_loop_body_idx_monadic P
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb)) \<le>
    SPEC (\<lambda>st'.
      rational_loop_invar \<delta> P todo0 acc0 st' \<and>
      rational_todo_mu_mset \<delta>
        (rational_state_todo st') <
      rational_todo_mu_mset \<delta>
        (rational_state_todo
          (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))))"
proof -
  let ?st = "(i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
  let ?todo = "rational_state_todo ?st"
  let ?acc = "rational_state_acc ?st"
  let ?step = "rational_queue_step_int P ?todo ?acc"
  let ?body = "rational_loop_body_idx_monadic P ?st"
  let ?shape = "\<lambda>st'. case st' of
      (i', (tlna, tlda, trnb, trdb), (alna', alda', arnb', ardb')) \<Rightarrow>
        interval_vec_invar (tlna, tlda, trnb, trdb) \<and>
        interval_vec_invar (alna', alda', arnb', ardb') \<and>
        rational_gmp_interval_vec_ordered (tlna, tlda, trnb, trdb) \<and>
        int (length tlna) \<le>
          int (length lna) +
            rational_queue_step_todo_extra P ?todo \<and>
        int (length alna') \<le>
          int (length alna) +
            rational_queue_step_acc_extra P ?todo"
  let ?queue = "\<lambda>st'.
      (rational_state_todo st',
       rational_state_acc st') = ?step"
  let ?progress = "\<lambda>st'.
      rational_queue_main_int P
        (rational_state_todo st')
        (rational_state_acc st') =
      rational_queue_main_int P todo0 acc0 \<and>
      rational_todo_mu_mset \<delta>
        (rational_state_todo st') <
      rational_todo_mu_mset \<delta> ?todo"
  have todo_inv: "interval_vec_invar (lna, lda, rnb, rdb)"
    and acc_inv: "interval_vec_invar (alna, alda, arnb, ardb)"
    and todo_ordered: "rational_gmp_interval_vec_ordered (lna, lda, rnb, rdb)"
    and todo_cap:
      "int (length lna) + rational_todo_append_budget \<delta> ?todo + 2 <
        int (max_snat LENGTH(gmp_poly_len))"
    and acc_cap:
      "int (length alna) + rational_todo_acc_budget \<delta> ?todo + 1 <
        int (max_snat LENGTH(gmp_poly_len))"
    using inv
    unfolding rational_loop_invar_def
    by simp_all
  have i_lt: "i < length lna"
    using cond unfolding rational_loop_cond_def by simp
  have todo_budget_nonneg:
    "0 \<le> rational_todo_append_budget \<delta> ?todo"
    by simp
  have acc_budget_nonneg:
    "0 \<le> rational_todo_acc_budget \<delta> ?todo"
    by simp
  have todo_push2: "interval_vec_pushable2 (lna, lda, rnb, rdb)"
    by (rule interval_vec_pushable2_from_budget_tuple[
      OF todo_inv todo_cap todo_budget_nonneg])
  have acc_push: "interval_vec_pushable (alna, alda, arnb, ardb)"
    by (rule interval_vec_pushable_from_budget_tuple[
      OF acc_inv acc_cap acc_budget_nonneg])
  have i_bound: "i + 1 < max_snat LENGTH(gmp_poly_len)"
    by (rule rational_loop_i_bound_from_todo_budget_tuple[
      OF cond todo_cap todo_budget_nonneg])
  have ordered_todo: "\<And>I. I \<in> set ?todo \<Longrightarrow> fst I < snd I"
    by (rule rational_state_todo_orderedD[OF todo_ordered])
  have ordered_todo_drop:
    "\<And>I. I \<in> set (drop i
        (interval_vec_to_list (lna, lda, rnb, rdb))) \<Longrightarrow>
      fst I < snd I"
    using ordered_todo by simp
  have todo_cap_drop:
    "int (length lna) + rational_todo_append_budget \<delta>
        (drop i (interval_vec_to_list (lna, lda, rnb, rdb))) + 2 <
      int (max_snat LENGTH(gmp_poly_len))"
    using todo_cap by simp
  have acc_cap_drop:
    "int (length alna) + rational_todo_acc_budget \<delta>
        (drop i (interval_vec_to_list (lna, lda, rnb, rdb))) + 1 <
      int (max_snat LENGTH(gmp_poly_len))"
    using acc_cap by simp

  have shape_le: "?body \<le> SPEC ?shape"
    by (rule rational_loop_body_idx_monadic_shape_spec[
      OF todo_inv todo_ordered i_lt acc_inv acc_push todo_push2
         i_bound P_len P_bound])
  have queue_le: "?body \<le> SPEC ?queue"
    by (rule rational_loop_body_idx_monadic_queue_step_spec[
      OF todo_inv todo_ordered i_lt acc_inv acc_push todo_push2
         i_bound P_len P_bound])
  have progress_le: "?body \<le> SPEC ?progress"
    by (rule rational_loop_body_idx_monadic_progress_spec[
      OF \<delta>_pos small_fast inv cond P_len P_bound])
  have shape_queue_le:
    "?body \<le> SPEC (\<lambda>st'. ?shape st' \<and> ?queue st')"
    by (rule dsc_nres_SPEC_conjI[OF shape_le queue_le])
  have combined_le:
    "?body \<le> SPEC (\<lambda>st'. (?shape st' \<and> ?queue st') \<and>
      ?progress st')"
    by (rule dsc_nres_SPEC_conjI[OF shape_queue_le progress_le])

  show ?thesis
  proof (rule order_trans[OF combined_le])
    show "SPEC (\<lambda>st'. (?shape st' \<and> ?queue st') \<and>
        ?progress st') \<le>
      SPEC (\<lambda>st'.
        rational_loop_invar \<delta> P todo0 acc0 st' \<and>
        rational_todo_mu_mset \<delta>
          (rational_state_todo st') <
        rational_todo_mu_mset \<delta> ?todo)"
      using \<delta>_pos ordered_todo small_fast todo_cap acc_cap
      apply (clarsimp simp: pw_le_iff refine_pw_simps split: prod.splits)
      subgoal
        by (rule rational_loop_invar_stepI[
          where todo_abs="drop i
            (interval_vec_to_list (lna, lda, rnb, rdb))"
            and acc_abs="interval_vec_to_list
              (alna, alda, arnb, ardb)",
          OF \<delta>_pos ordered_todo_drop small_fast todo_cap_drop acc_cap_drop])
          assumption+
      done
  qed
qed

lemma rational_state_todo_empty_iff:
  assumes "interval_vec_invar todo"
  shows "rational_state_todo (i, todo, acc) = [] \<longleftrightarrow>
    \<not> rational_loop_cond (i, todo, acc)"
  using assms
  unfolding rational_state_todo_def
    rational_loop_cond_def
  by (cases todo) (auto simp: interval_vec_to_list_length)

lemma rational_state_todo_nonempty_iff:
  assumes "interval_vec_invar todo"
  shows "rational_state_todo (i, todo, acc) \<noteq> [] \<longleftrightarrow>
    rational_loop_cond (i, todo, acc)"
  using rational_state_todo_empty_iff[OF assms, of i acc]
  by blast

sepref_register "PR_CONST rational_loop_cond"
  :: "rational_loop_state \<Rightarrow> bool"

definition rational_loop_cond_mop_monadic ::
  "rational_loop_state \<Rightarrow> bool nres" where
"rational_loop_cond_mop_monadic st \<equiv> doN {
  let (i, todo, acc) = st;
  len \<leftarrow> (PR_CONST interval_vec_length_monadic) todo;
  RETURN (i < len)
}"

lemma rational_loop_cond_mop_monadic_eq:
  "rational_loop_cond_mop_monadic =
    RETURN o rational_loop_cond"
  unfolding rational_loop_cond_mop_monadic_def
    rational_loop_cond_def
    interval_vec_length_monadic_def poly_length_monadic_def PR_CONST_def
  by (auto intro!: ext split: prod.splits)

sepref_definition rational_loop_cond_impl [llvm_inline] is
  "rational_loop_cond_mop_monadic" ::
  "rational_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding rational_loop_cond_mop_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma rational_loop_cond_impl_hnr[sepref_fr_rules]:
  "(rational_loop_cond_impl,
    RETURN o (PR_CONST rational_loop_cond)) \<in>
    rational_loop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using rational_loop_cond_impl.refine
  by (simp add: rational_loop_cond_mop_monadic_eq PR_CONST_def)

definition rational_loop_monadic ::
  "gmp_poly \<Rightarrow> gmp_interval_vec \<Rightarrow> gmp_interval_vec \<Rightarrow>
    rational_loop_state nres" where
"rational_loop_monadic P todo acc \<equiv> doN {
  st \<leftarrow> WHILET
    (\<lambda>st. (PR_CONST rational_loop_cond) st)
    (\<lambda>st. (PR_CONST rational_loop_body_idx_monadic) P st)
    (0, todo, acc);
  RETURN st
}"

lemma rational_todo_mu_mset_rel_wf:
  "wf {(st' :: rational_loop_state, st).
      rational_todo_mu_mset \<delta> (rational_state_todo st') <
      rational_todo_mu_mset \<delta> (rational_state_todo st)}"
proof -
  have wf_ms_pred: "wfp ((<) :: nat multiset \<Rightarrow> nat multiset \<Rightarrow> bool)"
    by simp
  have wf_ms:
    "wf ({(x, y). x < y} :: (nat multiset \<times> nat multiset) set)"
    using wf_ms_pred by (simp add: wfp_def)
  show ?thesis
    using wf_inv_image[OF wf_ms,
      of "\<lambda>st. rational_todo_mu_mset \<delta>
        (rational_state_todo st)"]
    by (simp add: inv_image_def)
qed

sepref_register "PR_CONST rational_loop_monadic"
  :: "gmp_poly \<Rightarrow> gmp_interval_vec \<Rightarrow> gmp_interval_vec \<Rightarrow>
      rational_loop_state nres"

sepref_definition rational_loop_impl [llvm_inline] is
  "uncurry2 rational_loop_monadic" ::
  "[\<lambda>((P, _), _).
      0 < length P \<and> length P + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a gmp_interval_vec_assn\<^sup>d *\<^sub>a
      gmp_interval_vec_assn\<^sup>d \<rightarrow> rational_loop_state_assn"
  unfolding rational_loop_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
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

lemma rational_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry2 rational_loop_impl,
    uncurry2 (PR_CONST rational_loop_monadic)) \<in>
    [\<lambda>((P, _), _).
      0 < length P \<and> length P + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a gmp_interval_vec_assn\<^sup>d *\<^sub>a
        gmp_interval_vec_assn\<^sup>d \<rightarrow> rational_loop_state_assn"
  using rational_loop_impl.refine
  by (simp add: PR_CONST_def)

definition dsc_rational_main_list ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_interval_vec nres" where
"dsc_rational_main_list na da nb db P \<equiv> doN {
  todo0 \<leftarrow> (PR_CONST interval_vec_empty_sz_monadic) 1;
  c_na \<leftarrow> RETURN (COPY na);
  c_da \<leftarrow> RETURN (COPY da);
  c_nb \<leftarrow> RETURN (COPY nb);
  c_db \<leftarrow> RETURN (COPY db);
  ASSERT (interval_vec_pushable todo0);
  todo1 \<leftarrow> (PR_CONST interval_vec_push_monadic) todo0 c_na c_da c_nb c_db;
  acc0 \<leftarrow> (PR_CONST interval_vec_empty_sz_monadic) 1;
  st \<leftarrow> (PR_CONST rational_loop_monadic) P todo1 acc0;
  let (i, todo, acc) = st;
  (PR_CONST interval_vec_free_monadic) todo;
  RETURN acc
}"

sepref_register "PR_CONST dsc_rational_main_list"
  :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow>
      gmp_interval_vec nres"

sepref_definition dsc_rational_main_list_impl [llvm_code] is
  "uncurry4 dsc_rational_main_list" ::
  "[\<lambda>((((_, _), _), _), P).
      0 < length P \<and> length P + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
  unfolding dsc_rational_main_list_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

end
