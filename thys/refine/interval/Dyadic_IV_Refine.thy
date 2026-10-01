theory Dyadic_IV_Refine
  imports "IsaRRI_LLVM.Dyadic_Interval"
begin

text \<open>Dyadic-interval refinement plumbing, shared by every worklist keystone.
  Main definitions: \<open>dyadic_iv_node_iv\<close> / \<open>_of\<close> (a node's rational interval),
  \<open>dyadic_iv_acc_ivs\<close> / \<open>_todo_ivs\<close> (the interval sets of the two columns),
  \<open>dyadic_iv_interval_mu\<close> / \<open>_todo_mu_mset\<close> / \<open>_phi\<close> / \<open>_alpha*\<close> (the termination measures) and
  the four budget predicates.

  What is not here: \<open>loop_abs\<close>, \<open>refine_invar\<close>, \<open>newdsc_int_spec\<close> and \<open>newdsc_sound_complete_spec\<close>
  are parameterised by each solver's own loop (\<open>nlr_\<close> in \<open>Newton_Loop_Refine\<close>, \<open>blr_\<close> in
  \<open>Bail_Loop_Refine\<close>), and \<open>alpha\<close>, \<open>alpha_acc\<close>, \<open>alpha_todo\<close> and \<open>newdsc_int_pre\<close> mention the
  solver state types, which live above this theory.\<close>

definition dyadic_iv_unit_dyadic :: "rat \<times> rat \<Rightarrow> bool" where
"dyadic_iv_unit_dyadic ab \<longleftrightarrow> (\<exists>l k. fst ab = of_int l / 2 ^ k \<and> snd ab = of_int (l + 1) / 2 ^ k)"

definition dyadic_iv_node_iv :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (rat \<times> rat)" where
"dyadic_iv_node_iv l0 r0 k0 l r k =
  (let lo = dyadic_rat l0 k0; hi = dyadic_rat r0 k0 in
   ((dyadic_rat l k - lo) / (hi - lo), (dyadic_rat r k - lo) / (hi - lo)))"

definition dyadic_iv_node_iv_of :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> ((int \<times> int) \<times> nat) \<Rightarrow> (rat \<times> rat)" where
"dyadic_iv_node_iv_of l0 r0 k0 t = dyadic_iv_node_iv l0 r0 k0 (fst (fst t)) (snd (fst t)) (snd t)"

definition dyadic_iv_acc_ivs :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> ((int \<times> int) \<times> nat) list \<Rightarrow> (rat \<times> rat) list" where
"dyadic_iv_acc_ivs l0 r0 k0 acc = map (dyadic_iv_node_iv_of l0 r0 k0) acc"

definition dyadic_iv_todo_ivs :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (((int \<times> int) \<times> nat) \<times> gmp_poly) list \<Rightarrow> (rat \<times> rat) list" where
"dyadic_iv_todo_ivs l0 r0 k0 todo = map (\<lambda>nd. dyadic_iv_node_iv_of l0 r0 k0 (fst nd)) todo"

definition dyadic_iv_rat_intervals_of :: "gmp_dyadic_interval_vec \<Rightarrow> (rat \<times> rat) list" where
"dyadic_iv_rat_intervals_of acc = dyadic_interval_vec_to_list acc"

definition dyadic_iv_interval_mu :: "real \<Rightarrow> (rat \<times> rat) \<Rightarrow> nat" where
"dyadic_iv_interval_mu \<delta> I = mu \<delta> (of_rat (fst I)) (of_rat (snd I))"

definition dyadic_iv_todo_mu_mset :: "real \<Rightarrow> (rat \<times> rat) list \<Rightarrow> nat multiset" where
"dyadic_iv_todo_mu_mset \<delta> todo = mset (map (dyadic_iv_interval_mu \<delta>) todo)"

definition dyadic_iv_phi :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (rat \<times> rat) \<Rightarrow> (rat \<times> rat)" where
"dyadic_iv_phi l0 r0 k0 ab =
  (let lo = dyadic_rat l0 k0; hi = dyadic_rat r0 k0 in
   (lo + fst ab * (hi - lo), lo + snd ab * (hi - lo)))"


definition dyadic_iv_cs_invar :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"dyadic_iv_cs_invar c cnt \<equiv>
   (c = 0) = (cnt = 0) \<and> (c = 1) = (cnt = 1) \<and> (2 \<le> c) = (2 \<le> cnt)
   \<and> (4 \<le> c \<longrightarrow> c = cnt + 2)"


definition dyadic_iv_interval_acc_budget :: "real \<Rightarrow> (rat \<times> rat) \<Rightarrow> int" where
"dyadic_iv_interval_acc_budget \<delta> I = int ((2::nat) ^ Suc (dyadic_iv_interval_mu \<delta> I)) - 1"

definition dyadic_iv_interval_todo_budget :: "real \<Rightarrow> (rat \<times> rat) \<Rightarrow> int" where
"dyadic_iv_interval_todo_budget \<delta> I = int ((2::nat) ^ Suc (dyadic_iv_interval_mu \<delta> I)) - 2"

definition dyadic_iv_todo_acc_budget :: "real \<Rightarrow> (rat \<times> rat) list \<Rightarrow> int" where
"dyadic_iv_todo_acc_budget \<delta> todo = sum_list (map (dyadic_iv_interval_acc_budget \<delta>) todo)"

definition dyadic_iv_todo_append_budget :: "real \<Rightarrow> (rat \<times> rat) list \<Rightarrow> int" where
"dyadic_iv_todo_append_budget \<delta> todo = sum_list (map (dyadic_iv_interval_todo_budget \<delta>) todo)"

end
