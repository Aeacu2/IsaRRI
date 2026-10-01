theory Rational_Refine
  imports Rational_Solver
begin

text \<open>Refines the plain-endpoint Descartes solver (\<open>Rational_Solver\<close>) end to end to
  \<open>dsc_int\<close>. Bridge lemmas \<open>dsc_int_sound_real_image\<close> / \<open>dsc_int_complete_real_image\<close> connect
  the multiset specification to the real-root soundness and completeness statements.\<close>

section \<open>Loop-Body Wrappers and WHILET Loop Theorem\<close>

lemma rational_loop_monadic_body_invar_spec:
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and inv: "rational_loop_invar \<delta> P todo0 acc0 st"
    and cond: "rational_loop_cond st"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_loop_body_idx_monadic P st \<le>
    SPEC (\<lambda>st'.
      rational_loop_invar \<delta> P todo0 acc0 st' \<and>
      rational_todo_mu_mset \<delta>
        (rational_state_todo st') <
      rational_todo_mu_mset \<delta>
        (rational_state_todo st))"
proof -
  obtain i todo acc where st_eq: "st = (i, todo, acc)"
    by (cases st) auto
  obtain lna lda rnb rdb where todo_eq:
    "todo = (lna, lda, rnb, rdb)"
    by (cases todo) auto
  obtain alna alda arnb ardb where acc_eq:
    "acc = (alna, alda, arnb, ardb)"
    by (cases acc) auto
  have inv':
    "rational_loop_invar \<delta> P todo0 acc0
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
    using inv by (simp add: st_eq todo_eq acc_eq)
  have cond':
    "rational_loop_cond
      (i, (lna, lda, rnb, rdb), (alna, alda, arnb, ardb))"
    using cond by (simp add: st_eq todo_eq acc_eq)
  show ?thesis
    unfolding st_eq todo_eq acc_eq
    by (rule rational_loop_body_idx_monadic_invar_spec[
      OF \<delta>_pos small_fast inv' cond' P_len P_bound])
qed

lemma rational_loop_monadic_body_invar_rel_spec:
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and inv: "rational_loop_invar \<delta> P todo0 acc0 st"
    and cond: "rational_loop_cond st"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_loop_body_idx_monadic P st \<le>
    SPEC (\<lambda>st'.
      rational_loop_invar \<delta> P todo0 acc0 st' \<and>
      (st', st) \<in> {(st', st).
        rational_todo_mu_mset \<delta>
          (rational_state_todo st') <
        rational_todo_mu_mset \<delta>
          (rational_state_todo st)})"
proof (rule order_trans)
  show "rational_loop_body_idx_monadic P st \<le>
    SPEC (\<lambda>st'.
      rational_loop_invar \<delta> P todo0 acc0 st' \<and>
      rational_todo_mu_mset \<delta>
        (rational_state_todo st') <
      rational_todo_mu_mset \<delta>
        (rational_state_todo st))"
    by (rule rational_loop_monadic_body_invar_spec[
      OF \<delta>_pos small_fast inv cond P_len P_bound])
  show "SPEC (\<lambda>st'.
      rational_loop_invar \<delta> P todo0 acc0 st' \<and>
      rational_todo_mu_mset \<delta>
        (rational_state_todo st') <
      rational_todo_mu_mset \<delta>
        (rational_state_todo st)) \<le>
    SPEC (\<lambda>st'.
      rational_loop_invar \<delta> P todo0 acc0 st' \<and>
      (st', st) \<in> {(st', st).
        rational_todo_mu_mset \<delta>
          (rational_state_todo st') <
        rational_todo_mu_mset \<delta>
          (rational_state_todo st)})"
    by (auto simp: pw_le_iff refine_pw_simps)
qed

lemma rational_loop_monadic_not_cond_todo_empty:
  assumes inv: "rational_loop_invar \<delta> P todo0 acc0 st"
    and not_cond: "\<not> rational_loop_cond st"
  shows "rational_state_todo st = []"
proof -
  obtain i todo acc where st_eq: "st = (i, todo, acc)"
    by (cases st) auto
  have todo_inv: "interval_vec_invar todo"
    using inv by (simp add: st_eq rational_loop_invar_def)
  show ?thesis
    using rational_state_todo_empty_iff[OF todo_inv, of i acc]
      not_cond
    by (simp add: st_eq)
qed

lemma rational_loop_invar_empty_acc:
  assumes inv: "rational_loop_invar \<delta> P todo0 acc0 st"
    and empty: "rational_state_todo st = []"
  shows "rational_state_acc st =
    rational_queue_main_int P todo0 acc0"
proof -
  obtain i todo acc where st_eq: "st = (i, todo, acc)"
    by (cases st) auto
  have main_eq:
    "rational_queue_main_int P
      (rational_state_todo st)
      (rational_state_acc st) =
     rational_queue_main_int P todo0 acc0"
    using inv unfolding rational_loop_invar_def
    by (simp add: st_eq)
  show ?thesis
    using main_eq empty by simp
qed

lemma rational_loop_invar_empty_acc_vec:
  assumes inv: "rational_loop_invar \<delta> P todo0 acc0
      (i, todo, acc)"
    and empty: "rational_state_todo (i, todo, acc) = []"
  shows "interval_vec_to_list acc =
    rational_queue_main_int P todo0 acc0"
  using assms
  unfolding rational_loop_invar_def
  by simp

lemma rational_loop_monadic_spec:
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and init: "rational_loop_invar \<delta> P todo0 acc0
      (0, todo, acc)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "rational_loop_monadic P todo acc \<le>
    SPEC (\<lambda>st.
      rational_loop_invar \<delta> P todo0 acc0 st \<and>
      \<not> rational_loop_cond st \<and>
      rational_state_todo st = [])"
  using assms
  unfolding rational_loop_monadic_def PR_CONST_def
  apply (refine_vcg WHILET_rule[
    where I="rational_loop_invar \<delta> P todo0 acc0"
      and R="{(st', st).
        rational_todo_mu_mset \<delta>
          (rational_state_todo st') <
        rational_todo_mu_mset \<delta>
          (rational_state_todo st)}"])
  subgoal
    by (rule rational_todo_mu_mset_rel_wf)
  subgoal for s
    by (rule rational_loop_monadic_body_invar_rel_spec[
      OF \<delta>_pos small_fast _ _ P_len P_bound])
  subgoal premises prems
    by (rule rational_loop_monadic_not_cond_todo_empty[
      OF prems(6) prems(7)])
  done

section \<open>Main-List Wrapper Allocation Facts\<close>

lemma gmp_interval_vec_empty_pushable:
  assumes inv: "interval_vec_invar v"
    and empty: "interval_vec_pairs v = []"
  shows "interval_vec_pushable v"
proof -
  obtain lna lda rnb rdb where v_eq: "v = (lna, lda, rnb, rdb)"
    by (cases v) auto
  have len: "length lna = 0"
    using interval_vec_pairs_length[OF inv[unfolded v_eq]]
      empty
    by (simp add: v_eq)
  show ?thesis
    using inv len
    unfolding v_eq interval_vec_invar_def
      interval_vec_pushable_def
    by (simp add: max_snat_def)
qed

lemma gmp_interval_vec_singleton_ordered:
  assumes da_pos: "0 < da"
    and db_pos: "0 < db"
    and less: "rat_of_pair (na, da) <
      rat_of_pair (nb, db)"
    and inv: "interval_vec_invar todo"
    and list: "interval_vec_to_list todo =
      [interval_of_pair ((na, da), (nb, db))]"
    and pairs: "interval_vec_pairs todo =
      [((na, da), (nb, db))]"
  shows "rational_gmp_interval_vec_ordered todo"
  using interval_pair_orderedI[OF da_pos db_pos less] pairs
  unfolding rational_gmp_interval_vec_ordered_def
  by simp

lemma interval_vec_push_monadic_spec_state:
  assumes inv: "interval_vec_invar v"
    and push: "interval_vec_pushable v"
  shows "interval_vec_push_monadic v na da nb db \<le>
    SPEC (\<lambda>v'. interval_vec_invar v' \<and>
      interval_vec_pairs v' =
        interval_vec_pairs v @ [((na, da), (nb, db))] \<and>
      interval_vec_to_list v' =
        interval_vec_to_list v @
          [interval_of_pair ((na, da), (nb, db))])"
proof -
  obtain lna lda rnb rdb where v_eq: "v = (lna, lda, rnb, rdb)"
    by (cases v) auto
  show ?thesis
    unfolding v_eq
    by (rule interval_vec_push_monadic_spec[
      OF inv[unfolded v_eq] push[unfolded v_eq]])
qed

lemma rational_loop_invar_initial:
  assumes da_pos: "0 < da"
    and db_pos: "0 < db"
    and less: "rat_of_pair (na, da) <
      rat_of_pair (nb, db)"
    and todo_inv: "interval_vec_invar todo"
    and todo_list: "interval_vec_to_list todo =
      [interval_of_pair ((na, da), (nb, db))]"
    and todo_pairs: "interval_vec_pairs todo =
      [((na, da), (nb, db))]"
    and acc_inv: "interval_vec_invar acc"
    and acc_list: "interval_vec_to_list acc = []"
    and todo_cap:
      "1 + rational_todo_append_budget \<delta>
          [interval_of_pair ((na, da), (nb, db))] + 2 <
        int (max_snat LENGTH(gmp_poly_len))"
    and acc_cap:
      "rational_todo_acc_budget \<delta>
          [interval_of_pair ((na, da), (nb, db))] + 1 <
        int (max_snat LENGTH(gmp_poly_len))"
  shows "rational_loop_invar \<delta> P
    [interval_of_pair ((na, da), (nb, db))] []
    (0, todo, acc)"
proof -
  have ordered: "rational_gmp_interval_vec_ordered todo"
    by (rule gmp_interval_vec_singleton_ordered[
      OF da_pos db_pos less todo_inv todo_list todo_pairs])
  have todo_len: "rational_vec_len todo = 1"
  proof -
    obtain lna lda rnb rdb where todo_eq: "todo = (lna, lda, rnb, rdb)"
      by (cases todo) auto
    have "length (interval_vec_to_list (lna, lda, rnb, rdb)) =
      length lna"
      by (rule interval_vec_to_list_length[
        OF todo_inv[unfolded todo_eq]])
    then show ?thesis
      using todo_list unfolding todo_eq by simp
  qed
  have acc_len: "rational_vec_len acc = 0"
  proof -
    obtain alna alda arnb ardb where acc_eq: "acc = (alna, alda, arnb, ardb)"
      by (cases acc) auto
    have "length (interval_vec_to_list (alna, alda, arnb, ardb)) =
      length alna"
      by (rule interval_vec_to_list_length[
        OF acc_inv[unfolded acc_eq]])
    then show ?thesis
      using acc_list unfolding acc_eq by simp
  qed
  show ?thesis
    using todo_inv acc_inv ordered todo_list acc_list todo_cap acc_cap
      todo_len acc_len
    unfolding rational_loop_invar_def
    by simp
qed

lemma dsc_rational_main_list_spec:
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and da_pos: "0 < da"
    and db_pos: "0 < db"
    and less: "rat_of_pair (na, da) <
      rat_of_pair (nb, db)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and todo_cap:
      "1 + rational_todo_append_budget \<delta>
          [interval_of_pair ((na, da), (nb, db))] + 2 <
        int (max_snat LENGTH(gmp_poly_len))"
    and acc_cap:
      "rational_todo_acc_budget \<delta>
          [interval_of_pair ((na, da), (nb, db))] + 1 <
        int (max_snat LENGTH(gmp_poly_len))"
  shows "dsc_rational_main_list na da nb db P \<le>
    SPEC (\<lambda>acc.
      interval_vec_invar acc \<and>
      interval_vec_to_list acc =
        rational_queue_main_int P
          [interval_of_pair ((na, da), (nb, db))] [])"
  unfolding dsc_rational_main_list_def PR_CONST_def COPY_def
  apply (refine_vcg interval_vec_empty_sz_monadic_spec)
   apply (clarsimp intro!: gmp_interval_vec_empty_pushable)
  apply (rule order_trans[OF interval_vec_push_monadic_spec_state])
    apply simp
   apply assumption
  apply (clarsimp simp: refine_pw_simps)
  apply (refine_vcg
    interval_vec_empty_sz_monadic_spec
    rational_loop_monadic_spec)
       apply (rule \<delta>_pos)
      apply (rule small_fast; assumption)
     apply (rule rational_loop_invar_initial[
        OF da_pos db_pos less _ _ _ _ _ todo_cap acc_cap])
          apply assumption
         apply simp
        apply simp
       apply simp
      apply simp
    apply (rule P_len)
    apply (rule P_bound)
  unfolding interval_vec_free_monadic_def PR_CONST_def
  apply refine_vcg
  apply (clarsimp simp: rational_state_todo_def
    rational_loop_invar_def)
  apply (clarsimp)
  apply (frule rational_loop_invar_empty_acc)
   apply (simp add: rational_state_todo_def)
  apply (simp add: rational_state_acc_def)
  done

section \<open>Proof-Friendly Queue Driver\<close>

lemma rational_queue_stack_step_mset_parts:
  "mset (fst (rational_queue_step_int P todo acc)) =
    mset (fst (rational_stack_step_int P todo acc)) \<and>
   mset (snd (rational_queue_step_int P todo acc)) =
    mset (snd (rational_stack_step_int P todo acc))"
  by (cases todo)
    (auto simp: rational_queue_step_int_def
      rational_stack_step_int_def Let_def ac_simps split: prod.splits)

lemma rational_queue_stack_step_todo_mset:
  "mset (fst (rational_queue_step_int P todo acc)) =
    mset (fst (rational_stack_step_int P todo acc))"
  using rational_queue_stack_step_mset_parts[of P todo acc]
  by simp

lemma rational_queue_stack_step_acc_mset:
  "mset (snd (rational_queue_step_int P todo acc)) =
    mset (snd (rational_stack_step_int P todo acc))"
  using rational_queue_stack_step_mset_parts[of P todo acc]
  by simp

lemma rat_half_times_two:
  "(((a::rat) + b) / 2) * 2 = a + b"
  by simp

lemma rat_times_two_eq_sumD:
  "(x::rat) * 2 = a + b \<Longrightarrow> x = (a + b) / 2"
  by simp

function (domintros) rational_queue_fun_int ::
  "gmp_poly \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) list \<Rightarrow>
    (rat \<times> rat) list" where
  "rational_queue_fun_int P todo acc =
    (case todo of
      [] \<Rightarrow> acc
    | (a, b) # rest \<Rightarrow>
        (let v = descartes_list_int a b P in
         if v = 0 then rational_queue_fun_int P rest acc
         else if v = 1 then
           rational_queue_fun_int P rest (acc @ [(a, b)])
         else
           (let m = (a + b) / 2 in
            rational_queue_fun_int P
              (rest @ [(a, m), (m, b)])
              (acc @
                (if poly (map_poly rat_of_int (Poly P)) m = 0
                 then [(m, m)] else [])))))"
  by pat_completeness auto

lemma rational_queue_main_int_eq_fun_int:
  assumes dom: "rational_queue_fun_int_dom (P, todo, acc)"
  shows "rational_queue_main_int P todo acc =
    rational_queue_fun_int P todo acc"
  using dom
proof (induction P todo acc rule: rational_queue_fun_int.pinduct)
  case (1 P todo acc)
  show ?case
  proof (cases todo)
    case Nil
    then show ?thesis
      using "1.hyps" rational_queue_fun_int.psimps
      by simp
  next
    case (Cons I rest)
    obtain a b where I_eq: "I = (a, b)"
      by (cases I) auto
    have dom_cons:
      "rational_queue_fun_int_dom (P, (a, b) # rest, acc)"
      using "1.hyps"(1) Cons I_eq by simp
    have fun_unfold:
      "rational_queue_fun_int P ((a, b) # rest) acc =
        (let v = descartes_list_int a b P in
         if v = 0 then rational_queue_fun_int P rest acc
         else if v = 1 then
           rational_queue_fun_int P rest (acc @ [(a, b)])
         else
           (let m = (a + b) / 2 in
            rational_queue_fun_int P
              (rest @ [(a, m), (m, b)])
              (acc @
                (if poly (map_poly rat_of_int (Poly P)) m = 0
                 then [(m, m)] else []))))"
      using dom_cons
      by (subst rational_queue_fun_int.psimps)
        (simp_all split: list.splits prod.splits)
    have main_unfold:
      "rational_queue_main_int P ((a, b) # rest) acc =
        (let v = descartes_list_int a b P in
         if v = 0 then rational_queue_main_int P rest acc
         else if v = 1 then
           rational_queue_main_int P rest (acc @ [(a, b)])
         else
           (let m = (a + b) / 2 in
            rational_queue_main_int P
              (rest @ [(a, m), (m, b)])
              (acc @
                (if poly (map_poly rat_of_int (Poly P)) m = 0
                 then [(m, m)] else []))))"
      by (simp add: rational_queue_main_int_Cons_cases)
    show ?thesis
    proof (cases "descartes_list_int a b P = 0")
      case True
      have IH0:
        "rational_queue_main_int P rest acc =
         rational_queue_fun_int P rest acc"
        using "1.IH"(1)[of "(a, b)" rest a b
          "descartes_list_int a b P"] Cons I_eq True
        by simp
      show ?thesis
        unfolding Cons I_eq
        using True IH0 by (simp add: fun_unfold main_unfold Let_def)
    next
      case v0: False
      show ?thesis
      proof (cases "descartes_list_int a b P = 1")
        case True
        have IH1:
          "rational_queue_main_int P rest (acc @ [(a, b)]) =
           rational_queue_fun_int P rest (acc @ [(a, b)])"
          using "1.IH"(2)[of "(a, b)" rest a b
            "descartes_list_int a b P"] Cons I_eq v0 True
          by simp
        show ?thesis
          unfolding Cons I_eq
          using v0 True IH1 by (simp add: fun_unfold main_unfold Let_def)
      next
        case v1: False
        let ?m = "(a + b) / 2"
        have IH2:
          "rational_queue_main_int P
             (rest @ [(a, ?m), (?m, b)])
             (acc @
               (if poly (map_poly rat_of_int (Poly P)) ?m = 0
                then [(?m, ?m)] else [])) =
           rational_queue_fun_int P
             (rest @ [(a, ?m), (?m, b)])
             (acc @
               (if poly (map_poly rat_of_int (Poly P)) ?m = 0
                then [(?m, ?m)] else []))"
          using "1.IH"(3)[of "(a, b)" rest a b
            "descartes_list_int a b P" ?m] Cons I_eq v0 v1
          by (simp add: rat_half_times_two)
        show ?thesis
          unfolding Cons I_eq
          using v0 v1 IH2 by (simp add: fun_unfold main_unfold Let_def)
      qed
    qed
  qed
qed

lemma rational_todo_mu_mset_list_rel_wf:
  "wf {(todo', todo).
      rational_todo_mu_mset \<delta> todo' <
      rational_todo_mu_mset \<delta> todo}"
proof -
  have wf_ms_pred: "wfp ((<) :: nat multiset \<Rightarrow> nat multiset \<Rightarrow> bool)"
    by simp
  have wf_ms:
    "wf ({(x, y). x < y} :: (nat multiset \<times> nat multiset) set)"
    using wf_ms_pred by (simp add: wfp_def)
  show ?thesis
    using wf_inv_image[OF wf_ms,
      of "\<lambda>todo. rational_todo_mu_mset \<delta> todo"]
    by (simp add: inv_image_def)
qed

lemma rational_queue_step_next_ordered:
  assumes ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
  shows "\<And>I. I \<in> set (fst (rational_queue_step_int P todo acc)) \<Longrightarrow>
    fst I < snd I"
proof -
  fix I
  assume I_in: "I \<in> set (fst (rational_queue_step_int P todo acc))"
  show "fst I < snd I"
  proof (cases todo)
    case Nil
    then show ?thesis
      using I_in by (simp add: rational_queue_step_int_def)
  next
    case (Cons H rest)
    obtain a b where H_eq: "H = (a, b)"
      by (cases H) auto
    have ab: "a < b"
      using ordered[of "(a, b)"] Cons H_eq by simp
    let ?m = "(a + b) / 2"
    have am: "a < ?m"
      using ab by simp
    have mb: "?m < b"
      using ab by simp
    show ?thesis
      using I_in Cons H_eq ordered am mb
      by (auto simp: rational_queue_step_int_def Let_def
        split: prod.splits if_splits)
  qed
qed

lemma rational_queue_fun_int_domI:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
  shows "rational_queue_fun_int_dom (P, todo, acc)"
  using ordered
proof (induction todo arbitrary: acc
    rule: wf_induct_rule[OF rational_todo_mu_mset_list_rel_wf])
  fix todo acc
  assume IH:
    "\<And>todo' acc.
      (todo', todo) \<in> {(todo', todo).
        rational_todo_mu_mset \<delta> todo' <
        rational_todo_mu_mset \<delta> todo} \<Longrightarrow>
      (\<And>I. I \<in> set todo' \<Longrightarrow> fst I < snd I) \<Longrightarrow>
      rational_queue_fun_int_dom (P, todo', acc)"
    and ordered_todo: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
  show "rational_queue_fun_int_dom (P, todo, acc)"
  proof (cases todo)
    case Nil
    then show ?thesis
      by (auto intro: rational_queue_fun_int.domintros)
  next
    case (Cons H rest)
    obtain a b where H_eq: "H = (a, b)"
      by (cases H) auto
    let ?v = "descartes_list_int a b P"
    let ?m = "(a + b) / 2"
    let ?acc' =
      "acc @
        (if poly (map_poly rat_of_int (Poly P)) ?m = 0
         then [(?m, ?m)] else [])"
    have todo_ne: "todo \<noteq> []"
      using Cons by simp
    have step_dec:
      "rational_todo_mu_mset \<delta>
          (fst (rational_queue_step_int P todo acc)) <
       rational_todo_mu_mset \<delta> todo"
      by (rule rational_queue_step_mu_mset_decreases[
        OF \<delta>_pos ordered_todo small_fast todo_ne])
    show ?thesis
    proof (cases "?v = 0")
      case True
      have dec:
        "rational_todo_mu_mset \<delta> rest <
         rational_todo_mu_mset \<delta> todo"
        using step_dec Cons H_eq True
        by (simp add: rational_queue_step_int_def)
      have ordered_rest: "\<And>I. I \<in> set rest \<Longrightarrow> fst I < snd I"
        using ordered_todo Cons by simp
      have dom_rest:
        "rational_queue_fun_int_dom (P, rest, acc)"
        by (rule IH[of rest acc, OF _ ordered_rest]) (simp add: dec)
      show ?thesis
        using Cons H_eq True dom_rest
        by (auto intro: rational_queue_fun_int.domintros)
    next
      case v0: False
      show ?thesis
      proof (cases "?v = 1")
        case True
        have dec:
          "rational_todo_mu_mset \<delta> rest <
           rational_todo_mu_mset \<delta> todo"
          using step_dec Cons H_eq True
          by (simp add: rational_queue_step_int_def)
        have ordered_rest: "\<And>I. I \<in> set rest \<Longrightarrow> fst I < snd I"
          using ordered_todo Cons by simp
        have dom_rest:
          "rational_queue_fun_int_dom (P, rest, acc @ [(a, b)])"
          by (rule IH[of rest "acc @ [(a, b)]", OF _ ordered_rest])
            (simp add: dec)
        show ?thesis
          using Cons H_eq v0 True dom_rest
          by (auto intro: rational_queue_fun_int.domintros)
      next
        case v1: False
        let ?todo' = "rest @ [(a, ?m), (?m, b)]"
        have dec:
          "rational_todo_mu_mset \<delta> ?todo' <
           rational_todo_mu_mset \<delta> todo"
          using step_dec Cons H_eq v0 v1
          by (simp add: rational_queue_step_int_def Let_def)
        have ab: "a < b"
          using ordered_todo[of "(a, b)"] Cons H_eq by simp
        have ordered_next: "\<And>I. I \<in> set ?todo' \<Longrightarrow> fst I < snd I"
          using ordered_todo Cons H_eq ab by auto
        have dom_next:
          "rational_queue_fun_int_dom (P, ?todo', ?acc')"
          by (rule IH[of ?todo' ?acc', OF _ ordered_next]) (simp add: dec)
        show ?thesis
          unfolding Cons H_eq
          apply (rule rational_queue_fun_int.domintros)
          using v0 v1 dom_next
          by (auto dest: rat_times_two_eq_sumD)
      qed
    qed
  qed
qed

section \<open>Proof-Friendly Tree View and Scheduling Bridge\<close>

function (domintros) rational_tree_fun_int ::
  "gmp_poly \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> (rat \<times> rat) list" where
  "rational_tree_fun_int P a b =
    (let v = descartes_list_int a b P in
     if v = 0 then []
     else if v = 1 then [(a, b)]
     else
       (let m = (a + b) / 2 in
        (if poly (map_poly rat_of_int (Poly P)) m = 0
         then [(m, m)] else []) @
        rational_tree_fun_int P a m @
        rational_tree_fun_int P m b))"
  by pat_completeness auto

lemma rational_tree_fun_int_domI:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
  shows "\<And>a b. a < b \<Longrightarrow> rational_tree_fun_int_dom (P, a, b)"
proof -
  define \<mu> where
    "\<mu> = (\<lambda>a b. rational_interval_mu \<delta> (a, b))"
  let ?Prop =
    "\<lambda>n::nat. \<forall>a b. \<mu> a b < n \<longrightarrow> a < b \<longrightarrow>
      rational_tree_fun_int_dom (P, a, b)"
  have step: "\<And>n. (\<And>m. m < n \<Longrightarrow> ?Prop m) \<Longrightarrow> ?Prop n"
  proof (intro allI impI)
    fix n a b
    assume IH: "\<And>m. m < n \<Longrightarrow> ?Prop m"
      and mu_lt_n: "\<mu> a b < n"
      and ab: "a < b"
    let ?v = "descartes_list_int a b P"
    show "rational_tree_fun_int_dom (P, a, b)"
    proof (cases "?v = 0 \<or> ?v = 1")
      case True
      then show ?thesis
        by (auto intro: rational_tree_fun_int.domintros)
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
      let ?m = "(a + b) / 2"
      have am: "a < ?m"
        using ab by simp
      have mb: "?m < b"
        using ab by simp
      have left_lt: "\<mu> a ?m < \<mu> a b"
        using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"]
          \<delta>_pos ab \<delta>_lt
        unfolding \<mu>_def rational_interval_mu_def
        by (simp add: of_rat_add of_rat_divide)
      have right_lt: "\<mu> ?m b < \<mu> a b"
        using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"]
          \<delta>_pos ab \<delta>_lt
        unfolding \<mu>_def rational_interval_mu_def
        by (simp add: of_rat_add of_rat_divide)
      have IH_at_mu: "?Prop (\<mu> a b)"
        using IH mu_lt_n by simp
      have dom_left: "rational_tree_fun_int_dom (P, a, ?m)"
        using IH_at_mu left_lt am by blast
      have dom_right: "rational_tree_fun_int_dom (P, ?m, b)"
        using IH_at_mu right_lt mb by blast
      show ?thesis
        apply (rule rational_tree_fun_int.domintros)
        using False dom_left dom_right
        by (auto dest: rat_times_two_eq_sumD)
    qed
  qed
  have all_Prop: "\<And>n. ?Prop n"
    by (rule less_induct, rule step)
  show "\<And>a b. a < b \<Longrightarrow> rational_tree_fun_int_dom (P, a, b)"
    using all_Prop by blast
qed

definition rational_tree_mset_list ::
  "gmp_poly \<Rightarrow> (rat \<times> rat) list \<Rightarrow> (rat \<times> rat) multiset" where
  "rational_tree_mset_list P todo =
    sum_list (map (\<lambda>I.
      mset (rational_tree_fun_int P (fst I) (snd I))) todo)"

lemma rational_tree_mset_list_Nil[simp]:
  "rational_tree_mset_list P [] = {#}"
  by (simp add: rational_tree_mset_list_def)

lemma rational_tree_mset_list_Cons[simp]:
  "rational_tree_mset_list P (I # rest) =
    mset (rational_tree_fun_int P (fst I) (snd I)) +
    rational_tree_mset_list P rest"
  by (simp add: rational_tree_mset_list_def)

lemma rational_tree_mset_list_append[simp]:
  "rational_tree_mset_list P (xs @ ys) =
    rational_tree_mset_list P xs +
    rational_tree_mset_list P ys"
  by (simp add: rational_tree_mset_list_def)

lemma rational_queue_fun_int_mset_tree:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and ordered: "\<And>I. I \<in> set todo \<Longrightarrow> fst I < snd I"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
  shows "mset (rational_queue_fun_int P todo acc) =
    mset acc + rational_tree_mset_list P todo"
proof -
  have qdom: "rational_queue_fun_int_dom (P, todo, acc)"
    by (rule rational_queue_fun_int_domI[
      OF \<delta>_pos ordered small_fast])
  show ?thesis
    using qdom ordered small_fast
  proof (induction P todo acc rule: rational_queue_fun_int.pinduct)
    case (1 P todo acc)
    show ?case
    proof (cases todo)
      case Nil
      then show ?thesis
        using "1.hyps" rational_queue_fun_int.psimps
        by simp
    next
      case (Cons I rest)
      obtain a b where I_eq: "I = (a, b)"
        by (cases I) auto
      have ordered_rest: "\<And>I. I \<in> set rest \<Longrightarrow> fst I < snd I"
        using "1.prems"(1) Cons by simp
      have ab: "a < b"
        using "1.prems"(1)[of "(a, b)"] Cons I_eq by simp
      have tree_dom:
        "rational_tree_fun_int_dom (P, a, b)"
      proof (rule rational_tree_fun_int_domI[
          where \<delta> = \<delta> and P = P])
        show "\<delta> > 0"
          by (fact \<delta>_pos)
        show "\<And>aa ba. aa < ba \<Longrightarrow>
          of_rat ba - of_rat aa \<le> \<delta> \<Longrightarrow>
          descartes_list_int aa ba P \<le> 1"
          using "1.prems"(2) by blast
        show "a < b"
          by (fact ab)
      qed
      have queue_unfold:
        "rational_queue_fun_int P ((a, b) # rest) acc =
          (let v = descartes_list_int a b P in
           if v = 0 then rational_queue_fun_int P rest acc
           else if v = 1 then
             rational_queue_fun_int P rest (acc @ [(a, b)])
           else
             (let m = (a + b) / 2 in
              rational_queue_fun_int P
                (rest @ [(a, m), (m, b)])
                (acc @
                  (if poly (map_poly rat_of_int (Poly P)) m = 0
                   then [(m, m)] else []))))"
        using "1.hyps"(1) Cons I_eq
        by (subst rational_queue_fun_int.psimps)
          (simp_all split: list.splits prod.splits)
      have tree_unfold:
        "rational_tree_fun_int P a b =
          (let v = descartes_list_int a b P in
           if v = 0 then []
           else if v = 1 then [(a, b)]
           else
             (let m = (a + b) / 2 in
              (if poly (map_poly rat_of_int (Poly P)) m = 0
               then [(m, m)] else []) @
              rational_tree_fun_int P a m @
              rational_tree_fun_int P m b))"
        using tree_dom
        by (subst rational_tree_fun_int.psimps) simp_all
      show ?thesis
      proof (cases "descartes_list_int a b P = 0")
        case True
        have IH0:
          "mset (rational_queue_fun_int P rest acc) =
           mset acc + rational_tree_mset_list P rest"
          using "1.IH"(1)[of "(a, b)" rest a b
            "descartes_list_int a b P"] Cons I_eq True
            ordered_rest "1.prems"(2)
          by simp
        show ?thesis
          unfolding Cons I_eq
          using True IH0
          by (simp add: queue_unfold tree_unfold ac_simps)
      next
        case v0: False
        show ?thesis
        proof (cases "descartes_list_int a b P = 1")
          case True
          have IH1:
            "mset (rational_queue_fun_int P rest (acc @ [(a, b)])) =
             mset (acc @ [(a, b)]) +
             rational_tree_mset_list P rest"
            using "1.IH"(2)[of "(a, b)" rest a b
              "descartes_list_int a b P"] Cons I_eq v0 True
              ordered_rest "1.prems"(2)
            by simp
          show ?thesis
            unfolding Cons I_eq
            using v0 True IH1
            by (simp add: queue_unfold tree_unfold ac_simps)
        next
          case v1: False
          let ?m = "(a + b) / 2"
          let ?mid =
            "(if poly (map_poly rat_of_int (Poly P)) ?m = 0
              then [(?m, ?m)] else [])"
          have ordered_next:
            "\<And>I. I \<in> set (rest @ [(a, ?m), (?m, b)]) \<Longrightarrow>
              fst I < snd I"
            using ordered_rest ab by auto
          have IH2:
            "mset (rational_queue_fun_int P
                (rest @ [(a, ?m), (?m, b)]) (acc @ ?mid)) =
             mset (acc @ ?mid) +
             rational_tree_mset_list P
                (rest @ [(a, ?m), (?m, b)])"
            using "1.IH"(3)[of "(a, b)" rest a b
              "descartes_list_int a b P" ?m] Cons I_eq v0 v1
              ordered_next "1.prems"(2)
            by (simp add: rat_half_times_two)
          have IH2_norm:
            "mset (rational_queue_fun_int P
                (rest @ [(a, ?m), (?m, b)]) (acc @ ?mid)) =
             mset acc +
             (rational_tree_mset_list P rest +
              mset (?mid @
                rational_tree_fun_int P a ?m @
                rational_tree_fun_int P ?m b))"
            using IH2 by (simp add: ac_simps)
          show ?thesis
            unfolding Cons I_eq
            using v0 v1 IH2_norm
            by (simp add: queue_unfold tree_unfold Let_def mset_append union_ac)
        qed
      qed
    qed
  qed
qed

section \<open>Bridge to Abstract Dsc\<close>

lemma rational_tree_fun_int_mset_dsc:
  fixes \<delta> :: real and xs :: gmp_poly
  assumes dom: "dsc_dom (p, a', b', P')"
    and a'_eq: "a' = of_rat a"
    and b'_eq: "b' = of_rat b"
    and P'_eq: "P' = (map_poly of_int (Poly xs) :: real poly)"
    and pdeg: "p = degree (Poly xs)"
    and P0: "Poly xs \<noteq> 0"
    and canon: "coeffs (Poly xs) = xs"
    and ab: "a < b"
    and \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b xs \<le> 1"
  shows "mset (rational_tree_fun_int xs a b) =
    mset (map real_to_rat_pair (dsc p a' b' P'))"
  using dom a'_eq b'_eq P'_eq pdeg P0 canon ab
proof (induction p a' b' P' arbitrary: a b rule: dsc.pinduct)
  case (1 p a' b' P' a b)
  let ?Q = "Poly xs"
  let ?Q_real = "map_poly of_int ?Q :: real poly"
  let ?Q_rat = "map_poly of_int ?Q :: rat poly"
  let ?v_int = "descartes_list_int a b xs"
  let ?v_real = "Bernstein_changes p (of_rat a) (of_rat b) ?Q_real"
  have tree_dom: "rational_tree_fun_int_dom (xs, a, b)"
  proof (rule rational_tree_fun_int_domI[
      where \<delta> = \<delta> and P = xs])
    show "\<delta> > 0"
      by (fact \<delta>_pos)
    show "\<And>aa ba. aa < ba \<Longrightarrow>
      of_rat ba - of_rat aa \<le> \<delta> \<Longrightarrow>
      descartes_list_int aa ba xs \<le> 1"
      by (rule small_fast)
    show "a < b"
      using "1.prems" by simp
  qed
  have a'_norm: "a' = of_rat a"
    using "1.prems" by simp
  have b'_norm: "b' = of_rat b"
    using "1.prems" by simp
  have P'_norm: "P' = ?Q_real"
    using "1.prems" by simp
  have p_norm: "p = degree ?Q"
    using "1.prems" by simp
  have deg_p: "degree ?Q_real = p"
    using p_norm by simp
  have p_eq: "p = degree ?Q"
    by (fact p_norm)
  have Q0: "?Q \<noteq> 0"
    using "1.prems" by simp
  have canon_xs: "coeffs ?Q = xs"
    using "1.prems" by simp
  have strip_xs: "strip_while ((=) 0) xs = xs"
    using canon_xs by simp
  have v_eq: "int ?v_int = ?v_real"
    using descartes_roots_test_sc_of_int[OF \<open>a < b\<close> Q0]
    by (simp add: descartes_roots_test_sc_eq_Bernstein_changes
        deg_p p_eq strip_xs)
  have tree_unfold:
    "rational_tree_fun_int xs a b =
      (let v = ?v_int in
       if v = 0 then []
       else if v = 1 then [(a, b)]
       else
         (let m = (a + b) / 2 in
          (if poly ?Q_rat m = 0 then [(m, m)] else []) @
          rational_tree_fun_int xs a m @
          rational_tree_fun_int xs m b))"
    using tree_dom
    by (subst rational_tree_fun_int.psimps) simp_all
  have dsc_unfold0:
    "dsc p a' b' P' =
      (let v = Bernstein_changes p a' b' P' in
       if v = 0 then []
       else if v = 1 then [(a', b')]
       else
         (let m = (a' + b') / 2 in
          (if poly P' m = 0 then [(m, m)] else []) @
          dsc p a' m P' @
          dsc p m b' P'))"
    using "1.hyps"
    by (subst dsc.psimps) simp_all
  have dsc_unfold:
    "dsc p a' b' P' =
      (let v = ?v_real in
       if v = 0 then []
       else if v = 1 then [(of_rat a, of_rat b)]
       else
         (let m = (of_rat a + of_rat b) / 2 in
          (if poly ?Q_real m = 0 then [(m, m)] else []) @
          dsc p (of_rat a) m ?Q_real @
          dsc p m (of_rat b) ?Q_real))"
    using dsc_unfold0
    unfolding a'_norm b'_norm P'_norm p_norm
    by (simp add: of_rat_add of_rat_divide)
  show ?case
  proof (cases "?v_int = 0")
    case True
    then show ?thesis
      using tree_unfold dsc_unfold v_eq "1.prems"
      by simp
  next
    case v0: False
    show ?thesis
    proof (cases "?v_int = 1")
      case True
      then show ?thesis
        using v0 tree_unfold dsc_unfold v_eq "1.prems"
        by simp
    next
      case v1: False
      let ?m = "(a + b) / 2"
      let ?m_real = "((of_rat a + of_rat b) / 2 :: real)"
      let ?mid_rat =
        "(if poly ?Q_rat ?m = 0 then [(?m, ?m)] else [])"
      let ?mid_real =
        "(if poly ?Q_real ?m_real = 0
          then [(?m_real, ?m_real)] else [])"
      have m_real_eq: "(of_rat ?m :: real) = ?m_real"
        by (simp add: of_rat_add of_rat_divide)
      have a_lt_m: "a < ?m"
        using "1.prems" by simp
      have m_lt_b: "?m < b"
        using "1.prems" by simp
      have v_real_nonzero: "?v_real \<noteq> 0"
        using v0 v_eq by auto
      have v_real_not_one: "?v_real \<noteq> 1"
        using v1 v_eq by auto
      have m_sum_real:
        "of_rat a + of_rat b = of_rat ?m * (2::real)"
        by (simp add: of_rat_add of_rat_divide)
      have mid_map: "map real_to_rat_pair ?mid_real = ?mid_rat"
        using poly_rat_eq_poly_real[of ?Q ?m] m_real_eq
        by (smt (verit, ccfv_threshold) list.map(1,2)
            real_to_rat_pair_of_rat)
      have IH_left_raw:
        "mset (rational_tree_fun_int xs a ?m) =
         mset (map real_to_rat_pair (dsc p a' ?m_real P'))"
      proof (rule "1.IH"(1)[of ?v_real ?m_real a ?m])
        show "?v_real = Bernstein_changes p a' b' P'"
          unfolding a'_norm b'_norm P'_norm by simp
        show "?v_real \<noteq> 0"
          by (fact v_real_nonzero)
        show "?v_real \<noteq> 1"
          by (fact v_real_not_one)
        show "?m_real = (a' + b') / 2"
          unfolding a'_norm b'_norm by simp
        show "a' = of_rat a"
          by (fact a'_norm)
        show "?m_real = of_rat ?m"
          using m_real_eq by simp
        show "P' = (map_poly of_int ?Q :: real poly)"
          by (fact P'_norm)
        show "p = degree ?Q"
          by (fact p_norm)
        show "?Q \<noteq> 0"
          by (fact Q0)
        show "coeffs ?Q = xs"
          by (fact canon_xs)
        show "a < ?m"
          by (fact a_lt_m)
      qed
      have IH_left:
        "mset (rational_tree_fun_int xs a ?m) =
         mset (map real_to_rat_pair
          (dsc p (of_rat a) ?m_real ?Q_real))"
        using IH_left_raw
        unfolding a'_norm P'_norm
        by simp
      have IH_right_raw:
        "mset (rational_tree_fun_int xs ?m b) =
         mset (map real_to_rat_pair (dsc p ?m_real b' P'))"
      proof (rule "1.IH"(2)[of ?v_real ?m_real ?m b])
        show "?v_real = Bernstein_changes p a' b' P'"
          unfolding a'_norm b'_norm P'_norm by simp
        show "?v_real \<noteq> 0"
          by (fact v_real_nonzero)
        show "?v_real \<noteq> 1"
          by (fact v_real_not_one)
        show "?m_real = (a' + b') / 2"
          unfolding a'_norm b'_norm by simp
        show "?m_real = of_rat ?m"
          using m_real_eq by simp
        show "b' = of_rat b"
          by (fact b'_norm)
        show "P' = (map_poly of_int ?Q :: real poly)"
          by (fact P'_norm)
        show "p = degree ?Q"
          by (fact p_norm)
        show "?Q \<noteq> 0"
          by (fact Q0)
        show "coeffs ?Q = xs"
          by (fact canon_xs)
        show "?m < b"
          by (fact m_lt_b)
      qed
      have IH_right:
        "mset (rational_tree_fun_int xs ?m b) =
         mset (map real_to_rat_pair
          (dsc p ?m_real (of_rat b) ?Q_real))"
        using IH_right_raw
        unfolding b'_norm P'_norm
        by simp
      show ?thesis
        using v0 v1 tree_unfold dsc_unfold v_eq IH_left IH_right
          mid_map "1.prems"
        by (simp add: Let_def mset_append union_ac)
    qed
  qed
qed

lemma rational_queue_main_int_mset_dsc_int:
  fixes \<delta> :: real and xs :: gmp_poly
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b xs \<le> 1"
    and dom: "dsc_dom
      (degree (Poly xs), of_rat a, of_rat b,
        map_poly of_int (Poly xs) :: real poly)"
    and P0: "Poly xs \<noteq> 0"
    and canon: "coeffs (Poly xs) = xs"
    and ab: "a < b"
  shows "mset (rational_queue_main_int xs [(a, b)] []) =
    mset (dsc_int a b (Poly xs))"
proof -
  have qdom: "rational_queue_fun_int_dom (xs, [(a, b)], [])"
    by (rule rational_queue_fun_int_domI[
      OF \<delta>_pos _ small_fast]) (simp add: ab)
  have queue_fun:
    "rational_queue_main_int xs [(a, b)] [] =
     rational_queue_fun_int xs [(a, b)] []"
    by (rule rational_queue_main_int_eq_fun_int[OF qdom])
  have queue_tree:
    "mset (rational_queue_fun_int xs [(a, b)] []) =
     mset (rational_tree_fun_int xs a b)"
    using rational_queue_fun_int_mset_tree[
      OF \<delta>_pos _ small_fast, of "[(a, b)]" "[]"]
      ab
    by simp
  have tree_dsc:
    "mset (rational_tree_fun_int xs a b) =
     mset (map real_to_rat_pair
      (dsc (degree (Poly xs)) (of_rat a) (of_rat b)
        (map_poly of_int (Poly xs) :: real poly)))"
    by (rule rational_tree_fun_int_mset_dsc[
      OF dom refl refl refl refl P0 canon ab \<delta>_pos small_fast])
  have dscint:
    "mset (dsc_int a b (Poly xs)) =
     mset (map real_to_rat_pair
      (dsc (degree (Poly xs)) (of_rat a) (of_rat b)
        (map_poly of_int (Poly xs) :: real poly)))"
    using dsc_int_eq_dsc[OF dom refl P0 ab]
    by (metis mset_rev)
  show ?thesis
    using queue_fun queue_tree tree_dsc dscint by simp
qed

lemma rational_queue_main_int_set_dsc_int:
  fixes \<delta> :: real and xs :: gmp_poly
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b xs \<le> 1"
    and dom: "dsc_dom
      (degree (Poly xs), of_rat a, of_rat b,
        map_poly of_int (Poly xs) :: real poly)"
    and P0: "Poly xs \<noteq> 0"
    and canon: "coeffs (Poly xs) = xs"
    and ab: "a < b"
  shows "set (rational_queue_main_int xs [(a, b)] []) =
    set (dsc_int a b (Poly xs))"
    using rational_queue_main_int_mset_dsc_int[
      OF \<delta>_pos small_fast dom P0 canon ab]
  by (metis set_mset_mset)

section \<open>Exact HNR Packaging Against dsc_int\<close>

lemma dsc_rational_main_list_mset_dsc_int_spec:
  fixes \<delta> :: real
    and na da nb db :: int
    and P :: gmp_poly
  defines "I \<equiv> interval_of_pair ((na, da), (nb, db))"
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast:
      "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
        descartes_list_int a b P \<le> 1"
    and da_pos: "0 < da"
    and db_pos: "0 < db"
    and less: "rat_of_pair (na, da) <
      rat_of_pair (nb, db)"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and todo_cap:
      "1 + rational_todo_append_budget \<delta> [I] + 2 <
        int (max_snat LENGTH(gmp_poly_len))"
    and acc_cap:
      "rational_todo_acc_budget \<delta> [I] + 1 <
        int (max_snat LENGTH(gmp_poly_len))"
    and dom: "dsc_dom
      (degree (Poly P), of_rat (fst I), of_rat (snd I),
        map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0"
    and canon: "coeffs (Poly P) = P"
  shows "dsc_rational_main_list na da nb db P \<le>
    SPEC (\<lambda>acc.
      interval_vec_invar acc \<and>
      mset (interval_vec_to_list acc) =
        mset (dsc_int (fst I) (snd I) (Poly P)))"
proof -
  have I_less: "fst I < snd I"
    using less unfolding I_def interval_of_pair_def by simp
  have main_spec:
    "dsc_rational_main_list na da nb db P \<le>
      SPEC (\<lambda>acc.
        interval_vec_invar acc \<and>
        interval_vec_to_list acc =
          rational_queue_main_int P [I] [])"
    unfolding I_def
    by (rule dsc_rational_main_list_spec[
      OF \<delta>_pos small_fast da_pos db_pos less P_len P_bound])
      (use todo_cap acc_cap I_def in simp_all)
  have queue_mset:
    "mset (rational_queue_main_int P [I] []) =
     mset (dsc_int (fst I) (snd I) (Poly P))"
    using rational_queue_main_int_mset_dsc_int[
      OF \<delta>_pos small_fast dom P0 canon I_less]
    by simp
  show ?thesis
    apply (rule order_trans[OF main_spec])
    using queue_mset
    by (auto simp: refine_pw_simps)
qed

definition dsc_rational_main_list_dsc_int_spec ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_interval_vec nres" where
"dsc_rational_main_list_dsc_int_spec na da nb db P \<equiv>
  (let I = interval_of_pair ((na, da), (nb, db)) in
    SPEC (\<lambda>acc.
      interval_vec_invar acc \<and>
      mset (interval_vec_to_list acc) =
        mset (dsc_int (fst I) (snd I) (Poly P))))"

definition dsc_rational_main_list_dsc_int_pre ::
  "real \<Rightarrow> ((((int \<times> int) \<times> int) \<times> int) \<times> gmp_poly) \<Rightarrow> bool"
where
"dsc_rational_main_list_dsc_int_pre \<delta> x \<longleftrightarrow>
  (case x of ((((na, da), nb), db), P) \<Rightarrow>
    let I = interval_of_pair ((na, da), (nb, db)) in
      \<delta> > 0 \<and>
      (\<forall>a b. a < b \<longrightarrow> of_rat b - of_rat a \<le> \<delta> \<longrightarrow>
        descartes_list_int a b P \<le> 1) \<and>
      0 < da \<and>
      0 < db \<and>
      rat_of_pair (na, da) < rat_of_pair (nb, db) \<and>
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      1 + rational_todo_append_budget \<delta> [I] + 2 <
        int (max_snat LENGTH(gmp_poly_len)) \<and>
      rational_todo_acc_budget \<delta> [I] + 1 <
        int (max_snat LENGTH(gmp_poly_len)) \<and>
      dsc_dom (degree (Poly P), of_rat (fst I), of_rat (snd I),
        map_poly of_int (Poly P) :: real poly) \<and>
      Poly P \<noteq> 0 \<and>
      coeffs (Poly P) = P)"

definition dsc_rational_main_list_dsc_squarefree_pre ::
  "real \<Rightarrow> ((((int \<times> int) \<times> int) \<times> int) \<times> gmp_poly) \<Rightarrow> bool"
where
"dsc_rational_main_list_dsc_squarefree_pre \<delta> x \<longleftrightarrow>
  (case x of ((((na, da), nb), db), P) \<Rightarrow>
    let I = interval_of_pair ((na, da), (nb, db));
        P_int = Poly P;
        P_real = (map_poly of_int P_int :: real poly)
    in
      \<delta> = delta_P P_real \<and>
      0 < da \<and>
      0 < db \<and>
      rat_of_pair (na, da) < rat_of_pair (nb, db) \<and>
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      1 + rational_todo_append_budget \<delta> [I] + 2 <
        int (max_snat LENGTH(gmp_poly_len)) \<and>
      rational_todo_acc_budget \<delta> [I] + 1 <
        int (max_snat LENGTH(gmp_poly_len)) \<and>
      P_int \<noteq> 0 \<and>
      coeffs P_int = P \<and>
      degree P_int \<noteq> 0 \<and>
      square_free P_real)"

lemma rational_fast_descartes_list_int_delta_P_le1:
  fixes P :: gmp_poly
  defines "P_int \<equiv> Poly P"
    and "P_real \<equiv> (map_poly of_int (Poly P) :: real poly)"
  assumes P0: "P_int \<noteq> 0"
    and canon: "coeffs P_int = P"
    and p0: "degree P_int \<noteq> 0"
    and sf: "square_free P_real"
    and ab: "a < b"
    and small: "of_rat b - of_rat a \<le> delta_P P_real"
  shows "descartes_list_int a b P \<le> 1"
proof -
  have P_real0: "P_real \<noteq> 0"
    using P0 unfolding P_real_def P_int_def by simp
  have deg_le: "degree P_real \<le> degree P_int"
    unfolding P_real_def P_int_def by simp
  have ab_real: "of_rat a < (of_rat b :: real)"
    using ab by (simp add: of_rat_less)
  have bc_le:
    "Bernstein_changes (degree P_int) (of_rat a) (of_rat b) P_real \<le> 1"
    using Bernstein_changes_small_interval_le_1[
      OF P_real0 deg_le p0 rsquarefree_lift[OF sf] ab_real small] .
  have v_eq:
    "int (descartes_list_int a b P) =
      Bernstein_changes (degree P_int) (of_rat a) (of_rat b) P_real"
  proof -
    have "int (descartes_list_int a b (coeffs P_int)) =
      descartes_roots_test_sc (of_rat a) (of_rat b) P_real"
      using descartes_roots_test_sc_of_int[OF ab P0]
      unfolding P_real_def P_int_def .
    also have "... =
      Bernstein_changes (degree P_int) (of_rat a) (of_rat b) P_real"
      by (simp add: descartes_roots_test_sc_eq_Bernstein_changes
        P_real_def P_int_def)
    finally show ?thesis
      using canon by simp
  qed
  show ?thesis
    using v_eq bc_le by linarith
qed

lemma rational_dom_squarefree:
  fixes P :: gmp_poly
    and na da nb db :: int
  defines "I \<equiv> interval_of_pair ((na, da), (nb, db))"
    and "P_int \<equiv> Poly P"
    and "P_real \<equiv> (map_poly of_int (Poly P) :: real poly)"
  assumes P0: "P_int \<noteq> 0"
    and p0: "degree P_int \<noteq> 0"
    and sf: "square_free P_real"
    and less: "rat_of_pair (na, da) <
      rat_of_pair (nb, db)"
  shows "dsc_dom (degree P_int, of_rat (fst I), of_rat (snd I), P_real)"
proof -
  have P_real0: "P_real \<noteq> 0"
    using P0 unfolding P_real_def P_int_def by simp
  have deg_le: "degree P_real \<le> degree P_int"
    unfolding P_real_def P_int_def by simp
  have I_less: "of_rat (fst I) < (of_rat (snd I) :: real)"
    using less unfolding I_def interval_of_pair_def
    by (simp add: of_rat_less)
  show ?thesis
    by (rule dsc_terminates_squarefree[OF P_real0 deg_le p0 sf I_less])
qed

lemma dsc_rational_main_list_dsc_squarefree_pre_imp_int_pre:
  assumes pre: "dsc_rational_main_list_dsc_squarefree_pre \<delta> x"
  shows "dsc_rational_main_list_dsc_int_pre \<delta> x"
proof -
  obtain na da nb db P where x_eq: "x = ((((na, da), nb), db), P)"
    by (cases x) auto
  let ?I = "interval_of_pair ((na, da), (nb, db))"
  let ?P_int = "Poly P"
  let ?P_real = "map_poly of_int ?P_int :: real poly"

  have pre_unfold:
    "\<delta> = delta_P ?P_real \<and>
      0 < da \<and>
      0 < db \<and>
      rat_of_pair (na, da) <
        rat_of_pair (nb, db) \<and>
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      1 + rational_todo_append_budget (delta_P ?P_real) [?I] + 2 <
        int (max_snat LENGTH(gmp_poly_len)) \<and>
      rational_todo_acc_budget (delta_P ?P_real) [?I] + 1 <
        int (max_snat LENGTH(gmp_poly_len)) \<and>
      ?P_int \<noteq> 0 \<and>
      coeffs ?P_int = P \<and>
      degree ?P_int \<noteq> 0 \<and>
      square_free ?P_real"
    using pre
    unfolding x_eq dsc_rational_main_list_dsc_squarefree_pre_def
    by (auto simp: Let_def)
  have delta_eq: "\<delta> = delta_P ?P_real"
    using pre_unfold by blast
  have da_pos: "0 < da"
    using pre_unfold by blast
  have db_pos: "0 < db"
    using pre_unfold by blast
  have less: "rat_of_pair (na, da) <
      rat_of_pair (nb, db)"
    using pre_unfold by blast
  have P_len: "0 < length P"
    using pre_unfold by blast
  have P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    using pre_unfold by blast
  have todo_cap:
    "1 + rational_todo_append_budget \<delta> [?I] + 2 <
      int (max_snat LENGTH(gmp_poly_len))"
    using pre_unfold delta_eq by simp
  have acc_cap:
    "rational_todo_acc_budget \<delta> [?I] + 1 <
      int (max_snat LENGTH(gmp_poly_len))"
    using pre_unfold delta_eq by simp
  have P0: "?P_int \<noteq> 0"
    using pre_unfold by blast
  have canon: "coeffs ?P_int = P"
    using pre_unfold by blast
  have p0: "degree ?P_int \<noteq> 0"
    using pre_unfold by blast
  have sf: "square_free ?P_real"
    using pre_unfold by blast

  have delta_pos: "\<delta> > 0"
    using delta_eq P0 delta_P_pos by simp
  have small_fast:
    "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow>
      descartes_list_int a b P \<le> 1"
    using rational_fast_descartes_list_int_delta_P_le1[
      OF P0 canon p0 sf] delta_eq by simp
  have dom: "dsc_dom
    (degree ?P_int, of_rat (fst ?I), of_rat (snd ?I), ?P_real)"
    by (rule rational_dom_squarefree[
      OF P0 p0 sf less])

  show ?thesis
    unfolding x_eq dsc_rational_main_list_dsc_int_pre_def
    apply (simp add: Let_def)
    apply (intro conjI allI impI)
    using delta_pos small_fast da_pos db_pos less P_len P_bound
      todo_cap acc_cap dom P0 canon
    apply simp_all
    done
qed

theorem dsc_rational_main_list_dsc_terminates_squarefree:
  assumes pre: "dsc_rational_main_list_dsc_squarefree_pre \<delta> x"
  shows "dsc_rational_main_list_dsc_int_pre \<delta> x"
  using pre
  by (rule dsc_rational_main_list_dsc_squarefree_pre_imp_int_pre)

lemma dsc_rational_main_list_dsc_int_refine:
  "(uncurry2 (uncurry2 dsc_rational_main_list),
    uncurry2 (uncurry2 dsc_rational_main_list_dsc_int_spec))
   \<in> [dsc_rational_main_list_dsc_int_pre \<delta>]\<^sub>f
      Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI)
  unfolding dsc_rational_main_list_dsc_int_pre_def
    dsc_rational_main_list_dsc_int_spec_def
  apply (clarsimp simp: Let_def)
  apply (rule dsc_rational_main_list_mset_dsc_int_spec)
  apply auto
  done

theorem dsc_rational_main_list_impl_refine_dsc_int:
  "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
    uncurry2 (uncurry2 dsc_rational_main_list_dsc_int_spec))
   \<in> [dsc_rational_main_list_dsc_int_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
proof -
  have h:
    "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
      uncurry2 (uncurry2 dsc_rational_main_list_dsc_int_spec))
     \<in> [\<lambda>((((na, da), nb), db), P).
          dsc_rational_main_list_dsc_int_pre \<delta>
            ((((na, da), nb), db), P) \<and>
          P \<noteq> [] \<and>
          Suc (length P) < max_snat 64]\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
          mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
          gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
    using dsc_rational_main_list_impl.refine[
      FCOMP dsc_rational_main_list_dsc_int_refine[where \<delta>=\<delta>]]
    by blast
  show ?thesis
    apply (rule hfref_weaken_pre[OF _ h])
    apply (clarsimp simp: dsc_rational_main_list_dsc_int_pre_def
      Let_def)
    done
qed

section \<open>Soundness and Completeness Packaging\<close>

lemma dsc_int_set_real_dsc:
  fixes P :: "int poly"
  assumes dom: "dsc_dom
      (degree P, of_rat a, of_rat b, map_poly of_int P :: real poly)"
    and P0: "P \<noteq> 0"
    and ab: "a < b"
  shows "set (dsc_int a b P) =
    real_to_rat_pair ` set
      (dsc (degree P) (of_rat a) (of_rat b)
        (map_poly of_int P :: real poly))"
proof -
  have "set (rev (dsc_int a b P)) =
    set (map real_to_rat_pair
      (dsc (degree P) (of_rat a) (of_rat b)
        (map_poly of_int P :: real poly)))"
    using dsc_int_eq_dsc[OF dom refl P0 ab]
    by simp
  then show ?thesis
    by simp
qed

lemma dsc_int_sound_real_image:
  fixes P :: "int poly"
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes dom: "dsc_dom (degree P, of_rat a, of_rat b, P_real)"
    and P0: "P \<noteq> 0"
    and ab: "a < b"
  shows "\<forall>I \<in> set (dsc_int a b P).
    \<exists>J \<in> set (dsc (degree P) (of_rat a) (of_rat b) P_real).
      I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
proof -
  have set_eq: "set (dsc_int a b P) =
    real_to_rat_pair ` set
      (dsc (degree P) (of_rat a) (of_rat b) P_real)"
    using dsc_int_set_real_dsc[OF dom[unfolded P_real_def] P0 ab]
    unfolding P_real_def .
  have deg: "degree P_real \<le> degree P"
    unfolding P_real_def by (rule degree_map_poly_le)
  have P_real0: "P_real \<noteq> 0"
    using P0 unfolding P_real_def by simp
  have ab_real: "of_rat a < (of_rat b :: real)"
    using ab by (simp add: of_rat_less)
  have sound:
    "\<forall>J \<in> set (dsc (degree P) (of_rat a) (of_rat b) P_real).
      dsc_pair_ok P_real J"
    by (rule dsc_sound[OF dom deg P_real0 ab_real])
  show ?thesis
    using set_eq sound by auto
qed

lemma dsc_int_complete_real_image:
  fixes P :: "int poly"
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes dom: "dsc_dom (degree P, of_rat a, of_rat b, P_real)"
    and P0: "P \<noteq> 0"
    and root: "poly P_real x = 0"
    and ax: "of_rat a < x"
    and xb: "x < of_rat b"
  shows "\<exists>I \<in> set (dsc_int a b P).
    \<exists>J \<in> set (dsc (degree P) (of_rat a) (of_rat b) P_real).
      I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
proof -
  have ab: "a < b"
    using ax xb by (meson less_trans of_rat_less)
  have set_eq: "set (dsc_int a b P) =
    real_to_rat_pair ` set
      (dsc (degree P) (of_rat a) (of_rat b) P_real)"
    using dsc_int_set_real_dsc[OF dom[unfolded P_real_def] P0 ab]
    unfolding P_real_def .
  have deg: "degree P_real \<le> degree P"
    unfolding P_real_def by (rule degree_map_poly_le)
  have P_real0: "P_real \<noteq> 0"
    using P0 unfolding P_real_def by simp
  obtain J where J_in:
      "J \<in> set (dsc (degree P) (of_rat a) (of_rat b) P_real)"
    and J_cover: "fst J \<le> x \<and> x \<le> snd J"
    using dsc_complete[OF dom deg P_real0 root ax xb]
    by blast
  then have "real_to_rat_pair J \<in> set (dsc_int a b P)"
    using set_eq by blast
  then show ?thesis
    using J_in J_cover by blast
qed

definition dsc_rational_main_list_dsc_sound_complete_spec ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_interval_vec nres" where
"dsc_rational_main_list_dsc_sound_complete_spec na da nb db P \<equiv>
  (let I = interval_of_pair ((na, da), (nb, db));
       P_int = Poly P;
       P_real = (map_poly of_int P_int :: real poly);
       ds = dsc (degree P_int) (of_rat (fst I)) (of_rat (snd I)) P_real
   in SPEC (\<lambda>acc.
      interval_vec_invar acc \<and>
      (\<forall>R \<in> set (interval_vec_to_list acc).
        \<exists>J \<in> set ds.
          R = real_to_rat_pair J \<and> dsc_pair_ok P_real J) \<and>
      (\<forall>x. poly P_real x = 0 \<longrightarrow>
        of_rat (fst I) < x \<longrightarrow> x < of_rat (snd I) \<longrightarrow>
        (\<exists>R \<in> set (interval_vec_to_list acc).
          \<exists>J \<in> set ds.
            R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))))"

lemma dsc_rational_main_list_dsc_int_spec_sound_complete:
  fixes \<delta> :: real
  assumes pre: "dsc_rational_main_list_dsc_int_pre \<delta>
    ((((na, da), nb), db), P)"
  shows "dsc_rational_main_list_dsc_int_spec na da nb db P \<le>
    dsc_rational_main_list_dsc_sound_complete_spec na da nb db P"
proof -
  let ?I = "interval_of_pair ((na, da), (nb, db))"
  let ?P_int = "Poly P"
  let ?P_real = "map_poly of_int ?P_int :: real poly"
  have less: "rat_of_pair (na, da) <
    rat_of_pair (nb, db)"
    using pre
    unfolding dsc_rational_main_list_dsc_int_pre_def Let_def
    by simp
  have I_less: "fst ?I < snd ?I"
    using less unfolding interval_of_pair_def by simp
  have dom: "dsc_dom
    (degree ?P_int, of_rat (fst ?I), of_rat (snd ?I), ?P_real)"
    using pre
    unfolding dsc_rational_main_list_dsc_int_pre_def Let_def
    by simp
  have P0: "?P_int \<noteq> 0"
    using pre
    unfolding dsc_rational_main_list_dsc_int_pre_def Let_def
    by simp
  have sound:
    "\<forall>R \<in> set (dsc_int (fst ?I) (snd ?I) ?P_int).
      \<exists>J \<in> set (dsc (degree ?P_int) (of_rat (fst ?I))
        (of_rat (snd ?I)) ?P_real).
        R = real_to_rat_pair J \<and> dsc_pair_ok ?P_real J"
    by (rule dsc_int_sound_real_image[OF dom P0 I_less])
  have complete:
    "\<And>x. poly ?P_real x = 0 \<Longrightarrow>
      of_rat (fst ?I) < x \<Longrightarrow> x < of_rat (snd ?I) \<Longrightarrow>
      \<exists>R \<in> set (dsc_int (fst ?I) (snd ?I) ?P_int).
        \<exists>J \<in> set (dsc (degree ?P_int) (of_rat (fst ?I))
          (of_rat (snd ?I)) ?P_real).
          R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
    by (rule dsc_int_complete_real_image[OF dom P0])
  show ?thesis
    unfolding dsc_rational_main_list_dsc_int_spec_def
      dsc_rational_main_list_dsc_sound_complete_spec_def Let_def
    using sound complete
    apply (auto simp: refine_pw_simps)
    apply (metis set_mset_mset)
    by (metis set_mset_mset)
qed

lemma dsc_rational_main_list_dsc_sound_complete_refine:
  "(uncurry2 (uncurry2 dsc_rational_main_list_dsc_int_spec),
    uncurry2 (uncurry2
      dsc_rational_main_list_dsc_sound_complete_spec))
   \<in> [dsc_rational_main_list_dsc_int_pre \<delta>]\<^sub>f
      Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI)
  apply clarsimp
  apply (rule dsc_rational_main_list_dsc_int_spec_sound_complete)
  apply assumption
  done

theorem dsc_rational_main_list_impl_refine_dsc_sound_complete:
  "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
    uncurry2 (uncurry2
      dsc_rational_main_list_dsc_sound_complete_spec))
   \<in> [dsc_rational_main_list_dsc_int_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
proof -
  have h:
    "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
      uncurry2 (uncurry2
        dsc_rational_main_list_dsc_sound_complete_spec))
     \<in> [\<lambda>((((na, da), nb), db), P).
          dsc_rational_main_list_dsc_int_pre \<delta>
            ((((na, da), nb), db), P)]\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
          mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
          gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
    using dsc_rational_main_list_impl_refine_dsc_int[
      where \<delta>=\<delta>,
      FCOMP dsc_rational_main_list_dsc_sound_complete_refine[
        where \<delta>=\<delta>]]
    by blast
  show ?thesis
    apply (rule hfref_weaken_pre[OF _ h])
    apply clarsimp
    done
qed

definition dsc_rational_main_list_dsc_sound_spec ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_interval_vec nres" where
"dsc_rational_main_list_dsc_sound_spec na da nb db P \<equiv>
  (let I = interval_of_pair ((na, da), (nb, db));
       P_int = Poly P;
       P_real = (map_poly of_int P_int :: real poly);
       ds = dsc (degree P_int) (of_rat (fst I)) (of_rat (snd I)) P_real
   in SPEC (\<lambda>acc.
      interval_vec_invar acc \<and>
      (\<forall>R \<in> set (interval_vec_to_list acc).
        \<exists>J \<in> set ds.
          R = real_to_rat_pair J \<and> dsc_pair_ok P_real J)))"

definition dsc_rational_main_list_dsc_complete_spec ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow>
    gmp_interval_vec nres" where
"dsc_rational_main_list_dsc_complete_spec na da nb db P \<equiv>
  (let I = interval_of_pair ((na, da), (nb, db));
       P_int = Poly P;
       P_real = (map_poly of_int P_int :: real poly);
       ds = dsc (degree P_int) (of_rat (fst I)) (of_rat (snd I)) P_real
   in SPEC (\<lambda>acc.
      interval_vec_invar acc \<and>
      (\<forall>x. poly P_real x = 0 \<longrightarrow>
        of_rat (fst I) < x \<longrightarrow> x < of_rat (snd I) \<longrightarrow>
        (\<exists>R \<in> set (interval_vec_to_list acc).
          \<exists>J \<in> set ds.
            R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))))"

lemma dsc_rational_main_list_dsc_int_spec_sound:
  fixes \<delta> :: real
  assumes pre: "dsc_rational_main_list_dsc_int_pre \<delta>
    ((((na, da), nb), db), P)"
  shows "dsc_rational_main_list_dsc_int_spec na da nb db P \<le>
    dsc_rational_main_list_dsc_sound_spec na da nb db P"
proof -
  let ?I = "interval_of_pair ((na, da), (nb, db))"
  let ?P_int = "Poly P"
  let ?P_real = "map_poly of_int ?P_int :: real poly"
  have less: "rat_of_pair (na, da) <
    rat_of_pair (nb, db)"
    using pre
    unfolding dsc_rational_main_list_dsc_int_pre_def Let_def
    by simp
  have I_less: "fst ?I < snd ?I"
    using less unfolding interval_of_pair_def by simp
  have dom: "dsc_dom
    (degree ?P_int, of_rat (fst ?I), of_rat (snd ?I), ?P_real)"
    using pre
    unfolding dsc_rational_main_list_dsc_int_pre_def Let_def
    by simp
  have P0: "?P_int \<noteq> 0"
    using pre
    unfolding dsc_rational_main_list_dsc_int_pre_def Let_def
    by simp
  have sound:
    "\<forall>R \<in> set (dsc_int (fst ?I) (snd ?I) ?P_int).
      \<exists>J \<in> set (dsc (degree ?P_int) (of_rat (fst ?I))
        (of_rat (snd ?I)) ?P_real).
        R = real_to_rat_pair J \<and> dsc_pair_ok ?P_real J"
    by (rule dsc_int_sound_real_image[OF dom P0 I_less])
  show ?thesis
    unfolding dsc_rational_main_list_dsc_int_spec_def
      dsc_rational_main_list_dsc_sound_spec_def Let_def
    using sound
    apply (auto simp: refine_pw_simps)
    by (metis set_mset_mset)
qed

lemma dsc_rational_main_list_dsc_int_spec_complete:
  fixes \<delta> :: real
  assumes pre: "dsc_rational_main_list_dsc_int_pre \<delta>
    ((((na, da), nb), db), P)"
  shows "dsc_rational_main_list_dsc_int_spec na da nb db P \<le>
    dsc_rational_main_list_dsc_complete_spec na da nb db P"
proof -
  let ?I = "interval_of_pair ((na, da), (nb, db))"
  let ?P_int = "Poly P"
  let ?P_real = "map_poly of_int ?P_int :: real poly"
  have less: "rat_of_pair (na, da) <
    rat_of_pair (nb, db)"
    using pre
    unfolding dsc_rational_main_list_dsc_int_pre_def Let_def
    by simp
  have I_less: "fst ?I < snd ?I"
    using less unfolding interval_of_pair_def by simp
  have dom: "dsc_dom
    (degree ?P_int, of_rat (fst ?I), of_rat (snd ?I), ?P_real)"
    using pre
    unfolding dsc_rational_main_list_dsc_int_pre_def Let_def
    by simp
  have P0: "?P_int \<noteq> 0"
    using pre
    unfolding dsc_rational_main_list_dsc_int_pre_def Let_def
    by simp
  have complete:
    "\<And>x. poly ?P_real x = 0 \<Longrightarrow>
      of_rat (fst ?I) < x \<Longrightarrow> x < of_rat (snd ?I) \<Longrightarrow>
      \<exists>R \<in> set (dsc_int (fst ?I) (snd ?I) ?P_int).
        \<exists>J \<in> set (dsc (degree ?P_int) (of_rat (fst ?I))
          (of_rat (snd ?I)) ?P_real).
          R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
    by (rule dsc_int_complete_real_image[OF dom P0])
  show ?thesis
    unfolding dsc_rational_main_list_dsc_int_spec_def
      dsc_rational_main_list_dsc_complete_spec_def Let_def
    using complete
    apply (auto simp: refine_pw_simps)
    by (metis set_mset_mset)
qed

lemma dsc_rational_main_list_dsc_sound_refine:
  "(uncurry2 (uncurry2
      dsc_rational_main_list_dsc_int_spec),
    uncurry2 (uncurry2
      dsc_rational_main_list_dsc_sound_spec))
   \<in> [dsc_rational_main_list_dsc_int_pre \<delta>]\<^sub>f
      Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI)
  apply clarsimp
  apply (rule dsc_rational_main_list_dsc_int_spec_sound)
  apply assumption
  done

lemma dsc_rational_main_list_dsc_complete_refine:
  "(uncurry2 (uncurry2
      dsc_rational_main_list_dsc_int_spec),
    uncurry2 (uncurry2
      dsc_rational_main_list_dsc_complete_spec))
   \<in> [dsc_rational_main_list_dsc_int_pre \<delta>]\<^sub>f
      Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI)
  apply clarsimp
  apply (rule dsc_rational_main_list_dsc_int_spec_complete)
  apply assumption
  done

theorem dsc_rational_main_list_impl_refine_dsc_sound:
  "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
    uncurry2 (uncurry2
      dsc_rational_main_list_dsc_sound_spec))
   \<in> [dsc_rational_main_list_dsc_int_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
proof -
  have h:
    "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
      uncurry2 (uncurry2
        dsc_rational_main_list_dsc_sound_spec))
     \<in> [\<lambda>((((na, da), nb), db), P).
          dsc_rational_main_list_dsc_int_pre \<delta>
            ((((na, da), nb), db), P)]\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
          mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
          gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
    using dsc_rational_main_list_impl_refine_dsc_int[
      where \<delta>=\<delta>,
      FCOMP dsc_rational_main_list_dsc_sound_refine[
        where \<delta>=\<delta>]]
    by blast
  show ?thesis
    apply (rule hfref_weaken_pre[OF _ h])
    apply clarsimp
    done
qed

theorem dsc_rational_main_list_impl_refine_dsc_complete:
  "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
    uncurry2 (uncurry2
      dsc_rational_main_list_dsc_complete_spec))
   \<in> [dsc_rational_main_list_dsc_int_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
proof -
  have h:
    "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
      uncurry2 (uncurry2
        dsc_rational_main_list_dsc_complete_spec))
     \<in> [\<lambda>((((na, da), nb), db), P).
          dsc_rational_main_list_dsc_int_pre \<delta>
            ((((na, da), nb), db), P)]\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
          mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
          gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
    using dsc_rational_main_list_impl_refine_dsc_int[
      where \<delta>=\<delta>,
      FCOMP dsc_rational_main_list_dsc_complete_refine[
        where \<delta>=\<delta>]]
    by blast
  show ?thesis
    apply (rule hfref_weaken_pre[OF _ h])
    apply clarsimp
    done
qed

section \<open>Squarefree Dsc Client Corollaries\<close>

theorem dsc_rational_main_list_impl_refine_dsc_int_squarefree:
  "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
    uncurry2 (uncurry2 dsc_rational_main_list_dsc_int_spec))
   \<in> [dsc_rational_main_list_dsc_squarefree_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
  apply (rule hfref_weaken_pre[
    OF _ dsc_rational_main_list_impl_refine_dsc_int[
      where \<delta>=\<delta>]])
  by (blast intro:
    dsc_rational_main_list_dsc_squarefree_pre_imp_int_pre)

theorem dsc_rational_main_list_impl_refine_dsc_sound_squarefree:
  "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
    uncurry2 (uncurry2
      dsc_rational_main_list_dsc_sound_spec))
   \<in> [dsc_rational_main_list_dsc_squarefree_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
  apply (rule hfref_weaken_pre[
    OF _ dsc_rational_main_list_impl_refine_dsc_sound[
      where \<delta>=\<delta>]])
  by (blast intro:
    dsc_rational_main_list_dsc_squarefree_pre_imp_int_pre)

theorem dsc_rational_main_list_impl_refine_dsc_complete_squarefree:
  "(uncurry2 (uncurry2 dsc_rational_main_list_impl),
    uncurry2 (uncurry2
      dsc_rational_main_list_dsc_complete_spec))
   \<in> [dsc_rational_main_list_dsc_squarefree_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_interval_vec_assn"
  apply (rule hfref_weaken_pre[
    OF _ dsc_rational_main_list_impl_refine_dsc_complete[
      where \<delta>=\<delta>]])
  by (blast intro:
    dsc_rational_main_list_dsc_squarefree_pre_imp_int_pre)

end
