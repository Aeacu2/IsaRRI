theory List_Changes

imports
  Main
  Triangle
  Descartes_Sign_Rule.Descartes_Sign_Rule
begin

text \<open>Sign-variation counting over coefficient LISTS — the list-level twin of the AFP's
  \<open>changes\<close> on polynomials.
  Layer: FUNCTIONAL SPEC.
  Main exports: \<open>sign_changes\<close>, \<open>changes\<close>-transfer lemmas. \<^bold>\<open>NB\<close> the constant \<open>changes\<close> declared here
  must not be used as a variable name in theories that import this one.\<close>


lemma changes_filter_zeros: "changes xs = changes (filter (\<lambda>x. x \<noteq> 0) xs)"
proof (induction xs rule: changes.induct)
  case 1 then show ?case by simp
next
  case (2 x) then show ?case by simp
next
  case (3 x1 x2 xs)
  show ?case
  proof (cases "x2 = 0")
    case True
    have "changes (x1 # x2 # xs) = changes (x1 # xs)"
      using True by (simp)
    also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (x1 # xs))"
      by (metis changes_filter_eq)
    also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (x1 # x2 # xs))"
      using True by simp
    finally show ?thesis .
  next
    case False
    note x2_nz = False
    show ?thesis
    proof (cases "x1 = 0")
      case True
      have "changes (x1 # x2 # xs) = changes (x2 # xs)"
        using True x2_nz by simp
      also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (x2 # xs))"
        using "3.IH"(1,3) x2_nz by blast
      also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (x1 # x2 # xs))"
        using True by simp
      finally show ?thesis .
    next
      case False
      have "changes (x1 # x2 # xs) = (if x1*x2 < 0 then 1 else 0) + changes (x2 # xs)"
        using x2_nz by simp
      also have "\<dots> = (if x1*x2 < 0 then 1 else 0) + changes (filter (\<lambda>x. x \<noteq> 0) (x2 # xs))"
        using "3.IH"(1,3) x2_nz by presburger
      also have "\<dots> = changes (x1 # x2 # (filter (\<lambda>x. x \<noteq> 0) xs))"
        using x2_nz False by simp
      also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (x1 # x2 # xs))"
        using x2_nz False by simp
      finally show ?thesis .
    qed
  qed
qed

lemma changes_eq_sign_changes_no_zeros:
  assumes "\<forall>x \<in> set xs. x \<noteq> 0"
  shows "changes xs = int (sign_changes xs)"
  using assms
proof (induction xs rule: induct_list012)
  case 1 then show ?case by (simp add: sign_changes_def)
next
  case (2 x) then show ?case 
    by (simp add: sign_changes_def Let_def)
next
  case (3 x1 x2 xs)
  have x1_nz: "x1 \<noteq> 0" and x2_nz: "x2 \<noteq> 0" and xs_nz: "\<forall>x \<in> set xs. x \<noteq> 0"
    using 3 by auto

  let ?L = "x1 # x2 # xs"
  let ?sgn_L = "remdups_adj (map sgn ?L)"

  have sgn_rel: "sgn x1 \<noteq> sgn x2 \<longleftrightarrow> x1 * x2 < 0"
    using x1_nz x2_nz
    by (simp add: mult_less_0_iff sgn_1_neg sgn_if)
    
  show ?case
  proof (cases "x1 * x2 < 0")
    case True
    have "sgn x1 \<noteq> sgn x2" using sgn_rel True by simp

    have ch_L: "changes ?L = 1 + changes (x2 # xs)"
      using True by simp

    have "sign_changes ?L = length (remdups_adj (map sgn (x1#x2#xs))) - 1"
      using x1_nz x2_nz xs_nz 
      unfolding sign_changes_def 
      by (simp add: filter_id_conv sgn_eq_0_iff)
    also have "\<dots> = length (sgn x1 # remdups_adj (map sgn (x2#xs))) - 1"
      using `sgn x1 \<noteq> sgn x2` by auto
    also have "\<dots> = 1 + (length (remdups_adj (map sgn (x2#xs))) - 1)"
      by (simp add: algebra_simps)
    also have "\<dots> = 1 + sign_changes (x2 # xs)"
      using x2_nz xs_nz unfolding sign_changes_def 
      by (metis True calculation sign_changes_Cons_Cons_different
          sign_changes_def)
      
    finally show ?thesis 
      using "3.IH"(2) ch_L x2_nz xs_nz by auto
  next
    case False
    have "sgn x1 = sgn x2" 
      using sgn_rel False x1_nz x2_nz 
      by metis

    have ch_L: "changes ?L = changes (x2 # xs)"
      using False x2_nz by simp

    have "remdups_adj (map sgn (x1#x2#xs)) = remdups_adj (map sgn (x2#xs))"
      using `sgn x1 = sgn x2` by force
      
    then have "sign_changes ?L = sign_changes (x2 # xs)"
      unfolding sign_changes_def using x1_nz x2_nz xs_nz 
      by force
      
    show ?thesis
      using "3.IH"(2) \<open>sign_changes (x1 # x2 # xs) = sign_changes (x2 # xs)\<close> ch_L x2_nz
        xs_nz by force
  qed
qed

lemma changes_eq_sign_changes: "changes xs = int (sign_changes xs)"
proof -
  let ?xs' = "filter (\<lambda>x. x \<noteq> 0) xs"

  have "changes xs = changes ?xs'" 
    using changes_filter_zeros 
  by blast

  have "sign_changes xs = sign_changes ?xs'"
    unfolding sign_changes_def 
    by (metis sign_changes_def sign_changes_filter)

  have "changes ?xs' = int (sign_changes ?xs')"
    apply (rule changes_eq_sign_changes_no_zeros)
    by simp
    
  show ?thesis
    using `changes xs = changes ?xs'` `sign_changes xs = sign_changes ?xs'` 
          `changes ?xs' = int (sign_changes ?xs')`
    by simp
qed


lemma sign_changes_convex_insert:
  fixes x y t :: real
  assumes "0 < t" "t < 1"
  shows "sign_changes [x, (1-t)*x + t*y, y] = sign_changes [x, y]"
proof -
  let ?z = "(1 - t) * x + t * y"
  
  have between: "x < y \<Longrightarrow> x < ?z \<and> ?z < y" 
    using assms 
  proof -
    assume a1: "x < y"
    then have f2: "t * x < t * y"
      by (simp add: assms(1))
    have "(1 - t) * x < (1 - t) * y"
      using a1 assms(2) by fastforce
    then show ?thesis
      using f2 by argo
  qed
  have between_rev: "y < x \<Longrightarrow> y < ?z \<and> ?z < x" 
    using assms
  proof -
    assume a1: "y < x"
    then have f2: "t * y < t * x"
      by (simp add: assms(1))
    have "(1 - t) * y < (1 - t) * x"
      using a1 assms(2) by fastforce
    then show ?thesis
      using f2 by argo
  qed
  show ?thesis
  proof (cases "x = y")
    case True
    with assms show ?thesis
      by (metis (no_types, opaque_lifting) diff_add_cancel distrib_left
          linorder_neqE_linordered_idom mult.commute mult.right_neutral
          sign_changes_0_Cons sign_changes_Cons_Cons_same zero_less_mult_iff)
  next
    case False
    show ?thesis 
      by (smt (verit, del_insts) assms(1,2) divisors_zero mult_less_0_iff mult_not_zero
          sign_changes_0_Cons sign_changes_Cons_Cons_0 sign_changes_Cons_Cons_different
          sign_changes_Cons_Cons_same sign_changes_singleton)
    
  qed
qed

lemma sign_changes_convex_context:
  fixes x y t :: real
  assumes "0 < t" "t < 1"
  shows "sign_changes (x # ((1-t)*x + t*y) # y # zs) = sign_changes (x # y # zs)"
proof -
  let ?m = "(1-t)*x + t*y"

  have "sign_changes (x # ?m # y # zs) = sign_changes ([x, ?m, y] @ zs)" by simp

  show ?thesis
  proof (cases "y = 0")
    case True 
    have m_val: "?m = (1 - t) * x" using True by simp

    have "sign_changes (x # ?m # y # zs) = sign_changes (x # ?m # zs)"
      using True 
      by (smt (verit, best) mult_not_zero no_zero_divisors sign_changes_Cons_Cons_0
          sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same)

    also have "... = sign_changes (x # zs)"
    proof (cases "x = 0")
      case True
      then show ?thesis using m_val
        by auto
    next
      case False
      have "x * ?m > 0" 
        using m_val False assms
        by (metis diff_gt_0_iff_gt linorder_cases mult_less_0_iff mult_neg_neg
            mult_pos_pos)
      
      have "sign_changes (x # ?m # zs) = sign_changes (?m # zs)"
        using \<open>x * ?m > 0\<close> by (simp add: sign_changes_Cons_Cons_same)
      also have "... = sign_changes (x # zs)"
      proof -
        have "sgn ?m = sgn x" using \<open>x * ?m > 0\<close>
          by (metis assms(2) diff_gt_0_iff_gt m_val mult.commute mult.right_neutral sgn_mult
              sgn_pos)
        then have "map sgn (?m # zs) = map sgn (x # zs)" by simp
        then show ?thesis using sign_changes_cong by blast
      qed
      finally show ?thesis .
    qed

    also have "... = sign_changes (x # y # zs)"
      using True by (simp add: sign_changes_Cons_Cons_0)
      
    finally show ?thesis .
  next
    case False
    have "sign_changes (x # ?m # y # zs) = sign_changes [x, ?m, y] + sign_changes (y # zs)"
      using False
      by (smt (z3) add_cancel_right_left no_zero_divisors plus_1_eq_Suc
          plus_nat.simps(2) sign_changes_0_Cons sign_changes_Cons_Cons_0
          sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same
          sign_changes_singleton)
      
    also have "... = sign_changes [x, y] + sign_changes (y # zs)"
      using sign_changes_convex_insert[OF assms] by simp
      
    also have "... = sign_changes (x # y # zs)"
      using False 
      by (metis (no_types, opaque_lifting) add.commute add.right_neutral
          linorder_neqE_linordered_idom mult_eq_0_iff sign_changes_0_Cons
          sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same
          sign_changes_singleton)
      
    finally show ?thesis .
  qed
qed

lemma sign_changes_prepend_aligned:
  fixes x y z :: real
  assumes "y \<noteq> 0" "z \<noteq> 0" 
  assumes "sgn y = sgn z"
  assumes "sign_changes (y # ys) \<le> sign_changes (z # zs)"
  shows   "sign_changes (x # y # ys) \<le> sign_changes (x # z # zs)"
proof (cases "x = 0")
  case True thus ?thesis using assms(4) by (simp)
next
  case False
  show ?thesis
  proof (cases "x * y > 0")
    case True
    have "x * z > 0" 
      using True assms(1,2,3) by (smt (verit) zero_less_mult_iff sgn_if)
    
    have "sign_changes (x # y # ys) = sign_changes (y # ys)"
      using True by (simp add: sign_changes_Cons_Cons_same)
    moreover have "sign_changes (x # z # zs) = sign_changes (z # zs)"
      using \<open>x * z > 0\<close> by (simp add: sign_changes_Cons_Cons_same)
    ultimately show ?thesis using assms(4) by simp
  next
    case False
    have "x * y < 0" 
      using False \<open>x \<noteq> 0\<close> assms(1) by (metis mult_eq_0_iff not_less_iff_gr_or_eq)
    hence "x * z < 0" 
      using assms(2,3) 
      by (metis sgn_1_neg sgn_mult)

    have "sign_changes (x # y # ys) = 1 + sign_changes (y # ys)"
      using \<open>x * y < 0\<close> by (simp add: sign_changes_Cons_Cons_different)
    moreover have "sign_changes (x # z # zs) = 1 + sign_changes (z # zs)"
      using \<open>x * z < 0\<close> by (simp add: sign_changes_Cons_Cons_different)
    ultimately show ?thesis using assms(4) by simp
  qed
qed

lemma sign_changes_prepend_aligned_eq:
  fixes x y z :: real
  assumes "y \<noteq> 0" "z \<noteq> 0" 
  assumes "sgn y = sgn z"
  assumes "sign_changes (y # ys) = sign_changes (z # zs)"
  shows   "sign_changes (x # y # ys) = sign_changes (x # z # zs)"
proof (cases "x = 0")
  case True
  have "sign_changes (x # y # ys) = sign_changes (y # ys)" 
    using True sign_changes_0_Cons by simp
  also have "... = sign_changes (z # zs)" 
    using assms(4) by simp
  also have "... = sign_changes (x # z # zs)" 
    using True sign_changes_0_Cons by simp
  then show ?thesis
    using calculation by force
next
  case False
  show ?thesis
  proof -
    have interaction_eq: "(if x * y < 0 then 1 else 0) = (if x * z < 0 then 1 else 0)"
      using assms(1,2,3) 

      by (metis sgn_1_neg sgn_mult)
    have lhs: "sign_changes (x # y # ys) = (if x * y < 0 then 1 else 0) + sign_changes (y # ys)"
      using False assms(1) 
      by (simp add: not_less_iff_gr_or_eq sign_changes_Cons_Cons_different
          sign_changes_Cons_Cons_same)
    have rhs: "sign_changes (x # z # zs) = (if x * z < 0 then 1 else 0) + sign_changes (z # zs)"
      using False assms(2) 

      by (simp add: not_less_iff_gr_or_eq sign_changes_Cons_Cons_different
          sign_changes_Cons_Cons_same)
    show ?thesis 
      using lhs rhs interaction_eq assms(4) by simp
  qed
qed

lemma remdups_adj_append_two: 
  "remdups_adj (xs @ y # y # ys) = remdups_adj (xs @ y # ys)"
proof (induct xs)
  case Nil
  show ?case by force
next
  case (Cons a xs)
  show ?case 
    using Cons.hyps by (auto simp: remdups_adj_Cons)
qed

lemma sign_changes_convex_insert_general:
  fixes x y t :: real
  assumes "0 < t" "t < 1"
  shows "sign_changes (us @ [x, (1-t)*x + t*y, y] @ vs) = sign_changes (us @ [x, y] @ vs)"
proof -
  let ?m = "(1-t)*x + t*y"
  let ?transform = "\<lambda>xs. filter (\<lambda>z. z \<noteq> (0::real)) (map sgn xs)"

  let ?L = "?transform us"
  let ?R = "?transform vs"
  let ?M1 = "?transform [x, ?m, y]"
  let ?M2 = "?transform [x, y]"

  have LHS: "sign_changes (us @ [x, ?m, y] @ vs) = length (remdups_adj (?L @ ?M1 @ ?R)) - 1"
    by (simp add: sign_changes_def)
    
  have RHS: "sign_changes (us @ [x, y] @ vs) = length (remdups_adj (?L @ ?M2 @ ?R)) - 1"
    by (simp add: sign_changes_def)

  have "remdups_adj (?L @ ?M1 @ ?R) = remdups_adj (?L @ ?M2 @ ?R)"
  proof (cases "x = 0")
    case True
    have "sgn ?m = sgn y" using True assms by (simp add: sgn_mult)
    then show ?thesis
      using True 
      by (auto simp: remdups_adj_append_two)
  next
    case False
    note x_nz = False
    show ?thesis 
    proof (cases "y = 0")
      case True
      have "sgn ?m = sgn x" using True assms by (simp add: sgn_mult)
      then show ?thesis
        using True 
        by (auto simp: remdups_adj_append_two)
    next
      case False
      note y_nz = False
      show ?thesis
      proof (cases "sgn x = sgn y")
        case True
        have "sgn ?m = sgn x"
          using True x_nz y_nz assms
          by (smt (verit, best) mult_less_0_iff sgn_if zero_less_mult_iff)
        then show ?thesis
          using True 
          by (auto simp: remdups_adj_append_two)
      next
        case False
        show ?thesis
        proof (cases "?m = 0")
          case True
          then show ?thesis by simp
        next
          case False
          have "sgn ?m = sgn x \<or> sgn ?m = sgn y"
            using False x_nz y_nz assms
            by (smt (verit) mult_less_0_iff sgn_if zero_less_mult_iff)
            
          then show ?thesis
          proof
            assume "sgn ?m = sgn x"
            then show ?thesis 
              by (auto simp: remdups_adj_append_two)
          next
            assume "sgn ?m = sgn y"

          have M1_eval: "?M1 = [sgn x, sgn y, sgn y]"
            using `sgn ?m = sgn y` x_nz y_nz by (simp add: sgn_if)
            
          have M2_eval: "?M2 = [sgn x, sgn y]" 
            using x_nz y_nz 
            by (simp add: sgn_eq_0_iff)

          have "remdups_adj (?L @ ?M1 @ ?R) = remdups_adj ((?L @ [sgn x]) @ sgn y # sgn y # ?R)"
            using M1_eval by simp
            
          also have "... = remdups_adj ((?L @ [sgn x]) @ sgn y # ?R)"
            using remdups_adj_append_two 
            by metis
            
          also have "... = remdups_adj (?L @ ?M2 @ ?R)"
            using M2_eval by simp
            
          finally show ?thesis .
          qed
        qed
      qed
    qed
  qed

  then show ?thesis using LHS RHS by simp
qed

lemma length_remdups_adj_insert_le:
  "length (remdups_adj (xs @ ys)) \<le> length (remdups_adj (xs @ y # ys))"
proof (induct xs)
  case Nil
  show ?case
  proof (cases ys)
    case Nil then show ?thesis by simp
  next
    case (Cons z zs)

    then show ?thesis by simp
  qed
next
  case (Cons a xs)
  let ?L = "xs @ ys"
  let ?R = "xs @ y # ys"
  
  have IH: "length (remdups_adj ?L) \<le> length (remdups_adj ?R)"
    using Cons.hyps .

  show ?case
  proof (cases "?L = []")
    case True
    then show ?thesis by simp 
  next
    case False
    show ?thesis 
    proof (cases "xs = []")
      case False
      then have "hd (remdups_adj ?L) = hd (remdups_adj ?R)"
        by (simp add: remdups_adj_Cons)
      then show ?thesis 
        using IH False
        by (smt (verit) Nil_is_append_conv append_Cons hd_append2 length_Suc_conv
            list.distinct(1) list.inject list.sel(1) not_less_eq_eq
            remdups_adj.elims)
    next
      case True
      show ?thesis
        using IH True 
        by (smt (verit) append_Cons append_Nil length_Suc_conv list.distinct(1)
            list.inject nle_le not_less_eq_eq remdups_adj.elims)
    qed
  qed
qed

lemma sign_changes_remove_general:
  fixes x :: real
  shows "sign_changes (us @ vs) \<le> sign_changes (us @ [x] @ vs)"
proof (cases "x = 0")
  case True
  then show ?thesis
    by (simp add: sign_changes_def)
next
  case False
  let ?signs_U = "filter (\<lambda>z. z \<noteq> 0) (map sgn us)"
  let ?signs_V = "filter (\<lambda>z. z \<noteq> 0) (map sgn vs)"
  
  have LHS: "sign_changes (us @ vs) = length (remdups_adj (?signs_U @ ?signs_V)) - 1"
    by (simp add: sign_changes_def filter_map o_def)

  have RHS: "sign_changes (us @ [x] @ vs) = length (remdups_adj (?signs_U @ [sgn x] @ ?signs_V)) - 1"
    using False
    by (simp add: sgn_eq_0_iff sign_changes_def)

  have "length (remdups_adj (?signs_U @ ?signs_V)) \<le> length (remdups_adj (?signs_U @ sgn x # ?signs_V))"
    using length_remdups_adj_insert_le  by fast
    
  then show ?thesis 
    using LHS RHS by simp
qed

fun interleave_dc :: "real \<Rightarrow> real list \<Rightarrow> real list" where
  "interleave_dc t [] = []"
| "interleave_dc t [x] = [x]"
| "interleave_dc t (x # y # zs) =
     x # ((1 - t) * x + t * y) # interleave_dc t (y # zs)"

lemma interleave_dc_collapse:
  "interleave_dc t (y # zs) = y # tl (interleave_dc t (y # zs))"
  by (cases zs) simp_all

lemma sign_changes_interleave_dc_gen:
  fixes us xs :: "real list"
  fixes t :: real
  assumes t0: "0 < t" and t1: "t < 1"
  shows "sign_changes (us @ interleave_dc t xs) = sign_changes (us @ xs)"
proof (induction xs arbitrary: us)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons b ys)
    let ?m = "(1 - t) * a + t * b"

    have decomp: "interleave_dc t (b # ys) = b # tl (interleave_dc t (b # ys))"
      by (cases ys) simp_all

    have step1:
      "sign_changes (us @ interleave_dc t (a # b # ys))
       = sign_changes (us @ [a, ?m, b] @ tl (interleave_dc t (b # ys)))"
      using decomp by simp

    have step2:
      "sign_changes (us @ [a, ?m, b] @ tl (interleave_dc t (b # ys)))
       = sign_changes (us @ [a, b] @ tl (interleave_dc t (b # ys)))"
      using sign_changes_convex_insert_general[OF t0 t1,
            of us a b "tl (interleave_dc t (b # ys))"]
      by simp

    have step3:
      "sign_changes (us @ [a, b] @ tl (interleave_dc t (b # ys)))
       = sign_changes ((us @ [a]) @ interleave_dc t (b # ys))"
      using decomp by simp

    have step4:
      "sign_changes ((us @ [a]) @ interleave_dc t (b # ys))
       = sign_changes ((us @ [a]) @ (b # ys))"
      using Cons.IH[of "us @ [a]"] Cons by simp

    show ?thesis
      using Cons step1 step2 step3 step4 by simp
  qed
qed




fun strip_even :: "'a list \<Rightarrow> 'a list" where
  "strip_even [] = []"
| "strip_even [x] = []"
| "strip_even (x # y # zs) = y # strip_even zs"

lemma sign_changes_strip_even_le:
  fixes us zs :: "real list"
  shows "sign_changes (us @ strip_even zs) \<le> sign_changes (us @ zs)"
proof (induction zs arbitrary: us rule: strip_even.induct)
  case 1
  then show ?case by simp

next
  case (2 a)
  have "sign_changes (us @ strip_even [a]) = sign_changes (us @ [])" by simp
  also have "... \<le> sign_changes (us @ [a])"
    using sign_changes_remove_general 
    by (metis append.right_neutral)
  finally show ?case by simp

next
  case (3 a b zs)
  have le_tail:
    "sign_changes ((us @ [b]) @ strip_even zs) \<le> sign_changes ((us @ [b]) @ zs)"
    using "3" by blast

  have le1:
    "sign_changes (us @ b # strip_even zs) \<le> sign_changes (us @ b # zs)"
    using le_tail by simp

  have le2:
    "sign_changes (us @ b # zs) \<le> sign_changes (us @ a # b # zs)"
    using sign_changes_remove_general 
    by auto

  show ?case
    using le_trans[OF le1 le2] by simp
qed

lemma dc_step_Cons2 [simp]:
  "dc_step t (x # y # zs) = ((1 - t) * x + t * y) # dc_step t (y # zs)"
  by (simp add: dc_step_def)

lemma strip_even_interleave_dc:
  "strip_even (interleave_dc t xs) = dc_step t xs"
proof (induction t xs rule: interleave_dc.induct)
  case (1 t)
  then show ?case by (simp add: dc_step_def)
next
  case (2 t x) 
  then show ?case by (simp add: dc_step_def)
next
  case (3 t x y zs)
  let ?m = "(1 - t) * x + t * y"
  have "strip_even (interleave_dc t (x # y # zs))
        = ?m # strip_even (interleave_dc t (y # zs))"
    by simp
  also have "... = ?m # dc_step t (y # zs)"
    using 3 by blast
  also have "... = dc_step t (x # y # zs)"
    by simp
  finally show ?case .
qed

lemma sign_changes_dc_step_le:
  fixes us xs :: "real list"
  assumes "0 < t" "t < 1"
  shows "sign_changes (us @ dc_step t xs) \<le> sign_changes (us @ xs)"
proof -
  have "sign_changes (us @ dc_step t xs)
        = sign_changes (us @ strip_even (interleave_dc t xs))"
    by (simp add: strip_even_interleave_dc)
  also have "... \<le> sign_changes (us @ interleave_dc t xs)"
    using sign_changes_strip_even_le by simp
  also have "... = sign_changes (us @ xs)"
    using sign_changes_interleave_dc_gen[OF assms] by simp
  finally show ?thesis .
qed

definition dc_split_list :: "real \<Rightarrow> real list \<Rightarrow> real list" where
  "dc_split_list t xs = dc_left t xs @ tl (dc_right t xs)"

lemma last_dc_left:
  "xs \<noteq> [] \<Longrightarrow> last (dc_left t xs) = hd (last (dc_triangle t xs))" 
  by (simp add: dc_left_def last_map)

lemma last_dc_triangle_length1:
  assumes "xs \<noteq> []"
  shows   "length (last (dc_triangle t xs)) = 1"
using assms
proof (induction t xs rule: dc_triangle.induct)
  case (1 t)
  then show ?case by simp
next
  case (2 t x)
  then show ?case by simp
next
  case (3 t xs)
  show ?case
    using "3.IH" by force
qed

lemma hd_dc_right:
  assumes "xs \<noteq> []"
  shows   "hd (dc_right t xs) = last (dc_left t xs)"
proof -
  have tri_ne: "dc_triangle t xs \<noteq> []"
    using assms by simp

  have len1: "length (last (dc_triangle t xs)) = 1"
    using last_dc_triangle_length1[OF assms] .

  have hd_eq_last_last:
    "hd (last (dc_triangle t xs)) = last (last (dc_triangle t xs))"
  proof -
    obtain u where L: "last (dc_triangle t xs) = [u]"
      using len1 by (cases "last (dc_triangle t xs)") auto
    then show ?thesis by simp
  qed

  have left_last:
    "last (dc_left t xs) = hd (last (dc_triangle t xs))"
    using tri_ne by (simp add: dc_left_def last_map)

  have right_hd:
    "hd (dc_right t xs) = last (last (dc_triangle t xs))"
    using tri_ne
    by (simp add: dc_right_def hd_rev last_map)

  show ?thesis
    using left_last right_hd hd_eq_last_last by simp
qed

lemma dc_right_unfold_len2:
  assumes "2 \<le> length xs"
  shows "dc_right t xs = dc_right t (dc_step t xs) @ [last xs]"
proof -
  have tri: "dc_triangle t xs = xs # dc_triangle t (dc_step t xs)"
    using assms by (cases xs; cases "tl xs"; simp)

  have maplast:
    "map last (dc_triangle t xs)
     = last xs # map last (dc_triangle t (dc_step t xs))"
    using tri assms by simp

  show ?thesis
    unfolding dc_right_def
    using maplast assms
    by simp
qed

lemma dc_split_list_unfold_len2:
  assumes "2 \<le> length xs"
  shows "dc_split_list t xs =
           [hd xs] @ dc_split_list t (dc_step t xs) @ [last xs]"
proof -
  have step_ne: "dc_right t (dc_step t xs) \<noteq> []"
    using assms
    by (metis One_nat_def Suc_1 diff_is_0_eq length_dc_right length_dc_step
        list.size(3) not_less_eq_eq one_le_numeral)

  have tl_append:
    "tl (dc_right t (dc_step t xs) @ [last xs])
     = tl (dc_right t (dc_step t xs)) @ [last xs]"
    using step_ne by (cases "dc_right t (dc_step t xs)") simp_all

  show ?thesis
    unfolding dc_split_list_def
    using assms
    by (simp add: dc_left_unfold_len2 dc_right_unfold_len2 tl_append)
qed

lemma sign_changes_append_ge_sum:
  fixes us vs :: "real list"
  shows "sign_changes us + sign_changes vs \<le> sign_changes (us @ vs)"
proof (induction vs arbitrary: us)
  case Nil
  then show ?case by simp
next
  case (Cons a vs)
  show ?case
  proof (cases "a = 0")
    case True
    have "sign_changes us + sign_changes (a # vs) = sign_changes us + sign_changes vs"
      using True by simp
    also have "... \<le> sign_changes (us @ vs)"
      using Cons.IH by simp
    also have "... = sign_changes (us @ a # vs)"
      using True by (simp add: sign_changes_def)
    finally show ?thesis by simp
  next
    case False
    have grow: "sign_changes us \<le> sign_changes (us @ [a])"
      using sign_changes_remove_general[of us "[]" a] by simp
    have decomp:
      "sign_changes (us @ a # vs) = sign_changes (us @ [a]) + sign_changes (a # vs)"
      using sign_changes_decompose[OF False, of us vs] by simp
    have "sign_changes us + sign_changes (a # vs)
          \<le> sign_changes (us @ [a]) + sign_changes (a # vs)"
      using grow by simp
    also have "... = sign_changes (us @ a # vs)"
      using decomp by simp
    finally show ?thesis by simp
  qed
qed


lemma sign_changes_left_right_le_split_list:
  shows "sign_changes (dc_left t xs) + sign_changes (dc_right t xs)
         \<le> sign_changes (dc_split_list t xs)"
proof (cases "xs = []")
  case True
  then show ?thesis
    by (simp add: dc_split_list_def dc_left_def dc_right_def)
next
  case False
  let ?L = "dc_left t xs"
  let ?R = "dc_right t xs"

  have Lne: "?L \<noteq> []" using False
    using dc_left_def by auto
  have Rne: "?R \<noteq> []" using False
    by (simp add: dc_right_def)

  from Rne obtain m rt where R: "?R = m # rt"
    by (cases ?R) auto

  have m_last: "m = last ?L"
    using hd_dc_right[OF False] R 
    by (metis list.sel(1))

  have split: "dc_split_list t xs = ?L @ rt"
    using R by (simp add: dc_split_list_def)

  show ?thesis
  proof (cases "m = 0")
    case True
    have scR: "sign_changes ?R = sign_changes rt"
      using True R by simp
    have le: "sign_changes ?L + sign_changes rt \<le> sign_changes (?L @ rt)"
      using sign_changes_append_ge_sum[of ?L rt] .
    show ?thesis
      using split scR le by simp
  next
    case mne: False

    have Lform: "?L = butlast ?L @ [m]"
      using Lne m_last by (simp)

    have eq1: "?L @ rt = butlast ?L @ m # rt"
      using Lform by simp

    have decomp1:
      "sign_changes (butlast ?L @ m # rt)
       = sign_changes (butlast ?L @ [m]) + sign_changes (m # rt)"
      using sign_changes_decompose[OF mne, of "butlast ?L" rt] by simp

    have decomp:
      "sign_changes (?L @ rt) = sign_changes ?L + sign_changes ?R"
      using R Lform eq1 decomp1
      by presburger

    show ?thesis
      using split decomp by simp
  qed
qed

lemma dc_split_list_cons2:
  "dc_split_list t (x # y # zs) =
     x # dc_split_list t (dc_step t (x # y # zs)) @ [last (x # y # zs)]"
  by (simp add: dc_split_list_unfold_len2)


lemma sign_changes_interleave_dc_ctx:
  fixes us vs xs :: "real list"
  fixes t :: real
  assumes "0 < t" "t < 1"
  shows "sign_changes (us @ interleave_dc t xs @ vs) = sign_changes (us @ xs @ vs)"
proof (induction xs arbitrary: us vs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons b ys)
    let ?m = "(1 - t) * a + t * b"

    have decomp: "interleave_dc t (b # ys) = b # tl (interleave_dc t (b # ys))"
      using interleave_dc_collapse by simp

    have step1:
      "sign_changes (us @ interleave_dc t (a # b # ys) @ vs)
       = sign_changes (us @ [a, ?m, b] @ tl (interleave_dc t (b # ys)) @ vs)"
      using decomp 
      by (metis append_Cons append_Nil interleave_dc.simps(3))

    have step2:
      "sign_changes (us @ [a, ?m, b] @ tl (interleave_dc t (b # ys)) @ vs)
       = sign_changes (us @ [a, b] @ tl (interleave_dc t (b # ys)) @ vs)"
      using sign_changes_convex_insert_general 
      using assms(1,2) by blast

    have step3:
      "sign_changes (us @ [a, b] @ tl (interleave_dc t (b # ys)) @ vs)
       = sign_changes ((us @ [a]) @ interleave_dc t (b # ys) @ vs)"
      using decomp 
      by (metis append.assoc append_Cons append_self_conv2)

    have step4:
      "sign_changes ((us @ [a]) @ interleave_dc t (b # ys) @ vs)
       = sign_changes ((us @ [a]) @ (b # ys) @ vs)"
      using Cons.IH[OF Cons.prems, of "us @ [a]" vs] Cons by simp

    show ?thesis
      using step1 step2 step3 step4 Cons by simp
  qed
qed

fun strip_odd :: "'a list \<Rightarrow> 'a list" where
  "strip_odd [] = []"
| "strip_odd [x] = [x]"
| "strip_odd (x # y # zs) = x # strip_odd zs"

lemma sign_changes_strip_odd_le_ctx:
  fixes us vs zs :: "real list"
  shows "sign_changes (us @ strip_odd zs @ vs) \<le> sign_changes (us @ zs @ vs)"
proof (induction zs arbitrary: us vs rule: strip_odd.induct)
  case 1
  then show ?case by simp
next
  case (2 a)
  then show ?case by simp
next
  case (3 a b zs)
  have le_tail:
    "sign_changes ((us @ [a]) @ strip_odd zs @ vs) \<le> sign_changes ((us @ [a]) @ zs @ vs)"
    using 3 by blast

  have le1:
    "sign_changes (us @ a # strip_odd zs @ vs) \<le> sign_changes (us @ a # zs @ vs)"
    using le_tail by simp

  have le2:
    "sign_changes (us @ a # zs @ vs) \<le> sign_changes (us @ a # b # zs @ vs)"
    using sign_changes_remove_general[of "us @ [a]" "zs @ vs" b]
    by simp

  show ?case
    using le_trans[OF le1 le2] by simp
qed



lemma strip_odd_butlast_tl_interleave_dc:
  "strip_odd (butlast (tl (interleave_dc t xs))) = dc_step t xs"
proof (induction t xs rule: interleave_dc.induct)
  case (1 t)
  then show ?case
    by (metis butlast.simps(1) interleave_dc.simps(1) list.sel(2) strip_even.simps(1)
        strip_even_interleave_dc strip_odd.simps(1))
next
  case (2 t x)
  then show ?case by (simp add: dc_step_def)
next
  case (3 t x y zs)
  let ?m = "(1 - t) * x + t * y"
  show ?case
  proof (cases zs)
    case Nil
    then show ?thesis
      by (simp add: dc_step_def)
  next
    case (Cons z zs')
    have "strip_odd (butlast (tl (interleave_dc t (x # y # z # zs'))))
        = strip_odd (butlast (?m # interleave_dc t (y # z # zs')))"
      by simp
    also have "... = strip_odd (?m # butlast (interleave_dc t (y # z # zs')))"
      by simp
    also have "... = strip_odd (?m # y # butlast (tl (interleave_dc t (y # z # zs'))))"
      by simp
    also have "... = ?m # strip_odd (butlast (tl (interleave_dc t (y # z # zs'))))"
      by simp
    also have "... = ?m # dc_step t (y # z # zs')"
      using "3.IH" Cons by simp
    also have "... = dc_step t (x # y # z # zs')"
      by simp
    finally show ?thesis 
      using local.Cons by blast
  qed
qed

lemma last_interleave_dc:
  assumes "xs \<noteq> []"
  shows "last (interleave_dc t xs) = last xs"
using assms
proof (induction t xs rule: interleave_dc.induct)
  case (1 t)
  then show ?case by simp
next
  case (2 t x)
  then show ?case by simp
next
  case (3 t x y zs)
  show ?case
  proof (cases zs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons z zs')
    have "last (interleave_dc t (x # y # z # zs')) = last (interleave_dc t (y # z # zs'))"
      by simp
    also have "... = last (y # z # zs')" using "3.IH" local.Cons by fastforce
    also have "... = last (x # y # z # zs')" by simp
    finally show ?thesis
      using local.Cons by blast
  qed
qed



lemma sign_changes_drop_originals_from_interleave:
  fixes us vs xs :: "real list"
  assumes "2 \<le> length xs"
  shows "sign_changes (us @ ([hd xs] @ dc_step t xs @ [last xs]) @ vs)
       \<le> sign_changes (us @ interleave_dc t xs @ vs)"
proof -
  from assms obtain x y zs where xs: "xs = x # y # zs"
    by (cases xs; simp; cases "tl xs"; simp)

  let ?L = "interleave_dc t xs"
  have tl_ne: "tl ?L \<noteq> []"
    using xs by simp

  have tl_decomp:
    "tl ?L = butlast (tl ?L) @ [last xs]"
    using tl_ne xs last_interleave_dc
    by (metis last_tl list.discI snoc_eq_iff_butlast)

  have L_decomp:
    "?L = [hd xs] @ butlast (tl ?L) @ [last xs]"
    using xs tl_decomp by simp

  have main_le:
    "sign_changes ((us @ [hd xs]) @ strip_odd (butlast (tl ?L)) @ [last xs] @ vs)
     \<le> sign_changes ((us @ [hd xs]) @ butlast (tl ?L) @ [last xs] @ vs)"
    using sign_changes_strip_odd_le_ctx by presburger

  have strip_id:
    "strip_odd (butlast (tl ?L)) = dc_step t xs"
    using strip_odd_butlast_tl_interleave_dc by simp

  show ?thesis
    using main_le strip_id L_decomp
    by (metis append.assoc)
qed

lemma length_dc_step_lt:
  assumes "2 \<le> length xs"
  shows "length (dc_step t xs) < length xs"
  using assms
  by (cases xs; cases "tl xs"; simp)

lemma sign_changes_dc_split_ctx:
  fixes t :: real and xs :: "real list"
  assumes t0: "0 < t" and t1: "t < 1"
  shows "(\<forall>us vs. sign_changes (us @ dc_split_list t xs @ vs)
                 \<le> sign_changes (us @ xs @ vs))"
proof (induction xs rule: length_induct)
  case (1 xs)
  show ?case
  proof (intro allI)
    fix us vs
    show "sign_changes (us @ dc_split_list t xs @ vs) \<le> sign_changes (us @ xs @ vs)"
    proof (cases xs)
      case Nil
      then show ?thesis
        by (simp add: dc_split_list_def dc_left_def dc_right_def)
    next
      case (Cons a xs1)
      note xs_outer = Cons
      show ?thesis
      proof (cases xs1)
        case Nil
        then show ?thesis
          using Cons by (simp add: dc_split_list_def dc_left_def dc_right_def)
      next
        case (Cons b zs)
        have len_step: "length (dc_step t xs) < length xs"
          using length_dc_step_lt Cons xs_outer
        by force

        have IH_step:
          "\<forall>u v. sign_changes (u @ dc_split_list t (dc_step t xs) @ v)
               \<le> sign_changes (u @ dc_step t xs @ v)"
          using "1.IH" len_step 
          by blast

        have unfold:
          "dc_split_list t xs = a # dc_split_list t (dc_step t xs) @ [last xs]"
          using Cons xs_outer
          using dc_split_list_cons2 by blast

        have le_IH_inst:
          "sign_changes ((us @ [a]) @ dc_split_list t (dc_step t xs) @ ([last xs] @ vs))
           \<le> sign_changes ((us @ [a]) @ dc_step t xs @ ([last xs] @ vs))"
          using IH_step by blast

        have le_bridge:
          "sign_changes (us @ ([hd xs] @ dc_step t xs @ [last xs]) @ vs)
           \<le> sign_changes (us @ interleave_dc t xs @ vs)"
          using sign_changes_drop_originals_from_interleave[of us xs t vs]
          by (metis Suc_1 dc_step_Cons2 diff_is_0_eq length_0_conv length_dc_step
              list.distinct(1) local.Cons not_less_eq_eq
              sign_changes_drop_originals_from_interleave xs_outer)

        have eq_interleave:
          "sign_changes (us @ interleave_dc t xs @ vs) = sign_changes (us @ xs @ vs)"
          using sign_changes_interleave_dc_ctx[OF t0 t1, of us xs vs] .
        have
          "sign_changes (us @ dc_split_list t xs @ vs)
           = sign_changes ((us @ [a]) @ dc_split_list t (dc_step t xs) @ ([last xs] @ vs))"
          using unfold by (simp)
        also have "... \<le> sign_changes ((us @ [a]) @ dc_step t xs @ ([last xs] @ vs))"
          using le_IH_inst .
        also have "... = sign_changes (us @ ([a] @ dc_step t xs @ [last xs]) @ vs)"
          by (simp)
        also have "... = sign_changes (us @ ([hd xs] @ dc_step t xs @ [last xs]) @ vs)"
          using Cons xs_outer by auto
        also have "... \<le> sign_changes (us @ interleave_dc t xs @ vs)"
          using le_bridge .
        also have "... = sign_changes (us @ xs @ vs)"
          using eq_interleave .
        finally show ?thesis .
      qed
    qed
  qed
qed

lemma sign_changes_dc_split:
  assumes "0 < t" "t < 1"
  shows "sign_changes (dc_split_list t xs) \<le> sign_changes xs"
  using sign_changes_dc_split_ctx[OF assms, of xs]
  by (metis append.right_neutral append_Nil)

lemma sign_changes_final:
  assumes "0 < t" "t < 1"
  shows "sign_changes (dc_left t xs) + sign_changes (dc_right t xs)
         \<le> sign_changes xs"
  by (meson assms(1,2) dual_order.trans sign_changes_dc_split
      sign_changes_left_right_le_split_list)

end