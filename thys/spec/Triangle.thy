theory Triangle
  imports Three_Circles.Bernstein_01
begin

text \<open>The de Casteljau triangle as a list of rows, and its algebra.
  Layer: FUNCTIONAL SPEC.
  \<open>dc_step\<close> computes a row from the one above it; \<open>dc_triangle\<close> iterates it, and
  \<open>dc_left\<close> and \<open>dc_right\<close> read off the two boundaries.
  Main exports: \<open>Bernstein_coeffs_01_split_left\<close> and \<open>Bernstein_coeffs_01_split_right\<close>: the
  boundaries are the Bernstein coefficients of the two pieces of a split at \<open>t\<close>. The
  sign-change induction built on them is in \<open>List_Changes\<close>, and the splitting inequality in
  \<open>Bernstein_Split\<close>.\<close>

lemma pascal_bernstein_step:
  assumes "0 < i" "i \<le> j"
  shows "real (j choose i) * t^i * (1-t)^(j-i) = 
         (1-t) * (real ((j-1) choose i) * t^i * (1-t)^(j - 1 - i)) + 
         t * (real ((j-1) choose (i-1)) * t^(i - 1) * (1-t)^(j - i))"
proof -
  have term1_zero: "(j-1) choose i = 0" if "i = j"
    using assms(1) that by force

  have term1_exp: "(1-t) * (1-t)^(j - 1 - i) = (1-t)^(j-i)" if "i < j"
  proof -
    have "j - 1 - i = (j - i) - 1" using that by auto
    moreover have "j - i > 0" using that by auto
    ultimately show ?thesis 
      by (simp add: power_eq_if)
  qed

  have term2_simp: "t * (t^(i - 1)) = t^i"
    using assms(1)
    by (simp add: power_eq_if)

  show ?thesis
  proof (cases "i = j")
    case True
    then show ?thesis 
      using term1_zero term2_simp assms by auto
  next
    case False
    then have i_le_pred_j: "i \<le> j - 1" using assms by simp

    have rhs_simplified: 
      "(1-t) * (real ((j-1) choose i) * t^i * (1-t)^(j - 1 - i)) + 
       t * (real ((j-1) choose (i-1)) * t^(i - 1) * (1-t)^(j - i)) =
       real ((j-1) choose i) * t^i * (1-t)^(j-i) + 
       real ((j-1) choose (i-1)) * t^i * (1-t)^(j - i)"
      using term1_exp term2_simp
      by (smt (verit, best) False assms(2) le_eq_less_or_eq mult.assoc mult.left_commute
          term1_exp term2_simp)

    also have "... = (real ((j-1) choose i) + real ((j-1) choose (i-1))) * t^i * (1-t)^(j-i)"
      by (simp add: algebra_simps)
    also have "... = real (j choose i) * t^i * (1-t)^(j-i)"
      using assms False 
      using binomial_eq_0_iff choose_reduce_nat zero_less_binomial
        zero_less_iff_neq_zero by fastforce
    finally show ?thesis by simp
  qed
qed

lemma binomial_swap_identity:
  assumes "k \<le> i" "i \<le> p"
  shows "real (p choose i) * real (i choose k) = real (p choose k) * real ((p-k) choose (i-k))"
  using assms
  by (metis choose_mult of_nat_mult)

lemma power_diff_expansion:
  fixes t x :: real
  shows "(1 - t * x) ^ m = (\<Sum>j=0..m. (m choose j) * ((1-t)*x)^j * (1-x)^(m-j))"
proof -
  have "1 - t * x = ((1-t)*x) + (1-x)" by (simp add: algebra_simps)
  then show ?thesis
    by (metis (lifting) ext atLeast0AtMost binomial_ring)
qed

definition dc_step :: "real \<Rightarrow> real list \<Rightarrow> real list" where
  "dc_step t xs = map (\<lambda>(a, b). (1 - t) * a + t * b) (zip xs (tl xs))"

lemma length_dc_step [simp]: 
  "length (dc_step t xs) = (if xs = [] then 0 else length xs - 1)"
  by (auto simp: dc_step_def)

lemma nth_dc_step [simp]:
  assumes "i < length xs - 1"
  shows "dc_step t xs ! i = (1 - t) * (xs ! i) + t * (xs ! (i + 1))"
  using assms unfolding dc_step_def 
  by (auto simp: nth_tl) 

lemma dc_step_rev:
  "dc_step t (rev xs) = rev (dc_step (1-t) xs)"
proof (rule list_eq_iff_nth_eq[THEN iffD2])
  show "length (dc_step t (rev xs)) = length (rev (dc_step (1 - t) xs)) \<and>
      (\<forall>i<length (dc_step t (rev xs)).
        dc_step t (rev xs) ! i = rev (dc_step (1 - t) xs) ! i)" 
  proof (intro conjI)
    show "length (dc_step t (rev xs)) = length (rev (dc_step (1 - t) xs))"
      by simp
 show "\<forall>i<length (dc_step t (rev xs)).
        dc_step t (rev xs) ! i = rev (dc_step (1 - t) xs) ! i "
   by (smt (verit) Suc_pred add.commute add.right_neutral diff_diff_left diff_le_self
       le_eq_less_or_eq length_dc_step length_greater_0_conv length_rev length_tl lessI
       list.sel(2) not_gr_zero nth_dc_step plus_1_eq_Suc rev_nth
       zero_less_diff)
  qed
qed

fun dc_triangle :: "real \<Rightarrow> real list \<Rightarrow> real list list" where
  "dc_triangle t [] = []" |
  "dc_triangle t [x] = [[x]]" |
  "dc_triangle t xs = xs # dc_triangle t (dc_step t xs)"

definition dc_left :: "real \<Rightarrow> real list \<Rightarrow> real list" where
  "dc_left t xs = map hd (dc_triangle t xs)"

definition dc_right :: "real \<Rightarrow> real list \<Rightarrow> real list" where
  "dc_right t xs = rev (map last (dc_triangle t xs))"

lemma length_dc_triangle [simp]: 
  "length (dc_triangle t xs) = length xs"
  by (induction t xs rule: dc_triangle.induct) auto

lemma dc_triangle_ne_Nil [simp]: 
  "xs \<noteq> [] \<Longrightarrow> dc_triangle t xs \<noteq> []"
  by (induction t xs rule: dc_triangle.induct) auto

lemma length_dc_left [simp]: 
  "length (dc_left t xs) = length xs"
  by (simp add: dc_left_def)

lemma length_dc_right [simp]: 
  "length (dc_right t xs) = length xs"
  by (simp add: dc_right_def)

lemma dc_triangle_rev:
  "dc_triangle t (rev xs) = map rev (dc_triangle (1-t) xs)"
proof (induction xs arbitrary: t rule: length_induct)
  case (1 xs)
  then show ?case 
    by (smt (verit) One_nat_def dc_step_rev dc_triangle.elims dc_triangle.simps(1,2)
        diff_less length_dc_step length_greater_0_conv lessI list.map(1,2)
        rev_is_Nil_conv rev_singleton_conv)
qed

lemma dc_right_eq_rev_dc_left:
  "dc_right t xs = rev (dc_left (1-t) (rev xs))"
  unfolding dc_right_def dc_left_def
  by (simp add: dc_triangle_rev hd_rev)

definition basis_list :: "nat \<Rightarrow> nat \<Rightarrow> real list" where
  "basis_list k p = (replicate (p + 1) 0)[k := 1]"

lemma length_basis_list [simp]:
  "length (basis_list k p) = p + 1"
  by (metis basis_list_def length_list_update length_replicate)

lemma nth_basis_list:
  "i < p + 1 \<longrightarrow> basis_list k p ! i = (if i = k then 1 else 0)"
  unfolding basis_list_def 
  by (metis diff_zero length_map length_upt map_replicate_trivial nth_list_update_eq
      nth_list_update_neq nth_replicate)

lemma nth_map2_dsc:
  assumes "i < length xs" "i < length ys"
  shows "map2 f xs ys ! i = f (xs ! i) (ys ! i)"
  using assms
proof (induction i arbitrary: xs ys)
  case 0
  then show ?case
    by (cases xs; cases ys; simp)
next
  case (Suc i)
  then show ?case
    by (cases xs; cases ys; simp)
qed

lemma dc_step_linear_add:
  assumes len: "length xs = length ys"
  shows "dc_step t (map2 (+) xs ys) = map2 (+) (dc_step t xs) (dc_step t ys)"
proof (cases xs)
  case Nil
  then show ?thesis
    using len by (cases ys) (simp_all add: dc_step_def)
next
  case xsCons: (Cons x xs')
  show ?thesis
  proof (cases xs')
    case Nil
    from len xsCons Nil obtain y where ys: "ys = [y]"
      by (cases ys) simp_all
    show ?thesis
      by (simp add: xsCons Nil ys dc_step_def)
  next
    case xs'Cons: (Cons x2 xs'')
    have ys_ne: "ys \<noteq> []" using len xsCons by auto
    have map2_ne: "map2 (+) xs ys \<noteq> []"
      using xsCons ys_ne by auto

    have len_map2: "length (map2 (+) xs ys) = length xs"
      using len by simp

    show ?thesis
    proof (rule nth_equalityI)
      show "length (dc_step t (map2 (+) xs ys)) =
            length (map2 (+) (dc_step t xs) (dc_step t ys))"
        using len xsCons ys_ne map2_ne by simp
    next
      fix i
      assume hi: "i < length (dc_step t (map2 (+) xs ys))"

      have i_lt_map2m1: "i < length (map2 (+) xs ys) - 1"
        using hi map2_ne by simp
      have i_lt_xsm1: "i < length xs - 1"
        using i_lt_map2m1 by (simp add: len_map2)
      have i_lt_ysm1: "i < length ys - 1"
        using i_lt_xsm1 len by simp

      have i_lt_xs: "i < length xs" using i_lt_xsm1 by arith
      have i1_lt_xs: "i + 1 < length xs" using i_lt_xsm1 by arith
      have i_lt_ys: "i < length ys" using i_lt_ysm1 by arith
      have i1_lt_ys: "i + 1 < length ys" using i_lt_ysm1 by arith

      have lhs:
        "dc_step t (map2 (+) xs ys) ! i =
           (1 - t) * (map2 (+) xs ys ! i) + t * (map2 (+) xs ys ! (i + 1))"
        using nth_dc_step[of i "map2 (+) xs ys" t] i_lt_map2m1 by simp

      have map2_i:  "map2 (+) xs ys ! i = xs ! i + ys ! i"
        using nth_map2_dsc[OF i_lt_xs i_lt_ys] by auto
      have map2_i1: "map2 (+) xs ys ! (i + 1) = xs ! (i + 1) + ys ! (i + 1)"
        using nth_map2_dsc[of "i+1" xs ys "(+)"] i1_lt_xs i1_lt_ys by simp

      have step_xs:
        "dc_step t xs ! i = (1 - t) * (xs ! i) + t * (xs ! (i + 1))"
        using nth_dc_step[OF i_lt_xsm1] .
      have step_ys:
        "dc_step t ys ! i = (1 - t) * (ys ! i) + t * (ys ! (i + 1))"
        using nth_dc_step[OF i_lt_ysm1] .

      have i_lt_step_xs: "i < length (dc_step t xs)"
        using i_lt_xsm1 xsCons by simp
      have i_lt_step_ys: "i < length (dc_step t ys)"
        using i_lt_ysm1 ys_ne by (simp add: ys_ne)

      have rhs:
        "map2 (+) (dc_step t xs) (dc_step t ys) ! i =
           dc_step t xs ! i + dc_step t ys ! i"
        using nth_map2_dsc[of i "dc_step t xs" "dc_step t ys" "(+)"] i_lt_step_xs i_lt_step_ys
        by simp

      show "dc_step t (map2 (+) xs ys) ! i =
            map2 (+) (dc_step t xs) (dc_step t ys) ! i"
        using lhs rhs map2_i map2_i1 step_xs step_ys
        by (simp add: algebra_simps)
    qed
  qed
qed

lemma dc_left_unfold2:
  "dc_left t (x # y # zs) = x # dc_left t (dc_step t (x # y # zs))"
  unfolding dc_left_def by simp

lemma dc_left_unfold_len2:
  assumes "2 \<le> length xs"
  shows "dc_left t xs = hd xs # dc_left t (dc_step t xs)"
proof -
  obtain a b zs where xs: "xs = a # b # zs"
    using assms by (cases xs; cases "tl xs"; auto)
  show ?thesis
    by (simp add: xs dc_left_def)
qed

lemma dc_right_unfold2:
  "dc_right t (x # y # zs) =
     dc_right t (dc_step t (x # y # zs)) @ [last (x # y # zs)]"
  unfolding dc_right_def by simp


lemma dc_left_linear_sum:
  assumes len: "length xs = length ys"
  shows "dc_left t (map2 (+) xs ys) = map2 (+) (dc_left t xs) (dc_left t ys)"
using len
proof (induction xs arbitrary: ys rule: length_induct)
  case (1 xs)
  have IH:
    "\<And>xs' ys'. length xs' < length xs \<Longrightarrow> length xs' = length ys' \<Longrightarrow>
      dc_left t (map2 (+) xs' ys') = map2 (+) (dc_left t xs') (dc_left t ys')"
    using "1.IH" by blast

  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      using "1.prems" 
      by (simp add: dc_left_def)
  next
    case xsCons: (Cons x xs1)
    show ?thesis
    proof (cases xs1)
      case Nil
      from "1.prems" xsCons Nil obtain y where ys: "ys = [y]"
        by (cases ys) simp_all
      show ?thesis
        by (simp add: dc_left_def local.Nil xsCons ys)
    next
      case xs1Cons: (Cons x2 xs2)
      from "1.prems" xsCons xs1Cons obtain y ys1 where ys: "ys = y # ys1"
        by (cases ys) simp_all
      then obtain y2 ys2 where ys1: "ys1 = y2 # ys2"
        using "1.prems" xsCons xs1Cons by (cases ys1) simp_all
      have ys2form: "ys = y # y2 # ys2"
        using ys ys1 by simp

      have L1:
        "dc_left t (map2 (+) xs ys)
         = (x + y) # dc_left t (dc_step t (map2 (+) xs ys))"
        using xsCons xs1Cons ys2form
        by (simp add: dc_left_unfold2)

      have L2:
        "map2 (+) (dc_left t xs) (dc_left t ys)
         = (x + y) # map2 (+) (dc_left t (dc_step t xs)) (dc_left t (dc_step t ys))"
        using xsCons xs1Cons ys2form
        by (simp add: dc_left_unfold2)

      have step_add:
        "dc_step t (map2 (+) xs ys) = map2 (+) (dc_step t xs) (dc_step t ys)"
        using dc_step_linear_add[of xs ys t] "1.prems" by simp

      have len_step:
        "length (dc_step t xs) = length (dc_step t ys)"
        using "1.prems" xsCons ys2form by simp

      have lt_step: "length (dc_step t xs) < length xs"
        using xsCons xs1Cons by simp

      have rec:
        "dc_left t (map2 (+) (dc_step t xs) (dc_step t ys))
         = map2 (+) (dc_left t (dc_step t xs)) (dc_left t (dc_step t ys))"
        using IH[OF lt_step len_step] .

      show ?thesis
        using L1 L2 step_add rec
        by simp
    qed
  qed
qed

lemma dc_step_linear_smult:
  "dc_step t (map ((*) c) xs) = map ((*) c) (dc_step t xs)"
proof (cases xs)
  case Nil
  then show ?thesis
    by (simp add: dc_step_def)
next
  case xsCons: (Cons x xs')
  show ?thesis
  proof (cases xs')
    case Nil
    then show ?thesis
      by (simp add: dc_step_def xsCons)
  next
    case xs'Cons: (Cons x2 xs'')
    show ?thesis
    proof (rule nth_equalityI)
      show "length (dc_step t (map ((*) c) xs)) = length (map ((*) c) (dc_step t xs))"
        using xsCons by simp
    next
      fix i
      assume hi: "i < length (dc_step t (map ((*) c) xs))"

      have i_lt: "i < length xs - 1"
        using hi xsCons by simp
      have i_lt_map: "i < length (map ((*) c) xs) - 1"
        using i_lt by simp

      have i_lt_len: "i < length xs" using i_lt by arith
      have i1_lt_len: "i + 1 < length xs" using i_lt by arith

      have lhs:
        "dc_step t (map ((*) c) xs) ! i =
           (1 - t) * (map ((*) c) xs ! i) + t * (map ((*) c) xs ! (i + 1))"
        using nth_dc_step[OF i_lt_map] .

      have map_i:  "map ((*) c) xs ! i = c * (xs ! i)"
        using i_lt_len by simp
      have map_i1: "map ((*) c) xs ! (i + 1) = c * (xs ! (i + 1))"
        using i1_lt_len by simp

      have step_xs:
        "dc_step t xs ! i = (1 - t) * (xs ! i) + t * (xs ! (i + 1))"
        using nth_dc_step[OF i_lt] .

      have i_lt_step: "i < length (dc_step t xs)"
        using i_lt xsCons by simp
      have rhs:
        "map ((*) c) (dc_step t xs) ! i = c * (dc_step t xs ! i)"
        using i_lt_step by simp

      show "dc_step t (map ((*) c) xs) ! i = map ((*) c) (dc_step t xs) ! i"
        using lhs rhs map_i map_i1 step_xs
        by (simp add: algebra_simps)
    qed
  qed
qed


lemma dc_step_basis:
  assumes ppos: "p > 0" and kpos: "0 < k" and kle: "k \<le> p"
  shows
    "dc_step t (basis_list k p) =
       map2 (+) (map ((*) (1 - t)) (basis_list k (p - 1)))
                (map ((*) t)       (basis_list (k - 1) (p - 1)))"
proof (rule nth_equalityI)
  have len1: "length (basis_list k (p - 1)) = p"
    using ppos by (simp add: basis_list_def)
  have len2: "length (basis_list (k - 1) (p - 1)) = p"
    using ppos by (simp add: basis_list_def)

  show "length (dc_step t (basis_list k p)) =
        length (map2 (+) (map ((*) (1 - t)) (basis_list k (p - 1)))
                         (map ((*) t)       (basis_list (k - 1) (p - 1))))"
    using ppos 
    by (metis (no_types, opaque_lifting) add.commute add_diff_cancel_left' len2
        length_basis_list length_dc_step length_map list.size(3) map_fst_zip
        zero_eq_add_iff_both_eq_0)
next
  fix i
  assume hi: "i < length (dc_step t (basis_list k p))"
  hence hi_p: "i < p"
    using ppos 
    by (metis add_diff_cancel_right' length_basis_list length_dc_step
        less_nat_zero_code)

  have hi_step: "i < length (basis_list k p) - 1"
    using hi_p ppos by simp

  have k_eq: "k = Suc (k - 1)"
    using kpos by simp

  have LHS:
    "dc_step t (basis_list k p) ! i =
       (1 - t) * (basis_list k p ! i) + t * (basis_list k p ! (i + 1))"
    using nth_dc_step[OF hi_step] .

    have i_lt1: "i < length (basis_list k (p - 1))"
    using hi_p ppos by simp 

  have i_lt2: "i < length (basis_list (k - 1) (p - 1))"
    using hi_p ppos by simp

  have RHS:
    "map2 (+) (map ((*) (1 - t)) (basis_list k (p - 1)))
             (map ((*) t)       (basis_list (k - 1) (p - 1))) ! i =
     (1 - t) * (basis_list k (p - 1) ! i) + t * (basis_list (k - 1) (p - 1) ! i)"
  proof -
    have
      "map2 (+) (map ((*) (1 - t)) (basis_list k (p - 1)))
               (map ((*) t)       (basis_list (k - 1) (p - 1))) ! i
       =
       (map ((*) (1 - t)) (basis_list k (p - 1)) ! i)
       + (map ((*) t)     (basis_list (k - 1) (p - 1)) ! i)"
      using i_lt1 i_lt2
      by (simp add: nth_map2_dsc) 
    also have "... =
       (1 - t) * (basis_list k (p - 1) ! i) + t * (basis_list (k - 1) (p - 1) ! i)"
      using i_lt1 i_lt2 by simp
    finally show ?thesis .
  qed


  have i_lt_p1: "i < p + 1" using hi_p by simp
  have i1_lt_p1: "i + 1 < p + 1" using hi_p by simp

  have bi : "basis_list k p ! i = (if i = k then 1 else 0)"
    using nth_basis_list[of i p k] i_lt_p1 by blast
  have bi1: "basis_list k p ! (i + 1) = (if i + 1 = k then 1 else 0)"
    using nth_basis_list[of "i+1" p k] i1_lt_p1 by blast

  have bpi : "basis_list k (p - 1) ! i = (if i = k then 1 else 0)"
    using nth_basis_list[of i "p-1" k] hi_p by simp
  have bpi' : "basis_list (k - 1) (p - 1) ! i = (if i = k - 1 then 1 else 0)"
    using nth_basis_list[of i "p-1" "k-1"] hi_p by simp

  have ind:
    "(if i + 1 = k then (1::real) else 0) = (if i = k - 1 then 1 else 0)"
    using kpos by auto

  show "dc_step t (basis_list k p) ! i =
        map2 (+) (map ((*) (1 - t)) (basis_list k (p - 1)))
                 (map ((*) t)       (basis_list (k - 1) (p - 1))) ! i"
    using LHS RHS [linarith_split_limit = 10000] 
    using bi bi1 bpi bpi' ind by presburger
qed

lemma dc_step_basis0_Suc:
  "dc_step t (basis_list 0 (Suc p)) = map ((*) (1 - t)) (basis_list 0 p)"
proof (rule nth_equalityI)
  show "length (dc_step t (basis_list 0 (Suc p))) =
        length (map ((*) (1 - t)) (basis_list 0 p))"
    by (simp add: basis_list_def)
next
  fix i
  assume hi: "i < length (dc_step t (basis_list 0 (Suc p)))"
  have hi': "i < length (basis_list 0 (Suc p)) - 1"
    using hi by (simp add: basis_list_def)
  have hi_p: "i < p + 1"
    using hi by (simp add: basis_list_def)

  have LHS:
    "dc_step t (basis_list 0 (Suc p)) ! i =
      (1 - t) * (basis_list 0 (Suc p) ! i) + t * (basis_list 0 (Suc p) ! (i+1))"
    using nth_dc_step[OF hi'] .

  have bi:  "basis_list 0 (Suc p) ! i = (if i = 0 then 1 else 0)"
    using nth_basis_list[of i "Suc p" 0] 
    using add_Suc hi_p less_Suc_eq by presburger
  have bi1: "basis_list 0 (Suc p) ! (i+1) = 0"
  proof -
    have "i+1 \<noteq> 0" by simp
    moreover have "i+1 < (Suc p) + 1" using hi_p by simp
    ultimately show ?thesis
      using nth_basis_list[of "i+1" "Suc p" 0] by simp
  qed

  show "dc_step t (basis_list 0 (Suc p)) ! i =
        map ((*) (1 - t)) (basis_list 0 p) ! i"
    using LHS bi bi1 hi_p nth_basis_list[of i p 0]
    by (simp add: basis_list_def algebra_simps)
qed

lemma zip_replicate_Suc:
  "zip (replicate (Suc n) a) (replicate n a) = replicate n (a, a)"
  by (induction n) simp_all

lemma dc_step_replicate0:
  "dc_step t (replicate (Suc n) (0::real)) = replicate n 0"
  unfolding dc_step_def using zip_replicate_Suc
  by (metis (no_types, lifting) One_nat_def add.right_neutral diff_Suc_Suc diff_zero
      map_replicate mult.commute mult_zero_left old.prod.case tl_replicate)

lemma dc_left_replicate0:
  "dc_left t (replicate n (0::real)) = replicate n 0"
proof (induction n)
  case 0
  then show ?case by (simp add: dc_left_def)
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by (simp add: dc_left_def)
  next
    case (Suc m)
    have "dc_left t (replicate (Suc (Suc m)) (0::real)) =
          0 # dc_left t (dc_step t (replicate (Suc (Suc m)) 0))"
      by (simp add: dc_left_unfold2)
    also have "dc_step t (replicate (Suc (Suc m)) 0) = replicate (Suc m) 0"
      using dc_step_replicate0 by blast
    also have "dc_left t (replicate (Suc m) 0) = replicate (Suc m) 0"
      using Suc.IH Suc by force
    finally show ?thesis
      using Suc by auto
  qed
qed

lemma hd_basis_list:
  "hd (basis_list k p) = (if k = 0 then 1 else 0)"
proof -
  have ne: "basis_list k p \<noteq> []"
    by (metis length_basis_list list.size(3) one_neq_zero
        zero_eq_add_iff_both_eq_0)
  have "hd (basis_list k p) = basis_list k p ! 0"
    using ne by (simp add: hd_conv_nth)
  also have "... = (if 0 = k then 1 else 0)"
    using nth_basis_list[of 0 p k] by simp
  finally show ?thesis by simp
qed

lemma dc_left_linear_smult:
  "dc_left t (map ((*) c) xs) = map ((*) c) (dc_left t xs)"
proof (induction xs rule: length_induct)
  case (1 xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      by (simp add: dc_left_def)
  next
    case Cons1: (Cons a xs1)
    show ?thesis
    proof (cases xs1)
      case Nil
      then show ?thesis
        by (simp add: dc_left_def Cons1)
    next
      case (Cons b xs2)
      have xs_eq: "xs = a # b # xs2"
        using Cons Cons1 by blast
      have len2: "2 \<le> length xs"
        using xs_eq by simp
      have len2m: "2 \<le> length (map ((*) c) xs)"
        using len2 by simp

      have L:
        "dc_left t (map ((*) c) xs) =
           hd (map ((*) c) xs) # dc_left t (dc_step t (map ((*) c) xs))"
        using dc_left_unfold_len2[OF len2m] .

      have R:
        "dc_left t xs =
           hd xs # dc_left t (dc_step t xs)"
        using dc_left_unfold_len2[OF len2] .

      have hd_map: "hd (map ((*) c) xs) = c * hd xs"
        using xs_eq by simp

      have step_map: "dc_step t (map ((*) c) xs) = map ((*) c) (dc_step t xs)"
        using dc_step_linear_smult by simp

      have xs_ne: "xs \<noteq> []"
        using xs_eq by simp
      have len_step: "length (dc_step t xs) = length xs - 1"
        using xs_ne by simp
      have lt_step: "length (dc_step t xs) < length xs"
        using len_step len2 by arith

      have IHstep:
        "dc_left t (map ((*) c) (dc_step t xs)) = map ((*) c) (dc_left t (dc_step t xs))"
        using "1.IH" lt_step 
        using "1" lt_step by presburger

      have tail:
        "dc_left t (dc_step t (map ((*) c) xs)) =
           map ((*) c) (dc_left t (dc_step t xs))"
        using step_map IHstep by simp

      show ?thesis
        using L R hd_map tail
        by auto
    qed
  qed
qed

lemma dc_left_basis_rec_zero:
  "dc_left t (basis_list 0 (Suc p))
   = 1 # map ((*) (1 - t)) (dc_left t (basis_list 0 p))"
proof -
  have len2: "2 \<le> length (basis_list 0 (Suc p))"
    by (simp add: basis_list_def)

  have L:
    "dc_left t (basis_list 0 (Suc p))
     = hd (basis_list 0 (Suc p)) # dc_left t (dc_step t (basis_list 0 (Suc p)))"
    using dc_left_unfold_len2[OF len2] .

  have hd0: "hd (basis_list 0 (Suc p)) = 1"
    by (simp add: hd_basis_list)

  have step0:
    "dc_step t (basis_list 0 (Suc p)) = map ((*) (1 - t)) (basis_list 0 p)"
    using dc_step_basis0_Suc .

  have tail0:
    "dc_left t (dc_step t (basis_list 0 (Suc p)))
     = map ((*) (1 - t)) (dc_left t (basis_list 0 p))"
    using step0 dc_left_linear_smult by auto
  show ?thesis
    using L hd0 tail0 by simp
qed

lemma dc_left_basis_rec_pos:
  assumes kpos: "0 < k" and kle: "k \<le> Suc p"
  shows
    "dc_left t (basis_list k (Suc p)) =
       0 # map2 (+)
              (map ((*) (1 - t)) (dc_left t (basis_list k p)))
              (map ((*) t)       (dc_left t (basis_list (k - 1) p)))"
proof -
  have len2: "2 \<le> length (basis_list k (Suc p))"
    by auto

  have L:
    "dc_left t (basis_list k (Suc p))
     = hd (basis_list k (Suc p)) # dc_left t (dc_step t (basis_list k (Suc p)))"
    using dc_left_unfold_len2[OF len2] .

  have hdk: "hd (basis_list k (Suc p)) = 0"
    using kpos by (simp add: hd_basis_list)

  have stepk:
    "dc_step t (basis_list k (Suc p)) =
       map2 (+) (map ((*) (1 - t)) (basis_list k p))
                (map ((*) t)       (basis_list (k - 1) p))"
    using dc_step_basis[of "Suc p" k t] kpos kle by simp

  have lenAB:
    "length (map ((*) (1 - t)) (basis_list k p)) =
     length (map ((*) t)       (basis_list (k - 1) p))"
    by simp

  have tailk:
    "dc_left t (dc_step t (basis_list k (Suc p))) =
       map2 (+) (map ((*) (1 - t)) (dc_left t (basis_list k p)))
                (map ((*) t)       (dc_left t (basis_list (k - 1) p)))"
  proof -
    have
      "dc_left t (dc_step t (basis_list k (Suc p))) =
       dc_left t (map2 (+) (map ((*) (1 - t)) (basis_list k p))
                         (map ((*) t)       (basis_list (k - 1) p)))"
      using stepk by simp
    also have "... =
       map2 (+) (dc_left t (map ((*) (1 - t)) (basis_list k p)))
                (dc_left t (map ((*) t)       (basis_list (k - 1) p)))"
      using dc_left_linear_sum[OF lenAB] by simp
    also have "... =
       map2 (+) (map ((*) (1 - t)) (dc_left t (basis_list k p)))
                (map ((*) t)       (dc_left t (basis_list (k - 1) p)))"
      using dc_left_linear_smult by simp
    finally show ?thesis .
  qed

  show ?thesis
    using L hdk tailk by simp
qed

definition bern_list :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real list" where
  "bern_list k p t =
     [ real (i choose k) * t^k * (1 - t)^(i - k) . i \<leftarrow> [0..<p+1] ]"

lemma length_bern_list [simp]:
  "length (bern_list k p t) = p + 1"
  by (simp add: bern_list_def)

lemma nth_bern_list :
  assumes "i < p + 1"
  shows "bern_list k p t ! i = real (i choose k) * t^k * (1 - t)^(i - k)"
  using assms 
  by (metis (no_types, lifting) add_cancel_right_left bern_list_def minus_nat.diff_0
      nth_map_upt)

lemma bern_list_rec_zero:
  "bern_list 0 (Suc p) t = 1 # map ((*) (1 - t)) (bern_list 0 p t)"
proof (rule nth_equalityI)
  show "length (bern_list 0 (Suc p) t) =
        length (1 # map ((*) (1 - t)) (bern_list 0 p t))"
    by simp
next
  fix i
  assume hi: "i < length (bern_list 0 (Suc p) t)"
  show "bern_list 0 (Suc p) t ! i =
        (1 # map ((*) (1 - t)) (bern_list 0 p t)) ! i"
  proof (cases i)
    case 0
    then show ?thesis by (simp add: nth_bern_list)
  next
    case (Suc n)
    have hn: "n < p + 1"
      using hi by (simp add: Suc)
    have hn': "Suc n < Suc p + 1"
      using hi by (simp add: Suc)

    have LHS:
      "bern_list 0 (Suc p) t ! Suc n = (1 - t)^(Suc n)"
      using hn' by (simp add: nth_bern_list)

    have RHS:
      "(1 # map ((*) (1 - t)) (bern_list 0 p t)) ! Suc n
        = (1 - t) * (bern_list 0 p t ! n)"
      using hn by simp
    also have "... = (1 - t) * (1 - t)^n"
      using hn by (simp add: nth_bern_list)
    also have "... = (1 - t)^(Suc n)"
      by (simp add: algebra_simps)
    finally have RHS': "(1 # map ((*) (1 - t)) (bern_list 0 p t)) ! Suc n = (1 - t)^(Suc n)" .

    show ?thesis
      using Suc LHS RHS' by simp
  qed
qed

lemma bern_list_rec_pos:
  assumes kpos: "0 < k"
  shows
    "bern_list k (Suc p) t =
       0 # map2 (+)
              (map ((*) (1 - t)) (bern_list k p t))
              (map ((*) t)       (bern_list (k - 1) p t))"
proof (rule nth_equalityI)
  show "length (bern_list k (Suc p) t) =
        length (0 # map2 (+)
                     (map ((*) (1 - t)) (bern_list k p t))
                     (map ((*) t)       (bern_list (k - 1) p t)))"
    by simp
next
  fix i
  assume hi: "i < length (bern_list k (Suc p) t)"
  show "bern_list k (Suc p) t ! i =
        (0 # map2 (+)
               (map ((*) (1 - t)) (bern_list k p t))
               (map ((*) t)       (bern_list (k - 1) p t))) ! i"
  proof (cases i)
    case 0
    have "(0 choose k) = 0"
      using kpos by (simp)
    then show ?thesis
      by (simp add: 0 nth_bern_list)
  next
    case (Suc n)
    have hn: "n < p + 1"
      using hi by (simp add: Suc)
    have hn': "Suc n < Suc p + 1"
      using hi by (simp add: Suc)

    have LHS:
      "bern_list k (Suc p) t ! Suc n =
        real (Suc n choose k) * t^k * (1 - t)^(Suc n - k)"
      using hn' by (simp add: nth_bern_list)

    have i_ltA: "n < length (map ((*) (1 - t)) (bern_list k p t))"
      using hn by simp
    have i_ltB: "n < length (map ((*) t) (bern_list (k - 1) p t))"
      using hn by simp

    have RHS0:
      "(0 # map2 (+)
             (map ((*) (1 - t)) (bern_list k p t))
             (map ((*) t)       (bern_list (k - 1) p t))) ! Suc n
       =
       map2 (+) (map ((*) (1 - t)) (bern_list k p t))
                (map ((*) t)       (bern_list (k - 1) p t)) ! n"
      using hn by simp

    have RHS1:
      "map2 (+) (map ((*) (1 - t)) (bern_list k p t))
               (map ((*) t)       (bern_list (k - 1) p t)) ! n
       =
       (map ((*) (1 - t)) (bern_list k p t) ! n)
       + (map ((*) t)     (bern_list (k - 1) p t) ! n)"
      using nth_map2_dsc[OF i_ltA i_ltB] by simp

    have RHS2:
      "(map ((*) (1 - t)) (bern_list k p t) ! n)
       + (map ((*) t)     (bern_list (k - 1) p t) ! n)
       =
       (1 - t) * (bern_list k p t ! n) + t * (bern_list (k - 1) p t ! n)"
      using hn by auto

    have RHS3:
      "(1 - t) * (bern_list k p t ! n) + t * (bern_list (k - 1) p t ! n)
       =
       (1 - t) * (real (n choose k) * t^k * (1 - t)^(n - k)) +
       t * (real (n choose (k - 1)) * t^(k - 1) * (1 - t)^(n - (k - 1)))"
      using hn by (simp add: nth_bern_list algebra_simps)

    have k_eq: "k = Suc (k - 1)"
      using kpos by simp

    have step_eq:
      "(1 - t) * (real (n choose k) * t^k * (1 - t)^(n - k)) +
       t * (real (n choose (k - 1)) * t^(k - 1) * (1 - t)^(n - (k - 1)))
       =
       real (Suc n choose k) * t^k * (1 - t)^(Suc n - k)"
    proof (cases "k \<le> Suc n")
      case True
      have pas:
        "real (Suc n choose k) * t^k * (1 - t)^(Suc n - k) =
           (1 - t) * (real (n choose k) * t^k * (1 - t)^(Suc n - 1 - k)) +
           t * (real (n choose (k - 1)) * t^(k - 1) * (1 - t)^(Suc n - k))"
        using pascal_bernstein_step[of k "Suc n" t] kpos True by simp

      have rew1: "Suc n - 1 - k = n - k" by simp
      have rew2: "Suc n - k = n - (k - 1)"
        using Suc_diff_eq_diff_pred kpos by blast

      show ?thesis
        using pas
        by (simp add: rew1 rew2 algebra_simps)
    next
      case False
      have cnk0: "(Suc n choose k) = 0"
        using False by (simp)
      have cnk0': "(n choose k) = 0"
        using False by (simp)
      have cnk1': "(n choose (k - 1)) = 0"
      proof -
        have "n < k - 1"
          using False kpos by arith
        thus ?thesis by (simp)
      qed
      show ?thesis
        by (metis add.right_neutral cnk0 cnk0' cnk1' mult_eq_0_iff of_nat_0)
    qed

    have RHS:
      "(0 # map2 (+)
             (map ((*) (1 - t)) (bern_list k p t))
             (map ((*) t)       (bern_list (k - 1) p t))) ! Suc n
       =
       real (Suc n choose k) * t^k * (1 - t)^(Suc n - k)"
      using RHS0 RHS1 RHS2 RHS3 step_eq
      by simp

    show ?thesis
      using Suc LHS RHS by simp
  qed
qed

lemma basis_list_oob:
  assumes "p < k"
  shows "basis_list k p = replicate (p + 1) (0::real)"
proof (rule nth_equalityI)
  show "length (basis_list k p) = length (replicate (p + 1) (0::real))"
    by fastforce
next
  fix i
  assume hi: "i < length (basis_list k p)"
  hence i_lt: "i < p + 1" 
    by simp
  have "basis_list k p ! i = (if i = k then 1 else 0)"
    using nth_basis_list[of i p k] i_lt by blast
  also have "... = 0"
    using assms i_lt by auto
  finally show "basis_list k p ! i = replicate (p + 1) (0::real) ! i"
    using i_lt
    by (metis nth_replicate)
qed

lemma dc_left_basis_oob:
  assumes "p < k"
  shows "dc_left t (basis_list k p) = replicate (p + 1) (0::real)"
  using assms basis_list_oob dc_left_replicate0 
  by presburger

lemma bern_list_oob:
  assumes "p < k"
  shows "bern_list k p t = replicate (p + 1) (0::real)"
proof (rule nth_equalityI)
  show "length (bern_list k p t) = length (replicate (p + 1) (0::real))"
    by (simp add: bern_list_def)
next
  fix i
  assume hi: "i < length (bern_list k p t)"
  hence i_lt: "i < p + 1" by (simp add: bern_list_def)
  have i_le_p: "i \<le> p" using i_lt by arith
  have i_lt_k: "i < k" using i_le_p assms by arith
  have "(i choose k) = 0" using i_lt_k by (simp)
  thus "bern_list k p t ! i = replicate (p + 1) (0::real) ! i"
    using i_lt 
    by (metis mult_zero_left nth_bern_list nth_replicate of_nat_0)
qed

lemma map2_add_replicate0_left:
  assumes "length xs = n"
  shows "map2 (+) (replicate n (0::real)) xs = xs"
proof (rule nth_equalityI)
  show "length (map2 (+) (replicate n (0::real)) xs) = length xs"
    using assms by simp
next
  fix i
  assume hi: "i < length (map2 (+) (replicate n (0::real)) xs)"
  hence i_lt_xs: "i < length xs" using assms by simp
  have i_lt_rep: "i < length (replicate n (0::real))"
    using assms i_lt_xs by simp
  show "map2 (+) (replicate n (0::real)) xs ! i = xs ! i"
    using nth_map2_dsc[OF i_lt_rep i_lt_xs]
    using assms i_lt_xs by force
qed

lemma dc_left_basis:
  assumes kle: "k \<le> p"
  shows "dc_left t (basis_list k p) =
         [ real (i choose k) * t^k * (1 - t)^(i - k) . i \<leftarrow> [0..<p+1] ]"
proof -
  have main: "dc_left t (basis_list k p) = bern_list k p t"
    using kle
  proof (induction p arbitrary: k)
    case 0
    then have "k = 0" by simp
    then show ?case
      by (simp add: bern_list_def dc_left_def basis_list_def)
  next
    case (Suc p k)
    show ?case
    proof (cases k)
      case 0
      have L: "dc_left t (basis_list 0 (Suc p))
               = 1 # map ((*) (1 - t)) (dc_left t (basis_list 0 p))"
        using dc_left_basis_rec_zero .
      have R: "bern_list 0 (Suc p) t
               = 1 # map ((*) (1 - t)) (bern_list 0 p t)"
        using bern_list_rec_zero .
      have IH: "dc_left t (basis_list 0 p) = bern_list 0 p t"
        using Suc.IH[of 0] by simp
      show ?thesis using L R IH
        using "0" by presburger
    next
      case (Suc k')
      have kpos: "0 < Suc k'" by simp
      have kle_suc: "Suc k' \<le> Suc p" using Suc.prems Suc by simp

      have L:
        "dc_left t (basis_list (Suc k') (Suc p)) =
           0 # map2 (+)
                  (map ((*) (1 - t)) (dc_left t (basis_list (Suc k') p)))
                  (map ((*) t)       (dc_left t (basis_list k' p)))"
        using dc_left_basis_rec_pos[OF kpos kle_suc] by simp

      have R:
        "bern_list (Suc k') (Suc p) t =
           0 # map2 (+)
                  (map ((*) (1 - t)) (bern_list (Suc k') p t))
                  (map ((*) t)       (bern_list k' p t))"
        using bern_list_rec_pos[OF kpos] by simp

      show ?thesis
      proof (cases "Suc k' \<le> p")
        case True
        have IH1: "dc_left t (basis_list (Suc k') p) = bern_list (Suc k') p t"
          using Suc.IH[of "Suc k'"] True by simp
        have IH2: "dc_left t (basis_list k' p) = bern_list k' p t"
          using Suc.IH[of k'] True by simp
        show ?thesis
          using L R IH1 IH2 
          using Suc by argo
      next
        case False
        have kp: "k' = p" using kle_suc False Suc by arith

        have ZL: "dc_left t (basis_list (Suc p) p) = replicate (p + 1) (0::real)"
          using dc_left_basis_oob[of p "Suc p" t] by simp
        have ZR: "bern_list (Suc p) p t = replicate (p + 1) (0::real)"
          using bern_list_oob[of p "Suc p" t] by simp

        have IHlast: "dc_left t (basis_list p p) = bern_list p p t"
          using Suc.IH[of p] by simp

        show ?thesis
          using L R kp ZL ZR IHlast
          using Suc by argo
      qed
    qed
  qed
  thus ?thesis
    by (simp add: bern_list_def)
qed

lemma rev_basis_list:
  assumes "k \<le> p"
  shows "rev (basis_list k p) = basis_list (p - k) p"
proof (rule nth_equalityI)
  show "length (rev (basis_list k p)) = length (basis_list (p - k) p)"
    by simp
next
  fix i
  assume hi: "i < length (rev (basis_list k p))"
  have i_lt: "i < p + 1"
    using hi by auto
  have i_le: "i \<le> p" using i_lt by arith

  have rev_nth':
    "rev (basis_list k p) ! i = basis_list k p ! (p - i)"
    using hi 
    by (simp add: rev_nth)

  have pk_lt: "p - i < p + 1"
    using i_le by simp

  have L:
    "rev (basis_list k p) ! i = (if p - i = k then 1 else 0)"
    using rev_nth' nth_basis_list[of "p - i" p k] pk_lt by simp

  have R:
    "basis_list (p - k) p ! i = (if i = p - k then 1 else 0)"
    using nth_basis_list[of i p "p - k"] i_lt by simp

  have eq_iff: "(p - i = k) \<longleftrightarrow> (i = p - k)"
  proof
    assume h: "p - i = k"
    have "p - k = p - (p - i)" using h by simp
    also have "... = i" using i_le by simp
    finally show "i = p - k" by simp
  next
    assume h: "i = p - k"
    have "p - i = p - (p - k)" using h by simp
    also have "... = k" using assms by simp
    finally show "p - i = k" .
  qed

  show "rev (basis_list k p) ! i = basis_list (p - k) p ! i"
    using L R eq_iff by simp
qed

lemma dc_right_basis:
  assumes "k \<le> p"
  shows
    "dc_right t (basis_list k p) =
     rev [ real (i choose (p-k)) * (1-t)^(p-k) * t^(i-(p-k)) . i \<leftarrow> [0..<p+1] ]"
proof -
  have rev_bl: "rev (basis_list k p) = basis_list (p - k) p"
    using rev_basis_list[OF assms] .

  have kp: "p - k \<le> p" by simp

  have "dc_right t (basis_list k p) = rev (dc_left (1 - t) (rev (basis_list k p)))"
    by (simp add: dc_right_eq_rev_dc_left)
  also have "... = rev (dc_left (1 - t) (basis_list (p - k) p))"
    using rev_bl by simp
  also have "... =
    rev [ real (i choose (p - k)) * (1 - t)^(p - k) * (1 - (1 - t))^(i - (p - k))
        . i \<leftarrow> [0..<p+1] ]"
    using dc_left_basis[OF kp, of "1 - t"] by simp
  also have "... =
    rev [ real (i choose (p-k)) * (1-t)^(p-k) * t^(i-(p-k)) . i \<leftarrow> [0..<p+1] ]"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma Bernstein_coeffs_01_basis:
  assumes kp: "k \<le> p"
  shows "Bernstein_coeffs_01 p (Bernstein_Poly_01 k p) = basis_list k p"
proof (rule nth_equalityI)
  show "length (Bernstein_coeffs_01 p (Bernstein_Poly_01 k p)) = length (basis_list k p)"
    by (simp add: length_Bernstein_coeffs_01)
next
  fix i
  assume hi: "i < length (Bernstein_coeffs_01 p (Bernstein_Poly_01 k p))"
  have i_lt: "i < p + 1"
    using hi by (simp add: length_Bernstein_coeffs_01)
  have i_le: "i \<le> p" using i_lt by arith

  have nthB:
    "Bernstein_coeffs_01 p (Bernstein_Poly_01 k p) ! i =
      inverse (real (p choose i)) *
      coeff (reciprocal_poly p (Bernstein_Poly_01 k p) \<circ>\<^sub>p [:1, 1:]) (p - i)"
    using i_lt
    by (metis (no_types, lifting) Bernstein_coeffs_01_def minus_nat.diff_0 nth_map_upt
        plus_nat.add_0)

  have subeq: "(p - i = p - k) \<longleftrightarrow> (i = k)"
  proof
    assume h: "p - i = p - k"
    have "i = p - (p - i)" using i_le by simp
    also have "... = p - (p - k)" using h by simp
    also have "... = k" using kp by simp
    finally show "i = k" .
  next
    assume "i = k" then show "p - i = p - k" by simp
  qed

  have coeff_monom':
    "coeff (reciprocal_poly p (Bernstein_Poly_01 k p) \<circ>\<^sub>p [:1, 1:]) (p - i)
     = (if i = k then real (p choose k) else 0)"
    using Bernstein_reciprocal_translate subeq by fastforce


  have nth_coeff:
    "Bernstein_coeffs_01 p (Bernstein_Poly_01 k p) ! i = (if i = k then 1 else 0)"
    using nthB coeff_monom'
    using kp by auto

  have nth_basis:
    "basis_list k p ! i = (if i = k then 1 else 0)"
    using nth_basis_list[of i p k] i_lt by blast

  show "Bernstein_coeffs_01 p (Bernstein_Poly_01 k p) ! i = basis_list k p ! i"
    using nth_coeff nth_basis by simp
qed

lemma poly_Bernstein_Poly_01:
  "poly (Bernstein_Poly_01 i p) x =
     real (p choose i) * x^i * (1 - x)^(p - i)"
  by (simp add: Bernstein_Poly_01_def poly_monom poly_pcompose algebra_simps)

lemma poly_split_left_LHS:
  assumes "k \<le> p"
  shows "poly (Bernstein_Poly_01 k p \<circ>\<^sub>p [:0, t:]) x =
         real (p choose k) * t^k * x^k * (1 - t*x)^(p - k)"
proof -
  have "poly (Bernstein_Poly_01 k p \<circ>\<^sub>p [:0, t:]) x
        = poly (Bernstein_Poly_01 k p) (poly [:0, t:] x)"
    by (simp add: poly_pcompose)
  also have "... = poly (Bernstein_Poly_01 k p) (t * x)"
    by (simp add: mult.commute)
  also have "... = real (p choose k) * (t * x)^k * (1 - (t * x))^(p - k)"
    by (simp add: poly_Bernstein_Poly_01)
  also have "... = real (p choose k) * t^k * x^k * (1 - t*x)^(p - k)"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma poly_split_left_RHS:
  "poly (\<Sum>i=0..p. smult (real (i choose k) * t^k * (1 - t)^(i - k))
                        (Bernstein_Poly_01 i p)) x
   =
   (\<Sum>i=0..p. real (i choose k) * real (p choose i) * t^k *
            (1 - t)^(i - k) * x^i * (1 - x)^(p - i))"
  by (simp add: poly_sum poly_Bernstein_Poly_01 algebra_simps)

lemma sum_drop_lt_choose_factor:
  fixes g :: "nat \<Rightarrow> real"
  assumes kp: "k \<le> p"
  shows "(\<Sum>i=0..p. real (i choose k) * g i) =
         (\<Sum>i=k..p. real (i choose k) * g i)"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc k')
  have kp': "Suc k' \<le> p" using kp Suc by simp

  let ?f = "\<lambda>i. real (i choose Suc k') * g i"

  have decomp: "{0..p} = {0..k'} \<union> {Suc k'..p}"
    using kp' by auto
  have disj: "{0..k'} \<inter> {Suc k'..p} = {}"
    by auto

  have left0: "sum ?f {0..k'} = (0::real)"
  proof -
    have "sum ?f {0..k'} = sum (\<lambda>i. (0::real)) {0..k'}"
    proof (rule sum.cong, simp)
      fix i assume hi: "i \<in> {0..k'}"
      hence "i < Suc k'" by simp
      hence "(i choose Suc k') = 0"
        by (simp)
      then show "?f i = 0" by simp
    qed
    then show ?thesis by simp
  qed

  have "(\<Sum>i=0..p. real (i choose Suc k') * g i) = sum ?f {0..p}"
    by simp
  also have "... = sum ?f ({0..k'} \<union> {Suc k'..p})"
    using decomp by simp
  also have "... = sum ?f {0..k'} + sum ?f {Suc k'..p}"
    using disj by (simp add: sum.union_disjoint)
  also have "... = sum ?f {Suc k'..p}"
    using left0 by simp
  finally show ?thesis
    using Suc
    by (simp add:
        \<open>(\<Sum>i\<in>{0..k'} \<union> {Suc k'..p}. real (i choose Suc k') * g i) = (\<Sum>i = 0..k'. real (i choose Suc k') * g i) + (\<Sum>i = Suc k'..p. real (i choose Suc k') * g i)\<close>
        decomp left0)
qed


lemma sum_shift_k_add:
  "(\<Sum>i=k..k+(m::nat). F i) = (\<Sum>j=0..m. F (k+j))"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have "k + Suc m = Suc (k + m)" by simp
  then show ?case
    using Suc by simp
qed

lemma pow_mult_same:
  fixes a b :: real
  shows "a^n * b^n = (a*b)^n"
  by (simp add: algebra_simps)

lemma split_left_main_sum:
  fixes t x :: real
  assumes kp: "k \<le> p"
  shows
    "(\<Sum>j=0..p-k.
        real ((k + j) choose k) * real (p choose (k + j)) * t^k *
        (1 - t)^j * x^(k + j) * (1 - x)^(p - (k + j)))
    =
    real (p choose k) * t^k * x^k *
    (\<Sum>j=0..p-k. real ((p-k) choose j) * ((1 - t) * x)^j * (1 - x)^((p-k) - j))"
  proof -
  have ter:
    "real ((k + j) choose k) * real (p choose (k + j)) * t^k *
     (1 - t)^j * x^(k + j) * (1 - x)^(p - (k + j))
     =
     real (p choose k) * t^k * x^k *
     (real ((p-k) choose j) * ((1 - t) * x)^j * (1 - x)^((p-k) - j))"
    if hj: "j \<in> {0..p-k}" for j
  proof -
    have j_le: "j \<le> p - k" using hj by simp
    have i_le: "k + j \<le> p" using kp j_le by arith

    have swap:
      "real (p choose (k+j)) * real ((k+j) choose k)
       = real (p choose k) * real ((p-k) choose ((k+j) - k))"
      using binomial_swap_identity[of k "k+j" p] kp i_le by simp
    hence swap': "real ((k+j) choose k) * real (p choose (k+j))
                  = real (p choose k) * real ((p-k) choose j)"
      by (simp add: algebra_simps)

    have px: "p - (k + j) = (p - k) - j"
      using kp j_le by arith

    show ?thesis
      using swap'
      by (smt (verit) ab_semigroup_mult_class.mult_ac(1) mult.left_commute pow_mult_same
          power_add px)
  qed

  have
    "(\<Sum>j=0..p-k.
        real ((k + j) choose k) * real (p choose (k + j)) * t^k *
        (1 - t)^j * x^(k + j) * (1 - x)^(p - (k + j)))
     =
     (\<Sum>j=0..p-k.
        real (p choose k) * t^k * x^k *
        (real ((p-k) choose j) * ((1 - t) * x)^j * (1 - x)^((p-k) - j)))"
    by (meson sum.cong ter)
  also have "... =
     real (p choose k) * t^k * x^k *
     (\<Sum>j=0..p-k. real ((p-k) choose j) * ((1 - t) * x)^j * (1 - x)^((p-k) - j))"
    by (simp add: sum_distrib_left algebra_simps)
  finally show ?thesis .
qed


lemma split_left_sum_identity:
  assumes kp: "k \<le> p"
  shows
  "(\<Sum>i=0..p. real (i choose k) * real (p choose i) * t^k *
            (1 - t)^(i - k) * x^i * (1 - x)^(p - i))
   = real (p choose k) * t^k * x^k * (1 - t*x)^(p - k)"
proof -
  let ?A = "\<lambda>i.
      real (i choose k) * real (p choose i) * t^k *
      (1 - t)^(i - k) * x^i * (1 - x)^(p - i)"

    have drop:
    "(\<Sum>i=0..p. ?A i) = (\<Sum>i=k..p. ?A i)"
  proof -
    let ?g = "\<lambda>i.
        real (p choose i) * t^k *
        (1 - t)^(i - k) * x^i * (1 - x)^(p - i)"
    have A_fac: "\<And>i. ?A i = real (i choose k) * ?g i"
      by (simp add: algebra_simps)

    show ?thesis
      using sum_drop_lt_choose_factor[OF kp, of ?g]
      by (simp add: A_fac)
  qed

  have shift:
    "(\<Sum>i=k..p. ?A i) = (\<Sum>j=0..p-k. ?A (k+j))"
  proof -
    have "p = k + (p - k)" using kp by arith
    hence "(\<Sum>i=k..p. ?A i) = (\<Sum>i=k..k+(p-k). ?A i)" by simp
    also have "... = (\<Sum>j=0..p-k. ?A (k+j))"
      by (simp add: sum_shift_k_add)
    finally show ?thesis .
  qed

  have rewrite_term:
    "j \<in> {0..p-k} \<Longrightarrow>
     ?A (k+j)
     =
     real (p choose k) * t^k * x^k *
     (real ((p-k) choose j) * ((1 - t) * x)^j * (1 - x)^((p-k) - j))"
  proof -
    fix j assume hj: "j \<in> {0..p-k}"
    hence j_le: "j \<le> p - k" by simp
    have i_le: "k + j \<le> p" using kp j_le by arith

    have swap:
      "real (p choose (k+j)) * real ((k+j) choose k)
       = real (p choose k) * real ((p-k) choose j)"
      using binomial_swap_identity[of k "k+j" p] kp i_le by simp

    have px: "p - (k + j) = (p - k) - j" using kp j_le by arith

    show "?A (k+j) =
          real (p choose k) * t^k * x^k *
          (real ((p-k) choose j) * ((1 - t) * x)^j * (1 - x)^((p-k) - j))"
      using swap
      by (simp add: px power_add pow_mult_same algebra_simps)
  qed

  have main:
  "(\<Sum>j=0..p-k. ?A (k+j))
   = real (p choose k) * t^k * x^k *
     (\<Sum>j=0..p-k. real ((p-k) choose j) * ((1 - t) * x)^j * (1 - x)^((p-k) - j))"
proof -
  have "(\<Sum>j=0..p-k. ?A (k+j))
        =
        (\<Sum>j=0..p-k.
            real ((k + j) choose k) * real (p choose (k + j)) * t^k *
            (1 - t)^j * x^(k + j) * (1 - x)^(p - (k + j)))"
    by (simp add: algebra_simps power_add)
  also have "... =
        real (p choose k) * t^k * x^k *
        (\<Sum>j=0..p-k. real ((p-k) choose j) * ((1 - t) * x)^j * (1 - x)^((p-k) - j))"
    using split_left_main_sum[OF kp, of t x] .
  finally show ?thesis .
qed

    also have "... =
      real (p choose k) * t^k * x^k *
      (\<Sum>j=0..p-k. real ((p-k) choose j) * ((1 - t) * x)^j * (1 - x)^((p-k) - j))"
      by (simp add: sum_distrib_left algebra_simps)
    finally show ?thesis 
      using drop main power_diff_expansion shift by presburger
  have powexp:
    "(\<Sum>j=0..p-k. real ((p-k) choose j) * ((1 - t) * x)^j * (1 - x)^((p-k) - j))
     = (1 - t*x)^(p-k)"
    using power_diff_expansion[of t x "p-k"] by simp
qed


lemma Bernstein_Poly_01_split_left_basis_poly:
  assumes kp: "k \<le> p"
  shows "Bernstein_Poly_01 k p \<circ>\<^sub>p [:0, t:] =
         (\<Sum>i=0..p. smult (real (i choose k) * t^k * (1 - t)^(i - k))
                         (Bernstein_Poly_01 i p))"
proof (rule poly_ext)  
  fix x :: real
  have sum_id:
    "(\<Sum>i=0..p. real (i choose k) * real (p choose i) * t^k *
             (1 - t)^(i - k) * x^i * (1 - x)^(p - i))
     = real (p choose k) * t^k * x^k * (1 - t*x)^(p - k)"
    using split_left_sum_identity[OF kp] by simp

  show "poly (Bernstein_Poly_01 k p \<circ>\<^sub>p [:0, t:]) x =
        poly (\<Sum>i=0..p. smult (real (i choose k) * t^k * (1 - t)^(i - k))
                             (Bernstein_Poly_01 i p)) x"
  proof -
    have "poly (Bernstein_Poly_01 k p \<circ>\<^sub>p [:0, t:]) x
          = real (p choose k) * t^k * x^k * (1 - t*x)^(p - k)"
      using poly_split_left_LHS[OF kp, of t x] .
    also have "... =
      (\<Sum>i=0..p. real (i choose k) * real (p choose i) * t^k *
               (1 - t)^(i - k) * x^i * (1 - x)^(p - i))"
      using sum_id by simp
    also have "... =
      poly (\<Sum>i=0..p. smult (real (i choose k) * t^k * (1 - t)^(i - k))
                           (Bernstein_Poly_01 i p)) x"
      using poly_split_left_RHS
      by presburger
    finally show ?thesis .
  qed
qed

lemma Bernstein_coeffs_01_Bernstein_sum_nth_default:
  fixes b :: "nat \<Rightarrow> real"
  assumes ile: "i \<le> p"
  shows
    "nth_default 0 (Bernstein_coeffs_01 p (\<Sum>j=0..p. smult (b j) (Bernstein_Poly_01 j p))) i
     = b i"
proof -
  have deg: "degree (\<Sum>j=0..p. smult (b j) (Bernstein_Poly_01 j p)) \<le> p"
  proof (rule degree_sum_le)
    fix j assume "j \<in> {0..p}"
    show "degree (smult (b j) (Bernstein_Poly_01 j p)) \<le> p"
      by (simp add: degree_smult_le degree_Bernstein_le)
  qed simp

  have
    "nth_default 0 (Bernstein_coeffs_01 p (\<Sum>j=0..p. smult (b j) (Bernstein_Poly_01 j p))) i
     = inverse (p choose i) *
       coeff (reciprocal_poly p (\<Sum>j=0..p. smult (b j) (Bernstein_Poly_01 j p)) \<circ>\<^sub>p [:1, 1:])
             (p - i)"
    using nth_default_Bernstein_coeffs_01[OF deg] by simp
  also have "... = inverse (p choose i) * ((p choose i) * b i)"
    using coeff_Bernstein_sum_01 ile by presburger
  also have "... = b i"
    using ile by (simp add: field_simps)
  finally show ?thesis .
qed

lemma Bernstein_coeffs_01_Bernstein_sum_list:
  fixes b :: "nat \<Rightarrow> real"
  shows
    "Bernstein_coeffs_01 p (\<Sum>i=0..p. smult (b i) (Bernstein_Poly_01 i p))
     = [ b i . i \<leftarrow> [0..<p+1] ]"
proof (rule nth_equalityI)
  show "length (Bernstein_coeffs_01 p (\<Sum>i=0..p. smult (b i) (Bernstein_Poly_01 i p)))
        = length [ b i . i \<leftarrow> [0..<p+1] ]"
    by (simp add: length_Bernstein_coeffs_01)
next
  fix i
  assume hi: "i < length (Bernstein_coeffs_01 p (\<Sum>i=0..p. smult (b i) (Bernstein_Poly_01 i p)))"
  have i_le: "i \<le> p"
    using hi by (simp add: length_Bernstein_coeffs_01)

  have lhs:
    "Bernstein_coeffs_01 p (\<Sum>j=0..p. smult (b j) (Bernstein_Poly_01 j p)) ! i
     = nth_default 0 (Bernstein_coeffs_01 p (\<Sum>j=0..p. smult (b j) (Bernstein_Poly_01 j p))) i"
    using hi by (simp add: length_Bernstein_coeffs_01 nth_default_nth)

  have rhs:
    "[ b j . j \<leftarrow> [0..<p+1] ] ! i = b i"
    using i_le 
    by (metis (lifting) Bernstein_coeffs_01_def add_0 diff_zero hi length_map
        length_upt nth_map nth_upt)

  show "Bernstein_coeffs_01 p (\<Sum>j=0..p. smult (b j) (Bernstein_Poly_01 j p)) ! i
        = [ b j . j \<leftarrow> [0..<p+1] ] ! i"
    using lhs rhs Bernstein_coeffs_01_Bernstein_sum_nth_default[OF i_le] by simp
qed

fun vecsum_upto :: "nat \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> real list" where
  "vecsum_upto 0 f = f 0"
| "vecsum_upto (Suc n) f = map2 (+) (vecsum_upto n f) (f (Suc n))"

lemma nth_vecsum_upto:
  fixes f :: "nat \<Rightarrow> real list"
  assumes len: "\<And>k. k \<le> n \<Longrightarrow> length (f k) = L"
      and iL: "i < L"
  shows "vecsum_upto n f ! i = (\<Sum>k=0..n. f k ! i)"
using len
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have iA: "i < length (vecsum_upto n f)"
  proof -
    have "length (vecsum_upto n f) = L"
      using Suc.prems(1) by (induction n) (simp_all add: len)
    then show ?thesis using iL by simp
  qed
  have iB: "i < length (f (Suc n))"
    using len[of "Suc n"] iL 
    by (simp add: Suc.prems)

  have "vecsum_upto (Suc n) f ! i
        = map2 (+) (vecsum_upto n f) (f (Suc n)) ! i"
    by simp
  also have "... = (vecsum_upto n f ! i) + (f (Suc n) ! i)"
    using nth_map2_dsc[OF iA iB] 
    by blast
  also have "... = (\<Sum>k=0..n. f k ! i) + f (Suc n) ! i"
    using Suc.IH Suc.prems iL by simp
  also have "... = (\<Sum>k=0..Suc n. f k ! i)"
    by simp
  finally show ?case .
qed

lemma length_vecsum_upto [simp]:
  assumes len: "\<And>k. k \<le> n \<Longrightarrow> length (f k) = L"
  shows "length (vecsum_upto n f) = L"
using len
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have IH: "length (vecsum_upto n f) = L"
    using Suc.IH Suc.prems by simp
  have lf: "length (f (Suc n)) = L"
    using Suc.prems by simp
  show ?case
    using IH lf
    by simp
qed

lemma length_vecsum_upto_len0:
  assumes len: "\<And>k. k \<le> n \<Longrightarrow> length (f k) = length (f 0)"
  shows "length (vecsum_upto n f) = length (f 0)"
  using length_vecsum_upto[of n f "length (f 0)"] len
  by blast

lemma vecsum_upto_basis_decomp:
  assumes lenxs: "length xs = p + 1"
  shows "vecsum_upto p (\<lambda>k. map ((*) (xs ! k)) (basis_list k p)) = xs"
proof (rule nth_equalityI)
  show "length (vecsum_upto p (\<lambda>k. map ((*) (xs ! k)) (basis_list k p))) = length xs"
    using lenxs by (induction p) simp_all
next
  fix i
  assume hi: "i < length (vecsum_upto p (\<lambda>k. map ((*) (xs ! k)) (basis_list k p)))"
  have i_lt: "i < p + 1"
    using hi lenxs by (induction p) simp_all

  have lenf: "\<And>k. k \<le> p \<Longrightarrow> length (map ((*) (xs ! k)) (basis_list k p)) = p + 1"
    by simp

  have nth_sum:
    "vecsum_upto p (\<lambda>k. map ((*) (xs ! k)) (basis_list k p)) ! i
     = (\<Sum>k=0..p. (map ((*) (xs ! k)) (basis_list k p)) ! i)"
    using nth_vecsum_upto[OF lenf i_lt] by simp

  have ter:
    "(map ((*) (xs ! k)) (basis_list k p)) ! i = (if k = i then xs ! i else 0)"
    if "k \<le> p" for k
  proof -
    have iLp: "i < p + 1" using i_lt .
    have kLp: "k < p + 1" using that by arith
    have xs_k: "xs ! k = xs ! k" by simp
    have "basis_list k p ! i = (if i = k then 1 else 0)"
      using nth_basis_list[of i p k] iLp by blast
    thus ?thesis
      using i_lt by auto
  qed

  have sum_delta:
    "(\<Sum>k=0..p. (if k = i then xs ! i else 0)) = xs ! i"
    using i_lt by simp

  show "vecsum_upto p (\<lambda>k. map ((*) (xs ! k)) (basis_list k p)) ! i = xs ! i"
    using nth_sum i_lt
    by (smt (z3) One_nat_def Suc_leI add.right_neutral add_Suc_right basis_list_oob
        length_basis_list linorder_not_less mult_not_zero nth_map nth_replicate sum.cong
        sum_delta ter)
qed


lemma nth_dc_left_basis:
  assumes kp: "k \<le> p" and i_lt: "i < p + 1"
  shows "dc_left t (basis_list k p) ! i
        = real (i choose k) * t^k * (1 - t)^(i - k)"
  using dc_left_basis[OF kp, of t] i_lt
  by (metis (no_types, lifting) add_cancel_right_left diff_zero
      nth_map_upt)

lemma dc_left_vecsum_upto:
  assumes len: "\<And>k. k \<le> n \<Longrightarrow> length (f k) = L"
  shows "dc_left t (vecsum_upto n f) = vecsum_upto n (\<lambda>k. dc_left t (f k))"
using len
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have len_v: "length (vecsum_upto n f) = L"
    using length_vecsum_upto[OF Suc.prems]
    by simp
  have len_fn: "length (f (Suc n)) = L"
    using Suc.prems by simp
  have len_eq: "length (vecsum_upto n f) = length (f (Suc n))"
    using len_v len_fn by simp

  have step1:
    "dc_left t (vecsum_upto (Suc n) f)
     = dc_left t (map2 (+) (vecsum_upto n f) (f (Suc n)))"
    by simp
  also have step2:
    "... = map2 (+) (dc_left t (vecsum_upto n f)) (dc_left t (f (Suc n)))"
    using dc_left_linear_sum[OF len_eq] by simp
  also have step3:
    "... = map2 (+) (vecsum_upto n (\<lambda>k. dc_left t (f k))) (dc_left t (f (Suc n)))"
    using Suc.IH Suc.prems by simp
  finally show ?case
    by simp
qed

lemma dc_left_matrix_nth:
  assumes lenxs: "length xs = p + 1"
      and i_lt: "i < p + 1"
  shows
    "dc_left t xs ! i =
     (\<Sum>k=0..p. xs ! k * (real (i choose k) * t^k * (1 - t)^(i - k)))"
proof -
  have xs_decomp:
    "xs = vecsum_upto p (\<lambda>k. map ((*) (xs ! k)) (basis_list k p))"
    using vecsum_upto_basis_decomp[OF lenxs] by simp

  have dc_left_decomp:
    "dc_left t xs =
     vecsum_upto p (\<lambda>k. dc_left t (map ((*) (xs ! k)) (basis_list k p)))"
  proof -
    have lenf: "\<And>k. k \<le> p \<Longrightarrow> length (map ((*) (xs ! k)) (basis_list k p)) = p + 1"
      by simp
    show ?thesis
      using xs_decomp
    proof (induction p)
      case 0
      then show ?case by simp
    next
      case (Suc p)
      have L1:
        "dc_left t (vecsum_upto (Suc p) (\<lambda>k. map ((*) (xs ! k)) (basis_list k (Suc p))))
         =
         dc_left t (map2 (+)
                     (vecsum_upto p (\<lambda>k. map ((*) (xs ! k)) (basis_list k (Suc p))))
                     (map ((*) (xs ! Suc p)) (basis_list (Suc p) (Suc p))))"
        by simp
      also have "... =
         map2 (+)
           (dc_left t (vecsum_upto p (\<lambda>k. map ((*) (xs ! k)) (basis_list k (Suc p)))))
           (dc_left t (map ((*) (xs ! Suc p)) (basis_list (Suc p) (Suc p))))"
      proof -
        let ?f = "\<lambda>k. map ((*) (xs ! k)) (basis_list k (Suc p))"
      have dc_left_vecsum_fixed:
  "dc_left t (vecsum_upto p ?f)
   = vecsum_upto p (\<lambda>k. dc_left t (?f k))"
proof (rule dc_left_vecsum_upto)
  show "\<And>k. k \<le> p \<Longrightarrow> length (?f k) = Suc p + 1"
    by simp
qed
        have lenA: "length (vecsum_upto p (\<lambda>k. map ((*) (xs ! k)) (basis_list k (Suc p))))
                    = length (map ((*) (xs ! Suc p)) (basis_list (Suc p) (Suc p)))"
          by simp
        show ?thesis
          using dc_left_linear_sum[OF lenA, of t] by simp
      qed
      also have "... =
         map2 (+)
           (vecsum_upto p (\<lambda>k. dc_left t (map ((*) (xs ! k)) (basis_list k (Suc p)))))
           (dc_left t (map ((*) (xs ! Suc p)) (basis_list (Suc p) (Suc p))))"
        using Suc.IH 
        by (simp add: dc_left_vecsum_upto)
        then show ?case 
        using Suc.prems 
        using calculation vecsum_upto.simps(2) by presburger
    qed
  qed

  have lenf2:
    "\<And>k. k \<le> p \<Longrightarrow> length (dc_left t (map ((*) (xs ! k)) (basis_list k p))) = p + 1"
    by simp

  have nth_vec:
    "vecsum_upto p (\<lambda>k. dc_left t (map ((*) (xs ! k)) (basis_list k p))) ! i
     = (\<Sum>k=0..p. dc_left t (map ((*) (xs ! k)) (basis_list k p)) ! i)"
    using nth_vecsum_upto[OF lenf2 i_lt] .

  have eachk:
    "dc_left t (map ((*) (xs ! k)) (basis_list k p)) ! i
     = xs ! k * (real (i choose k) * t^k * (1 - t)^(i - k))"
    if "k \<le> p" for k
  proof -
    have "dc_left t (map ((*) (xs ! k)) (basis_list k p))
          = map ((*) (xs ! k)) (dc_left t (basis_list k p))"
      using dc_left_linear_smult by simp
    hence "dc_left t (map ((*) (xs ! k)) (basis_list k p)) ! i
           = xs ! k * (dc_left t (basis_list k p) ! i)"
      using i_lt by simp
    also have "... = xs ! k * (real (i choose k) * t^k * (1 - t)^(i - k))"
      using nth_dc_left_basis[OF that i_lt] by simp
    finally show ?thesis
      by (simp add: algebra_simps)
  qed

  show ?thesis
    using dc_left_decomp nth_vec
    by (simp add: eachk algebra_simps)
qed


lemma sum_smult_smult_swap:
  fixes c :: "nat \<Rightarrow> real"
    and a :: "nat \<Rightarrow> nat \<Rightarrow> real"
    and B :: "nat \<Rightarrow> real poly"
  shows
    "(\<Sum>k=0..p. smult (c k) (\<Sum>i=0..p. smult (a i k) (B i)))
     =
     (\<Sum>i=0..p. smult (\<Sum>k=0..p. c k * a i k) (B i))"
proof -
  have "(\<Sum>k=0..p. smult (c k) (\<Sum>i=0..p. smult (a i k) (B i)))
        = (\<Sum>k=0..p. \<Sum>i=0..p. smult (c k) (smult (a i k) (B i)))"

    by (simp add: poly_vs.scale_sum_right)
  also have "... = (\<Sum>k=0..p. \<Sum>i=0..p. smult (c k * a i k) (B i))"
    by (simp add: algebra_simps)
  also have "... = (\<Sum>i=0..p. \<Sum>k=0..p. smult (c k * a i k) (B i))"
    using sum.swap by force
  also have "... = (\<Sum>i=0..p. smult (\<Sum>k=0..p. c k * a i k) (B i))"
    by (simp add: smult_sum)
  finally show ?thesis .
qed


theorem Bernstein_coeffs_01_split_left:
  assumes hP: "degree P \<le> p"
  shows "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:0, t:]) = dc_left t (Bernstein_coeffs_01 p P)"
proof (rule nth_equalityI)
  show "length (Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:0, t:])) = length (dc_left t (Bernstein_coeffs_01 p P))"
    by (simp add: Bernstein_coeffs_01_def)
next
  fix i
  assume hi: "i < length (Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:0, t:]))"
  have i_lt: "i < p + 1" using hi by (simp add: length_Bernstein_coeffs_01)
  have lenC: "length (Bernstein_coeffs_01 p P) = p + 1"
    by (simp add: length_Bernstein_coeffs_01)

  define c where "c k = nth_default 0 (Bernstein_coeffs_01 p P) k" for k
  define d where
    "d i = (\<Sum>k=0..p. c k * (real (i choose k) * t^k * (1 - t)^(i - k)))" for i

  have P_bern:
    "P = (\<Sum>k=0..p. smult (c k) (Bernstein_Poly_01 k p))"
    using Bernstein_coeffs_01_sum[OF hP] by (simp add: c_def)

  have P_comp:
    "P \<circ>\<^sub>p [:0, t:]
     = (\<Sum>k=0..p. smult (c k) (Bernstein_Poly_01 k p \<circ>\<^sub>p [:0, t:]))"
    using P_bern by (simp add: pcompose_sum pcompose_smult)

  have P_comp_as_bern_sum:
    "P \<circ>\<^sub>p [:0, t:] = (\<Sum>i=0..p. smult (d i) (Bernstein_Poly_01 i p))"
  proof -
    let ?a = "\<lambda>i k. real (i choose k) * t^k * (1 - t)^(i - k)"
    let ?B = "\<lambda>i. Bernstein_Poly_01 i p"
    have rearrange:
  "(\<Sum>k=0..p. smult (c k) (\<Sum>i=0..p. smult (?a i k) (?B i)))
   =
   (\<Sum>i=0..p. smult (\<Sum>k=0..p. c k * ?a i k) (?B i))"
  by (rule sum_smult_smult_swap)

    have "P \<circ>\<^sub>p [:0, t:]
          = (\<Sum>k=0..p. smult (c k)
              (\<Sum>i=0..p. smult (real (i choose k) * t^k * (1 - t)^(i - k))
                               (Bernstein_Poly_01 i p)))"
      using P_comp by (simp add: Bernstein_Poly_01_split_left_basis_poly)
    also have "... =
      (\<Sum>i=0..p. smult (\<Sum>k=0..p. c k * (real (i choose k) * t^k * (1 - t)^(i - k)))
                    (Bernstein_Poly_01 i p))"
      using rearrange by blast
    also have "... = (\<Sum>i=0..p. smult (d i) (Bernstein_Poly_01 i p))"
      by (simp add: d_def)
    finally show ?thesis .
  qed

  have lhs_i:
    "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:0, t:]) ! i = d i"
    using P_comp_as_bern_sum i_lt
    by (metis (no_types, lifting) Bernstein_coeffs_01_Bernstein_sum_list add_0
        diff_zero nth_map_upt)

  have rhs_i:
    "dc_left t (Bernstein_coeffs_01 p P) ! i = d i"
  proof -
    have "dc_left t (Bernstein_coeffs_01 p P) ! i
          = (\<Sum>k=0..p. (Bernstein_coeffs_01 p P ! k) * (real (i choose k) * t^k * (1 - t)^(i - k)))"
      using dc_left_matrix_nth[OF lenC i_lt] .
    also have "... = (\<Sum>k=0..p. c k * (real (i choose k) * t^k * (1 - t)^(i - k)))"
      by (simp add: c_def lenC nth_default_nth)
    also have "... = d i"
      by (simp add: d_def)
    finally show ?thesis .
  qed

  show "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:0, t:]) ! i = dc_left t (Bernstein_coeffs_01 p P) ! i"
    using lhs_i rhs_i by simp
qed

lemma Bernstein_Poly_01_reflect:
  assumes kp: "k \<le> p"
  shows "Bernstein_Poly_01 k p \<circ>\<^sub>p [:1, -1:] = Bernstein_Poly_01 (p - k) p"
proof (rule poly_ext)
  fix x :: real
  have "poly (Bernstein_Poly_01 k p \<circ>\<^sub>p [:1, -1:]) x
        = poly (Bernstein_Poly_01 k p) (poly [:1, -1:] x)"
    by (simp add: poly_pcompose)
  also have "... = poly (Bernstein_Poly_01 k p) (1 - x)"
    by simp
  also have "... = real (p choose k) * (1 - x)^k * (1 - (1 - x))^(p - k)"
    by (simp add: poly_Bernstein_Poly_01)
  also have "... = real (p choose (p - k)) * x^(p - k) * (1 - x)^k"
    by (metis Bernstein_symmetry calculation diff_diff_cancel kp
        poly_Bernstein_Poly_01)
  also have "... = poly (Bernstein_Poly_01 (p - k) p) x"
    using Bernstein_symmetry calculation kp by force
  finally show "\<And>x. poly (Bernstein_Poly_01 k p \<circ>\<^sub>p [:1, - 1:]) x =
         poly (Bernstein_Poly_01 (p - k) p) x" 
    using Bernstein_symmetry kp by presburger
qed

lemma rev_upt_map_c:
  fixes c :: "nat \<Rightarrow> 'a"
  shows "[c (p - i). i \<leftarrow> [0..<p+1]] = rev [c i. i \<leftarrow> [0..<p+1]]"
proof (rule nth_equalityI)
  show "length [c (p - i). i \<leftarrow> [0..<p+1]] = length (rev [c i. i \<leftarrow> [0..<p+1]])"
    by simp
next
  fix i
  assume hi: "i < length [c (p - i). i \<leftarrow> [0..<p+1]]"
  hence i_lt: "i < p + 1" by simp

  have lhs: "[c (p - i). i \<leftarrow> [0..<p+1]] ! i = c (p - i)"
    using i_lt 
    by (metis add_0 diff_zero nth_map_upt)

  have rhs: "rev [c i. i \<leftarrow> [0..<p+1]] ! i = c (p - i)"
  proof -
    have "rev [c i. i \<leftarrow> [0..<p+1]] ! i
          = [c i. i \<leftarrow> [0..<p+1]] ! (length [c i. i \<leftarrow> [0..<p+1]] - Suc i)"
      using i_lt
      by (metis hi length_map rev_nth)
    also have "... = [c i. i \<leftarrow> [0..<p+1]] ! (p - i)"
      using i_lt by simp
    also have "... = c (p - i)"
      by (metis Suc_eq_plus1 comm_monoid_add_class.add_0 diff_less_Suc minus_nat.diff_0
          nth_map_upt)
    finally show ?thesis .
  qed

  show "[c (p - i). i \<leftarrow> [0..<p+1]] ! i = rev [c i. i \<leftarrow> [0..<p+1]] ! i"
    using lhs rhs by simp
qed


lemma Bernstein_coeffs_01_reflect:
  assumes hQ: "degree Q \<le> p"
  shows "Bernstein_coeffs_01 p (Q \<circ>\<^sub>p [:1, -1:]) = rev (Bernstein_coeffs_01 p Q)"
proof -
  define c where "c k = nth_default 0 (Bernstein_coeffs_01 p Q) k" for k

  have Qsum:
    "Q = (\<Sum>k=0..p. smult (c k) (Bernstein_Poly_01 k p))"
    using Bernstein_coeffs_01_sum[OF hQ] by (simp add: c_def)

  have Qref:
    "Q \<circ>\<^sub>p [:1, -1:]
     = (\<Sum>k=0..p. smult (c k) (Bernstein_Poly_01 (p - k) p))"
  proof -
    have "Q \<circ>\<^sub>p [:1, -1:]
          = (\<Sum>k=0..p. smult (c k) (Bernstein_Poly_01 k p)) \<circ>\<^sub>p [:1, -1:]"
      using Qsum by simp
    also have "... = (\<Sum>k=0..p. smult (c k) (Bernstein_Poly_01 k p \<circ>\<^sub>p [:1, -1:]))"
      by (simp add: pcompose_sum pcompose_smult)
    also have "... = (\<Sum>k=0..p. smult (c k) (Bernstein_Poly_01 (p - k) p))"
      using Bernstein_Poly_01_reflect
      by auto
    finally show ?thesis .
  qed

  have reindex:
    "(\<Sum>k=0..p. smult (c k) (Bernstein_Poly_01 (p - k) p))
     = (\<Sum>i=0..p. smult (c (p - i)) (Bernstein_Poly_01 i p))"
    by (rule sum.reindex_bij_witness[where i="\<lambda>i. p - i" and j="\<lambda>i. p - i"]) auto

  have coeffs_ref:
    "Bernstein_coeffs_01 p (Q \<circ>\<^sub>p [:1, -1:])
     = [c (p - i). i \<leftarrow> [0..<p+1]]"
    using Qref reindex Bernstein_coeffs_01_Bernstein_sum_list by simp

  have list_c: "[c i. i \<leftarrow> [0..<p+1]] = Bernstein_coeffs_01 p Q"
  proof (rule nth_equalityI)
    show "length [c i. i \<leftarrow> [0..<p+1]] = length (Bernstein_coeffs_01 p Q)"
      by (simp add: length_Bernstein_coeffs_01)
  next
    fix i assume hi: "i < length [c i. i \<leftarrow> [0..<p+1]]"
    hence i_lt: "i < p + 1" by simp
    hence i_in: "i < length (Bernstein_coeffs_01 p Q)"
      by (simp add: length_Bernstein_coeffs_01)
    show "[c i. i \<leftarrow> [0..<p+1]] ! i = Bernstein_coeffs_01 p Q ! i"
      using i_lt i_in 
      by (metis \<open>c \<equiv> nth_default 0 (Bernstein_coeffs_01 p Q)\<close>
          length_Bernstein_coeffs_01 map_nth_default)
  qed

  have rev_upt:
    "[c (p - i). i \<leftarrow> [0..<p+1]] = rev [c i. i \<leftarrow> [0..<p+1]]"
    using rev_upt_map_c by blast

  show ?thesis
    using coeffs_ref list_c rev_upt by simp
qed

theorem Bernstein_coeffs_01_split_right:
  assumes hP: "degree P \<le> p"
  shows "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:t, 1 - t:]) = dc_right t (Bernstein_coeffs_01 p P)"
proof -
  let ?s = "1 - t"

  have deg_ref: "degree (P \<circ>\<^sub>p [:1, -1:]) \<le> p"
    using hP by (simp add: degree_pcompose_le)

  have coeff_ref:
    "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:1, -1:]) = rev (Bernstein_coeffs_01 p P)"
    using Bernstein_coeffs_01_reflect[OF hP] .

  have comp1:
    "(P \<circ>\<^sub>p [:1, -1:]) \<circ>\<^sub>p [:0, ?s:] = P \<circ>\<^sub>p [:1, - ?s:]"
    by (rule poly_ext) (simp add: poly_pcompose algebra_simps)

  have left_on_ref:
    "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:1, - ?s:]) = dc_left ?s (rev (Bernstein_coeffs_01 p P))"
    using Bernstein_coeffs_01_split_left[OF deg_ref, of ?s] coeff_ref
    by (simp add: comp1)

  have deg1: "degree (P \<circ>\<^sub>p [:1, - ?s:]) \<le> p"
    using hP by (simp add: degree_pcompose_le)

  have comp2:
    "(P \<circ>\<^sub>p [:1, - ?s:]) \<circ>\<^sub>p [:1, -1:] = P \<circ>\<^sub>p [:t, 1 - t:]"
    by (rule poly_ext) (simp add: poly_pcompose algebra_simps)

  have rhs_as_rev_left:
    "Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:t, 1 - t:])
     = rev (Bernstein_coeffs_01 p (P \<circ>\<^sub>p [:1, - ?s:]))"
    using Bernstein_coeffs_01_reflect
    by (metis Bernstein_coeffs_01_reflect comp2 deg1)

  show ?thesis
    using rhs_as_rev_left left_on_ref
    by (simp add: dc_right_eq_rev_dc_left)
qed

end