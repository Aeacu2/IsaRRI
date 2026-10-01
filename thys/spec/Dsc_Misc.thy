theory Dsc_Misc
  imports
    Main
    Three_Circles.Three_Circles
    Polynomial_Factorization.Square_Free_Factorization
    "Polynomial_Interpolation.Ring_Hom_Poly"
    List_Changes
begin

text \<open>AFP compatibility shim for the spec layer.
  Layer: FUNCTIONAL SPEC.
  Main exports: the general-purpose polynomial/square-free facts the downstream spec proofs
  need, reconstructed from plain HOL so the chain does not drag Algebraic_Numbers.\<close>

text \<open>AFP compatibility shim. The downstream spec proofs were originally developed against
  facts/abbreviations that reached them transitively through \<open>Dsc_Exec\<close>'s (now-removed) imports
  of \<open>Algebraic_Numbers.Algebraic_Numbers_External_Code\<close> and \<open>Descartes_Sign_Rule\<close>. Every one
  of those is a general-purpose lemma with nothing algebraic-numbers-specific about it, so we
  reconstruct them here from plain HOL (using the AFP's own one-line proofs) — this keeps the
  heavy \<^emph>\<open>Algebraic_Numbers\<close> AFP entry off the \<open>IsaRRI_Spec\<close> base entirely
  (the root-bound Cauchy math lives in the separate \<open>Dsc_Spec_Cauchy_Bound\<close> sibling session).\<close>

abbreviation real_of_int_poly :: "int poly \<Rightarrow> real poly" where
  "real_of_int_poly \<equiv> of_int_poly"

lemma pCons_as_add:
  fixes p :: "'a :: comm_semiring_1 poly"
  shows "pCons a p = [:a:] + monom 1 1 * p" by (auto simp: monom_Suc)

lemma mult_pCons_0: "(*) (pCons 0 1) = pCons 0" by auto

lemma min_minus [simp]: "min m (m - k) = m - k" for m k :: nat by arith

lemma image_diff_atMost: "(\<lambda>i. (n::nat) - i) ` {..n} = {..n}" (is "?l = ?r")
  unfolding set_eq_iff
proof (intro allI iffI)
  fix x assume "x \<in> ?r"
  thus "x \<in> ?l" unfolding image_def mem_Collect_eq
    by (intro bexI[of _ "n-x"], auto)
qed auto

lemma nth_append_take_is_nth_conv:
  assumes "i < j" and "j \<le> length xs" shows "(take j xs @ ys)!i = xs!i"
proof -
  from assms have "i < length (take j xs)" by simp
  hence "(take j xs @ ys)!i = take j xs ! i" unfolding nth_append by simp
  thus ?thesis unfolding nth_take[OF assms(1)] .
qed

text \<open>\<^bold>\<open>The bisection measure is a depth.\<close> Every consumer uses \<open>mu\<close> inside the budget
  \<open>2\<^sup>S\<^sup>u\<^sup>c\<^sup>\<mu> - 1\<close>, the node count of a binary tree of depth \<open>\<mu>\<close>, so \<open>\<mu>\<close> is the depth of the bisection
  tree, \<open>\<lceil>log\<^sub>2 ((b-a)/\<delta>)\<rceil>\<close>. A linear node count \<open>nat \<lceil>(b-a)/\<delta>\<rceil>\<close> would also be sound, but every
  machine-word premise stated against \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1\<close> would inherit an exponential blow-up, and those
  premises surface at the exported interface as caller obligations.

  The facts about \<open>mu\<close> that consumers use are \<open>mu_halve_strict\<close> (both directions),
  \<open>mu_subinterval_factor_strict\<close> and \<open>Hybrid_Keystone.mu_ge_1\<close>.

  \<^bold>\<open>Both wrappers are needed.\<close> The \<open>Suc\<close> keeps \<open>\<mu> \<ge> 1\<close> unconditional, so \<open>mu_ge_1\<close> holds on
  \<open>a < b\<close> alone (a bare \<open>nat \<lceil>log\<^sub>2 x\<rceil>\<close> is 0 once the width drops below \<open>\<delta>\<close>). The \<open>max 1\<close> keeps
  \<open>log\<close> off its junk domain, so the definition is total without a case split.\<close>
definition mu :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat"
  where "mu \<delta> a b = Suc (nat \<lceil>log 2 (max 1 ((b - a) / \<delta>))\<rceil>)"

text \<open>The single core step: halving (or better) strictly drops the ceiling-log. Both
  interface lemmas below are corollaries of this one fact.\<close>
lemma nat_ceil_log2_strict_half:
  fixes x y :: real
  assumes x1: "1 < x" and yx: "y \<le> x / 2"
  shows "nat \<lceil>log 2 (max 1 y)\<rceil> < nat \<lceil>log 2 (max 1 x)\<rceil>"
proof -
  have xmax: "max 1 x = x" using x1 by simp
  have logx_pos: "0 < log 2 x" using x1 by simp
  hence ceil_x: "(0::int) < \<lceil>log 2 x\<rceil>" by (simp add: less_ceiling_iff)
  have nat_x: "1 \<le> nat \<lceil>log 2 x\<rceil>"
    using ceil_x by (simp add: Suc_le_eq zero_less_nat_eq)
  show ?thesis
  proof (cases "y \<le> 1")
    case True
    hence "max 1 y = 1" by simp
    thus ?thesis using nat_x xmax x1 by simp
  next
    case False
    hence y1: "1 < y" by simp
    have ymax: "max 1 y = y" using y1 by simp
    have "log 2 y \<le> log 2 (x / 2)"
      using yx y1 x1 by (simp add: log_le_cancel_iff)
    also have "log 2 (x / 2) = log 2 x - 1"
      using x1 by (simp add: log_divide)
    finally have le1: "log 2 y \<le> log 2 x - 1" .
    have "\<lceil>log 2 y\<rceil> \<le> \<lceil>log 2 x - 1\<rceil>" using le1 by (rule ceiling_mono)
    also have "\<lceil>log 2 x - 1\<rceil> = \<lceil>log 2 x\<rceil> - 1" by simp
    finally have "\<lceil>log 2 y\<rceil> < \<lceil>log 2 x\<rceil>" by linarith
    moreover have "0 \<le> \<lceil>log 2 y\<rceil>"
    proof -
      have "0 < log 2 y" using y1 by simp
      moreover have "log 2 y \<le> of_int \<lceil>log 2 y\<rceil>" by (rule le_of_int_ceiling)
      ultimately show ?thesis by linarith
    qed
    ultimately show ?thesis using xmax ymax x1 by simp
  qed
qed

lemma mu_halve_strict:
  assumes "\<delta> > 0" "a < b" "\<delta> < b - a"
  shows "mu \<delta> a ((a + b) / 2) < mu \<delta> a b"
    and  "mu \<delta> ((a + b) / 2) b < mu \<delta> a b"
proof -
  have xgt1: "(b - a) / \<delta> > 1" using assms by (simp add: field_simps)
  have wL: "((a + b) / 2 - a) / \<delta> = ((b - a) / \<delta>) / 2" by (simp add: field_simps)
  have wR: "(b - (a + b) / 2) / \<delta> = ((b - a) / \<delta>) / 2" by (simp add: field_simps)
  show "mu \<delta> a ((a + b) / 2) < mu \<delta> a b"
    unfolding mu_def wL
    using nat_ceil_log2_strict_half[OF xgt1 order.refl] by simp
  show "mu \<delta> ((a + b) / 2) b < mu \<delta> a b"
    unfolding mu_def wR
    using nat_ceil_log2_strict_half[OF xgt1 order.refl] by simp
qed

lemma mu_subinterval_factor_strict:
  fixes \<delta> :: real
  assumes dpos: "\<delta> > 0"
      and ab: "a < b"
      and dw: "\<delta> < b - a"
      and N2: "N \<ge> 2"
      and width: "b' - a' = (b - a) / of_nat N"
  shows "mu \<delta> a' b' < mu \<delta> a b"
proof -
  have xgt1: "(b - a) / \<delta> > 1" using dpos dw by (simp add: field_simps)
  have Npos: "(0::real) < of_nat N" using N2 by simp
  have wsplit: "(b' - a') / \<delta> = ((b - a) / \<delta>) / of_nat N"
    unfolding width by (simp add: field_simps)
  \<comment> \<open>\<open>divide_left_mono\<close>'s third premise is \<open>0 < a * b\<close> in THAT order (\<open>real N * 2\<close>);
     writing it as \<open>2 * real N\<close> leaves the goal unrefined.\<close>
  have le_half: "((b - a) / \<delta>) / of_nat N \<le> ((b - a) / \<delta>) / 2"
    using N2 Npos xgt1 by (intro divide_left_mono) auto
  show ?thesis
    unfolding mu_def wsplit
    using nat_ceil_log2_strict_half[OF xgt1 le_half] by simp
qed

definition proots_dist_set :: "complex poly \<Rightarrow> real set" where
  "proots_dist_set P =
     {dist z1 z2 | z1 z2.
        z1 \<in> proots P \<and> z2 \<in> proots P \<and> z1 \<noteq> z2}"

lemma finite_proots_dist_set:
  assumes "P \<noteq> (0 :: complex poly)"
  shows   "finite (proots_dist_set P)"
proof -
  have fin_roots: "finite (proots P)"
    using assms finite_proots by blast
  then have "finite ((\<lambda>(z1,z2). dist z1 z2) ` (proots P \<times> proots P))"
     by blast
  then show ?thesis
    by (smt (verit, ccfv_SIG) finite_subset mem_Collect_eq
        mem_Sigma_iff pair_imageI proots_dist_set_def
        subsetI)
qed

lemma card_ge_2_imp_two_elems:
  assumes "finite (A :: 'a set)" and "card A \<ge> 2"
  shows "\<exists>x\<in>A. \<exists>y\<in>A. y \<noteq> x"
proof -
  from assms have "A \<noteq> {}" by auto
  then obtain x where xA: "x \<in> A" by auto

  let ?B = "A - {x}"
  have finB: "finite ?B"
    using assms(1) by auto

  have cardB: "card ?B = card A - 1"
    using assms(1) xA by (simp add: card_Diff_singleton_if)

  from assms(2) have "card A - 1 \<ge> 1"
    by linarith
  hence "card ?B \<ge> 1"
    using cardB by simp

  hence "\<exists>y. y \<in> ?B"
    using finB 
  by (metis One_nat_def all_not_in_conv card.empty
      linorder_not_less zero_less_Suc)
  then obtain y where yB: "y \<in> ?B" by auto

  from yB have yA: "y \<in> A" and yneq: "y \<noteq> x"
    by auto

  from xA yA yneq show ?thesis
    by blast
qed

lemma proots_dist_set_nonempty:
  assumes "P \<noteq> (0 :: complex poly)"
      and "card (proots P) \<ge> 2"
  shows   "proots_dist_set P \<noteq> {}"
proof -
  obtain z1 z2
    where z1: "z1 \<in> proots P"
      and z2: "z2 \<in> proots P"
      and ne: "z2 \<noteq> z1"
    using card_ge_2_imp_two_elems[
            OF finite_proots[OF assms(1)] assms(2)
          ] by blast

  hence "dist z1 z2 \<in> proots_dist_set P"
    unfolding proots_dist_set_def by blast

  thus ?thesis
  by blast
qed

definition root_sep :: "complex poly \<Rightarrow> real" where
  "root_sep P =
     (if card (proots P) \<ge> 2
      then Min (proots_dist_set P)
      else 1)"

lemma root_sep_pos:
  assumes P_nonzero: "P \<noteq> (0 :: complex poly)"
  shows   "root_sep P > 0"
proof (cases "card (proots P) \<ge> 2")
  case False
  then show ?thesis
    by (simp add: root_sep_def)
next
  case True
  have dist_set_finite: "finite (proots_dist_set P)"
    using P_nonzero finite_proots_dist_set by blast
  have dist_set_nonempty: "proots_dist_set P \<noteq> {}"
    using P_nonzero True proots_dist_set_nonempty by blast

  have Min_in_set: "Min (proots_dist_set P) \<in> proots_dist_set P"
    using dist_set_finite dist_set_nonempty by (rule Min_in)

  then obtain z1 z2 where
    Min_eq: "Min (proots_dist_set P) = dist z1 z2"
    and z1_root: "z1 \<in> proots P"
    and z2_root: "z2 \<in> proots P"
    and z1_neq_z2: "z1 \<noteq> z2"
    unfolding proots_dist_set_def
    by blast

  have Min_pos: "Min (proots_dist_set P) > 0"
    using Min_eq z1_neq_z2 by simp

  with True show ?thesis
    by (simp add: root_sep_def)
qed


lemma dist_two_roots_ge_root_sep:
  assumes "P \<noteq> (0 :: complex poly)"
      and "z1 \<in> proots P" "z2 \<in> proots P" "z1 \<noteq> z2"
      and "card (proots P) \<ge> 2"
  shows "dist z1 z2 \<ge> root_sep P"
proof -
  have fin: "finite (proots_dist_set P)"
    using assms(1) finite_proots_dist_set by blast
  have ne: "proots_dist_set P \<noteq> {}"
    using assms(1,5) proots_dist_set_nonempty by blast
  have "dist z1 z2 \<in> proots_dist_set P"
    unfolding proots_dist_set_def using assms(2-4) by blast
  then have "Min (proots_dist_set P) \<le> dist z1 z2"
    using fin ne by simp
  thus ?thesis
    using assms(5) by (simp add: root_sep_def)
qed

definition R0 :: real where
  "R0 = cmod (1/2 + (sqrt 3 / 6) * Complex.imaginary_unit) + sqrt 3 / 3"

definition cball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set" where
  "cball x r = {y. dist y x \<le> r}"

lemma upper_circle_01_subset_cball0:
  "upper_circle_01 \<subseteq> cball 0 R0"
proof
  fix x assume "x \<in> upper_circle_01"
  then have hx: "cmod (x - (1/2 + sqrt 3 / 6 * Complex.imaginary_unit)) < sqrt 3 / 3"
    by (simp add: upper_circle_01_def)
  have "cmod x = cmod ((x - (1/2 + sqrt 3 / 6 * Complex.imaginary_unit)) +
                       (1/2 + sqrt 3 / 6 * Complex.imaginary_unit))"
    by simp
  also have "\<dots> \<le> cmod (x - (1/2 + sqrt 3 / 6 * Complex.imaginary_unit)) +
                 cmod (1/2 + sqrt 3 / 6 * Complex.imaginary_unit)"
    using norm_triangle_ineq by blast
  also have "\<dots> \<le> sqrt 3 / 3 + cmod (1/2 + sqrt 3 / 6 * Complex.imaginary_unit)"
    using hx by simp
  also have "\<dots> = R0"
    by (simp add: R0_def)
  finally have "cmod x \<le> R0" .
  thus "x \<in> cball 0 R0"
    by (simp add: cball_def)
qed

lemma cmod_centres_eq:
  "cmod (1 / 2 + (sqrt 3 / 6) * Complex.imaginary_unit) =
   cmod (1 / 2 - (sqrt 3 / 6) * Complex.imaginary_unit)"
  apply (subst complex_mod_cnj[symmetric,
          of "1 / 2 + (sqrt 3 / 6) * Complex.imaginary_unit"])
  apply (simp)
  done

lemma lower_circle_01_subset_cball0:
  "lower_circle_01 \<subseteq> cball (0::complex) R0"
proof
  fix x assume "x \<in> lower_circle_01"
  then have hx:
    "cmod (x - (1/2 - sqrt 3 / 6 * Complex.imaginary_unit)) < sqrt 3 / 3"
    by (simp add: lower_circle_01_def)

  have "cmod x =
        cmod ((x - (1/2 - sqrt 3 / 6 * Complex.imaginary_unit)) +
               (1/2 - sqrt 3 / 6 * Complex.imaginary_unit))"
    by simp
  also have "\<dots> \<le> cmod (x - (1/2 - sqrt 3 / 6 * Complex.imaginary_unit)) +
                 cmod (1/2 - sqrt 3 / 6 * Complex.imaginary_unit)"
    using norm_triangle_ineq by blast
  also have "\<dots> \<le> sqrt 3 / 3 +
                 cmod (1/2 - sqrt 3 / 6 * Complex.imaginary_unit)"
    using hx by simp
  also have "\<dots> = sqrt 3 / 3 +
                 cmod (1/2 + sqrt 3 / 6 * Complex.imaginary_unit)"
    using cmod_centres_eq by simp
  also have "\<dots> = R0"
    by (simp add: R0_def)
  finally have "cmod x \<le> R0" .
  thus "x \<in> cball 0 R0"
    by (simp add: cball_def dist_complex_def)
qed

lemma diameter_upper_lower_01:
  assumes "x \<in> upper_circle_01 \<union> lower_circle_01"
      and "y \<in> upper_circle_01 \<union> lower_circle_01"
  shows "dist x y \<le> 2 * R0"
proof -
  have x_ball: "x \<in> cball (0::complex) R0"
    using assms(1) upper_circle_01_subset_cball0 lower_circle_01_subset_cball0
    by auto
  have y_ball: "y \<in> cball (0::complex) R0"
    using assms(2) upper_circle_01_subset_cball0 lower_circle_01_subset_cball0
    by auto

  from x_ball have dx0: "dist x 0 \<le> R0"
    by (simp add: cball_def)
  from y_ball have dy0: "dist y 0 \<le> R0"
    by (simp add: cball_def)

  have "dist x y \<le> dist x 0 + dist y 0"
    by (metis dist_triangle dist_commute)
  also have "\<dots> \<le> R0 + R0"
    using dx0 dy0 by linarith
  finally show ?thesis by simp
qed

definition T :: "real \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> complex" where
  "T a b z = of_real a + of_real (b - a) * z"

lemma dist_T_scale:
  fixes a b :: real and u v :: complex
  assumes "a < b"
  shows "dist (T a b u) (T a b v) = (b - a) * dist u v"
proof -
  have "dist (T a b u) (T a b v) = norm (T a b u - T a b v)"
    by (simp add: dist_complex_def)

  also have "T a b u - T a b v
             = of_real a + of_real (b - a) * u
               - (of_real a + of_real (b - a) * v)"
    by (simp add: T_def)
  also have "... = of_real (b - a) * (u - v)"
    by (simp add: algebra_simps)
  hence "norm (T a b u - T a b v) = norm (of_real (b - a) * (u - v))"
    using T_def by fastforce

  have "norm (of_real (b - a) * (u - v))
             = norm (of_real (b - a) :: complex) * norm (u - v)"
  by (simp add: norm_mult)

  have "norm (of_real (b - a) :: complex) = norm (b - a)"
    by (metis norm_of_real real_norm_def)

  from assms have "norm (b - a) = b - a"
    by simp

  have "norm (u - v) = dist u v"
    by (simp add: dist_complex_def)

  then show ?thesis
  using
    \<open>cmod (T a b u - T a b v) = cmod (complex_of_real (b - a) * (u - v))\<close>
    \<open>cmod (complex_of_real (b - a) * (u - v)) = cmod (complex_of_real (b - a)) * cmod (u - v)\<close>
    \<open>cmod (complex_of_real (b - a)) = norm (b - a)\<close>
    \<open>norm (b - a) = b - a\<close> dist_complex_def
  by force
qed

definition C_circle :: real where
  "C_circle = 2 * R0"

lemma diameter_upper_lower:
  fixes a b :: real and x y :: complex
  assumes ab: "a < b"
      and x_in: "x \<in> upper_circle a b \<union> lower_circle a b"
      and y_in: "y \<in> upper_circle a b \<union> lower_circle a b"
  shows "dist x y \<le> C_circle * (b - a)"
proof -
  have pos: "b - a > 0"
    using ab by simp

  have U_rescale:
    "upper_circle a b = T a b ` upper_circle_01"
    using upper_circle_rescale[OF ab]
    unfolding T_def 
  by (simp add: add.commute mult.commute)
  have L_rescale:
    "lower_circle a b = T a b ` lower_circle_01"
    using lower_circle_rescale[OF ab]
    unfolding T_def 
  by (simp add: add.commute mult.commute)

  have union_rescale:
    "upper_circle a b \<union> lower_circle a b =
       T a b ` (upper_circle_01 \<union> lower_circle_01)"
    by (simp add: U_rescale L_rescale image_Un)

  from x_in have "x \<in> T a b ` (upper_circle_01 \<union> lower_circle_01)"
      by (simp add: union_rescale)
  then obtain u where
    u01: "u \<in> upper_circle_01 \<union> lower_circle_01" and
    x_eq: "x = T a b u"
    by auto

  from y_in have "y \<in> T a b ` (upper_circle_01 \<union> lower_circle_01)"
    by (simp add: union_rescale)
  then obtain v where
    v01: "v \<in> upper_circle_01 \<union> lower_circle_01" and
    y_eq: "y = T a b v"
    by auto

  have "dist x y = (b - a) * dist u v"
    using dist_T_scale[OF ab, of u v]
    by (simp add: x_eq y_eq)

  also have "dist u v \<le> 2 * R0"
    using diameter_upper_lower_01[OF u01 v01] .

  hence "(b - a) * dist u v \<le> (b - a) * (2 * R0)"
    using pos by (intro mult_left_mono) simp_all

  finally show ?thesis
    by (simp add: C_circle_def mult_ac)
qed

lemma small_interval_no_two_distinct_roots:
  fixes Q :: "complex poly"
  assumes Q0: "Q \<noteq> 0"
      and ab: "a < b"
      and small: "b - a \<le> root_sep Q / (2 * C_circle)"
  shows "\<not> (\<exists>z1\<in>proots Q. \<exists>z2\<in>proots Q.
               z1 \<noteq> z2 \<and>
               z1 \<in> upper_circle a b \<union> lower_circle a b \<and>
               z2 \<in> upper_circle a b \<union> lower_circle a b)"
proof
  assume ex2:
    "\<exists>z1\<in>proots Q. \<exists>z2\<in>proots Q.
       z1 \<noteq> z2 \<and>
       z1 \<in> upper_circle a b \<union> lower_circle a b \<and>
       z2 \<in> upper_circle a b \<union> lower_circle a b"
  then obtain z1 z2 where
    z1_root: "z1 \<in> proots Q" and
    z2_root: "z2 \<in> proots Q" and
    ne: "z1 \<noteq> z2" and
    z1_in: "z1 \<in> upper_circle a b \<union> lower_circle a b" and
    z2_in: "z2 \<in> upper_circle a b \<union> lower_circle a b"
    by blast

  have ab_pos: "b - a > 0"
    using ab by simp

  have dist_upper: "dist z1 z2 \<le> C_circle * (b - a)"
    using diameter_upper_lower[OF ab z1_in z2_in] by simp

  have C_pos: "C_circle > 0"
    using C_circle_def R0_def 
  by (smt (verit, ccfv_threshold) Q0 ab_pos root_sep_pos
      small zero_less_divide_iff)

  from small have small':
    "C_circle * (b - a) \<le> C_circle * (root_sep Q / (2 * C_circle))"
    using C_pos 
  using mult_le_cancel_left_pos by blast

  have "C_circle * (root_sep Q / (2 * C_circle)) = root_sep Q / 2"
    using C_pos by (simp add: field_simps)
  then have bound: "C_circle * (b - a) \<le> root_sep Q / 2"
    using small' by simp

  have dist_lt_sep: "dist z1 z2 < root_sep Q"
  proof -
    have "dist z1 z2 \<le> C_circle * (b - a)"
      using dist_upper .
    also have "\<dots> \<le> root_sep Q / 2"
      using bound .
    finally have "dist z1 z2 \<le> root_sep Q / 2" .
    moreover have "root_sep Q / 2 < root_sep Q"
      using root_sep_pos[OF Q0]  by simp
    ultimately show ?thesis
      by linarith
  qed

  have card_ge2: "card (proots Q) \<ge> 2"
  proof -
    have "{z1,z2} \<subseteq> proots Q"
      using z1_root z2_root by auto
    moreover have "card {z1,z2} = 2"
      using ne by (simp add: card_insert_if)
    ultimately show ?thesis
      using Q0 finite_proots
      by (metis card_mono)
  qed

  have dist_ge_sep: "dist z1 z2 \<ge> root_sep Q"
    using dist_two_roots_ge_root_sep[OF Q0 z1_root z2_root ne card_ge2] .

  show False
    using dist_lt_sep dist_ge_sep by linarith
qed

definition delta_P :: "real poly \<Rightarrow> real" where
  "delta_P P =
     (if map_poly of_real P = (0 :: complex poly)
      then 1 
      else root_sep (map_poly of_real P) / (4 * R0))"

lemma delta_P_pos:
  assumes "P \<noteq> 0"
  shows "delta_P P > 0"
proof -
  have "map_poly of_real P \<noteq> (0 :: complex poly)"
    using assms by (simp add: map_poly_eq_0_iff)
  then have "root_sep (map_poly of_real P) > 0"
    using root_sep_pos by blast
  moreover have "4 * R0 > 0"
    unfolding R0_def
  by (smt (verit) complex_mod_triangle_ineq2 complex_mod_triangle_sub
      real_sqrt_gt_zero zero_less_divide_iff)
  ultimately show ?thesis
    unfolding delta_P_def using \<open>map_poly of_real P \<noteq> 0\<close>
    by (simp add: field_simps)
qed

lemma proots_count_le_1:
  fixes p :: "'a::field_char_0 poly"
  assumes rsf: "rsquarefree p"
      and card_le1: "card (proots_within p S) \<le> 1"
  shows "proots_count p S \<le> 1"
proof -
  from rsf have p0: "p \<noteq> 0"
    unfolding rsquarefree_def by auto

  have order_eq_1:
    "order z p = 1" if hz: "z \<in> proots_within p S" for z
  proof -
    from hz have "poly p z = 0"
      by (simp add: proots_within_def)
    from order_gt_0_iff[OF p0, of z] this have "order z p > 0"
      by simp
    moreover from rsf have "order z p = 0 \<or> order z p = 1"
      unfolding rsquarefree_def by blast
    ultimately show ?thesis by linarith
  qed

  have "proots_count p S = (\<Sum>z\<in>proots_within p S. order z p)"
    by (simp add: proots_count_def)
  also have "... = (\<Sum>z\<in>proots_within p S. 1)"
    using order_eq_1 by simp
  also have "... = card (proots_within p S)"
    by simp
  finally have "proots_count p S = card (proots_within p S)" .

  with card_le1 show ?thesis by simp
qed

lemma card_proots_within_circle_le1:
  fixes Q :: "complex poly"
  assumes Q0: "Q \<noteq> 0" 
      and ab: "a < b"
      and small: "b - a \<le> root_sep Q / (2 * C_circle)"
  shows "card (proots_within Q (upper_circle a b \<union> lower_circle a b)) \<le> 1"
proof -
  let ?S = "upper_circle a b \<union> lower_circle a b"

  have fin_proots: "finite (proots Q)"
    using Q0 finite_proots by blast

  have fin: "finite (proots_within Q ?S)"
  proof -
    have "proots_within Q ?S \<subseteq> proots Q"
      by (auto simp: proots_within_def proots_def)
    then show ?thesis
      using fin_proots finite_subset by blast
  qed

  have not_ge2:
    "\<not> (card (proots_within Q ?S) \<ge> 2)"
  proof
    assume ge2: "card (proots_within Q ?S) \<ge> 2"
    then obtain z1 z2 where
      z1_in: "z1 \<in> proots_within Q ?S" and
      z2_in: "z2 \<in> proots_within Q ?S" and
      ne: "z1 \<noteq> z2"
      using card_ge_2_imp_two_elems[OF fin ge2] by blast

    from z1_in have z1_root: "z1 \<in> proots Q" and z1_S: "z1 \<in> ?S"
      by (auto simp: proots_within_def)
    from z2_in have z2_root: "z2 \<in> proots Q" and z2_S: "z2 \<in> ?S"
      by (auto simp: proots_within_def)

    have False
      using small_interval_no_two_distinct_roots[OF Q0 ab small]
            z1_root z2_root ne z1_S z2_S
      by blast
    thus False ..
  qed

  from not_ge2 show ?thesis
    by linarith
qed

lemma proots_count_circle_le_1_small_interval:
  fixes P :: "real poly"
  defines "Q \<equiv> map_poly of_real P"
  assumes P0: "P \<noteq> 0"
      and rsf: "rsquarefree Q"
      and ab: "a < b"
      and small: "b - a \<le> delta_P P"
  shows "proots_count Q (upper_circle a b \<union> lower_circle a b) \<le> 1"
proof -
  have Q0: "Q \<noteq> (0 :: complex poly)"
    unfolding Q_def using P0 by (simp add: map_poly_eq_0_iff)

  have delta_expr: "delta_P P = root_sep Q / (4 * R0)"
    unfolding delta_P_def Q_def using Q0
  using Q_def by presburger

  have C_def: "C_circle = 2 * R0"
    by (simp add: C_circle_def)

  have small':
    "b - a \<le> root_sep Q / (2 * C_circle)"
  proof -
    have "root_sep Q / (2 * C_circle) = root_sep Q / (4 * R0)"
      by (simp add: C_def field_simps)
    with small delta_expr show ?thesis
    by argo
  qed

  have card_le1:
    "card (proots_within Q (upper_circle a b \<union> lower_circle a b)) \<le> 1"
    using card_proots_within_circle_le1[OF Q0 ab small'] .

  have "proots_count Q (upper_circle a b \<union> lower_circle a b) \<le> 1"
    using proots_count_le_1[OF rsf card_le1] .
  thus ?thesis .
qed

lemma halfplane_cover:
  "{x::complex. 0 < Re x} \<subseteq> {x. Im x < sqrt 3 * Re x} \<union> {x. Im x > - sqrt 3 * Re x}"
proof
  fix x :: complex
  assume hx: "x \<in> {x. 0 < Re x}"
  then have Re_pos: "0 < Re x" by simp
  show "x \<in> {x. Im x < sqrt 3 * Re x} \<union> {x. Im x > - sqrt 3 * Re x}"
  proof (cases "Im x < sqrt 3 * Re x")
    case True
    then show ?thesis by simp
  next
    case False
    hence ge: "Im x \<ge> sqrt 3 * Re x"
      by simp
    have "sqrt 3 * Re x > 0"
      using Re_pos by simp
    hence "- sqrt 3 * Re x < sqrt 3 * Re x"
      by simp
    from ge this have "Im x > - sqrt 3 * Re x"
      by linarith
    thus ?thesis by simp
  qed
qed

lemma circle_01_diam_subset_upper_lower_01:
  "circle_01_diam \<subseteq> upper_circle_01 \<union> lower_circle_01"
proof
  fix z :: complex
  assume z_in: "z \<in> circle_01_diam"
  hence hz: "1 / z \<in> (\<lambda>x::complex. x + 1) ` {x. 0 < Re x}"
    using circle_01_diam_def pos_real_map by blast
  then obtain y :: complex where
    y_in: "y \<in> {x. 0 < Re x}" and
    yz: "1 / z = y + 1"
    by auto

  have y_halfplane:
    "y \<in> {x. Im x < sqrt 3 * Re x} \<union> {x. Im x > - sqrt 3 * Re x}"
    using halfplane_cover[THEN subsetD, OF y_in] .

  then consider (upper) "Im y < sqrt 3 * Re y"
             | (lower) "Im y > - sqrt 3 * Re y"
    by auto
  then show "z \<in> upper_circle_01 \<union> lower_circle_01"
  proof cases
    case upper
    hence "1 / z \<in> (\<lambda>x::complex. x + 1) ` {x. Im x < sqrt 3 * Re x}"
      using yz by auto
    hence "z \<in> upper_circle_01"
      using upper_circle_01_def upper_circle_map
    by blast
    thus ?thesis by simp
  next
    case lower
    hence "1 / z \<in> (\<lambda>x::complex. x + 1) ` {x. Im x > - sqrt 3 * Re x}"
      using yz by auto
    hence "z \<in> lower_circle_01"
      using lower_circle_01_def lower_circle_map by blast
    thus ?thesis by simp
  qed
qed

lemma circle_diam_subset_upper_lower:
  assumes ab: "a < b"
  shows "circle_diam a b \<subseteq> upper_circle a b \<union> lower_circle a b"
proof -
  let ?f = "\<lambda>x::complex. x * (of_real (b - a)) + of_real a"
  have circ_rescale: "circle_diam a b = ?f ` circle_01_diam"
    using circle_diam_rescale[OF ab] by simp
  have upper_rescale: "upper_circle a b = ?f ` upper_circle_01"
    using upper_circle_rescale[OF ab] by simp
  have lower_rescale: "lower_circle a b = ?f ` lower_circle_01"
    using lower_circle_rescale[OF ab] by simp

  have "circle_diam a b \<subseteq> ?f ` (upper_circle_01 \<union> lower_circle_01)"
  proof -
    have "circle_01_diam \<subseteq> upper_circle_01 \<union> lower_circle_01"
      by (rule circle_01_diam_subset_upper_lower_01)
    then have "?f ` circle_01_diam \<subseteq> ?f ` (upper_circle_01 \<union> lower_circle_01)"
      by (rule image_mono)
    then show ?thesis
      by (simp add: circ_rescale)
  qed
  also have "... = upper_circle a b \<union> lower_circle a b"
    by (simp add: upper_rescale lower_rescale image_Un)
  finally show ?thesis .
qed

lemma proots_count_mono:
  fixes Q :: "complex poly"
  assumes Q0: "Q \<noteq> 0"
      and subset: "A \<subseteq> B"
  shows "proots_count Q A \<le> proots_count Q B"
proof -
  have subset_rw:
    "proots_within Q A \<subseteq> proots_within Q B"
    using subset by (auto simp: proots_within_def)
  have finB: "finite (proots_within Q B)"
  proof -
    have "proots_within Q B \<subseteq> proots Q"
      by (auto simp: proots_within_def proots_def)
    moreover have "finite (proots Q)"
      using Q0 finite_proots by blast
    ultimately show ?thesis
      using finite_subset by blast
  qed
  have "proots_count Q A =
          (\<Sum>z\<in>proots_within Q A. order z Q)"
    by (simp add: proots_count_def)
  also have "\<dots> \<le> (\<Sum>z\<in>proots_within Q B. order z Q)"
  proof (rule sum_mono2)
    show "finite (proots_within Q B)" 
      using finB subset_rw finite_subset by blast
    show "proots_within Q A \<subseteq> proots_within Q B"
      by (rule subset_rw)
    show "\<And>z. z \<in> proots_within Q B - proots_within Q A \<Longrightarrow> 0 \<le> order z Q"
      by simp
  qed
  also have "\<dots> = proots_count Q B"
    by (simp add: proots_count_def)
  finally show ?thesis .
qed

lemma Bernstein_changes_small_interval_le_1:
  fixes P :: "real poly"
  defines "Q \<equiv> map_poly (of_real :: real \<Rightarrow> complex) P"
  assumes P0: "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0: "p \<noteq> 0"
      and rsf: "rsquarefree Q"
      and ab: "a < b"
      and small: "b - a \<le> delta_P P"
  shows "Bernstein_changes p a b P \<le> 1"
proof -
  have Q0: "Q \<noteq> (0 :: complex poly)"
    unfolding Q_def using P0 by (simp add: map_poly_eq_0_iff)

  let ?S  = "upper_circle a b \<union> lower_circle a b"
  let ?Cu = "proots_count Q ?S"
  let ?Cd = "proots_count Q (circle_diam a b)"

  have Cu_le1: "?Cu \<le> 1"
    using proots_count_circle_le_1_small_interval P0 Q_def ab rsf small by blast

  have subset: "circle_diam a b \<subseteq> ?S"
    using circle_diam_subset_upper_lower[OF ab] .
  have Cd_le_Cu: "?Cd \<le> ?Cu"
    using proots_count_mono[OF Q0 subset] .

  have "Bernstein_changes p a b P \<le> 1"
  proof (cases "?Cu = 0")
    case True
    hence Cu0: "?Cu = 0" .
    from Cd_le_Cu Cu0 have Cd0: "?Cd = 0" by simp

    have "Bernstein_changes p a b P = 0"
      using three_circles(1)[OF ab deg P0 p0, of] Cd0
      by (simp add: Q_def)
    thus ?thesis by simp
  next
    case False
    hence "?Cu \<noteq> 0" .
    with Cu_le1 have Cu1: "?Cu = 1"
      by (cases ?Cu) simp_all

    have "Bernstein_changes p a b P = 1"
      using three_circles(2)[OF ab deg P0 p0, of] Cu1
      by (simp add: Q_def)
    thus ?thesis by simp
  qed
  thus ?thesis .
qed

definition roots_in :: "real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat" where
  "roots_in P a b = proots_count P {x. a < x \<and> x < b}"

lemma Bernstein_changes_0_no_root:
  assumes deg: "degree P \<le> p"
      and P0: "P \<noteq> 0"
      and ab: "a < b"
      and v0: "Bernstein_changes p a b P = 0"
  shows "roots_in P a b = 0"
proof -
  have le:
    "roots_in P a b \<le> Bernstein_changes p a b P"
    using Bernstein_changes_test[OF deg P0 ab]
    unfolding roots_in_def by auto
  with v0 show ?thesis
    by (simp add: roots_in_def)
qed

lemma Bernstein_changes_1_one_root:
  assumes deg: "degree P \<le> p"
      and P0: "P \<noteq> 0"
      and ab: "a < b"
      and v1: "Bernstein_changes p a b P = 1"
  shows "roots_in P a b = 1"
proof -
  have test:
    "roots_in P a b \<le> Bernstein_changes p a b P \<and>
     even (Bernstein_changes p a b P - roots_in P a b)"
    using Bernstein_changes_test[OF deg P0 ab]
    unfolding roots_in_def by auto
  from test have le1: "roots_in P a b \<le> 1" and ev: "even (1 - roots_in P a b)"
    using v1 by simp_all

  have "roots_in P a b \<noteq> 0"
  proof
    assume "roots_in P a b = 0"
    then have "1 - roots_in P a b = 1" by simp
    hence "\<not> even (1 - roots_in P a b)" by simp
    with ev show False by contradiction
  qed
  with le1 show ?thesis
    by arith
qed

lemma Bernstein_changes_pos_of_root:
  assumes deg: "degree P \<le> p"
      and P0:  "P \<noteq> 0"
      and ab:  "a < b"
      and root: "poly P x = 0" "a < x" "x < b"
  shows "Bernstein_changes p a b P \<noteq> 0"
proof -
  have roots_ge1: "roots_in P a b \<ge> 1"
  proof -
    have R_sub: "{x} \<subseteq> {y. a < y \<and> y < b}"
      using root(2,3) by auto
    have "card {x} \<le> proots_count P {y. a < y \<and> y < b}"
      using RRI_Misc.proots_count_of_root_set[OF P0 R_sub] root(1)
      by (simp add: roots_in_def)
    then show ?thesis
      by (simp add: roots_in_def)
  qed

  have le:
    "roots_in P a b \<le> Bernstein_changes p a b P"
    using Bernstein_changes_test[OF deg P0 ab]
    unfolding roots_in_def by auto

  from roots_ge1 le show ?thesis by linarith
qed

lemma Bernstein_changes_point: "Bernstein_changes p a a P = 0"
proof -
  let ?Q = "P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p [:0, a - a:]"
  have "[:0, a - a:] = 0" by simp
  hence "?Q = P \<circ>\<^sub>p [:a, 1:] \<circ>\<^sub>p 0" by simp
  also have "\<dots> = [:poly P a:]" 
  by (simp add: pcompose_0')
  finally have Q_val: "?Q = [:poly P a:]" .

  have "Bernstein_coeffs p a a P = replicate (p+1) (poly P a)"
  proof (rule nth_equalityI)
    show "length (Bernstein_coeffs p a a P) = length (replicate (p + 1) (poly P a))"
      unfolding Bernstein_coeffs_def by simp
  next
    fix i assume "i < length (Bernstein_coeffs p a a P)"
    hence i_bounds: "i \<le> p" unfolding Bernstein_coeffs_def by simp
    
    let ?R = "reciprocal_poly p ?Q \<circ>\<^sub>p [:1, 1:]"
    
    have "reciprocal_poly p ?Q = monom (poly P a) p"
      using Q_val unfolding reciprocal_poly_def 
      by (cases "poly P a = 0") (auto simp: monom_altdef Poly_append)
    
    hence R_eq: "?R = smult (poly P a) ([:1, 1:] ^ p)"
    by (simp add: monom_altdef pcompose_hom.hom_power pcompose_smult)
      
    have "coeff ?R (p-i) = poly P a * real (p choose (p-i))"
      using R_eq unfolding poly_binomial 
      by (metis (mono_tags, lifting) R_eq coeff_linear_poly_power coeff_smult diff_le_self
          mult.right_neutral power_one)
         
    have "inverse (real (p choose i)) * coeff ?R (p-i) = poly P a"
      using \<open>coeff ?R (p-i) = ...\<close> binomial_symmetric[OF i_bounds]
      by (simp add: field_simps)
      
    thus "Bernstein_coeffs p a a P ! i = replicate (p + 1) (poly P a) ! i"
      unfolding Bernstein_coeffs_def using i_bounds
      by (metis (no_types, lifting) Bernstein_coeffs_def \<open>i < length (Bernstein_coeffs p a a P)\<close>
          add_0 diff_zero length_map length_upt nth_map_upt nth_replicate)
  qed

  have "changes (replicate (p+1) (poly P a)) = 0"
  proof (induction p)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have "replicate (Suc n + 1) (poly P a) = poly P a # replicate (n + 1) (poly P a)"
      by simp
    then show ?case 
      using Suc.IH changes.simps 
      by (cases "poly P a = 0") (auto simp: mult_less_0_iff)
  qed
  
  thus ?thesis unfolding Bernstein_changes_def 
    by (simp add: \<open>Bernstein_coeffs p a a P = replicate (p+1) (poly P a)\<close>)
qed

definition dsc_pair_ok :: "real poly \<Rightarrow> (real \<times> real) \<Rightarrow> bool" where
  "dsc_pair_ok P I \<longleftrightarrow>
     ((fst I = snd I \<and> poly P (fst I) = 0) \<or>
      (fst I < snd I \<and> roots_in P (fst I) (snd I) = 1))"

lemma square_free_liftC:
  assumes"square_free (p::(real poly))"
  shows "square_free(map_poly (of_real :: real \<Rightarrow> complex) p)"
  by (simp add: assms field_hom_0'.intro field_hom_0'.square_free_map_poly
      of_real_hom.field_hom_axioms)

lemma rsquarefree_lift:
  assumes"square_free (p::(real poly))"
  shows "rsquarefree(map_poly (of_real :: real \<Rightarrow> complex) p)"
  by (simp add: assms square_free_liftC square_free_rsquarefree)

end