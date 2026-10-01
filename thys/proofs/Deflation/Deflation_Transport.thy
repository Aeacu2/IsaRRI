theory Deflation_Transport
  imports "IsaRRI_LLVM.Newton_Spec"
begin

section \<open>The termination transport for degree deflation\<close>

text \<open>\<^bold>\<open>The obligation.\<close> @{thm [source] newdsc_pol_domI_general} takes a smallness witness
  \<open>\<delta>\<close> with the hypothesis \<open>\<And>a b. a < b \<Longrightarrow> b - a \<le> \<delta> \<Longrightarrow> Bernstein_changes p a b P \<le> 1\<close>,
  a statement about one fixed \<open>P\<close>, because @{const newdsc_pol} carries \<open>P :: real poly\<close> as a fixed
  parameter: the box \<open>(a,b)\<close> moves down the recursion and \<open>P\<close> does not. Deflation makes \<open>P\<close> a
  recursion variable, so termination needs one \<open>\<delta>\<close> serving every polynomial reachable in the
  recursion, and every such polynomial is a divisor of the input.

  \<^bold>\<open>Why this transports.\<close> Deflation removes roots, so the reachable root sets are subsets and
  separation can only increase. The analogous transport for power substitution is false: \<open>x \<mapsto> x\<^sup>d\<close>
  compresses roots near zero, and \<open>P(x) = (2\<^sup>8\<^sup>0x\<^sup>2-1)(2\<^sup>8\<^sup>0x\<^sup>2-4) = Q(x\<^sup>2)\<close> is a counterexample.

  \<^bold>\<open>Divisibility alone is not enough, because of @{const root_sep}'s degenerate branch.\<close>
  @{thm [source] root_sep_def} returns \<open>1\<close> when \<open>card (proots P) < 2\<close>, so @{const root_sep}
  is not monotone under divisibility: take \<open>P\<close> with complex roots \<open>0\<close> and \<open>100\<close> and
  \<open>D = [:0,1:]\<close>; then \<open>root_sep D = 1\<close> while \<open>root_sep P = 100\<close>, and \<open>\<delta> = delta_P P\<close> is too large
  for \<open>D\<close>. The fix is to clamp \<open>\<delta>\<close> at the degenerate branch's own value, the constant
  \<open>1 / (4 * R0)\<close> (\<open>delta_defl\<close> below). Then one \<open>\<delta>\<close> covers both branches and no new Bernstein
  fact is needed.\<close>

subsection \<open>The clamped smallness witness\<close>

definition delta_defl :: "real poly \<Rightarrow> real" where
  "delta_defl P = min (delta_P P) (1 / (4 * R0))"

lemma R0_pos: "R0 > 0"
  unfolding R0_def
  by (smt (verit) complex_mod_triangle_ineq2 complex_mod_triangle_sub
      real_sqrt_gt_zero zero_less_divide_iff)

lemma delta_defl_pos:
  assumes "P \<noteq> 0"
  shows "delta_defl P > 0"
  unfolding delta_defl_def
  using delta_P_pos[OF assms] R0_pos by simp

lemma delta_defl_le_delta_P: "delta_defl P \<le> delta_P P"
  unfolding delta_defl_def by simp

subsection \<open>Roots of a divisor are roots\<close>

lemma proots_subset_of_dvd:
  fixes P D :: "complex poly"
  assumes "D dvd P"
  shows "proots D \<subseteq> proots P"
  using assms unfolding proots_def by (auto elim!: dvdE)

lemma proots_dist_set_subset_of_dvd:
  fixes P D :: "complex poly"
  assumes "D dvd P"
  shows "proots_dist_set D \<subseteq> proots_dist_set P"
  using proots_subset_of_dvd[OF assms]
  unfolding proots_dist_set_def by blast

subsection \<open>Separation is monotone under divisibility, ON THE NON-DEGENERATE BRANCH\<close>

lemma root_sep_ge_of_dvd:
  fixes P D :: "complex poly"
  assumes P0: "P \<noteq> 0"
      and dvd: "D dvd P"
      and card2: "card (proots D) \<ge> 2"
  shows "root_sep D \<ge> root_sep P"
proof -
  have sub: "proots D \<subseteq> proots P"
    using proots_subset_of_dvd[OF dvd] .
  have D0: "D \<noteq> 0"
    using dvd P0 by auto
  have cardP2: "card (proots P) \<ge> 2"
    using card2 sub finite_proots[OF P0] card_mono by (meson le_trans)
  have finD: "finite (proots_dist_set D)"
    using finite_proots_dist_set[OF D0] .
  have finP: "finite (proots_dist_set P)"
    using finite_proots_dist_set[OF P0] .
  have neD: "proots_dist_set D \<noteq> {}"
    using proots_dist_set_nonempty[OF D0 card2] .
  have "Min (proots_dist_set P) \<le> Min (proots_dist_set D)"
    using Min_antimono[OF proots_dist_set_subset_of_dvd[OF dvd] neD finP] .
  thus ?thesis
    using card2 cardP2 by (simp add: root_sep_def)
qed

subsection \<open>The clamped witness serves EVERY divisor\<close>

lemma map_poly_of_real_dvd:
  fixes P D :: "real poly"
  assumes "D dvd P"
  shows "map_poly (of_real :: real \<Rightarrow> complex) D dvd map_poly (of_real :: real \<Rightarrow> complex) P"
proof -
  from assms obtain K where K: "P = D * K" by (rule dvdE)
  have "map_poly (of_real :: real \<Rightarrow> complex) P
          = map_poly (of_real :: real \<Rightarrow> complex) D * map_poly (of_real :: real \<Rightarrow> complex) K"
    unfolding K by (rule of_real_poly_map_mult)
  thus ?thesis by (rule dvdI)
qed

lemma delta_defl_le_delta_P_of_dvd:
  fixes P D :: "real poly"
  assumes P0: "P \<noteq> 0"
      and dvd: "D dvd P"
  shows "delta_defl P \<le> delta_P D"
proof -
  have D0: "D \<noteq> 0" using dvd P0 by auto
  let ?cP = "map_poly (of_real :: real \<Rightarrow> complex) P"
  let ?cD = "map_poly (of_real :: real \<Rightarrow> complex) D"
  have cP0: "?cP \<noteq> 0" using P0 by (simp add: map_poly_eq_0_iff)
  have cD0: "?cD \<noteq> 0" using D0 by (simp add: map_poly_eq_0_iff)
  have cdvd: "?cD dvd ?cP" using map_poly_of_real_dvd[OF dvd] .
  show ?thesis
  proof (cases "card (proots ?cD) \<ge> 2")
    case True
    have "root_sep ?cP \<le> root_sep ?cD"
      using root_sep_ge_of_dvd[OF cP0 cdvd True] .
    hence "delta_P P \<le> delta_P D"
      unfolding delta_P_def using cP0 cD0 R0_pos by (simp add: divide_right_mono)
    thus ?thesis using delta_defl_le_delta_P[of P] by linarith
  next
    case False
    hence "root_sep ?cD = 1" by (simp add: root_sep_def)
    hence "delta_P D = 1 / (4 * R0)"
      unfolding delta_P_def using cD0 by simp
    thus ?thesis unfolding delta_defl_def by simp
  qed
qed

subsection \<open>The transport\<close>

text \<open>One \<open>\<delta>\<close>, namely @{term "delta_defl P"}, is a smallness witness for \<^bold>\<open>every divisor\<close>
  of \<open>P\<close> simultaneously. This is exactly what a deflating recursion's termination argument
  needs, since every polynomial it can reach divides the input.\<close>

theorem Bernstein_changes_small_interval_le_1_of_dvd:
  fixes P D :: "real poly"
  assumes P0: "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0: "p \<noteq> 0"
      and sf: "square_free P"
      and dvd: "D dvd P"
      and ab: "a < b"
      and small: "b - a \<le> delta_defl P"
  shows "Bernstein_changes p a b D \<le> 1"
proof -
  have D0: "D \<noteq> 0" using dvd P0 by auto
  have degD: "degree D \<le> p"
    using dvd_imp_degree_le[OF dvd P0] deg by linarith
  have sfD: "square_free D"
    using square_free_factor[OF dvd sf] .
  have rsfD: "rsquarefree (map_poly (of_real :: real \<Rightarrow> complex) D)"
    using rsquarefree_lift[OF sfD] .
  have smallD: "b - a \<le> delta_P D"
    using small delta_defl_le_delta_P_of_dvd[OF P0 dvd] by linarith
  show ?thesis
    using Bernstein_changes_small_interval_le_1[OF D0 degD p0 rsfD ab smallD] .
qed

subsection \<open>Why the clamp is NECESSARY — a machine-checked counterexample\<close>

text \<open>``Reachable polynomials are divisors, so root separation only increases'' is true only on
  @{const root_sep}'s non-degenerate branch, and @{const delta_defl} exists for the other one. The
  refutation below is stated as a theorem so that replacing @{const delta_defl} by
  @{const delta_P} fails a check instead of breaking termination.

  Witness: \<open>P = x(x - 100)\<close>, \<open>D = x\<close>. \<open>D\<close> divides \<open>P\<close>, but \<open>D\<close> has one complex root, so
  @{const root_sep} takes its \<open>else 1\<close> branch and returns \<open>1\<close>, while \<open>root_sep P = 100\<close>.\<close>

lemma root_sep_not_mono_under_dvd:
  "\<exists>P D :: complex poly. D dvd P \<and> P \<noteq> 0 \<and> root_sep D < root_sep P"
proof -
  define D :: "complex poly" where "D = [:0, 1:]"
  define E :: "complex poly" where "E = [:-100, 1:]"
  define P :: "complex poly" where "P = D * E"

  have D0: "D \<noteq> 0" by (simp add: D_def)
  have E0: "E \<noteq> 0" by (simp add: E_def)
  have P0: "P \<noteq> 0" by (simp add: P_def D0 E0)

  have polyP: "\<And>z. poly P z = z * (z - 100)"
    by (simp add: P_def D_def E_def)

  have prootsD: "proots D = {0}"
    unfolding proots_def D_def by auto
  have prootsP: "proots P = {0, 100}"
    unfolding proots_def using polyP by auto

  have "card (proots D) < 2"
    by (simp add: prootsD)
  hence sepD: "root_sep D = 1"
    by (simp add: root_sep_def)

  have card2: "card (proots P) \<ge> 2"
    by (simp add: prootsP)
  \<comment> \<open>Read the value off @{thm [source] Min_in} instead of computing the whole distance
      set: obtain the very pair the \<open>Min\<close> is attained at. Every pair of DISTINCT roots here
      is \<open>{0,100}\<close> in some order, so that value is \<open>100\<close> whichever pair it is — and no
      set comprehension has to be evaluated. (Three tactic attempts at the set equality
      failed, and sledgehammer found nothing: the goal wanted DECOMPOSITION, because a single
      tactic was being asked to do both the set reasoning and the complex-numeral arithmetic.)\<close>
  have finP: "finite (proots_dist_set P)"
    using finite_proots_dist_set[OF P0] .
  have neP: "proots_dist_set P \<noteq> {}"
    using proots_dist_set_nonempty[OF P0 card2] .
  have "Min (proots_dist_set P) \<in> proots_dist_set P"
    using finP neP by (rule Min_in)
  then obtain z1 z2 where
        mz:  "Min (proots_dist_set P) = dist z1 z2"
    and z1P: "z1 \<in> proots P" and z2P: "z2 \<in> proots P" and zne: "z1 \<noteq> z2"
    unfolding proots_dist_set_def by blast
  have minP: "Min (proots_dist_set P) = 100"
    using mz z1P z2P zne unfolding prootsP by (auto simp: dist_norm)
  have sepP: "root_sep P = 100"
    using card2 minP by (simp add: root_sep_def)

  have "D dvd P" by (simp add: P_def)
  moreover have "root_sep D < root_sep P" by (simp add: sepD sepP)
  ultimately show ?thesis using P0 by blast
qed

text \<open>Immediate corollary: the original witness site still works, i.e. this generalises
  @{thm [source] newdsc_pol_terminates_squarefree}'s smallness step rather than replacing it —
  take \<open>D = P\<close>.\<close>

corollary Bernstein_changes_small_interval_le_1_delta_defl:
  fixes P :: "real poly"
  assumes "P \<noteq> 0" "degree P \<le> p" "p \<noteq> 0" "square_free P" "a < b"
      and "b - a \<le> delta_defl P"
  shows "Bernstein_changes p a b P \<le> 1"
  using Bernstein_changes_small_interval_le_1_of_dvd[OF assms(1-4) dvd_refl assms(5-6)] .

end
