theory Pre_Vacuity_Probe
  imports "IsaRRI_Refine.Kiou_Bound_Hybrid_Reflect"
begin

text \<open>\<^bold>\<open>A shape guard against vacuous capacity clauses.\<close>

  A capacity clause of the form

    \<open>\<forall>k. (\<forall>x > 0. ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ k) \<longrightarrow> k * length xs < max_snat \<dots> \<and> \<dots>\<close>

  has a premise that is monotone in \<open>k\<close> and a conclusion that is anti-monotone, with \<open>k\<close> unbounded,
  so no \<open>xs\<close> satisfies it and every theorem assuming it is vacuously true. The precondition
  @{const dsc_isolate_all_split_pre} therefore states its capacity about the producer of the bound
  (\<open>kiou_bound_k_monadic xs \<le> SPEC \<dots>\<close>) instead.

  The lemmas below are about the shape, not about a particular definition: if an unbounded \<open>\<forall>k\<close>
  capacity clause of this form appears, \<open>split_pre_k_clause_vacuous\<close> refutes it in one step.
  Satisfiability of the precondition itself is witnessed in \<open>Split_Pre_Witness\<close>.\<close>

section \<open>The shape lemma: an unbounded \<open>\<forall>k\<close> capacity clause is unsatisfiable\<close>

text \<open>Stated over the bare clause, so it applies to any vertical that reintroduces the shape, and
  so that a refutation can never be blamed on some OTHER conjunct of a bundle. The only inputs are:
  the list is non-empty, the clause holds, and the roots are bounded by SOME \<open>2 ^ k0\<close>.\<close>

lemma split_pre_k_clause_vacuous:
  fixes xs :: "int list" and k0 :: nat
  assumes len: "1 \<le> length xs"
    and kcl: "\<forall>k. (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ k)
                  \<longrightarrow> k * length xs < max_snat LENGTH(gmp_poly_len)"
    and bnd: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ k0"
  shows False
proof -
  define K where "K = max k0 (max_snat LENGTH(gmp_poly_len))"
  have k0K: "k0 \<le> K" unfolding K_def by simp
  have msK: "max_snat LENGTH(gmp_poly_len) \<le> K" unfolding K_def by simp
  \<comment> \<open>the premise survives the jump to \<open>K\<close>: \<open>2 ^ k0 \<le> 2 ^ K\<close> over the reals\<close>
  have mono: "(2::real) ^ k0 \<le> 2 ^ K" using k0K by (rule power_increasing) simp
  have premK: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ K"
    using bnd mono by (metis order_less_le_trans)
  \<comment> \<open>so the capacity conclusion must hold at \<open>K\<close> \<dots>\<close>
  have "K * length xs < max_snat LENGTH(gmp_poly_len)" using kcl premK by blast
  \<comment> \<open>\<dots> while \<open>K\<close> alone already exhausts it\<close>
  moreover have "K \<le> K * length xs" using len by simp
  ultimately show False using msK by linarith
qed

section \<open>Why the premise of that lemma is never an obstacle\<close>

text \<open>The root bound the shape lemma needs exists for every non-zero polynomial: finitely many
  roots, hence a maximum, and \<open>2 ^ k\<close> is Archimedean. So the refutation applies to \<^emph>\<open>any\<close> list
  a caller could ever supply — which is what made the old clause unsatisfiable outright rather
  than merely hard.\<close>

lemma ripoly_roots_pow2_bounded:
  fixes xs :: "int list"
  assumes P0: "(map_poly of_int (Poly xs) :: real poly) \<noteq> 0"
  shows "\<exists>k0. \<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ k0"
proof -
  define P where "P = (map_poly of_int (Poly xs) :: real poly)"
  have fin: "finite {x::real. poly P x = 0}"
    unfolding P_def using P0 unfolding P_def by (rule poly_roots_finite)
  \<comment> \<open>\<open>insert 0\<close> keeps the set non-empty so \<open>Max\<close> is meaningful with no case split\<close>
  define B where "B = Max (insert 0 {x::real. poly P x = 0})"
  have finB: "finite (insert 0 {x::real. poly P x = 0})" using fin by simp
  have leB: "\<And>x::real. poly P x = 0 \<Longrightarrow> x \<le> B"
    unfolding B_def using finB by (simp add: Max_ge)
  obtain k0 :: nat where k0: "B < 2 ^ k0"
    using real_arch_pow[of 2 B] by auto
  show ?thesis
  proof (intro exI allI impI)
    fix x :: real assume "0 < x" and "ripoly (Poly xs) x = 0"
    then have "poly P x = 0" unfolding P_def by simp
    then have "x \<le> B" by (rule leB)
    thus "x < 2 ^ k0" using k0 by linarith
  qed
qed

end
