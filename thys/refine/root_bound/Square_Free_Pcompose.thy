theory Square_Free_Pcompose
  imports "IsaRRI_Spec.Dsc_Taylor" "Polynomial_Factorization.Square_Free_Factorization"
begin

text \<open>Squarefreeness is preserved by composition with a linear polynomial. Kept in its own theory so
  that the \<open>dvd\<close>/\<open>square_free\<close> reasoning runs in a small import context. Note that \<open>back\<close> is an
  Isar keyword and cannot be used as a fact label; the label below is \<open>pullback\<close>.\<close>

text \<open>A degree-1 substitution with a nonzero linear coefficient is invertible (compose with the
  inverse substitution to get back the identity) -- the algebraic fact underlying BOTH the
  positive dilation (\<open>c = 2^kb\<close>) and the reflection (\<open>c = -1\<close>) preserving squarefreeness, since
  the composed poly's square factors pull back to square factors of the original.\<close>
lemma pcompose_linear_inverse:
  fixes P :: "real poly" and c :: real
  assumes cne: "c \<noteq> 0"
  shows "(P \<circ>\<^sub>p [:0, c:]) \<circ>\<^sub>p [:0, inverse c:] = P"
proof -
  have "poly ((P \<circ>\<^sub>p [:0, c:]) \<circ>\<^sub>p [:0, inverse c:]) x = poly P x" for x
    using cne by (simp add: poly_pcompose field_simps)
  thus ?thesis by (simp add: poly_eq_poly_eq_iff[symmetric] ext)
qed

text \<open>Squarefreeness is preserved by ANY nonzero-linear-coefficient substitution: a square factor
  \<open>q*q\<close> of the composed poly pulls back, via the inverse substitution, to a square factor of the
  SAME degree (@{thm [source] degree_pcompose_linear}) dividing \<open>P\<close> itself -- contradicting \<open>P\<close>'s
  squarefreeness. Covers both the split's dilation (\<open>c>0\<close>) and reflection (\<open>c=-1\<close>) uniformly.\<close>
lemma square_free_pcompose_linear:
  fixes P :: "real poly" and c :: real
  assumes sf: "square_free P" and cne: "c \<noteq> 0"
  shows "square_free (P \<circ>\<^sub>p [:0, c:])"
proof (rule square_freeI)
  fix q :: "real poly"
  assume dq: "degree q > 0" and qne: "q \<noteq> 0" and dvd_hyp: "q * q dvd (P \<circ>\<^sub>p [:0, c:])"
  obtain s where s_eq: "P \<circ>\<^sub>p [:0, c:] = q * q * s" using dvd_hyp by blast
  have ic_ne: "inverse c \<noteq> 0" using cne by simp
  have pullback: "P = (q \<circ>\<^sub>p [:0, inverse c:]) * (q \<circ>\<^sub>p [:0, inverse c:]) * (s \<circ>\<^sub>p [:0, inverse c:])"
  proof -
    have "P = (P \<circ>\<^sub>p [:0, c:]) \<circ>\<^sub>p [:0, inverse c:]"
      using pcompose_linear_inverse[OF cne, of P] by simp
    also have "\<dots> = (q * q * s) \<circ>\<^sub>p [:0, inverse c:]" using s_eq by simp
    also have "\<dots> = (q \<circ>\<^sub>p [:0, inverse c:]) * (q \<circ>\<^sub>p [:0, inverse c:]) * (s \<circ>\<^sub>p [:0, inverse c:])"
      by (simp add: pcompose_mult)
    finally show ?thesis .
  qed
  have deg_q': "degree (q \<circ>\<^sub>p [:0, inverse c:]) = degree q"
    using degree_pcompose_linear[of 0 "inverse c"] ic_ne by simp
  have "(q \<circ>\<^sub>p [:0, inverse c:]) * (q \<circ>\<^sub>p [:0, inverse c:]) dvd P" using pullback by (rule dvdI)
  thus False using sf dq deg_q' unfolding square_free_def by auto
next
  from sf show "P \<circ>\<^sub>p [:0, c:] \<noteq> 0"
    using cne by (simp add: square_free_def pcompose_eq_0_iff)
qed

text \<open>Standalone helper, kept in its OWN minimal-context lemma: inlined into
  @{text square_free_uminus}'s proof, the same \<open>metis\<close>/\<open>simp\<close> call faces a much larger ambient
  fact pool and becomes very slow.\<close>
lemma neg_eq_mult_neg:
  fixes P q k :: "'a::idom poly"
  assumes "- P = q * q * k"
  shows "P = q * q * (- k)"
  using assms by (metis mult_minus_right verit_minus_simplify(4))

text \<open>Squarefreeness is preserved by global negation (\<open>-1\<close> is a unit, so it has EXACTLY the same
  divisors): needed for the split pipeline's odd-degree negate-back step, whose polynomial is
  \<open>map uminus (refl_list xs) = - Poly (refl_list xs)\<close> as a poly.\<close>
lemma square_free_uminus:
  fixes P :: "real poly"
  assumes sf: "square_free P"
  shows "square_free (- P)"
proof (rule square_freeI)
  fix q assume dq: "degree q > 0" and qne: "q \<noteq> 0" and dvd_hyp: "q * q dvd (- P)"
  have "q * q dvd P"
  proof -
    from dvd_hyp obtain k where hk: "- P = q * q * k" by (elim dvdE)
    have "P = q * q * (- k)" using neg_eq_mult_neg[OF hk] .
    thus ?thesis by (rule dvdI)
  qed
  thus False using sf dq unfolding square_free_def by auto
next
  from sf show "- P \<noteq> 0" unfolding square_free_def by simp
qed

end
