(*  The low-degree closed forms: the real-analysis layer.

    Everything here is stated over plain reals with no polynomial, monadic or GMP vocabulary.

    The two facts the closed forms rest on:
      quad_*   — the quadratic discriminant decides 0 or 2 distinct real roots, and it decides
                 whether they straddle zero.
      cubic_*  — a real cubic with negative discriminant has exactly one real root, and the sign
                 of that root is - sign (a * d).

    The cubic proof is real-only and square-root-free. Dividing f by f' and evaluating the linear
    remainder at f's two critical points, Vieta turns the product into a polynomial in a,b,c,d:

        9*a*f x = f' x * (3*a*x + b) + P0 * x + Q0,   P0 = 6*a*c - 2*b^2, Q0 = 9*a*d - b*c
        27*a^2 * f x1 * f x2 = - disc3 a b c d       (x1, x2 the roots of f')

    so disc3 < 0 says exactly that both extrema lie strictly on the same side of zero, which is
    the geometric content of "one real root". *)

theory Lowdeg_Math
  imports IsaRRI_Spec.Dsc_Misc
begin

section \<open>Degree 2\<close>

definition disc2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "disc2 a b c = b\<^sup>2 - 4*a*c"

text \<open>The division-free root criterion.  Completing the square without ever dividing by \<open>a\<close>:
  \<open>(2*a*x + b)\<^sup>2 - disc2 a b c = 4*a*(a*x\<^sup>2 + b*x + c)\<close>.  Every later degree-2 fact is a
  consequence of this one line, which is why nothing below needs \<open>field_simps\<close>.\<close>
lemma quad_square_id:
  fixes a b c x :: real
  shows "(2*a*x + b)\<^sup>2 - disc2 a b c = 4*a*(a*x\<^sup>2 + b*x + c)"
  by (simp add: disc2_def power2_eq_square algebra_simps)

lemma quad_root_iff:
  fixes a b c x :: real
  assumes a: "a \<noteq> 0"
  shows "(a*x\<^sup>2 + b*x + c = 0) \<longleftrightarrow> (2*a*x + b)\<^sup>2 = disc2 a b c"
proof -
  have "(2*a*x + b)\<^sup>2 = disc2 a b c \<longleftrightarrow> 4*a*(a*x\<^sup>2 + b*x + c) = 0"
    using quad_square_id[where a=a and b=b and c=c and x=x] by algebra
  also have "\<dots> \<longleftrightarrow> a*x\<^sup>2 + b*x + c = 0" using a by simp
  finally show ?thesis by simp
qed

text \<open>Negative discriminant: no real root at all.\<close>
lemma quad_no_real_root:
  fixes a b c x :: real
  assumes a: "a \<noteq> 0" and D: "disc2 a b c < 0"
  shows "a*x\<^sup>2 + b*x + c \<noteq> 0"
proof
  assume "a*x\<^sup>2 + b*x + c = 0"
  hence "(2*a*x + b)\<^sup>2 = disc2 a b c" using quad_root_iff[OF a] by simp
  moreover have "(0::real) \<le> (2*a*x + b)\<^sup>2" by simp
  ultimately show False using D by simp
qed

text \<open>Positive discriminant: exactly the two points where the affine form \<open>2*a*x + b\<close> hits
  \<open>\<plusminus>sqrt(disc2)\<close>.\<close>
definition qroot :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> real" where
  "qroot a b c hi = (if hi then (- b + sqrt (disc2 a b c)) / (2*a)
                           else (- b - sqrt (disc2 a b c)) / (2*a))"

lemma qroot_affine:
  fixes a b c :: real
  assumes a: "a \<noteq> 0"
  shows "2*a*(qroot a b c hi) + b = (if hi then sqrt (disc2 a b c) else - sqrt (disc2 a b c))"
  using a by (simp add: qroot_def)

lemma qroot_is_root:
  fixes a b c :: real
  assumes a: "a \<noteq> 0" and D: "0 \<le> disc2 a b c"
  shows "a*(qroot a b c hi)\<^sup>2 + b*(qroot a b c hi) + c = 0"
proof -
  have "(2*a*(qroot a b c hi) + b)\<^sup>2 = disc2 a b c"
    using qroot_affine[OF a, where b=b and c=c and hi=hi] D by (cases hi) auto
  thus ?thesis using quad_root_iff[OF a] by simp
qed

lemma quad_root_is_qroot:
  fixes a b c x :: real
  assumes a: "a \<noteq> 0" and D: "0 \<le> disc2 a b c" and r: "a*x\<^sup>2 + b*x + c = 0"
  shows "x = qroot a b c True \<or> x = qroot a b c False"
proof -
  from r have sq: "(2*a*x + b)\<^sup>2 = disc2 a b c" using quad_root_iff[OF a] by simp
  have "sqrt (disc2 a b c) = \<bar>2*a*x + b\<bar>" using sq D by (simp add: real_sqrt_abs[symmetric])
  hence "2*a*x + b = sqrt (disc2 a b c) \<or> 2*a*x + b = - sqrt (disc2 a b c)" by auto
  thus ?thesis using a by (auto simp: qroot_def field_simps)
qed

text \<open>Vieta, and the factorisation everything else is a one-liner from.  Both need only
  \<open>0 \<le> disc2\<close>, via \<open>sqrt (disc2)\<^sup>2 = disc2\<close>.\<close>
lemma qroot_sum:
  fixes a b c :: real
  assumes a: "a \<noteq> 0"
  shows "qroot a b c True + qroot a b c False = - b / a"
  using a by (simp add: qroot_def field_simps)

lemma qroot_prod:
  fixes a b c :: real
  assumes a: "a \<noteq> 0" and D: "0 \<le> disc2 a b c"
  shows "qroot a b c True * qroot a b c False = c / a"
proof -
  have sq: "(sqrt (disc2 a b c))\<^sup>2 = disc2 a b c" using D by simp
  have "qroot a b c True * qroot a b c False
          = (b\<^sup>2 - (sqrt (disc2 a b c))\<^sup>2) / (4*a\<^sup>2)"
    using a by (simp add: qroot_def power2_eq_square field_simps)
  also have "\<dots> = (4*a*c) / (4*a\<^sup>2)" using sq by (simp add: disc2_def)
  also have "\<dots> = c / a" using a by (simp add: power2_eq_square)
  finally show ?thesis .
qed

lemma quad_factor:
  fixes a b c x :: real
  assumes a: "a \<noteq> 0" and D: "0 \<le> disc2 a b c"
  shows "a*x\<^sup>2 + b*x + c = a * (x - qroot a b c True) * (x - qroot a b c False)"
proof -
  have "a * (x - qroot a b c True) * (x - qroot a b c False)
          = a*x\<^sup>2 - a*(qroot a b c True + qroot a b c False)*x
            + a*(qroot a b c True * qroot a b c False)"
    by (simp add: power2_eq_square algebra_simps)
  also have "\<dots> = a*x\<^sup>2 - a*(- b / a)*x + a*(c / a)"
    using qroot_sum[OF a, where b=b and c=c] qroot_prod[OF a D] by simp
  also have "\<dots> = a*x\<^sup>2 + b*x + c" using a by simp
  finally show ?thesis by simp
qed

text \<open>\<^bold>\<open>The emission-relevant fact for the opposite-sign case.\<close>  When \<open>a*c < 0\<close> the two roots straddle
  zero, so the pipeline's own split at zero already separates them and NO separator has to be
  computed at all.  Stated as a product so it is label-free (which of \<open>qroot True\<close>/\<open>qroot False\<close>
  is the larger depends on the sign of \<open>a\<close>).\<close>
lemma quad_straddles_zero:
  fixes a b c :: real
  assumes a: "a \<noteq> 0" and ac: "a*c < 0"
  shows "0 < disc2 a b c" and "qroot a b c True * qroot a b c False < 0"
proof -
  have b2: "0 \<le> b\<^sup>2" by simp
  have ac4: "4*a*c < 0" using ac by simp
  show D: "0 < disc2 a b c" using b2 ac4 unfolding disc2_def by linarith
  have "c / a = (a*c) / a\<^sup>2" using a by (simp add: power2_eq_square)
  moreover have "0 < a\<^sup>2" using a by simp
  ultimately have "c / a < 0" using ac by (simp add: divide_neg_pos)
  thus "qroot a b c True * qroot a b c False < 0"
    using qroot_prod[OF a less_imp_le[OF D]] by simp
qed

text \<open>\<^bold>\<open>The same-sign class, and WHICH sign.\<close>  When \<open>a*c > 0\<close> the two roots share a sign and the
  pipeline's split at zero does not separate them; \<open>a*b < 0\<close> then says the shared sign is
  POSITIVE, because the roots sum to \<open>-b/a\<close>.  Both facts are read off @{thm [source] qroot_sum}
  and @{thm [source] qroot_prod} --- no radical, and no case analysis on which of the two
  \<open>qroot\<close> labels is the larger.

  \<^bold>\<open>Only the POSITIVE case is stated\<close>, because the implementation reflects: when both roots are
  negative the emitting arm runs on \<open>refl_list\<close>, whose roots are these negated.  A second lemma
  about negative roots would be a second thing to keep true.\<close>
lemma quad_both_pos:
  fixes a b c :: real
  assumes a: "a \<noteq> 0" and D: "0 \<le> disc2 a b c"
    and ac: "0 < a*c" and ab: "a*b < 0"
  shows "0 < qroot a b c True" and "0 < qroot a b c False"
proof -
  have a2: "0 < a\<^sup>2" using a by simp
  have prod: "0 < qroot a b c True * qroot a b c False"
  proof -
    have "qroot a b c True * qroot a b c False = c / a" by (rule qroot_prod[OF a D])
    also have "\<dots> = (a*c) / a\<^sup>2" using a by (simp add: power2_eq_square)
    finally show ?thesis using divide_pos_pos[OF ac a2] by simp
  qed
  have sum: "0 < qroot a b c True + qroot a b c False"
  proof -
    have "qroot a b c True + qroot a b c False = - b / a" by (rule qroot_sum[OF a])
    also have "\<dots> = - ((a*b) / a\<^sup>2)" using a by (simp add: power2_eq_square)
    finally show ?thesis using divide_neg_pos[OF ab a2] by simp
  qed
  \<comment> \<open>A positive product leaves the two signs EQUAL; the positive sum then picks which.
     \<open>linarith\<close> takes the disjunction and the sum together --- the products are already
     discharged, so nothing nonlinear remains.\<close>
  have disj: "(0 < qroot a b c True \<and> 0 < qroot a b c False)
            \<or> (qroot a b c True < 0 \<and> qroot a b c False < 0)"
    using prod by (simp add: zero_less_mult_iff)
  from disj sum show "0 < qroot a b c True" by linarith
  from disj sum show "0 < qroot a b c False" by linarith
qed

text \<open>The mirror, for the arm that does NOT emit.  When both roots are negative the ORIGINAL
  polynomial has no positive root at all, which is what the non-emitting half of the two-window
  classification asserts.  Same two facts, opposite sum.\<close>
lemma quad_both_neg:
  fixes a b c :: real
  assumes a: "a \<noteq> 0" and D: "0 \<le> disc2 a b c"
    and ac: "0 < a*c" and ab: "0 < a*b"
  shows "qroot a b c True < 0" and "qroot a b c False < 0"
proof -
  have a2: "0 < a\<^sup>2" using a by simp
  have prod: "0 < qroot a b c True * qroot a b c False"
  proof -
    have "qroot a b c True * qroot a b c False = c / a" by (rule qroot_prod[OF a D])
    also have "\<dots> = (a*c) / a\<^sup>2" using a by (simp add: power2_eq_square)
    finally show ?thesis using divide_pos_pos[OF ac a2] by simp
  qed
  have sum: "qroot a b c True + qroot a b c False < 0"
  proof -
    have "qroot a b c True + qroot a b c False = - b / a" by (rule qroot_sum[OF a])
    also have "\<dots> = - ((a*b) / a\<^sup>2)" using a by (simp add: power2_eq_square)
    finally show ?thesis using divide_pos_pos[OF ab a2] by simp
  qed
  have disj: "(0 < qroot a b c True \<and> 0 < qroot a b c False)
            \<or> (qroot a b c True < 0 \<and> qroot a b c False < 0)"
    using prod by (simp add: zero_less_mult_iff)
  from disj sum show "qroot a b c True < 0" by linarith
  from disj sum show "qroot a b c False < 0" by linarith
qed

text \<open>\<^bold>\<open>The separator criterion for the same-sign case\<close>, in the same division-free coordinate: a
  point lies strictly between the two roots exactly when the affine form \<open>2*a*t + b\<close> is strictly
  inside \<open>\<plusminus>sqrt(disc2)\<close>.  An implementation may therefore CHECK \<open>(2*a*t + b)\<^sup>2 < disc2\<close> — one
  integer square and one compare, over exact integers when \<open>t\<close> is dyadic — instead of carrying a
  proof about how it chose \<open>t\<close>.  Stated as a product, for the same reason as above.\<close>
lemma quad_separator:
  fixes a b c t :: real
  assumes a: "a \<noteq> 0" and sep: "(2*a*t + b)\<^sup>2 < disc2 a b c"
  shows "0 < disc2 a b c"
    and "(t - qroot a b c True) * (t - qroot a b c False) < 0"
proof -
  show D: "0 < disc2 a b c" using sep by (smt (verit) zero_le_power2)
  have "4*a*(a*t\<^sup>2 + b*t + c) < 0" using sep quad_square_id[where a=a and b=b and c=c and x=t] by simp
  hence af: "a*(a*t\<^sup>2 + b*t + c) < 0" by simp
  have "a*(a*t\<^sup>2 + b*t + c)
          = a\<^sup>2 * ((t - qroot a b c True) * (t - qroot a b c False))"
    using quad_factor[OF a less_imp_le[OF D], where x=t] by (simp add: power2_eq_square)
  moreover have "0 < a\<^sup>2" using a by simp
  ultimately show "(t - qroot a b c True) * (t - qroot a b c False) < 0"
    using af by (simp add: zero_less_mult_iff mult_less_0_iff)
qed

section \<open>Degree 3\<close>

definition disc3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "disc3 a b c d = 18*a*b*c*d - 4*b^3*d + b\<^sup>2*c\<^sup>2 - 4*a*c^3 - 27*a\<^sup>2*d\<^sup>2"

abbreviation cub :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "cub a b c d x \<equiv> a*x^3 + b*x\<^sup>2 + c*x + d"

abbreviation cub' :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "cub' a b c x \<equiv> 3*a*x\<^sup>2 + 2*b*x + c"

lemma cub_DERIV: "DERIV (cub a b c d) x :> cub' a b c x"
  by (auto intro!: derivative_eq_intros simp: algebra_simps power2_eq_square power3_eq_cube)

lemma cub_isCont: "isCont (cub a b c d) x"
  using cub_DERIV DERIV_isCont by blast

lemma disc3_neg_all: "disc3 (-a) (-b) (-c) (-d) = disc3 a b c d"
  by (simp add: disc3_def)

lemma cub_neg_all: "cub (-a) (-b) (-c) (-d) x = - cub a b c d x"
  by (simp add: algebra_simps)

subsection \<open>Behaviour off the ends, without limits\<close>

text \<open>An explicit witness rather than a filter argument: for \<open>a > 0\<close> and \<open>x\<close> past
  \<open>1 + (|b|+|c|+|d|)/a\<close>, \<open>x\<^sup>2*(a*x - (|b|+|c|+|d|))\<close> is a lower bound for \<open>cub\<close>, and an upper
  bound for its reflection.  This supplies both the IVT root and the sign of the root below.\<close>
definition cub_far :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "cub_far a b c d = 1 + (\<bar>b\<bar> + \<bar>c\<bar> + \<bar>d\<bar>) / a"

lemma cub_far_ge_1: "0 < a \<Longrightarrow> 1 \<le> cub_far a b c d"
  by (simp add: cub_far_def)

lemma cub_pos_far:
  fixes a b c d x :: real
  assumes a: "0 < a" and x: "cub_far a b c d \<le> x"
  shows "0 < cub a b c d x"
proof -
  have x1: "1 \<le> x" using x cub_far_ge_1[OF a, where b=b and c=c and d=d] by linarith
  have x0: "0 \<le> x" using x1 by simp
  have xle: "x \<le> x\<^sup>2" using x1 x0 by (simp add: power2_eq_square mult_right_mono)
  have x1sq: "1 \<le> x\<^sup>2" using x1 xle by linarith
  have "(\<bar>b\<bar> + \<bar>c\<bar> + \<bar>d\<bar>) / a < x" using x unfolding cub_far_def by linarith
  hence key: "\<bar>b\<bar> + \<bar>c\<bar> + \<bar>d\<bar> < a*x" using a by (simp add: pos_divide_less_eq mult.commute)
  have t1: "0 \<le> (b + \<bar>b\<bar>)*x\<^sup>2"
  proof -
    have "0 \<le> b + \<bar>b\<bar>" by simp
    thus ?thesis by simp
  qed
  have t2: "0 \<le> \<bar>c\<bar>*x\<^sup>2 + c*x"
  proof -
    have "\<bar>c*x\<bar> = \<bar>c\<bar>*x" using x0 by (simp add: abs_mult)
    also have "\<dots> \<le> \<bar>c\<bar>*x\<^sup>2" using xle by (simp add: mult_left_mono)
    finally show ?thesis by simp
  qed
  have t3: "0 \<le> \<bar>d\<bar>*x\<^sup>2 + d"
  proof -
    have "\<bar>d\<bar> * 1 \<le> \<bar>d\<bar> * x\<^sup>2" by (rule mult_left_mono[OF x1sq]) simp
    thus ?thesis by simp
  qed
  have t4: "0 < x\<^sup>2*(a*x - (\<bar>b\<bar> + \<bar>c\<bar> + \<bar>d\<bar>))"
  proof -
    have "0 < x\<^sup>2" using x1sq by linarith
    moreover have "0 < a*x - (\<bar>b\<bar> + \<bar>c\<bar> + \<bar>d\<bar>)" using key by linarith
    ultimately show ?thesis by (rule mult_pos_pos)
  qed
  have "cub a b c d x - x\<^sup>2*(a*x - (\<bar>b\<bar> + \<bar>c\<bar> + \<bar>d\<bar>))
          = (b + \<bar>b\<bar>)*x\<^sup>2 + (\<bar>c\<bar>*x\<^sup>2 + c*x) + (\<bar>d\<bar>*x\<^sup>2 + d)"
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
  thus ?thesis using t1 t2 t3 t4 by linarith
qed

lemma cub_neg_far:
  fixes a b c d x :: real
  assumes a: "0 < a" and x: "cub_far a b c d \<le> x"
  shows "cub a b c d (- x) < 0"
proof -
  have "cub a b c d (- x) = - cub a (-b) c (-d) x"
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
  moreover have "0 < cub a (-b) c (-d) x"
    using cub_pos_far[OF a, where b="-b" and c=c and d="-d" and x=x] x by (simp add: cub_far_def)
  ultimately show ?thesis by simp
qed

lemma cub_has_root:
  fixes a b c d :: real
  assumes a: "0 < a"
  shows "\<exists>x. cub a b c d x = 0"
proof -
  let ?X = "cub_far a b c d"
  have "cub a b c d (- ?X) \<le> 0" using cub_neg_far[OF a, where b=b and c=c and d=d and x="cub_far a b c d"] by simp
  moreover have "0 \<le> cub a b c d ?X" using cub_pos_far[OF a, where b=b and c=c and d=d and x="cub_far a b c d"] by simp
  moreover have "- ?X \<le> ?X" using cub_far_ge_1[OF a, where b=b and c=c and d=d] by simp
  ultimately show ?thesis
    using IVT[of "cub a b c d" "- ?X" 0 ?X] cub_isCont by auto
qed


subsection \<open>The critical points, and the discriminant as the product of the two extrema\<close>

text \<open>Dividing \<open>f\<close> by \<open>f'\<close> leaves a LINEAR remainder, so at either critical point \<open>f\<close> is an
  affine function of that point — and Vieta then turns the product of the two extrema into a
  polynomial in \<open>a,b,c,d\<close> with no radicals.  Both identities are pure ring identities.\<close>

definition cubP0 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where "cubP0 a b c = 6*a*c - 2*b\<^sup>2"
definition cubQ0 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where "cubQ0 a b c d = 9*a*d - b*c"

lemma cub_div_id:
  fixes a b c d x :: real
  shows "9*a*(cub a b c d x) = (cub' a b c x)*(3*a*x + b) + cubP0 a b c * x + cubQ0 a b c d"
  unfolding cubP0_def cubQ0_def by algebra

lemma disc3_PQ_id:
  fixes a b c d :: real
  shows "c*(cubP0 a b c)\<^sup>2 - 2*b*(cubP0 a b c)*(cubQ0 a b c d) + 3*a*(cubQ0 a b c d)\<^sup>2
           = - 9*a*(disc3 a b c d)"
  unfolding cubP0_def cubQ0_def disc3_def by algebra

lemma cub_crit_val:
  fixes a b c d y :: real
  assumes r: "cub' a b c y = 0"
  shows "9*a*(cub a b c d y) = cubP0 a b c * y + cubQ0 a b c d"
  using cub_div_id[where a=a and b=b and c=c and d=d and x=y] r by simp

text \<open>\<open>f'\<close> is the quadratic \<open>3*a*y\<^sup>2 + 2*b*y + c\<close>, so the whole degree-2 section applies to it
  verbatim.  Its critical points are \<open>qroot (3*a) (2*b) c\<close>.\<close>
abbreviation cdisc :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "cdisc a b c \<equiv> disc2 (3*a) (2*b) c"

lemma cub'_is_quad: "cub' a b c y = (3*a)*y\<^sup>2 + (2*b)*y + c" by simp

lemma cub_crit_is_root:
  fixes a b c :: real
  assumes a: "a \<noteq> 0" and D: "0 \<le> cdisc a b c"
  shows "cub' a b c (qroot (3*a) (2*b) c hi) = 0"
  using qroot_is_root[of "3*a" "2*b" c hi] a D by simp

lemma cub_extrema_prod:
  fixes a b c d :: real
  assumes a: "a \<noteq> 0" and D: "0 \<le> cdisc a b c"
  shows "27*a\<^sup>2*((cub a b c d (qroot (3*a) (2*b) c False))
                 * (cub a b c d (qroot (3*a) (2*b) c True))) = - disc3 a b c d"
proof -
  define x1 where "x1 = qroot (3*a) (2*b) c False"
  define x2 where "x2 = qroot (3*a) (2*b) c True"
  have a3: "3*a \<noteq> 0" using a by simp
  have e1: "9*a*(cub a b c d x1) = cubP0 a b c * x1 + cubQ0 a b c d"
    using cub_crit_val[OF cub_crit_is_root[OF a D, of False]] unfolding x1_def by simp
  have e2: "9*a*(cub a b c d x2) = cubP0 a b c * x2 + cubQ0 a b c d"
    using cub_crit_val[OF cub_crit_is_root[OF a D, of True]] unfolding x2_def by simp
  have S3: "3*a*(x1 + x2) = - (2*b)"
    using qroot_sum[OF a3, where b="2*b" and c=c] a3
    unfolding x1_def x2_def by (simp add: field_simps)
  have P3: "3*a*(x1 * x2) = c"
    using qroot_prod[OF a3 D] a3 unfolding x1_def x2_def by (simp add: field_simps)
  have expand: "(9*a*(cub a b c d x1))*(9*a*(cub a b c d x2))
        = (cubP0 a b c)\<^sup>2*(x1*x2) + (cubP0 a b c)*(cubQ0 a b c d)*(x1+x2) + (cubQ0 a b c d)\<^sup>2"
  proof -
    have "(9*a*(cub a b c d x1))*(9*a*(cub a b c d x2))
            = (cubP0 a b c * x1 + cubQ0 a b c d) * (cubP0 a b c * x2 + cubQ0 a b c d)"
      using e1 e2 by simp
    also have "\<dots> = (cubP0 a b c)\<^sup>2*(x1*x2) + (cubP0 a b c)*(cubQ0 a b c d)*(x1+x2)
                     + (cubQ0 a b c d)\<^sup>2"
      by (simp add: power2_eq_square algebra_simps)
    finally show ?thesis .
  qed
  have "3*a*((9*a*(cub a b c d x1))*(9*a*(cub a b c d x2)))
          = (cubP0 a b c)\<^sup>2*(3*a*(x1*x2)) + (cubP0 a b c)*(cubQ0 a b c d)*(3*a*(x1+x2))
            + 3*a*(cubQ0 a b c d)\<^sup>2"
    using expand by (simp add: algebra_simps)
  also have "\<dots> = c*(cubP0 a b c)\<^sup>2 - 2*b*(cubP0 a b c)*(cubQ0 a b c d) + 3*a*(cubQ0 a b c d)\<^sup>2"
    using S3 P3 by (simp add: algebra_simps)
  also have "\<dots> = - 9*a*(disc3 a b c d)" by (rule disc3_PQ_id)
  finally have K: "3*a*((9*a*(cub a b c d x1))*(9*a*(cub a b c d x2))) = - 9*a*(disc3 a b c d)" .
  have ne: "(9::real)*a \<noteq> 0" using a by simp
  have eq9: "(9*a) * (27*a\<^sup>2*((cub a b c d x1)*(cub a b c d x2))) = (9*a) * (- disc3 a b c d)"
    using K by (simp add: power2_eq_square power3_eq_cube algebra_simps)
  have "27*a\<^sup>2*((cub a b c d x1)*(cub a b c d x2)) = - disc3 a b c d"
    using mult_left_cancel[OF ne] eq9 by blast
  thus ?thesis unfolding x1_def x2_def by simp
qed

subsection \<open>Monotonicity between the critical points\<close>

text \<open>The derivative is positive only on the OPEN intervals — it vanishes AT the critical points
  — so these use the open-interval monotonicity rules.  Continuity comes from @{thm cub_isCont}.\<close>

lemma cub_cont_on: "continuous_on {u..v} (cub a b c d)"
  by (simp add: continuous_at_imp_continuous_on cub_isCont)

lemma cub_incr_open:
  fixes u v :: real
  assumes uv: "u < v" and pos: "\<And>y. \<lbrakk>u < y; y < v\<rbrakk> \<Longrightarrow> 0 < cub' a b c y"
  shows "cub a b c d u < cub a b c d v"
  by (rule DERIV_pos_imp_increasing_open[OF uv _ cub_cont_on]) (use pos cub_DERIV in blast)

lemma cub_decr_open:
  fixes u v :: real
  assumes uv: "u < v" and neg: "\<And>y. \<lbrakk>u < y; y < v\<rbrakk> \<Longrightarrow> cub' a b c y < 0"
  shows "cub a b c d v < cub a b c d u"
  by (rule DERIV_neg_imp_decreasing_open[OF uv _ cub_cont_on]) (use neg cub_DERIV in blast)

text \<open>The factorisation of \<open>f'\<close> is what puts a sign on each of the three regions.\<close>
lemma cub'_factor:
  fixes a b c y :: real
  assumes a: "a \<noteq> 0" and D: "0 \<le> cdisc a b c"
  shows "cub' a b c y
           = 3*a*(y - qroot (3*a) (2*b) c True)*(y - qroot (3*a) (2*b) c False)"
  using quad_factor[of "3*a" "2*b" c y] a D by simp

lemma cub_crit_lt:
  fixes a b c :: real
  assumes a: "0 < a" and D: "0 < cdisc a b c"
  shows "qroot (3*a) (2*b) c False < qroot (3*a) (2*b) c True"
proof -
  have "0 < sqrt (cdisc a b c)" using D by simp
  thus ?thesis using a by (simp add: qroot_def divide_strict_right_mono)
qed


subsection \<open>Exactly one real root\<close>

lemma cub'_sign_lo:
  fixes a b c y :: real
  assumes a: "0 < a" and D: "0 < cdisc a b c" and y: "y < qroot (3*a) (2*b) c False"
  shows "0 < cub' a b c y"
proof -
  have anz: "a \<noteq> 0" using a by simp
  have n1: "y - qroot (3*a) (2*b) c True < 0" using y cub_crit_lt[OF a D] by simp
  have n2: "y - qroot (3*a) (2*b) c False < 0" using y by simp
  have "0 < 3*a*((y - qroot (3*a) (2*b) c True)*(y - qroot (3*a) (2*b) c False))"
    using mult_neg_neg[OF n1 n2] a by simp
  moreover have "cub' a b c y
      = 3*a*(y - qroot (3*a) (2*b) c True)*(y - qroot (3*a) (2*b) c False)"
    by (rule cub'_factor[OF anz less_imp_le[OF D]])
  ultimately show ?thesis by (simp add: mult.assoc)
qed

lemma cub'_sign_hi:
  fixes a b c y :: real
  assumes a: "0 < a" and D: "0 < cdisc a b c" and y: "qroot (3*a) (2*b) c True < y"
  shows "0 < cub' a b c y"
proof -
  have anz: "a \<noteq> 0" using a by simp
  have p1: "0 < y - qroot (3*a) (2*b) c True" using y by simp
  have p2: "0 < y - qroot (3*a) (2*b) c False" using y cub_crit_lt[OF a D] by simp
  have "0 < 3*a*((y - qroot (3*a) (2*b) c True)*(y - qroot (3*a) (2*b) c False))"
    using mult_pos_pos[OF p1 p2] a by simp
  moreover have "cub' a b c y
      = 3*a*(y - qroot (3*a) (2*b) c True)*(y - qroot (3*a) (2*b) c False)"
    by (rule cub'_factor[OF anz less_imp_le[OF D]])
  ultimately show ?thesis by (simp add: mult.assoc)
qed

lemma cub'_sign_mid:
  fixes a b c y :: real
  assumes a: "0 < a" and D: "0 < cdisc a b c"
      and y1: "qroot (3*a) (2*b) c False < y" and y2: "y < qroot (3*a) (2*b) c True"
  shows "cub' a b c y < 0"
proof -
  have anz: "a \<noteq> 0" using a by simp
  have n1: "y - qroot (3*a) (2*b) c True < 0" using y2 by simp
  have p2: "0 < y - qroot (3*a) (2*b) c False" using y1 by simp
  have "3*a*((y - qroot (3*a) (2*b) c True)*(y - qroot (3*a) (2*b) c False)) < 0"
    using mult_neg_pos[OF n1 p2] a by (simp add: mult_pos_neg)
  moreover have "cub' a b c y
      = 3*a*(y - qroot (3*a) (2*b) c True)*(y - qroot (3*a) (2*b) c False)"
    by (rule cub'_factor[OF anz less_imp_le[OF D]])
  ultimately show ?thesis by (simp add: mult.assoc)
qed

text \<open>\<^bold>\<open>The load-bearing step.\<close>  Two distinct real roots force the two extrema onto OPPOSITE
  sides of zero, i.e. \<open>f x1 * f x2 \<le> 0\<close>; but @{thm cub_extrema_prod} says that product is
  \<open>- disc3 / (27*a\<^sup>2)\<close>, which \<open>disc3 < 0\<close> makes strictly positive.\<close>
lemma cubic_neg_disc_no_two:
  fixes a b c d u v :: real
  assumes a: "0 < a" and D: "disc3 a b c d < 0"
      and uv: "u < v" and ru: "cub a b c d u = 0" and rv: "cub a b c d v = 0"
  shows False
proof -
  have anz: "a \<noteq> 0" using a by simp
  \<comment> \<open>Step 1: the derivative must itself have two distinct real roots.  Otherwise \<open>f\<close> is
     nondecreasing, so equal endpoint values make it FLAT on \<open>{u..v}\<close> — and a nonzero cubic
     cannot vanish on an interval.\<close>
  have D': "0 < cdisc a b c"
  proof (rule ccontr)
    assume "\<not> 0 < cdisc a b c"
    hence Dle: "cdisc a b c \<le> 0" by simp
    have nonneg: "0 \<le> cub' a b c y" for y
    proof -
      have id: "(2*(3*a)*y + 2*b)\<^sup>2 - cdisc a b c = 4*(3*a)*((3*a)*y\<^sup>2 + (2*b)*y + c)"
        by (rule quad_square_id)
      have sq: "0 \<le> (2*(3*a)*y + 2*b)\<^sup>2" by simp
      have "0 \<le> (2*(3*a)*y + 2*b)\<^sup>2 - cdisc a b c" using sq Dle by linarith
      hence "0 \<le> 12*a*(cub' a b c y)" using id by simp
      thus ?thesis using a by (auto simp: zero_le_mult_iff)
    qed
    have mono: "cub a b c d p \<le> cub a b c d q" if pq: "p \<le> q" for p q
      by (rule DERIV_nonneg_imp_nondecreasing[OF pq]) (use nonneg cub_DERIV in blast)
    have flat: "cub a b c d y = 0" if y1: "u \<le> y" and y2: "y \<le> v" for y
      using mono[OF y1] mono[OF y2] ru rv by simp
    have "{u..v} \<subseteq> {y. poly [:d,c,b,a:] y = 0}"
      using flat by (auto simp: algebra_simps power2_eq_square power3_eq_cube)
    moreover have "finite {y. poly [:d,c,b,a:] y = 0}"
      using anz by (intro poly_roots_finite) auto
    ultimately have "finite {u..v}" by (rule finite_subset)
    thus False using uv infinite_Icc by blast
  qed
  \<comment> \<open>Step 2: the two extrema, and the three regions they cut the line into.\<close>
  define x1 where "x1 = qroot (3*a) (2*b) c False"
  define x2 where "x2 = qroot (3*a) (2*b) c True"
  have x12: "x1 < x2" using cub_crit_lt[OF a D'] unfolding x1_def x2_def .
  have prod_pos: "0 < (cub a b c d x1)*(cub a b c d x2)"
  proof -
    have E: "27*a\<^sup>2*((cub a b c d x1)*(cub a b c d x2)) = - disc3 a b c d"
      using cub_extrema_prod[OF anz less_imp_le[OF D']] unfolding x1_def x2_def .
    have "0 < 27*a\<^sup>2*((cub a b c d x1)*(cub a b c d x2))" using E D by simp
    moreover have "0 < 27*a\<^sup>2" using anz by simp
    ultimately show ?thesis by (rule zero_less_mult_pos)
  qed
  have incr_lo: "cub a b c d p < cub a b c d q" if "p < q" and "q \<le> x1" for p q
    using that cub'_sign_lo[OF a D'] unfolding x1_def
    by (intro cub_incr_open) auto
  have decr_mid: "cub a b c d q < cub a b c d p" if "x1 \<le> p" and "p < q" and "q \<le> x2" for p q
    using that cub'_sign_mid[OF a D'] unfolding x1_def x2_def
    by (intro cub_decr_open) auto
  have incr_hi: "cub a b c d p < cub a b c d q" if "x2 \<le> p" and "p < q" for p q
    using that cub'_sign_hi[OF a D'] unfolding x2_def
    by (intro cub_incr_open) auto
  \<comment> \<open>Step 3: wherever the two roots sit, \<open>f x1 \<ge> 0 \<ge> f x2\<close>.\<close>
  have "0 \<le> cub a b c d x1 \<and> cub a b c d x2 \<le> 0"
  proof (cases "u \<le> x1")
    case True
    have A: "0 \<le> cub a b c d x1"
      using ru incr_lo[of u x1] True by (cases "u = x1") auto
    have v1: "x1 < v"
    proof (rule ccontr)
      assume "\<not> x1 < v"
      hence "cub a b c d u < cub a b c d v" using incr_lo[OF uv] by simp
      thus False using ru rv by simp
    qed
    have B: "cub a b c d x2 \<le> 0"
    proof (cases "v \<le> x2")
      case True
      thus ?thesis using rv decr_mid[of v x2] v1 by (cases "v = x2") auto
    next
      case False
      hence "cub a b c d x2 < cub a b c d v" using incr_hi[of x2 v] by simp
      thus ?thesis using rv by simp
    qed
    show ?thesis using A B by simp
  next
    case False
    hence ux: "x1 < u" by simp
    have v2: "x2 < v"
    proof (rule ccontr)
      assume "\<not> x2 < v"
      hence "cub a b c d v < cub a b c d u" using decr_mid[of u v] ux uv by simp
      thus False using ru rv by simp
    qed
    have ux2: "u \<le> x2"
    proof (rule ccontr)
      assume "\<not> u \<le> x2"
      hence "cub a b c d u < cub a b c d v" using incr_hi[of u v] uv by simp
      thus False using ru rv by simp
    qed
    have A: "0 \<le> cub a b c d x1" using ru decr_mid[of x1 u] ux ux2 by simp
    have B: "cub a b c d x2 \<le> 0"
      using ru decr_mid[of u x2] ux ux2 by (cases "u = x2") auto
    show ?thesis using A B by simp
  qed
  hence "(cub a b c d x1)*(cub a b c d x2) \<le> 0" by (simp add: mult_nonneg_nonpos)
  thus False using prod_pos by simp
qed

lemma cubic_neg_disc_unique_pos:
  fixes a b c d :: real
  assumes a: "0 < a" and D: "disc3 a b c d < 0"
  shows "\<exists>!x. cub a b c d x = 0"
proof -
  obtain r where r: "cub a b c d r = 0" using cub_has_root[OF a] by blast
  have "u = r" if ru: "cub a b c d u = 0" for u
  proof (rule ccontr)
    assume ne: "u \<noteq> r"
    show False
    proof (cases "u < r")
      case True from cubic_neg_disc_no_two[OF a D True ru r] show False .
    next
      case False
      hence "r < u" using ne by simp
      from cubic_neg_disc_no_two[OF a D this r ru] show False .
    qed
  qed
  with r show ?thesis by blast
qed

theorem cubic_neg_disc_unique:
  fixes a b c d :: real
  assumes a: "a \<noteq> 0" and D: "disc3 a b c d < 0"
  shows "\<exists>!x. cub a b c d x = 0"
proof (cases "0 < a")
  case True from cubic_neg_disc_unique_pos[OF True D] show ?thesis .
next
  case False
  hence a': "0 < - a" using a by simp
  have D': "disc3 (-a) (-b) (-c) (-d) < 0" using D by (simp add: disc3_neg_all)
  from cubic_neg_disc_unique_pos[OF a' D'] obtain z
    where z: "cub (-a) (-b) (-c) (-d) z = 0"
      and uq: "\<And>y. cub (-a) (-b) (-c) (-d) y = 0 \<Longrightarrow> y = z" by blast
  have "cub a b c d z = 0" using z by (simp add: cub_neg_all)
  moreover have "\<And>y. cub a b c d y = 0 \<Longrightarrow> y = z" using uq by (simp add: cub_neg_all)
  ultimately show ?thesis by blast
qed


subsection \<open>Which side of zero the root is on\<close>

text \<open>The emission has to put the window in the POSITIVE arm or the reflected NEGATIVE arm, and
  it decides that from one sign product.  With exactly one real root, \<open>f\<close> changes sign only
  there, so \<open>f 0 = d\<close> settles it: \<open>sign r = - sign (a*d)\<close>.\<close>

lemma cub_at_zero: "cub a b c d 0 = d" by simp

lemma cubic_root_pos_of_neg_d:
  fixes a b c d r :: real
  assumes a: "0 < a" and D: "disc3 a b c d < 0" and r: "cub a b c d r = 0" and d0: "d < 0"
  shows "0 < r"
proof -
  have uniq: "\<And>y. cub a b c d y = 0 \<Longrightarrow> y = r"
    using cubic_neg_disc_unique_pos[OF a D] r by blast
  have lo: "cub a b c d 0 \<le> 0" using d0 by simp
  have hi: "0 \<le> cub a b c d (cub_far a b c d)"
    using cub_pos_far[OF a, where b=b and c=c and d=d and x="cub_far a b c d"] by simp
  have le: "(0::real) \<le> cub_far a b c d"
    using cub_far_ge_1[OF a, where b=b and c=c and d=d] by simp
  obtain z where z: "0 \<le> z" "z \<le> cub_far a b c d" "cub a b c d z = 0"
    using IVT[of "cub a b c d" 0 0 "cub_far a b c d"] lo hi le cub_isCont by auto
  have "z \<noteq> 0"
  proof
    assume "z = 0"
    hence "d = 0" using z(3) by simp
    thus False using d0 by simp
  qed
  hence "0 < z" using z(1) by simp
  thus ?thesis using uniq[OF z(3)] by simp
qed

lemma cubic_root_neg_of_pos_d:
  fixes a b c d r :: real
  assumes a: "0 < a" and D: "disc3 a b c d < 0" and r: "cub a b c d r = 0" and d0: "0 < d"
  shows "r < 0"
proof -
  have uniq: "\<And>y. cub a b c d y = 0 \<Longrightarrow> y = r"
    using cubic_neg_disc_unique_pos[OF a D] r by blast
  have lo: "cub a b c d (- cub_far a b c d) \<le> 0"
    using cub_neg_far[OF a, where b=b and c=c and d=d and x="cub_far a b c d"] by simp
  have hi: "0 \<le> cub a b c d 0" using d0 by simp
  have le: "- cub_far a b c d \<le> (0::real)"
    using cub_far_ge_1[OF a, where b=b and c=c and d=d] by simp
  obtain z where z: "- cub_far a b c d \<le> z" "z \<le> 0" "cub a b c d z = 0"
    using IVT[of "cub a b c d" "- cub_far a b c d" 0 0] lo hi le cub_isCont by auto
  have "z \<noteq> 0"
  proof
    assume "z = 0"
    hence "d = 0" using z(3) by simp
    thus False using d0 by simp
  qed
  hence "z < 0" using z(2) by simp
  thus ?thesis using uniq[OF z(3)] by simp
qed

lemma cubic_root_sign_pos:
  fixes a b c d r :: real
  assumes a: "a \<noteq> 0" and D: "disc3 a b c d < 0" and r: "cub a b c d r = 0" and ad: "a*d < 0"
  shows "0 < r"
proof (cases "0 < a")
  case True
  hence "d < 0" using ad by (simp add: mult_less_0_iff)
  from cubic_root_pos_of_neg_d[OF True D r this] show ?thesis .
next
  case False
  hence a': "0 < - a" using a by simp
  have D': "disc3 (-a) (-b) (-c) (-d) < 0" using D by (simp add: disc3_neg_all)
  have r': "cub (-a) (-b) (-c) (-d) r = 0" using r by (simp add: cub_neg_all)
  have "0 < d" using ad False a by (simp add: mult_less_0_iff)
  hence "- d < 0" by simp
  from cubic_root_pos_of_neg_d[OF a' D' r' this] show ?thesis .
qed

lemma cubic_root_sign_neg:
  fixes a b c d r :: real
  assumes a: "a \<noteq> 0" and D: "disc3 a b c d < 0" and r: "cub a b c d r = 0" and ad: "0 < a*d"
  shows "r < 0"
proof (cases "0 < a")
  case True
  hence "0 < d" using ad by (simp add: zero_less_mult_iff)
  from cubic_root_neg_of_pos_d[OF True D r this] show ?thesis .
next
  case False
  hence a': "0 < - a" using a by simp
  have D': "disc3 (-a) (-b) (-c) (-d) < 0" using D by (simp add: disc3_neg_all)
  have r': "cub (-a) (-b) (-c) (-d) r = 0" using r by (simp add: cub_neg_all)
  have "d < 0" using ad False a by (simp add: zero_less_mult_iff)
  hence "0 < - d" by simp
  from cubic_root_neg_of_pos_d[OF a' D' r' this] show ?thesis .
qed

lemma cubic_root_zero_of_zero_d:
  fixes a b c d r :: real
  assumes a: "a \<noteq> 0" and D: "disc3 a b c d < 0" and r: "cub a b c d r = 0" and d0: "d = 0"
  shows "r = 0"
proof -
  have "cub a b c d 0 = 0" using d0 by simp
  thus ?thesis using cubic_neg_disc_unique[OF a D] r by blast
qed

end
