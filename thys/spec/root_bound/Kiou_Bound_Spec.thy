theory Kiou_Bound_Spec
  imports "HOL-Computational_Algebra.Polynomial" Complex_Main
begin

text \<open>The Kioustelidis positive-root bound, AFP-free.
  Layer: FUNCTIONAL SPEC.
  Main exports: \<open>kiou_k\<close>-style bound facts — the soundness target of the GMP \<open>kiou_\<close> kernel.\<close>

text \<open>Layer: FUNCTIONAL SPEC (AFP-FREE). The tight Kioustelidis positive-root bound and
  the sign-split reflection. Deliberately imports ZERO AFP: the soundness is a
  self-contained geometric-series argument proved directly from the coefficients, NOT
  derived from Cauchy's \<open>root_bound\<close>. \<open>ripoly P x = poly (map_poly of_int P) x\<close> is the real
  evaluation of an integer polynomial — definitionally AFP's \<open>ipoly\<close>, but as a plain HOL
  abbreviation, so nothing here pulls in \<open>Algebraic_Numbers\<close>.\<close>

abbreviation (input) ripoly :: "int poly \<Rightarrow> real \<Rightarrow> real" where
  "ripoly P x \<equiv> poly (map_poly of_int P) x"

section \<open>The per-coefficient Kioustelidis exponent term\<close>

text \<open>The bit-length kernel's per-coefficient contribution: \<open>ri\<close> = bit-length of
  \<open>|a_i|\<close>, \<open>rlead\<close> = bit-length of \<open>a_n\<close>, \<open>d = n-i\<close> = distance from the leading
  coefficient. \<open>1\<close> when \<open>a_i\<close> is already dominated at \<open>k=1\<close>, else \<open>1 + \<lceil>(ri+1-rlead)/d\<rceil>\<close>.\<close>
definition kiou_term :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "kiou_term ri rlead d = (if ri + 1 \<le> rlead then 1 else 1 + (ri + 1 - rlead + d - 1) div d)"

text \<open>Any \<open>k \<ge> kiou_term ri rlead d\<close> satisfies the \<open>kdom\<close> hypothesis \<open>kiou_k_sound\<close>
  (below) needs for this one coefficient — the defining property of \<open>kiou_term\<close>, plus
  monotonicity of \<open>(k-1)*d\<close> in \<open>k\<close>.\<close>
lemma kiou_term_dom:
  assumes d1: "1 \<le> d" and kge: "kiou_term ri rlead d \<le> k"
  shows "ri + 1 \<le> rlead + (k - 1) * d"
proof (cases "ri + 1 \<le> rlead")
  case True
  thus ?thesis by simp
next
  case False
  hence gi: "0 < ri + 1 - rlead" by simp
  define gi' where "gi' = ri + 1 - rlead"
  have kt: "kiou_term ri rlead d = 1 + (gi' + d - 1) div d"
    using False by (simp add: kiou_term_def gi'_def)
  have ceil_ub: "gi' \<le> (gi' + d - 1) div d * d"
  proof -
    have "gi' + d - 1 = (gi' + d - 1) div d * d + (gi' + d - 1) mod d"
      by (rule div_mult_mod_eq[symmetric])
    moreover have "(gi' + d - 1) mod d < d" using d1 by simp
    ultimately show ?thesis by linarith
  qed
  have "gi' \<le> (kiou_term ri rlead d - 1) * d" using kt ceil_ub by simp
  also have "\<dots> \<le> (k - 1) * d" using kge d1 by (intro mult_right_mono) auto
  finally have "gi' \<le> (k - 1) * d" .
  thus ?thesis using False by (simp add: gi'_def)
qed

text \<open>Under a nonzero last coefficient the list IS the polynomial's coefficient list.\<close>
lemma coeffs_Poly_self:
  assumes "xs \<noteq> []" "last xs \<noteq> 0" shows "coeffs (Poly xs) = xs"
proof -
  have "no_trailing (HOL.eq 0) xs"
    using assms by (simp add: no_trailing_unfold)
  thus ?thesis by simp
qed

text \<open>The coefficient of @{term "Poly xs"} at index @{term i} is the list lookup (0 past
  the end). A basic HOL fact — proved inline to keep this theory AFP-free.\<close>
lemma coeff_Poly_nth_default: "coeff (Poly xs) i = nth_default 0 xs i"
  by (induct xs arbitrary: i) (auto simp: nth_default_Cons split: nat.split)

text \<open>@{term "map_poly of_int"} does not raise the degree (\<open>of_int 0 = 0\<close>). Basic HOL,
  proved inline to stay AFP-free.\<close>
lemma degree_map_poly_of_int_le: "degree (map_poly of_int p) \<le> degree p"
proof (rule degree_le, intro allI impI)
  fix i assume "degree p < i"
  hence "coeff p i = 0" by (rule coeff_eq_0)
  thus "coeff (map_poly of_int p) i = 0" by (simp add: coeff_map_poly)
qed

section \<open>Finite geometric tail\<close>

text \<open>@{term "(\<Sum>i<n. (1/2)^(n-i))"} telescopes to @{term "1 - (1/2)^n"} \<open>< 1\<close>, the
  fact that makes the dropped-negative-terms sum strictly smaller than the leading term.\<close>
lemma sum_half_pow_gap:
  "(\<Sum>i<n. (1/2::real) ^ (n - i)) = 1 - (1/2) ^ n"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  have peel: "(\<Sum>i<Suc n. (1/2::real) ^ (Suc n - i))
            = (\<Sum>i<n. (1/2::real) ^ (Suc n - i)) + (1/2) ^ (Suc n - n)"
    by (rule sum.lessThan_Suc)
  have reidx: "(\<Sum>i<n. (1/2::real) ^ (Suc n - i))
             = (1/2) * (\<Sum>i<n. (1/2::real) ^ (n - i))"
  proof -
    have "(\<Sum>i<n. (1/2::real) ^ (Suc n - i)) = (\<Sum>i<n. (1/2::real) * (1/2) ^ (n - i))"
      by (rule sum.cong) (auto simp: Suc_diff_le order_less_imp_le)
    also have "\<dots> = (1/2) * (\<Sum>i<n. (1/2::real) ^ (n - i))"
      by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed
  show ?case using peel reidx Suc.hyps by simp
qed

section \<open>Kioustelidis positive-root bound: soundness\<close>

text \<open>The load-bearing lemma. If \<open>B \<ge> 1\<close> and every opposing-sign coefficient satisfies
  the factor-2 dominance \<open>|a_i| \<le> a_n (B/2)^(n-i)\<close> (which \<open>2^k \<ge> 2 max (|a_i|/a_n)^{1/(n-i)}\<close>
  encodes), then \<open>p(x) > 0\<close> for every \<open>x \<ge> B\<close>. Proof: drop the non-negative lower terms,
  bound each negative term by \<open>-a_n x^n (1/2)^(n-i)\<close>, and sum the geometric tail \<open>< 1\<close>.\<close>
lemma kioustelidis_pos_positive:
  fixes P :: "int poly" and B x :: real
  assumes P0: "P \<noteq> 0"
    and anpos: "0 < lead_coeff P"
    and B1: "1 \<le> B"
    and xge: "B \<le> x"
    and dom: "\<And>i. i < degree P \<Longrightarrow> coeff P i < 0 \<Longrightarrow>
               of_int (- coeff P i) \<le> of_int (lead_coeff P) * (B/2) ^ (degree P - i)"
  shows "0 < ripoly P x"
proof -
  let ?rp = "map_poly of_int P :: real poly"
  let ?n  = "degree P"
  let ?an = "of_int (lead_coeff P) :: real"
  define S where "S = {i. i < ?n \<and> coeff P i < 0}"

  have xpos: "0 < x" using B1 xge by simp
  have anR: "0 < ?an" using anpos by simp
  have xnpos: "0 < x ^ ?n" using xpos by simp

  have coeffrp: "\<And>i. coeff ?rp i = of_int (coeff P i)"
    by (simp add: coeff_map_poly)
  have degrp: "degree ?rp = ?n"
    using anpos by (intro degree_map_poly) auto
  have anlead: "coeff ?rp ?n = ?an"
    by (simp add: coeffrp)

  \<comment> \<open>expand the evaluation as a coefficient sum and peel off the leading term\<close>
  have setsplit: "{..?n} = insert ?n {..<?n}" by (auto simp: le_less)
  have poly_sum: "ripoly P x = (\<Sum>i\<le>?n. coeff ?rp i * x ^ i)"
    using poly_altdef[of ?rp x] degrp by simp
  have polyeq: "ripoly P x = ?an * x ^ ?n + (\<Sum>i<?n. coeff ?rp i * x ^ i)"
    using poly_sum by (simp add: setsplit anlead)

  have Ssub: "S \<subseteq> {..<?n}" by (auto simp: S_def)

  \<comment> \<open>Step A: dropping the non-negative lower terms only decreases the sum\<close>
  have stepA: "(\<Sum>i\<in>S. coeff ?rp i * x ^ i) \<le> (\<Sum>i<?n. coeff ?rp i * x ^ i)"
  proof (rule sum_mono2[OF finite_lessThan Ssub])
    fix i assume i: "i \<in> {..<?n} - S"
    hence "i < ?n" by simp
    moreover from i have "\<not> coeff P i < 0" by (simp add: S_def)
    ultimately have "0 \<le> coeff ?rp i" by (simp add: coeffrp)
    thus "0 \<le> coeff ?rp i * x ^ i" using xpos by simp
  qed

  \<comment> \<open>a purely algebraic rearrangement used inside Step B\<close>
  have geom_id: "\<And>i. i \<le> ?n \<Longrightarrow>
      (x/2) ^ (?n - i) * x ^ i = x ^ ?n * (1/2) ^ (?n - i)"
  proof -
    fix i :: nat assume ile: "i \<le> ?n"
    have "(x/2) ^ (?n - i) * x ^ i = (x ^ (?n - i) / 2 ^ (?n - i)) * x ^ i"
      by (simp add: power_divide)
    also have "\<dots> = (x ^ (?n - i) * x ^ i) / 2 ^ (?n - i)" by simp
    also have "\<dots> = x ^ ?n / 2 ^ (?n - i)"
      using ile by (simp add: power_add[symmetric])
    also have "\<dots> = x ^ ?n * (1/2) ^ (?n - i)"
      by (simp add: power_one_over)
    finally show "(x/2) ^ (?n - i) * x ^ i = x ^ ?n * (1/2) ^ (?n - i)" .
  qed

  \<comment> \<open>Step B: each negative term is bounded below by \<open>- a_n * x^n * (1/2)^(n-i)\<close>\<close>
  have stepB: "\<And>i. i \<in> S \<Longrightarrow>
      - (?an * x ^ ?n * (1/2) ^ (?n - i)) \<le> coeff ?rp i * x ^ i"
  proof -
    fix i assume iS: "i \<in> S"
    hence iN: "i < ?n" and cneg: "coeff P i < 0" by (auto simp: S_def)
    have ile: "i \<le> ?n" using iN by simp
    have bh: "0 \<le> B/2" using B1 by simp
    have bx: "(B/2) ^ (?n - i) \<le> (x/2) ^ (?n - i)"
      using xge bh by (intro power_mono) auto
    have "of_int (- coeff P i) \<le> ?an * (B/2) ^ (?n - i)" using dom[OF iN cneg] .
    also have "\<dots> \<le> ?an * (x/2) ^ (?n - i)" using bx anR by (simp add: mult_left_mono)
    finally have ub: "of_int (- coeff P i) \<le> ?an * (x/2) ^ (?n - i)" .
    have "- (?an * x ^ ?n * (1/2) ^ (?n - i)) = - (?an * ((x/2) ^ (?n - i) * x ^ i))"
      using geom_id[OF ile] by simp
    also have "\<dots> = - (?an * (x/2) ^ (?n - i)) * x ^ i" by (simp add: mult.assoc)
    also have "\<dots> \<le> coeff ?rp i * x ^ i"
    proof (rule mult_right_mono)
      have "coeff ?rp i = - of_int (- coeff P i)" by (simp add: coeffrp)
      thus "- (?an * (x/2) ^ (?n - i)) \<le> coeff ?rp i" using ub by simp
    next
      show "0 \<le> x ^ i" using xpos by simp
    qed
    finally show "- (?an * x ^ ?n * (1/2) ^ (?n - i)) \<le> coeff ?rp i * x ^ i" .
  qed

  \<comment> \<open>sum Step B over \<open>S\<close> and bound the geometric tail by \<open>1 - (1/2)^n\<close>\<close>
  have finS: "finite S" using Ssub finite_lessThan by (rule finite_subset)
  have "- (?an * x ^ ?n * (1 - (1/2) ^ ?n))
      = - (?an * x ^ ?n * (\<Sum>i<?n. (1/2::real) ^ (?n - i)))"
    by (simp add: sum_half_pow_gap)
  also have "\<dots> \<le> - (?an * x ^ ?n * (\<Sum>i\<in>S. (1/2::real) ^ (?n - i)))"
  proof -
    have "(\<Sum>i\<in>S. (1/2::real) ^ (?n - i)) \<le> (\<Sum>i<?n. (1/2::real) ^ (?n - i))"
      by (rule sum_mono2[OF finite_lessThan Ssub]) auto
    thus ?thesis using anR xnpos by (simp add: mult_left_mono)
  qed
  also have "\<dots> = (\<Sum>i\<in>S. - (?an * x ^ ?n * (1/2::real) ^ (?n - i)))"
    by (simp add: sum_distrib_left sum_negf)
  also have "\<dots> \<le> (\<Sum>i\<in>S. coeff ?rp i * x ^ i)"
    by (rule sum_mono) (rule stepB)
  finally have sumB: "- (?an * x ^ ?n * (1 - (1/2) ^ ?n))
                      \<le> (\<Sum>i\<in>S. coeff ?rp i * x ^ i)" .

  \<comment> \<open>combine: the evaluation is at least \<open>a_n * x^n * (1/2)^n > 0\<close>\<close>
  have "?an * x ^ ?n * (1/2) ^ ?n
      = ?an * x ^ ?n + (- (?an * x ^ ?n * (1 - (1/2) ^ ?n)))"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> ?an * x ^ ?n + (\<Sum>i\<in>S. coeff ?rp i * x ^ i)"
    using sumB by simp
  also have "\<dots> \<le> ?an * x ^ ?n + (\<Sum>i<?n. coeff ?rp i * x ^ i)"
    using stepA by simp
  also have "\<dots> = ripoly P x" using polyeq by simp
  finally have lb: "?an * x ^ ?n * (1/2) ^ ?n \<le> ripoly P x" .

  have "0 < ?an * x ^ ?n * (1/2) ^ ?n"
    using anR xnpos by simp
  thus "0 < ripoly P x" using lb by linarith
qed

text \<open>Soundness as a root bound: under the same factor-2 dominance, every positive real
  root lies strictly below \<open>B\<close> (so \<open>B = 2^k\<close> is a valid dyadic upper box endpoint).\<close>
lemma kioustelidis_pos_root_bound:
  fixes P :: "int poly" and B x :: real
  assumes P0: "P \<noteq> 0"
    and anpos: "0 < lead_coeff P"
    and B1: "1 \<le> B"
    and dom: "\<And>i. i < degree P \<Longrightarrow> coeff P i < 0 \<Longrightarrow>
               of_int (- coeff P i) \<le> of_int (lead_coeff P) * (B/2) ^ (degree P - i)"
    and xpos: "0 < x"
    and root: "ripoly P x = 0"
  shows "x < B"
proof (rule ccontr)
  assume "\<not> x < B"
  hence "B \<le> x" by simp
  from kioustelidis_pos_positive[OF P0 anpos B1 this dom] root show False by simp
qed

section \<open>Bridging the bit-length formula to the dominance hypothesis\<close>

text \<open>The impl computes @{term k} from base-2 bit lengths: \<open>ri = sizeinbase(a_i,2)\<close>,
  \<open>rlead = sizeinbase(a_n,2)\<close>, and (per opposing coefficient) \<open>k \<ge> 1 + \<lceil>(ri - rlead + 1)/(n-i)\<rceil>\<close>.
  The three hypotheses below are EXACTLY what @{text sizeinbase} guarantees
  (\<open>2^(rlead-1) \<le> a_n\<close> i.e. \<open>2^rlead \<le> 2 a_n\<close>; \<open>|a_i| < 2^ri\<close>) plus the ceil bound in
  add-only form (\<open>ri + 1 \<le> rlead + (k-1)(n-i)\<close>). This is the pure integer step; it
  yields the factor-2 dominance @{thm [source] kioustelidis_pos_positive} needs.\<close>
lemma kioustelidis_bitlen_dominance:
  fixes an ai :: int and ri rlead d k :: nat
  assumes anpos: "0 < an"
    and an_lb: "2 ^ rlead \<le> 2 * an"
    and ai_ub: "\<bar>ai\<bar> < 2 ^ ri"
    and kdom: "ri + 1 \<le> rlead + (k - 1) * d"
  shows "\<bar>ai\<bar> \<le> an * 2 ^ ((k - 1) * d)"
proof -
  have step: "(2::int) ^ (ri + 1) \<le> 2 * (an * 2 ^ ((k - 1) * d))"
  proof -
    have "(2::int) ^ (ri + 1) \<le> 2 ^ (rlead + (k - 1) * d)"
      using kdom by (rule power_increasing) simp
    also have "\<dots> = 2 ^ rlead * 2 ^ ((k - 1) * d)" by (simp add: power_add)
    also have "\<dots> \<le> (2 * an) * 2 ^ ((k - 1) * d)"
      using an_lb by (intro mult_right_mono) simp_all
    finally show ?thesis by (simp add: mult.assoc)
  qed
  have e: "(2::int) ^ (ri + 1) = 2 * 2 ^ ri" by simp
  from ai_ub e step show ?thesis by linarith
qed

text \<open>The same, cast to reals in the exact shape of @{thm [source] kioustelidis_pos_positive}'s
  \<open>dom\<close> premise: \<open>(2^k / 2)^d = 2^((k-1) d)\<close> for \<open>k \<ge> 1\<close>.\<close>
lemma kioustelidis_bitlen_dom_real:
  fixes an ai :: int and ri rlead d k :: nat
  assumes anpos: "0 < an"
    and an_lb: "2 ^ rlead \<le> 2 * an"
    and ai_ub: "\<bar>ai\<bar> < 2 ^ ri"
    and kdom: "ri + 1 \<le> rlead + (k - 1) * d"
    and kge1: "1 \<le> k"
  shows "real_of_int \<bar>ai\<bar> \<le> real_of_int an * ((2::real) ^ k / 2) ^ d"
proof -
  have int_dom: "\<bar>ai\<bar> \<le> an * 2 ^ ((k - 1) * d)"
    using kioustelidis_bitlen_dominance[OF anpos an_lb ai_ub kdom] .
  have half: "(2::real) ^ k / 2 = 2 ^ (k - 1)"
    using kge1 by (simp add: power_diff)
  have rhs: "real_of_int an * ((2::real) ^ k / 2) ^ d = real_of_int (an * 2 ^ ((k - 1) * d))"
    by (simp add: half power_mult of_int_mult of_int_power)
  show ?thesis
    unfolding rhs using int_dom by (rule of_int_le_iff[THEN iffD2])
qed

section \<open>Sign split: real roots as two positive-root searches\<close>

text \<open>Architectural correctness of the pos/neg split: the real roots of \<open>P\<close> are exactly
  the positive roots of \<open>P\<close>, together with the negations of the positive roots of \<open>x \<mapsto> P(-x)\<close>,
  together with \<open>0\<close> when it is a root. The isolator searches \<open>[0, 2^kpos]\<close> for \<open>P\<close> (bounded by
  @{thm [source] kioustelidis_pos_root_bound}) and \<open>[0, 2^kneg]\<close> for the reflection, negating the
  latter's intervals. Stated with \<open>ripoly P (-y)\<close> directly; the executable reflection is the
  odd-coefficient sign flip \<open>ripoly (Poly (refl xs)) y = ripoly (Poly xs) (-y)\<close>, a mechanical
  coefficient-list bridge deferred to the impl phase.\<close>
lemma real_roots_sign_split:
  "{x::real. ripoly P x = 0}
     = {x. 0 < x \<and> ripoly P x = 0}
       \<union> uminus ` {y. 0 < y \<and> ripoly P (- y) = 0}
       \<union> {x. x = 0 \<and> ripoly P x = 0}"
  (is "?L = ?A \<union> ?B \<union> ?C")
proof (intro equalityI subsetI)
  fix x :: real assume "x \<in> ?L"
  hence r: "ripoly P x = 0" by simp
  show "x \<in> ?A \<union> ?B \<union> ?C"
  proof (cases "0 < x")
    case True thus ?thesis using r by simp
  next
    case notpos: False
    show ?thesis
    proof (cases "x = 0")
      case True thus ?thesis using r by simp
    next
      case False
      hence xneg: "x < 0" using notpos by simp
      have m: "- x \<in> {y. 0 < y \<and> ripoly P (- y) = 0}" using xneg r by simp
      have "x \<in> ?B" by (rule rev_image_eqI[OF m]) simp
      thus ?thesis by simp
    qed
  qed
next
  fix x :: real assume "x \<in> ?A \<union> ?B \<union> ?C"
  thus "x \<in> ?L" by (auto simp: image_iff)
qed

section \<open>Executable reflection: the odd-coefficient sign flip\<close>

text \<open>The concrete reflection the impl performs on a coefficient list: negate the odd-index
  (odd-degree) coefficients. This realises \<open>x \<mapsto> P(-x)\<close> and closes the bridge left open by
  @{thm [source] real_roots_sign_split}: searching the positive roots of @{term "Poly (refl_list xs)"}
  = searching the negatives of @{term "Poly xs"}.\<close>
definition refl_list :: "int list \<Rightarrow> int list" where
  "refl_list xs = map (\<lambda>i. if even i then xs ! i else - xs ! i) [0..<length xs]"

lemma length_refl_list[simp]: "length (refl_list xs) = length xs"
  by (simp add: refl_list_def)

lemma nth_refl_list: "i < length xs \<Longrightarrow> refl_list xs ! i = (if even i then xs ! i else - xs ! i)"
  by (simp add: refl_list_def)

lemma nth_default_refl_list:
  "nth_default 0 (refl_list xs) i = (- 1) ^ i * nth_default 0 xs i"
proof (cases "i < length xs")
  case True
  thus ?thesis by (simp add: nth_default_nth nth_refl_list minus_one_power_iff)
next
  case False
  thus ?thesis by (simp add: nth_default_beyond)
qed

lemma coeff_Poly_refl: "coeff (Poly (refl_list xs)) i = (- 1) ^ i * coeff (Poly xs) i"
proof (cases "i < length xs")
  case True
  have "coeff (Poly (refl_list xs)) i = (if even i then xs ! i else - xs ! i)"
    using True by (simp add: coeff_Poly_nth_default nth_default_nth nth_refl_list)
  also have "\<dots> = (- 1) ^ i * (xs ! i)" by (simp add: minus_one_power_iff)
  also have "\<dots> = (- 1) ^ i * coeff (Poly xs) i"
    using True by (simp add: coeff_Poly_nth_default nth_default_nth)
  finally show ?thesis .
next
  case False
  hence "coeff (Poly (refl_list xs)) i = 0 \<and> coeff (Poly xs) i = 0"
    by (simp add: coeff_Poly_nth_default nth_default_beyond)
  thus ?thesis by simp
qed

section \<open>Assembly: the bit-length fold gives a sound positive-root bound (\<open>rlead = 1\<close>)\<close>

text \<open>Impl-facing soundness contract for the Kioustelidis kernel. If \<open>k \<ge> 1\<close> dominates
  \<open>1 + \<lceil>ri/(n-i)\<rceil>\<close> for every opposing-sign coefficient — where \<open>ri\<close> is ANY exponent with
  \<open>|a_i| < 2^ri\<close> (e.g. \<open>sizeinbase\<close>, UPPER bound only) — then every positive real root is \<open>< 2^k\<close>.
  Crucially this uses \<open>rlead = 1\<close> (i.e. only \<open>a_n \<ge> 1\<close>), so it needs NO \<open>sizeinbase\<close> lower-bound
  axiom. It is exact for monic polynomials (Mignotte), and its minimum with the Cauchy bound, which
  is tight for dense polynomials, is tight on both families.\<close>
theorem kiou_k_sound:
  fixes xs :: "int list" and k rlead :: nat and ri :: "nat \<Rightarrow> nat" and x :: real
  assumes len2: "2 \<le> length xs"
    and lastnz: "last xs \<noteq> 0"
    and anpos: "0 < last xs"
    and k1: "1 \<le> k"
    and an_lb: "2 ^ rlead \<le> 2 * last xs"
    and ri_ub: "\<And>i. i < length xs - 1 \<Longrightarrow> \<bar>xs ! i\<bar> < 2 ^ ri i"
    and kdom: "\<And>i. i < length xs - 1 \<Longrightarrow> xs ! i < 0 \<Longrightarrow>
                 ri i + 1 \<le> rlead + (k - 1) * (length xs - 1 - i)"
    and xpos: "0 < x"
    and root: "ripoly (Poly xs) x = 0"
  shows "x < 2 ^ k"
proof -
  have xsne: "xs \<noteq> []" using len2 by auto
  have cs: "coeffs (Poly xs) = xs" using xsne lastnz by (rule coeffs_Poly_self)
  have Pnz: "Poly xs \<noteq> 0"
  proof
    assume "Poly xs = 0"
    hence "coeff (Poly xs) (length xs - 1) = 0" by simp
    moreover have "coeff (Poly xs) (length xs - 1) = last xs"
      using xsne by (simp add: coeff_Poly_eq nth_default_nth last_conv_nth)
    ultimately show False using lastnz by simp
  qed
  have deg: "degree (Poly xs) = length xs - 1"
    by (simp add: degree_eq_length_coeffs cs del: coeffs_Poly)
  have lc: "lead_coeff (Poly xs) = last xs"
    using last_coeffs_eq_coeff_degree[OF Pnz] cs by simp
  have anR: "0 < lead_coeff (Poly xs)" using lc anpos by simp
  \<comment> \<open>the per-opposing-coefficient factor-2 dominance, from @{thm [source] kioustelidis_bitlen_dom_real}\<close>
  have dom: "\<And>i. i < degree (Poly xs) \<Longrightarrow> coeff (Poly xs) i < 0 \<Longrightarrow>
        of_int (- coeff (Poly xs) i)
          \<le> of_int (lead_coeff (Poly xs)) * ((2::real) ^ k / 2) ^ (degree (Poly xs) - i)"
  proof -
    fix i assume iN: "i < degree (Poly xs)" and cneg: "coeff (Poly xs) i < 0"
    have il: "i < length xs" using iN deg by simp
    have iN': "i < length xs - 1" using iN deg by simp
    have ceq: "coeff (Poly xs) i = xs ! i"
      using il by (simp add: coeff_Poly_nth_default nth_default_nth)
    have "real_of_int \<bar>xs ! i\<bar>
            \<le> real_of_int (last xs) * ((2::real) ^ k / 2) ^ (length xs - 1 - i)"
    proof (rule kioustelidis_bitlen_dom_real[OF anpos an_lb])
      show "\<bar>xs ! i\<bar> < 2 ^ ri i" using ri_ub[OF iN'] .
    next
      show "ri i + 1 \<le> rlead + (k - 1) * (length xs - 1 - i)"
        using kdom[OF iN'] cneg ceq by simp
    next
      show "1 \<le> k" using k1 .
    qed
    thus "of_int (- coeff (Poly xs) i)
            \<le> of_int (lead_coeff (Poly xs)) * ((2::real) ^ k / 2) ^ (degree (Poly xs) - i)"
      using ceq cneg lc deg by simp
  qed
  show ?thesis
    by (rule kioustelidis_pos_root_bound[OF Pnz anR _ dom xpos root]) simp
qed

lemma ripoly_refl_list:
  "ripoly (Poly (refl_list xs)) (y::real) = ripoly (Poly xs) (- y)"
proof -
  let ?r1 = "map_poly of_int (Poly (refl_list xs)) :: real poly"
  let ?r2 = "map_poly of_int (Poly xs) :: real poly"
  let ?N = "length xs"
  have c1: "\<And>i. coeff ?r1 i = (- 1) ^ i * coeff ?r2 i"
    by (simp add: coeff_map_poly nth_default_refl_list)
  have dg1: "degree ?r1 \<le> ?N"
  proof -
    have "degree ?r1 \<le> degree (Poly (refl_list xs))" by (rule degree_map_poly_of_int_le)
    also have "\<dots> \<le> length (refl_list xs)" by (rule degree_Poly)
    also have "\<dots> = ?N" by simp
    finally show ?thesis .
  qed
  have dg2: "degree ?r2 \<le> ?N"
  proof -
    have "degree ?r2 \<le> degree (Poly xs)" by (rule degree_map_poly_of_int_le)
    also have "\<dots> \<le> length xs" by (rule degree_Poly)
    finally show ?thesis .
  qed
  have ext: "\<And>(p::real poly) z::real. degree p \<le> ?N \<Longrightarrow> poly p z = (\<Sum>i\<le>?N. coeff p i * z ^ i)"
  proof -
    fix p :: "real poly" and z :: real assume dP: "degree p \<le> ?N"
    have "poly p z = (\<Sum>i\<le>degree p. coeff p i * z ^ i)" by (rule poly_altdef)
    also have "\<dots> = (\<Sum>i\<le>?N. coeff p i * z ^ i)"
      using dP by (intro sum.mono_neutral_left) (auto simp: coeff_eq_0)
    finally show "poly p z = (\<Sum>i\<le>?N. coeff p i * z ^ i)" .
  qed
  have "ripoly (Poly (refl_list xs)) y = (\<Sum>i\<le>?N. coeff ?r1 i * y ^ i)"
    using ext[OF dg1] by simp
  also have "\<dots> = (\<Sum>i\<le>?N. coeff ?r2 i * (- y) ^ i)"
  proof (rule sum.cong[OF refl])
    fix i assume "i \<in> {..?N}"
    have "coeff ?r1 i * y ^ i = ((- 1) ^ i * coeff ?r2 i) * y ^ i" by (simp only: c1)
    also have "\<dots> = coeff ?r2 i * ((- 1) ^ i * y ^ i)" by (simp add: ac_simps)
    also have "\<dots> = coeff ?r2 i * (- y) ^ i" by (simp flip: power_mult_distrib)
    finally show "coeff ?r1 i * y ^ i = coeff ?r2 i * (- y) ^ i" .
  qed
  also have "\<dots> = ripoly (Poly xs) (- y)"
    using ext[OF dg2] by simp
  finally show ?thesis .
qed

end
