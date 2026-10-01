theory Deflation_Kernel
  imports "IsaRRI_Spec.Dsc_Taylor"
begin

section \<open>The deflation kernel\<close>

text \<open>The abstract recursion sheds a linear factor at a box midpoint (\<open>defl_step\<close>,
  \<open>Deflation_Recursion\<close>). This theory is the coefficient-list kernel the implementation refines.

  \<^bold>\<open>Why the divisor is linear in the local frame rather than \<open>x - m\<close>.\<close> At the abstract level \<open>m\<close> is
  an arbitrary real, so \<open>P div [:-m, 1:]\<close> leaves \<open>real poly\<close>. The carried frame does not work with
  the global polynomial: each node holds \<open>P\<close> transformed onto the local box \<open>[0,1]\<close> as an integer
  coefficient list, and the box midpoint is local \<open>1/2\<close>. Dividing by the local linear factor is
  therefore the same operation in the representation the solver runs on, and it stays in
  \<open>int list\<close>: the factor is primitive, so by Gauss's lemma it divides in \<open>\<int>[x]\<close> whenever it divides
  in \<open>\<rat>[x]\<close>. There are no denominators and no coefficient growth. Deflating the global integer
  polynomial by \<open>x - m\<close> at a dyadic \<open>m = a/2\<^sup>k\<close> would instead force a \<open>2\<^sup>k\<close> rescale per shed root.
  msolve also deflates in the local frame (\<open>is_zero_root\<close>, \<open>manage_root_at_one_half\<close> in its
  \<open>usolve.c\<close>).

  \<^bold>\<open>Why the divisor is \<open>1 - 2x\<close> and not \<open>2x - 1\<close>.\<close> The two differ only by the sign of the quotient,
  and \<open>sign_changes\<close>, hence every Descartes count downstream, is invariant under negation, so the
  choice is free at this layer. It is not free in the implementation. With \<open>2x - 1\<close> the recurrence is
  \<open>r\<^sub>i = 2r\<^sub>i\<^sub>-\<^sub>1 - q\<^sub>i\<close>, which needs an mpz subtraction every iteration, and the shared GMP layer has
  none (\<open>mpz_add_monadic\<close> and \<open>mpz_addmul_monadic\<close> are the primitives; \<open>mpz_sub_ui_snat_monadic\<close>
  subtracts a small \<open>nat\<close>). With \<open>1 - 2x\<close> the recurrence is
  \<open>s\<^sub>i = q\<^sub>i + 2s\<^sub>i\<^sub>-\<^sub>1 = (q\<^sub>i + s\<^sub>i\<^sub>-\<^sub>1) + s\<^sub>i\<^sub>-\<^sub>1\<close>: two additions. The sign is fixed here, in the kernel,
  because negating the coefficients afterwards would cost an mpz operation per coefficient.

  The kernel is synthetic division: one left-to-right pass, \<open>O(n)\<close> integer operations. Writing
  \<open>Q = \<Sum> q\<^sub>i x\<^sup>i\<close> and \<open>S = \<Sum> s\<^sub>i x\<^sup>i\<close> with \<open>Q = (1 - 2x) S\<close>:
  \<open>q\<^sub>0 = s\<^sub>0\<close>, \<open>q\<^sub>i = s\<^sub>i - 2s\<^sub>i\<^sub>-\<^sub>1\<close>, \<open>q\<^sub>n = -2s\<^sub>n\<^sub>-\<^sub>1\<close>, so \<open>s\<^sub>0 = q\<^sub>0\<close> and
  \<open>s\<^sub>i = q\<^sub>i + 2s\<^sub>i\<^sub>-\<^sub>1\<close>, and the final \<open>q\<^sub>n\<close> equation is a certificate rather than an output: it is
  exactly the remainder.\<close>

subsection \<open>The pass, and its remainder\<close>

fun defl_half_aux :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "defl_half_aux s [] = []"
| "defl_half_aux s (q # qs) = s # defl_half_aux (q + 2 * s) qs"

fun defl_half_rem :: "int \<Rightarrow> int list \<Rightarrow> int" where
  "defl_half_rem s [] = s"
| "defl_half_rem s (q # qs) = defl_half_rem (q + 2 * s) qs"

definition defl_half_list :: "int list \<Rightarrow> int list" where
  "defl_half_list qs = (case qs of [] \<Rightarrow> [] | q # qs' \<Rightarrow> defl_half_aux q qs')"

definition defl_half_cert :: "int list \<Rightarrow> int" where
  "defl_half_cert qs = (case qs of [] \<Rightarrow> 0 | q # qs' \<Rightarrow> defl_half_rem q qs')"

lemma length_defl_half_aux: "length (defl_half_aux s qs) = length qs"
  by (induction qs arbitrary: s) simp_all

lemma length_defl_half_list: "length (defl_half_list qs) = length qs - 1"
  unfolding defl_half_list_def by (cases qs) (simp_all add: length_defl_half_aux)

subsection \<open>The exact identity — no root hypothesis anywhere\<close>

text \<open>The pass is total, and this says exactly what it computes: the quotient by \<open>1 - 2x\<close>
  \<^bold>\<open>plus the remainder, as a single monomial\<close>. Stating it unconditionally is what makes the
  root case a corollary rather than a separate proof, and it is also what turns
  @{const defl_half_cert} into a runtime-checkable certificate.\<close>

lemma defl_half_aux_identity:
  "[:1, -2:] * Poly (defl_half_aux s qs)
     = pCons s (Poly qs) + monom (- defl_half_rem s qs) (length qs)"
proof (induction qs arbitrary: s)
  case Nil
  show ?case by (simp add: monom_0)
next
  case (Cons q qs)
  have "[:1, -2:] * Poly (defl_half_aux s (q # qs))
          = [:1, -2:] * pCons s (Poly (defl_half_aux (q + 2 * s) qs))"
    by simp
  also have "\<dots> = [:1, -2:] * [:s:] + [:1, -2:] * (pCons 0 (Poly (defl_half_aux (q + 2 * s) qs)))"
    by (simp add: pCons_one distrib_left)
  also have "\<dots> = [:s, -2*s:] + pCons 0 ([:1, -2:] * Poly (defl_half_aux (q + 2 * s) qs))"
    by (simp add: mult_pCons_right)
  also have "\<dots> = [:s, -2*s:]
                  + pCons 0 (pCons (q + 2 * s) (Poly qs)
                             + monom (- defl_half_rem (q + 2 * s) qs) (length qs))"
    using Cons.IH by simp
  also have "\<dots> = pCons s (pCons q (Poly qs))
                  + monom (- defl_half_rem (q + 2 * s) qs) (Suc (length qs))"
    by (simp add: monom_Suc)
  finally show ?case by simp
qed

theorem defl_half_list_identity:
  "[:1, -2:] * Poly (defl_half_list qs)
     = Poly qs + monom (- defl_half_cert qs) (length qs - 1)"
proof (cases qs)
  case Nil
  then show ?thesis by (simp add: defl_half_list_def defl_half_cert_def monom_0)
next
  case (Cons q qs')
  have "[:1, -2:] * Poly (defl_half_aux q qs')
          = pCons q (Poly qs') + monom (- defl_half_rem q qs') (length qs')"
    using defl_half_aux_identity[of q qs'] by simp
  then show ?thesis
    using Cons by (simp add: defl_half_list_def defl_half_cert_def)
qed

subsection \<open>The certificate, and what a zero certificate buys\<close>

text \<open>\<^bold>\<open>Exactness is decided by one integer test\<close>: no polynomial evaluation and no
  \<open>rsquarefree\<close> side condition. It is a runtime-checkable certificate rather than a proof-side
  hypothesis.\<close>

theorem defl_half_exact:
  assumes "defl_half_cert qs = 0"
  shows "Poly qs = [:1, -2:] * Poly (defl_half_list qs)"
  using defl_half_list_identity[of qs] assms by simp

corollary defl_half_dvd:
  assumes "defl_half_cert qs = 0"
  shows "[:1, -2:] dvd Poly qs"
  using defl_half_exact[OF assms] by (metis dvd_triv_left)

subsection \<open>The certificate DECIDES the root — so the runtime test never refuses a real one\<close>

text \<open>One rational identity gives both directions. It is written additively, with the hom steps
  applied by \<open>rule\<close>: a bare \<open>simp\<close> normalises \<open>[:1, -2:] * X\<close> into \<open>pCons\<close>/\<open>smult\<close> form and then
  cannot close its own goal.\<close>

lemma defl_half_rat_identity:
  "poly (of_int_poly (Poly qs) :: rat poly) (1/2)
     = of_int (defl_half_cert qs) * (1/2) ^ (length qs - 1)"
proof -
  have A: "(of_int_poly ([:1, -2::int:] * Poly (defl_half_list qs)) :: rat poly)
             = of_int_poly [:1, -2::int:] * of_int_poly (Poly (defl_half_list qs))"
    by (rule of_int_poly_hom.hom_mult)
  have B: "(of_int_poly (Poly qs + monom (- defl_half_cert qs) (length qs - 1)) :: rat poly)
             = of_int_poly (Poly qs) + monom (of_int (- defl_half_cert qs)) (length qs - 1)"
    by (simp add: of_int_hom.map_poly_hom_add of_int_hom.map_poly_hom_monom)
  have C: "(of_int_poly ([:1, -2::int:] * Poly (defl_half_list qs)) :: rat poly)
             = of_int_poly (Poly qs + monom (- defl_half_cert qs) (length qs - 1))"
    by (simp only: defl_half_list_identity)
  have key: "(of_int_poly [:1, -2::int:] :: rat poly) * of_int_poly (Poly (defl_half_list qs))
               = of_int_poly (Poly qs) + monom (of_int (- defl_half_cert qs)) (length qs - 1)"
    using A B C by simp
  have half: "poly (of_int_poly [:1, -2::int:] :: rat poly) (1/2) = 0" by simp
  have zero: "poly ((of_int_poly [:1, -2::int:] :: rat poly)
                      * of_int_poly (Poly (defl_half_list qs))) (1/2) = 0"
    using half by simp
  \<comment> \<open>Rewrite with \<open>key\<close> by \<open>simp only\<close>. A full \<open>simp\<close> would normalise the product back into
      \<open>pCons\<close>/\<open>smult\<close> form and the goal would stop matching.\<close>
  have "poly ((of_int_poly [:1, -2::int:] :: rat poly)
                * of_int_poly (Poly (defl_half_list qs))) (1/2)
          = poly ((of_int_poly (Poly qs) :: rat poly)
                    + monom (of_int (- defl_half_cert qs)) (length qs - 1)) (1/2)"
    by (simp only: key)
  also have "\<dots> = poly (of_int_poly (Poly qs) :: rat poly) (1/2)
                   - of_int (defl_half_cert qs) * (1/2) ^ (length qs - 1)"
    by (simp add: poly_monom)
  finally have "poly (of_int_poly (Poly qs) :: rat poly) (1/2)
                  - of_int (defl_half_cert qs) * (1/2) ^ (length qs - 1) = 0"
    using zero by simp
  thus ?thesis by simp
qed

theorem defl_half_cert_eq_zero_iff:
  "defl_half_cert qs = 0 \<longleftrightarrow> poly (of_int_poly (Poly qs) :: rat poly) (1/2) = 0"
  using defl_half_rat_identity[of qs] by simp

section \<open>The child-side divisors\<close>

text \<open>\<^bold>\<open>The certificate is already computed.\<close> @{const defl_half_cert} equals
  \<open>carried_right Q ! 0\<close>, the constant coefficient of the right child, which the child build at every
  subdivision node (\<open>truncate_children_mid_monadic\<close>) produces and whose sign it already reads. So a
  separate \<open>O(n)\<close> certificate pass is not needed.

  \<^bold>\<open>Why the pass can be dropped rather than reordered.\<close> The code cannot learn that the midpoint is a
  root before it has paid the \<open>O(n\<^sup>2)\<close> child build at the undeflated degree, but that does not force a
  third shift, because the shed root lands on a box endpoint of each child:

    \<^item> the right child has constant coefficient \<open>0\<close>, so it is divisible by \<open>x\<close>, and deflating it is
      dropping that coefficient (\<open>defl_drop0_exact\<close>): pointer moves and no mpz arithmetic, and
      \<open>sign_changes\<close> is unchanged because a leading zero contributes nothing;
    \<^item> the left child vanishes at \<open>1\<close>, so it is divisible by \<open>1 - x\<close>: one ascending pass with one
      addition per coefficient (\<open>defl_one_list\<close>), against @{const defl_half_list}'s two.

  Both are then exactly the children the deflated parent would have produced, up to the scalars
  \<open>2\<close> and \<open>-2\<close>, which every Descartes count ignores; \<open>Deflation_Bridge\<close> states this. On a node that
  does not shed, the deflation check costs nothing extra.

  \<^bold>\<open>The divisor is \<open>1 - x\<close> and not \<open>x - 1\<close>\<close>, for the same reason as above: with \<open>x - 1\<close> the ascending
  recurrence is \<open>m\<^sub>i = m\<^sub>i\<^sub>-\<^sub>1 - l\<^sub>i\<close>, an mpz subtraction the shared GMP layer does not have; with \<open>1 - x\<close>
  it is \<open>m\<^sub>i = l\<^sub>i + m\<^sub>i\<^sub>-\<^sub>1\<close>, one \<open>mpz_add\<close>.\<close>

subsection \<open>Division by \<open>1 - x\<close> — the LEFT child's divisor\<close>

fun defl_one_aux :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "defl_one_aux s [] = []"
| "defl_one_aux s (q # qs) = s # defl_one_aux (q + s) qs"

fun defl_one_rem :: "int \<Rightarrow> int list \<Rightarrow> int" where
  "defl_one_rem s [] = s"
| "defl_one_rem s (q # qs) = defl_one_rem (q + s) qs"

definition defl_one_list :: "int list \<Rightarrow> int list" where
  "defl_one_list qs = (case qs of [] \<Rightarrow> [] | q # qs' \<Rightarrow> defl_one_aux q qs')"

definition defl_one_cert :: "int list \<Rightarrow> int" where
  "defl_one_cert qs = (case qs of [] \<Rightarrow> 0 | q # qs' \<Rightarrow> defl_one_rem q qs')"

lemma length_defl_one_aux: "length (defl_one_aux s qs) = length qs"
  by (induction qs arbitrary: s) simp_all

lemma length_defl_one_list: "length (defl_one_list qs) = length qs - 1"
  unfolding defl_one_list_def by (cases qs) (simp_all add: length_defl_one_aux)

text \<open>The same unconditional identity as for the pass at \<open>1/2\<close> above — quotient plus
  remainder-as-a-monomial, with no root hypothesis — so exactness is again a corollary rather
  than a separate proof.\<close>

lemma defl_one_aux_identity:
  "[:1, -1:] * Poly (defl_one_aux s qs)
     = pCons s (Poly qs) + monom (- defl_one_rem s qs) (length qs)"
proof (induction qs arbitrary: s)
  case Nil
  show ?case by (simp add: monom_0)
next
  case (Cons q qs)
  have "[:1, -1:] * Poly (defl_one_aux s (q # qs))
          = [:1, -1:] * pCons s (Poly (defl_one_aux (q + s) qs))"
    by simp
  also have "\<dots> = [:1, -1:] * [:s:] + [:1, -1:] * (pCons 0 (Poly (defl_one_aux (q + s) qs)))"
    by (simp add: pCons_one distrib_left)
  also have "\<dots> = [:s, -s:] + pCons 0 ([:1, -1:] * Poly (defl_one_aux (q + s) qs))"
    by (simp add: mult_pCons_right)
  also have "\<dots> = [:s, -s:]
                  + pCons 0 (pCons (q + s) (Poly qs)
                             + monom (- defl_one_rem (q + s) qs) (length qs))"
    using Cons.IH by simp
  also have "\<dots> = pCons s (pCons q (Poly qs))
                  + monom (- defl_one_rem (q + s) qs) (Suc (length qs))"
    by (simp add: monom_Suc)
  finally show ?case by simp
qed

theorem defl_one_list_identity:
  "[:1, -1:] * Poly (defl_one_list qs)
     = Poly qs + monom (- defl_one_cert qs) (length qs - 1)"
proof (cases qs)
  case Nil
  then show ?thesis by (simp add: defl_one_list_def defl_one_cert_def monom_0)
next
  case (Cons q qs')
  have "[:1, -1:] * Poly (defl_one_aux q qs')
          = pCons q (Poly qs') + monom (- defl_one_rem q qs') (length qs')"
    using defl_one_aux_identity[of q qs'] by simp
  then show ?thesis
    using Cons by (simp add: defl_one_list_def defl_one_cert_def)
qed

theorem defl_one_exact:
  assumes "defl_one_cert qs = 0"
  shows "Poly qs = [:1, -1:] * Poly (defl_one_list qs)"
  using defl_one_list_identity[of qs] assms by simp

corollary defl_one_dvd:
  assumes "defl_one_cert qs = 0"
  shows "[:1, -1:] dvd Poly qs"
  using defl_one_exact[OF assms] by (metis dvd_triv_left)

text \<open>\<^bold>\<open>And here the certificate is an ORDINARY evaluation, over \<open>int\<close>.\<close> The pass at \<open>1/2\<close>
  needed the \<open>rat\<close> image because \<open>1/2\<close> is not an integer; at \<open>1\<close> the monomial term is
  \<open>- cert * 1\<^sup>k = - cert\<close>, so the whole decision statement is one \<open>poly\<close> equation with no
  coercion anywhere. That matters at the call site: the runtime test is the sign of a value the
  solver already holds, and this is the fact that says the two agree.\<close>

theorem defl_one_cert_eq_poly_1: "defl_one_cert qs = poly (Poly qs) 1"
proof -
  have "poly ([:1, -1:] * Poly (defl_one_list qs)) 1
          = poly (Poly qs + monom (- defl_one_cert qs) (length qs - 1)) 1"
    by (simp only: defl_one_list_identity)
  moreover have "poly ([:1, -1:] * Poly (defl_one_list qs)) 1 = 0" by simp
  ultimately have "poly (Poly qs) 1 - defl_one_cert qs = 0"
    by (simp add: poly_monom)
  thus ?thesis by simp
qed

corollary defl_one_exact_of_poly_1:
  assumes "poly (Poly qs) 1 = 0"
  shows "Poly qs = [:1, -1:] * Poly (defl_one_list qs)"
  using defl_one_exact assms by (simp add: defl_one_cert_eq_poly_1)

subsection \<open>Division by \<open>x\<close> — the RIGHT child's divisor, which is not arithmetic at all\<close>

text \<open>The right child's shed root sits at its box's LEFT endpoint, so the divisor is \<open>x\<close> and the
  quotient is the coefficient list with its head removed. No mpz operation is performed, and
  nothing grows — which is why the restructured branch's non-firing cost is zero rather than
  small. \<^bold>\<open>\<open>sign_changes\<close> does not move either\<close>: the dropped coefficient is \<open>0\<close>, and a zero
  contributes no sign change, so the child's Descartes count is literally unchanged.\<close>

lemma defl_drop0_exact:
  \<comment> \<open>\<open>int\<close>, not a class-polymorphic list: \<open>[:0, 1:]\<close> alone infers only
      \<open>{comm_semiring_0, one}\<close>, which has no \<open>1 * x = x\<close> law, so the coefficient goal
      cannot close. Every other constant in this file is \<open>int list\<close> anyway.\<close>
  assumes ne: "(xs::int list) \<noteq> []" and hd0: "xs ! 0 = 0"
  shows "Poly xs = [:0, 1:] * Poly (tl xs)"
proof -
  \<comment> \<open>Name the tail rather than rewriting with \<open>xs = 0 # tl xs\<close>: that equation has \<open>xs\<close>
      on both sides, so \<open>simp\<close> rewrites it inside its own right-hand side and never
      normalises. A fresh \<open>ys\<close> makes it an ordinary rewrite.\<close>
  obtain ys where xs_eq: "xs = 0 # ys" using ne hd0 by (cases xs) auto
  \<comment> \<open>\<open>simp\<close> reduces \<open>[:0,1:] * q\<close> to \<open>pCons 0 (smult 1 q)\<close> and then stalls on
      \<open>smult 1 q = q\<close> — adding \<open>smult_1_left\<close> did not move it. Discharge that step
      coefficientwise instead, which needs only \<open>poly_eqI\<close> and the simp-default
      \<open>coeff_smult\<close>.\<close>
  have s1: "smult 1 (Poly ys) = Poly ys"
    by (rule poly_eqI) simp
  have "[:0, 1:] * Poly ys = pCons 0 (Poly ys)"
    by (simp add: mult_pCons_left s1)
  then show ?thesis by (simp add: xs_eq)
qed

corollary defl_drop0_dvd:
  assumes "(xs::int list) \<noteq> []" and "xs ! 0 = 0"
  shows "[:0, 1:] dvd Poly xs"
  using defl_drop0_exact[OF assms] by (metis dvd_triv_left)

end
