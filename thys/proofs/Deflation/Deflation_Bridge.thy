theory Deflation_Bridge
  imports Deflation_Recursion "IsaRRI_Spec.Deflation_Kernel"
    "IsaRRI_Spec.Carried_Frame"
begin

text \<open>\<^bold>\<open>Why this is a separate theory from the kernel.\<close> The kernel is pure list-level arithmetic and
  lives in \<open>IsaRRI_Spec\<close>, where the implementation layer can see it. This theory holds what needs
  @{const defl_step}, which comes from the Newton specification.\<close>

section \<open>The bridge — why \<open>1 - 2x\<close> IS \<open>defl_step\<close>\<close>

text \<open>\<^bold>\<open>Connecting the kernel to the recursion.\<close> The recursion is proved correct in terms of
  @{const defl_step}, which divides the global polynomial by \<open>[:-m, 1:]\<close> at the box midpoint. The
  kernel divides by \<open>1 - 2x\<close>. This section shows they are the same operation in the two frames, so
  the implementation may do the cheap integer one and still run the certified recursion.

  The local view of a box \<open>(a,b)\<close> is the substitution \<open>x \<mapsto> a + (b-a)x\<close>, which carries \<open>[0,1]\<close> onto
  \<open>(a,b)\<close> and the local half \<open>1/2\<close> onto the global midpoint \<open>(a+b)/2\<close>.\<close>

definition loc :: "real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> real poly" where
  "loc a b P = pcompose P [:a, b - a:]"

lemma poly_loc: "poly (loc a b P) x = poly P (a + (b - a) * x)"
  unfolding loc_def by (simp add: poly_pcompose mult.commute)

lemma loc_mult: "loc a b (P * Q) = loc a b P * loc a b Q"
  unfolding loc_def by (rule pcompose_mult)

text \<open>\<^bold>\<open>The midpoint is the local half.\<close>\<close>

lemma poly_loc_half: "poly (loc a b P) (1/2) = poly P ((a + b) / 2)"
  by (simp add: poly_loc field_simps)

text \<open>\<^bold>\<open>And the divisor transforms into \<open>1 - 2x\<close>, up to a nonzero scalar.\<close> The scalar is
  \<open>-(b-a)/2\<close>, i.e. exactly the frame's own width factor (and the sign the kernel's
  \<open>1 - 2x\<close> orientation carries) — which is why it is invisible to the
  integer kernel, whose input is already scaled by the frame.\<close>

lemma loc_linear_at_mid:
  "loc a b [:- ((a + b) / 2), 1:] = smult (- ((b - a) / 2)) [:1, -2:]"
  unfolding loc_def by (simp add: pcompose_pCons) (simp add: field_simps)

theorem defl_step_is_division_by_one_minus_two_x:
  assumes root: "poly P ((a + b) / 2) = 0"
  shows "loc a b P
           = [:1, -2:] * smult (- ((b - a) / 2)) (loc a b (defl_step P ((a + b) / 2)))"
proof -
  let ?m = "(a + b) / 2"
  have "loc a b P = loc a b ([:- ?m, 1:] * defl_step P ?m)"
    using defl_step_factor[OF root] by simp
  also have "\<dots> = loc a b [:- ?m, 1:] * loc a b (defl_step P ?m)"
    by (rule loc_mult)
  also have "\<dots> = smult (- ((b - a) / 2)) [:1, -2:] * loc a b (defl_step P ?m)"
    by (simp only: loc_linear_at_mid)
  \<comment> \<open>Move the scalar across by the two \<open>smult\<close> rules explicitly. A bare \<open>simp\<close> expands
      \<open>[:1, -2:] * X\<close> into \<open>pCons\<close>/\<open>smult\<close> form and the two sides stop matching.\<close>
  also have "\<dots> = smult (- ((b - a) / 2)) ([:1, -2:] * loc a b (defl_step P ?m))"
    by (rule mult_smult_left)
  also have "\<dots> = [:1, -2:] * smult (- ((b - a) / 2)) (loc a b (defl_step P ?m))"
    by (rule mult_smult_right[symmetric])
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>And the two root tests agree\<close>, which is what lets the implementation decide
  deflation with @{const defl_half_cert} — one integer comparison — instead of evaluating the
  global polynomial at a rational midpoint.\<close>

corollary defl_step_fires_iff_local_half_root:
  "poly P ((a + b) / 2) = 0 \<longleftrightarrow> poly (loc a b P) (1/2) = 0"
  by (simp add: poly_loc_half)

section \<open>The child-side bridge: one read decides both deflations\<close>

text \<open>\<^bold>\<open>What this section provides.\<close> The previous section identifies the kernel's \<open>1 - 2x\<close> with
  @{const defl_step}, the parent-side deflation, which needs a certificate computed before the
  children are built. That certificate is already available: \<open>truncate_children_mid_monadic\<close> builds
  both children at every subdivision node and reads \<open>carried_right Q ! 0\<close> (sign and bit length,
  borrowed, no copy) for the guarded midpoint test. This section shows that the same read decides the
  deflation, and that when it fires both children can be deflated where they stand:

    \<^item> the right child's constant coefficient is that read, so it is \<open>0\<close> exactly when the test fires,
      and the child is then divisible by \<open>x\<close> (@{thm [source] defl_drop0_exact}): drop the head. No mpz
      operation, and \<open>sign_changes\<close> does not change;
    \<^item> the read also equals the left child's \<open>1 - x\<close> certificate (@{const defl_one_cert}), so the left
      child is divisible by \<open>1 - x\<close>: one ascending pass, one addition per coefficient.

  So a node that does not shed pays nothing extra: the decision is a value the code already holds.

  \<^bold>\<open>Not stated here\<close>: that the two deflated children are, up to the scalars \<open>2\<close> and \<open>-2\<close>, exactly
  \<open>carried_left\<close>/\<open>carried_right\<close> of @{const defl_half_list}, i.e. that deflating the children equals
  deflating the parent and then building. Nothing below depends on it: the implementation's soundness
  needs only the two divisibilities, because a root at a box endpoint is outside the open box the
  Descartes count is about.\<close>

subsection \<open>Lengths, and the one identification\<close>

lemma defl_carried_left_length [simp]: "length (carried_left xs) = length xs"
  by (simp add: carried_left_def)

lemma defl_carried_right_length [simp]: "length (carried_right xs) = length xs"
  by (simp add: carried_right_def)

text \<open>\<^bold>\<open>The \<open>O(1)\<close> read is the left child's evaluation at \<open>1\<close>.\<close> \<open>carried_right\<close> is
  \<open>taylor_shift_list 1\<close> of \<open>carried_left\<close>, so by @{thm [source] Poly_taylor_shift_list} its polynomial is
  \<open>carried_left\<close>'s composed with \<open>[:1, 1:]\<close>; reading coefficient \<open>0\<close> is evaluating at \<open>0\<close>, which is
  \<open>carried_left\<close> evaluated at \<open>1\<close>. (\<open>Hybrid_Keystone.carried_right_nth0_poly\<close> states the same fact;
  it is proved again here because this theory does not import the keystone.)\<close>

lemma carried_right_nth0_eq_left_poly_1:
  assumes ne: "0 < length xs"
  shows "carried_right xs ! 0 = poly (Poly (carried_left xs)) 1"
proof -
  have ne': "carried_right xs \<noteq> []"
    using ne defl_carried_right_length[of xs] by fastforce
  have "carried_right xs ! 0 = poly.coeff (Poly (carried_right xs)) 0"
    using ne ne' by (simp add: nth_default_def)
  also have "\<dots> = poly (Poly (carried_right xs)) 0"
    by (simp add: poly_0_coeff_0)
  also have "\<dots> = poly (pcompose (Poly (carried_left xs)) [:1, 1:]) 0"
    by (simp add: carried_right_def Poly_taylor_shift_list)
  also have "\<dots> = poly (Poly (carried_left xs)) 1"
    by (simp add: poly_pcompose)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>And therefore the read IS the left child's own certificate\<close> — the fact the wiring
  rests on, since it means the runtime test needs no pass of its own.\<close>

theorem carried_right_nth0_eq_defl_one_cert:
  assumes ne: "0 < length xs"
  shows "carried_right xs ! 0 = defl_one_cert (carried_left xs)"
  using carried_right_nth0_eq_left_poly_1[OF ne] defl_one_cert_eq_poly_1 by simp

subsection \<open>Both children deflate, from that one read\<close>

theorem defl_left_child_exact:
  assumes ne: "0 < length xs"
      and mid: "carried_right xs ! 0 = 0"
  shows "Poly (carried_left xs) = [:1, -1:] * Poly (defl_one_list (carried_left xs))"
proof -
  have "defl_one_cert (carried_left xs) = 0"
    using carried_right_nth0_eq_defl_one_cert[OF ne] mid by simp
  thus ?thesis by (rule defl_one_exact)
qed

theorem defl_right_child_exact:
  assumes ne: "0 < length xs"
      and mid: "carried_right xs ! 0 = 0"
  shows "Poly (carried_right xs) = [:0, 1:] * Poly (tl (carried_right xs))"
proof -
  have "carried_right xs \<noteq> []"
    using ne defl_carried_right_length[of xs] by fastforce
  from defl_drop0_exact[OF this mid] show ?thesis .
qed

text \<open>\<^bold>\<open>The shed root is at a box ENDPOINT of each child, which is why nothing inside moves.\<close>
  The left child loses a root at \<open>1\<close> and the right child a root at \<open>0\<close> — both endpoints of the
  local \<open>(0,1)\<close> the Descartes count is taken over, so no root strictly inside either box is
  disturbed. That, and not any statement about @{const defl_half_list}, is what the restructured
  branch's soundness consumes.\<close>

corollary defl_children_roots_in_box:
  assumes ne: "0 < length xs"
      and mid: "carried_right xs ! 0 = 0"
      and x: "0 < (x::real)" and x1: "x < 1"
  shows "(poly (of_int_poly (Poly (carried_left xs)) :: real poly) x = 0)
           = (poly (of_int_poly (Poly (defl_one_list (carried_left xs))) :: real poly) x = 0)"
    and "(poly (of_int_poly (Poly (carried_right xs)) :: real poly) x = 0)
           = (poly (of_int_poly (Poly (tl (carried_right xs))) :: real poly) x = 0)"
proof -
  \<comment> \<open>Push \<open>of_int_poly\<close> through the product by \<open>rule\<close>, not by \<open>simp\<close>: a bare \<open>simp\<close> normalises
      \<open>[:1, -1:] * X\<close> into \<open>pCons\<close>/\<open>smult\<close> form and then cannot close its own goal.\<close>
  have L: "(of_int_poly (Poly (carried_left xs)) :: real poly)
             = of_int_poly [:1, -1::int:]
                 * of_int_poly (Poly (defl_one_list (carried_left xs)))"
    by (simp only: defl_left_child_exact[OF ne mid] of_int_poly_hom.hom_mult)
  have R: "(of_int_poly (Poly (carried_right xs)) :: real poly)
             = of_int_poly [:0, 1::int:] * of_int_poly (Poly (tl (carried_right xs)))"
    by (simp only: defl_right_child_exact[OF ne mid] of_int_poly_hom.hom_mult)
  have lin: "poly (of_int_poly [:1, -1::int:] :: real poly) x = 1 - x" by simp
  have xz: "poly (of_int_poly [:0, 1::int:] :: real poly) x = x" by simp
  show "(poly (of_int_poly (Poly (carried_left xs)) :: real poly) x = 0)
          = (poly (of_int_poly (Poly (defl_one_list (carried_left xs))) :: real poly) x = 0)"
    using L lin x1 by simp
  show "(poly (of_int_poly (Poly (carried_right xs)) :: real poly) x = 0)
          = (poly (of_int_poly (Poly (tl (carried_right xs))) :: real poly) x = 0)"
    using R xz x by simp
qed

section \<open>Both deflated children are even, so halving is a scaling and not a truncation\<close>

text \<open>\<^bold>\<open>Why this section exists.\<close> The children of the previous section are exactly \<open>2\<close> and \<open>-2\<close> times
  the ones the deflate-then-dilate order produces, because @{const carried_left}'s scale exponent
  depends on the length of its own input. \<open>sign_changes\<close> ignores that scalar, but coefficient
  truncation does not: \<open>carried_retrunc_mop\<close> drops a fixed number of low bits, so where a coefficient
  truncates to zero its double truncates to \<open>\<plusminus>1\<close>, and the next level's dilation multiplies that unit by
  \<open>2\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>-\<^sup>i\<^sup>)\<close>. So the factor is divided out, with \<open>poly_trunc_in_place_monadic 1\<close>. That is a scaling
  rather than a truncation only if every coefficient of both children is even, and this section
  proves it. It is a soundness obligation: halving an odd coefficient moves roots.

  \<^bold>\<open>The argument is one observation.\<close> The fire condition is \<open>carried_right xs ! 0 = 0\<close>, and that
  coefficient is the plain sum of @{const carried_left}'s entries. Every entry but the last carries a
  positive power of two, so the sum vanishing forces the last one to be even too; hence all of
  \<open>carried_left xs\<close> is even, and so is every integer-linear image of it: the left child's partial
  sums, and the right child, which is \<open>taylor_shift_list 1\<close> of it.

  The explicit dilation form \<open>xs!i * 2\<^sup>(\<^sup>n\<^sup>-\<^sup>i\<^sup>)\<close> follows in three rewrites from
  @{thm [source] scale_for_fractional_shift_eq_map} in \<open>IsaRRI_Spec.Dsc_Int\<close>.\<close>

lemma defl_carried_left_nth:
  assumes j: "j < length xs"
  shows "carried_left xs ! j = xs ! j * 2 ^ (length xs - Suc j)"
proof -
  have jn: "length xs - Suc j < length xs" using j by simp
  have "carried_left xs ! j
          = scale_for_fractional_shift 2 1 (rev xs) ! (length xs - Suc j)"
    using j by (simp add: carried_left_def rev_nth)
  also have "\<dots> = rev xs ! (length xs - Suc j) * 1 * 2 ^ (length xs - Suc j)"
    using jn by (simp add: scale_for_fractional_shift_eq_map nth_enumerate_eq)
  also have "\<dots> = xs ! j * 2 ^ (length xs - Suc j)"
    using j jn by (simp add: rev_nth Suc_diff_Suc)
  finally show ?thesis .
qed

text \<open>The read at \<open>0\<close> is the SUM of the dilated coefficients — @{thm [source]
  carried_right_nth0_eq_left_poly_1} says it is \<open>Poly (carried_left xs)\<close> evaluated at \<open>1\<close>, and
  evaluating a \<open>Poly\<close> at \<open>1\<close> is summing its list.\<close>

\<comment> \<open>The type is pinned. Left polymorphic, \<open>Poly\<close>/\<open>poly\<close> infer only \<open>comm_semiring_0\<close> plus \<open>one\<close>, a
  class with no \<open>1 * x = x\<close> law, and the induction step stalls on
  \<open>a + 1 * sum_list ys = a + sum_list ys\<close>.\<close>
lemma poly_Poly_one_eq_sum_list:
  fixes ys :: "int list"
  shows "poly (Poly ys) 1 = sum_list ys"
  by (induction ys) auto

lemma defl_carried_left_all_even:
  assumes ne: "0 < length xs"
      and mid: "carried_right xs ! 0 = 0"
  shows "\<forall>y \<in> set (carried_left xs). (2::int) dvd y"
proof -
  let ?n = "length xs"
  let ?c = "carried_left xs"
  have len: "length ?c = ?n" by simp
  \<comment> \<open>Every entry but the last carries a positive power of two.\<close>
  have but_last: "(2::int) dvd ?c ! j" if "j < ?n - 1" for j
  proof -
    have jn: "j < ?n" using that by simp
    have "0 < ?n - Suc j" using that by simp
    then obtain k where k: "?n - Suc j = Suc k" by (cases "?n - Suc j") auto
    show ?thesis
      using defl_carried_left_nth[OF jn] by (simp add: k)
  qed
  \<comment> \<open>And the sum being zero forces the last one even as well.\<close>
  have sum0: "sum_list ?c = 0"
    using carried_right_nth0_eq_left_poly_1[OF ne] mid
    by (simp add: poly_Poly_one_eq_sum_list)
  have last_even: "(2::int) dvd ?c ! (?n - 1)"
  proof -
    have "sum_list ?c = (\<Sum>j<?n. ?c ! j)"
      using len by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = (\<Sum>j<?n - 1. ?c ! j) + ?c ! (?n - 1)"
      using ne by (simp add: sum.lessThan_Suc[symmetric] Suc_pred)
    finally have "?c ! (?n - 1) = - (\<Sum>j<?n - 1. ?c ! j)"
      using sum0 by simp
    moreover have "(2::int) dvd (\<Sum>j<?n - 1. ?c ! j)"
      by (rule dvd_sum) (use but_last in simp)
    ultimately show ?thesis by simp
  qed
  show ?thesis
  proof (rule ballI)
    fix y assume "y \<in> set ?c"
    then obtain j where j: "j < ?n" and yj: "y = ?c ! j"
      using len by (metis in_set_conv_nth)
    show "(2::int) dvd y"
    proof (cases "j < ?n - 1")
      case True
      thus ?thesis using yj but_last[of j] by simp
    next
      case False
      \<comment> \<open>The only index left is the last one; \<open>auto\<close> does not derive \<open>j = ?n - 1\<close> from \<open>j < ?n\<close> and
          \<open>\<not> j < ?n - 1\<close> under truncated \<open>nat\<close> subtraction by itself.\<close>
      have "j = ?n - 1" using j False by linarith
      thus ?thesis using yj last_even by simp
    qed
  qed
qed

text \<open>\<^bold>\<open>And therefore both children are even.\<close> The left child's entries are PARTIAL SUMS of
  @{const carried_left}'s (that is what division by \<open>1 - x\<close> is), and the right child is
  \<open>taylor_shift_list 1\<close> of it — an integer-linear image. Neither can leave the even integers.\<close>

lemma defl_one_aux_all_even:
  "\<lbrakk>(2::int) dvd s; \<forall>y \<in> set ys. (2::int) dvd y\<rbrakk>
     \<Longrightarrow> \<forall>y \<in> set (defl_one_aux s ys). (2::int) dvd y"
proof (induction ys arbitrary: s)
  case Nil
  thus ?case by simp
next
  case (Cons y ys)
  have s': "(2::int) dvd (y + s)" using Cons.prems by simp
  have tl': "\<forall>z \<in> set ys. (2::int) dvd z" using Cons.prems by simp
  have "\<forall>z \<in> set (defl_one_aux (y + s) ys). (2::int) dvd z"
    by (rule Cons.IH[OF s' tl'])
  thus ?case using Cons.prems by simp
qed

lemma defl_one_list_all_even:
  assumes "\<forall>y \<in> set ys. (2::int) dvd y"
  shows "\<forall>y \<in> set (defl_one_list ys). (2::int) dvd y"
proof (cases ys)
  case Nil
  thus ?thesis by (simp add: defl_one_list_def)
next
  case (Cons a as)
  have "(2::int) dvd a" and "\<forall>y \<in> set as. (2::int) dvd y"
    using assms Cons by simp_all
  from defl_one_aux_all_even[OF this] show ?thesis
    using Cons by (simp add: defl_one_list_def)
qed

theorem defl_left_child_all_even:
  assumes ne: "0 < length xs"
      and mid: "carried_right xs ! 0 = 0"
  shows "\<forall>y \<in> set (defl_one_list (carried_left xs)). (2::int) dvd y"
  by (rule defl_one_list_all_even[OF defl_carried_left_all_even[OF ne mid]])

text \<open>For the right child the argument goes through @{const Poly} rather than through
  \<open>taylor_shift_list\<close>'s recursion: \<open>Count_Spec.taylor_shift_list_map_smult\<close> is the direct
  route, but it sits in the parent session's directory and pulling it in would mean a
  session-qualified import for one rewrite. @{thm [source] Poly_taylor_shift_list} is already
  in scope (the child-side bridge above uses it), and composition with \<open>[:1, 1:]\<close> commutes with
  \<open>smult\<close>, which is all the evenness needs.\<close>

lemma Poly_map_double: "Poly (map ((*) (2::int)) ys) = smult 2 (Poly ys)"
  by (induction ys) simp_all

lemma all_even_map_double_div:
  assumes "\<forall>y \<in> set ys. (2::int) dvd y"
  shows "map ((*) 2) (map (\<lambda>y. y div 2) ys) = ys"
proof -
  have "map ((*) 2) (map (\<lambda>y. y div 2) ys) = map (\<lambda>y. 2 * (y div 2)) ys" by simp
  also have "\<dots> = ys" using assms by (intro map_idI) simp
  finally show ?thesis .
qed

theorem defl_right_child_all_even:
  assumes ne: "0 < length xs"
      and mid: "carried_right xs ! 0 = 0"
  shows "\<forall>y \<in> set (tl (carried_right xs)). (2::int) dvd y"
proof -
  let ?zs = "map (\<lambda>y. y div 2) (carried_left xs)"
  have cl: "carried_left xs = map ((*) 2) ?zs"
    by (rule all_even_map_double_div[OF defl_carried_left_all_even[OF ne mid], symmetric])
  \<comment> \<open>Pull the \<open>smult\<close> out in one controlled step. Rewriting \<open>cl\<close> under a plain \<open>simp\<close> fuses
      \<open>map ((*) 2) (map f zs)\<close> into \<open>map ((*) 2 \<circ> f)\<close>, after which @{thm [source] Poly_map_double} no
      longer matches its goal.\<close>
  have PL: "Poly (carried_left xs) = smult 2 (Poly ?zs)"
    by (subst cl) (rule Poly_map_double)
  have "Poly (carried_right xs) = pcompose (Poly (carried_left xs)) [:1, 1:]"
    by (simp add: carried_right_def Poly_taylor_shift_list)
  also have "\<dots> = pcompose (smult 2 (Poly ?zs)) [:1, 1:]"
    by (simp only: PL)
  also have "\<dots> = smult 2 (pcompose (Poly ?zs) [:1, 1:])"
    by (rule pcompose_smult)
  finally have P: "Poly (carried_right xs) = smult 2 (pcompose (Poly ?zs) [:1, 1:])" .
  have all: "\<forall>y \<in> set (carried_right xs). (2::int) dvd y"
  proof (rule ballI)
    fix y assume "y \<in> set (carried_right xs)"
    then obtain j where j: "j < length (carried_right xs)"
                    and yj: "y = carried_right xs ! j"
      by (metis in_set_conv_nth)
    have "carried_right xs ! j = poly.coeff (Poly (carried_right xs)) j"
      using j by (simp add: nth_default_def)
    also have "\<dots> = 2 * poly.coeff (pcompose (Poly ?zs) [:1, 1:]) j"
      by (simp add: P)
    finally show "(2::int) dvd y" using yj by simp
  qed
  \<comment> \<open>\<open>tl\<close>'s elements are a subset of the list's; done by cases rather than by a
      library name, since \<open>in_set_tlD\<close> does not exist in this session.\<close>
  show ?thesis using all by (cases "carried_right xs") auto
qed

text \<open>\<^bold>\<open>The form the implementation consumes.\<close> The right child is divided by \<open>-2\<close>, not \<open>2\<close> (see
  \<open>Deflation_Op.defl_drop_body_mop\<close>), so the halving is applied to \<open>map uminus (tl (carried_right xs))\<close>.
  Evenness does not depend on the sign, but the statement has to match the operand the op holds to be
  dischargeable at the call site.\<close>

corollary defl_right_child_neg_all_even:
  assumes ne: "0 < length xs"
      and mid: "carried_right xs ! 0 = 0"
  shows "\<forall>y \<in> set (map uminus (tl (carried_right xs))). (2::int) dvd y"
  using defl_right_child_all_even[OF ne mid] by auto

text \<open>\<^bold>\<open>Why the sign matters.\<close> \<open>sign_changes\<close> is invariant under negation, so a negated child is an
  equally valid answer for the count. But \<open>carried_retrunc_mop\<close> drops low bits, i.e. it floors: a small
  positive coefficient floors to \<open>0\<close> and its negation floors to \<open>-1\<close>. A negated child would keep a \<open>\<plusminus>1\<close>
  where the unnegated one keeps a zero, and the next level's dilation multiplies every such unit by
  \<open>2\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>-\<^sup>i\<^sup>)\<close>. So a change by a unit scalar is not free whenever a later step rounds.\<close>

end
