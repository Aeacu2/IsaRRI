theory Kiou_Bound_Reflect
  imports Kiou_Bound_Refine Square_Free_Pcompose "IsaRRI_LLVM.Split_Bisection"
    "IsaRRI_LLVM.Carried_Kernel" "IsaRRI_LLVM.Bisection_Solver"
    "IsaRRI_Refine.Bisection_Loop_Refine"
begin

text \<open>The executable reflection \<open>P \<mapsto> P(-x)\<close>. @{const refl_list} (\<open>Kiou_Bound_Spec.thy\<close>)
  is the odd-coefficient sign flip \<open>map (\<lambda>i. xs!i * (-1)^i) [0..<length xs]\<close> -- EXACTLY
  @{const scale_poly_list} with the constant \<open>-1\<close>. So the reflection kernel is not new
  Sepref work: it is @{const poly_scale_in_place_monadic} called with \<open>c := -1\<close>, whose
  correctness (@{thm [source] poly_scale_in_place_correct}) and \<open>[llvm_code]\<close> Sepref
  synthesis (\<open>poly_scale_in_place_impl\<close>, \<open>Dyadic_Interval.thy\<close>) are already certified.

  Layer: NRES REFINEMENT.\<close>

lemma refl_list_eq_scale_poly_list_neg1: "refl_list xs = scale_poly_list (-1) xs"
proof (rule nth_equalityI)
  show "length (refl_list xs) = length (scale_poly_list (-1) xs)"
    by (simp add: scale_poly_list_eq_map_upt)
next
  fix i assume "i < length (refl_list xs)"
  hence i: "i < length xs" by simp
  have "scale_poly_list (-1) xs ! i = xs ! i * (-1) ^ i"
    using i by (simp add: scale_poly_list_eq_map_upt)
  also have "\<dots> = (if even i then xs ! i else - xs ! i)"
    by (simp add: minus_one_power_iff)
  also have "\<dots> = refl_list xs ! i" using i by (simp add: nth_refl_list)
  finally show "refl_list xs ! i = scale_poly_list (-1) xs ! i" by simp
qed

text \<open>@{const poly_scale_in_place_monadic} at \<open>c=-1\<close> computes @{const refl_list} exactly --
  composes @{thm [source] poly_scale_in_place_correct} with the bridge above.\<close>
lemma poly_reflect_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_scale_in_place_monadic (-1) xs \<le> RETURN (refl_list xs)"
  using poly_scale_in_place_correct[OF assms, of "-1"]
  by (simp add: refl_list_eq_scale_poly_list_neg1)

text \<open>Root-real-root correctness of the reflection: the roots of \<open>Poly (refl_list xs)\<close> are
  exactly the negations of \<open>Poly xs\<close>'s roots evaluated at \<open>-y\<close> (bridges
  @{thm [source] ripoly_refl_list} to the executable coefficient list).\<close>
lemma ripoly_poly_reflect_monadic:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_scale_in_place_monadic (-1) xs \<le>
    SPEC (\<lambda>ys. \<forall>y::real. ripoly (Poly ys) y = ripoly (Poly xs) (- y))"
  using poly_reflect_monadic_correct[OF assms]
  by (auto simp: pw_le_iff refine_pw_simps ripoly_refl_list)

subsection \<open>Whole-poly uniform negation (for leading-sign normalization)\<close>


text \<open>\<open>Poly_map_uminus\<close>/\<open>ripoly_map_uminus\<close> (negation preserves the real roots) are proved in
  \<open>Kiou_Bound_Refine\<close> and visible here through that import.\<close>

section \<open>\<open>roots_in\<close>/\<open>dsc_pair_ok\<close> are negation-invariant under reflection\<close>

text \<open>The reflected real polynomial is exactly \<open>P_real\<close> composed with \<open>[:0,-1:]\<close> (the degree-1
  polynomial \<open>x \<mapsto> -x\<close>): both sides agree pointwise via @{thm [source] ripoly_refl_list} +
  @{thm [source] poly_pcompose}, and a real polynomial is determined by its values (infinite
  carrier), so @{thm [source] poly_eqI} lifts the pointwise identity to a POLYNOMIAL identity.\<close>
lemma Poly_refl_list_eq_pcompose:
  "(map_poly of_int (Poly (refl_list xs)) :: real poly)
     = (map_poly of_int (Poly xs) :: real poly) \<circ>\<^sub>p [:0, -1:]"
proof -
  have "poly (map_poly of_int (Poly (refl_list xs)) :: real poly)
      = poly ((map_poly of_int (Poly xs) :: real poly) \<circ>\<^sub>p [:0, -1:])"
  proof
    fix y :: real
    show "poly (map_poly of_int (Poly (refl_list xs)) :: real poly) y
        = poly ((map_poly of_int (Poly xs) :: real poly) \<circ>\<^sub>p [:0, -1:]) y"
      by (simp add: ripoly_refl_list poly_pcompose)
  qed
  thus ?thesis by (simp add: poly_eq_poly_eq_iff)
qed

text \<open>\<open>roots_in\<close> under the reflection is the negated-and-swapped interval on the original
  polynomial: composing with a degree-1 map is a bijection on the reals, so
  @{thm [source] proots_pcompose} converts root counts across it exactly.\<close>
lemma roots_in_refl_list:
  fixes xs :: "int list" and a b :: real
  assumes P0: "Poly xs \<noteq> 0"
  shows "roots_in (map_poly of_int (Poly (refl_list xs)) :: real poly) a b
       = roots_in (map_poly of_int (Poly xs) :: real poly) (- b) (- a)"
proof -
  let ?P = "map_poly of_int (Poly xs) :: real poly"
  have P0': "?P \<noteq> 0" using P0 by simp
  have "roots_in (map_poly of_int (Poly (refl_list xs)) :: real poly) a b
      = proots_count (?P \<circ>\<^sub>p [:0, -1:]) {x. a < x \<and> x < b}"
    unfolding roots_in_def by (simp add: Poly_refl_list_eq_pcompose)
  also have "\<dots> = proots_count ?P (poly [:0, -1::real:] ` {x. a < x \<and> x < b})"
    by (rule proots_pcompose[OF P0']) simp
  also have "poly [:0, -1::real:] ` {x. a < x \<and> x < b} = {y. - b < y \<and> y < - a}"
  proof (intro equalityI subsetI)
    fix y assume "y \<in> poly [:0, -1::real:] ` {x. a < x \<and> x < b}"
    then show "y \<in> {y. - b < y \<and> y < - a}" by auto
  next
    fix y assume y: "y \<in> {y. - b < y \<and> y < - a}"
    hence "- y \<in> {x. a < x \<and> x < b}" by auto
    hence "poly [:0, -1::real:] (- y) \<in> poly [:0, -1::real:] ` {x. a < x \<and> x < b}" by (rule imageI)
    thus "y \<in> poly [:0, -1::real:] ` {x. a < x \<and> x < b}" by simp
  qed
  also have "proots_count ?P {y. - b < y \<and> y < - a} = roots_in ?P (- b) (- a)"
    unfolding roots_in_def by simp
  finally show ?thesis .
qed

text \<open>\<open>dsc_pair_ok\<close> (a real interval isolates exactly one root, or is a degenerate exact root)
  is negation-invariant the same way: an interval \<open>(a,b)\<close> is OK for the reflection iff its
  negated-and-swapped image \<open>(-b,-a)\<close> is OK for the original polynomial.\<close>
lemma dsc_pair_ok_refl_list:
  fixes xs :: "int list" and I :: "real \<times> real"
  assumes P0: "Poly xs \<noteq> 0"
  shows "dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) I
       = dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) (- snd I, - fst I)"
proof -
  let ?P = "map_poly of_int (Poly xs) :: real poly"
  have ripoly_at: "\<And>y. poly (map_poly of_int (Poly (refl_list xs)) :: real poly) y = poly ?P (- y)"
    using ripoly_refl_list by simp
  show ?thesis
    unfolding dsc_pair_ok_def
    using ripoly_at roots_in_refl_list[OF P0, of "fst I" "snd I"]
    by auto
qed

section \<open>\<open>roots_in\<close>/\<open>dsc_pair_ok\<close> are dilation-covariant\<close>

text \<open>The SAME technique as @{thm [source] Poly_refl_list_eq_pcompose}, but with the degree-1
  map \<open>x \<mapsto> c \<cdot> x\<close> (\<open>[:0,of_int c:]\<close>) in place of negation \<open>x \<mapsto> -x\<close>: the dilated poly
  @{const scale_poly_list} produces is exactly the original composed with that map.\<close>
text \<open>Real evaluation of the dilated poly, proved by the SAME sum-expansion technique as
  @{thm [source] ripoly_refl_list} (\<open>Kiou_Bound_Spec.thy\<close>): extend both sides' \<open>poly_altdef\<close> sums
  to a common upper bound \<open>length xs\<close>, then match term-by-term.\<close>
lemma ripoly_scale_poly_list:
  "ripoly (Poly (scale_poly_list c xs)) (y::real) = ripoly (Poly xs) (of_int c * y)"
proof -
  let ?r1 = "map_poly of_int (Poly (scale_poly_list c xs)) :: real poly"
  let ?r2 = "map_poly of_int (Poly xs) :: real poly"
  let ?N = "length xs"
  have c1: "\<And>i. coeff ?r1 i = of_int c ^ i * coeff ?r2 i"
  proof -
    fix i
    show "coeff ?r1 i = of_int c ^ i * coeff ?r2 i"
    proof (cases "i < length xs")
      case True
      hence "nth_default 0 (scale_poly_list c xs) i = xs ! i * c ^ i"
        by (simp add: scale_poly_list_eq_map_upt nth_default_nth)
      thus ?thesis by (simp add: coeff_map_poly nth_default_nth[symmetric] True)
    next
      case False
      thus ?thesis
        by (simp add: coeff_map_poly nth_default_beyond scale_poly_list_eq_map_upt)
    qed
  qed
  have dg1: "degree ?r1 \<le> ?N"
  proof -
    have "degree ?r1 \<le> degree (Poly (scale_poly_list c xs))" by (rule degree_map_poly_of_int_le)
    also have "\<dots> \<le> length (scale_poly_list c xs)" by (rule degree_Poly)
    also have "\<dots> = ?N" by (simp add: scale_poly_list_eq_map_upt)
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
  have "ripoly (Poly (scale_poly_list c xs)) y = (\<Sum>i\<le>?N. coeff ?r1 i * y ^ i)"
    using ext[OF dg1] by simp
  also have "\<dots> = (\<Sum>i\<le>?N. coeff ?r2 i * (of_int c * y) ^ i)"
  proof (rule sum.cong[OF refl])
    fix i assume "i \<in> {..?N}"
    have "coeff ?r1 i * y ^ i = (of_int c ^ i * coeff ?r2 i) * y ^ i" by (simp only: c1)
    also have "\<dots> = coeff ?r2 i * (of_int c ^ i * y ^ i)" by (simp add: ac_simps)
    also have "\<dots> = coeff ?r2 i * (of_int c * y) ^ i" by (simp flip: power_mult_distrib)
    finally show "coeff ?r1 i * y ^ i = coeff ?r2 i * (of_int c * y) ^ i" .
  qed
  also have "\<dots> = ripoly (Poly xs) (of_int c * y)"
    using ext[OF dg2] by simp
  finally show ?thesis .
qed

text \<open>The dilated poly is exactly the original composed with \<open>x \<mapsto> c \<cdot> x\<close> -- bridges
  @{thm [source] ripoly_scale_poly_list} to a POLYNOMIAL identity via @{thm [source] poly_pcompose}
  and @{thm [source] poly_eq_poly_eq_iff} (a real polynomial is determined by its values), exactly
  as @{thm [source] Poly_refl_list_eq_pcompose} did for negation.\<close>
lemma Poly_scale_poly_list_eq_pcompose:
  "(map_poly of_int (Poly (scale_poly_list c xs)) :: real poly)
     = (map_poly of_int (Poly xs) :: real poly) \<circ>\<^sub>p [:0, of_int c:]"
proof -
  have "poly (map_poly of_int (Poly (scale_poly_list c xs)) :: real poly)
      = poly ((map_poly of_int (Poly xs) :: real poly) \<circ>\<^sub>p [:0, of_int c:])"
  proof
    fix y :: real
    show "poly (map_poly of_int (Poly (scale_poly_list c xs)) :: real poly) y
        = poly ((map_poly of_int (Poly xs) :: real poly) \<circ>\<^sub>p [:0, of_int c:]) y"
      by (simp add: ripoly_scale_poly_list poly_pcompose ac_simps)
  qed
  thus ?thesis by (simp add: poly_eq_poly_eq_iff)
qed

text \<open>\<open>roots_in\<close> under a POSITIVE dilation is the correspondingly dilated interval (order is
  preserved -- no endpoint swap, unlike negation): @{thm [source] proots_pcompose} again, now with
  \<open>c>0\<close> keeping the image set an ordinary open interval.\<close>
lemma roots_in_scale_poly_list:
  fixes xs :: "int list" and a b :: real and c :: int
  assumes P0: "Poly xs \<noteq> 0" and cpos: "0 < c"
  shows "roots_in (map_poly of_int (Poly (scale_poly_list c xs)) :: real poly) a b
       = roots_in (map_poly of_int (Poly xs) :: real poly) (of_int c * a) (of_int c * b)"
proof -
  let ?P = "map_poly of_int (Poly xs) :: real poly"
  have P0': "?P \<noteq> 0" using P0 by simp
  have cne: "(of_int c :: real) \<noteq> 0" using cpos by simp
  have "roots_in (map_poly of_int (Poly (scale_poly_list c xs)) :: real poly) a b
      = proots_count (?P \<circ>\<^sub>p [:0, of_int c:]) {x. a < x \<and> x < b}"
    unfolding roots_in_def by (simp add: Poly_scale_poly_list_eq_pcompose)
  also have "\<dots> = proots_count ?P (poly [:0, of_int c::real:] ` {x. a < x \<and> x < b})"
  proof (rule proots_pcompose[OF P0'])
    have "(of_int c :: real) \<noteq> 0" using cpos by simp
    thus "degree [:0, of_int c :: real:] = 1" by simp
  qed
  also have "poly [:0, of_int c::real:] ` {x. a < x \<and> x < b} = {y. of_int c * a < y \<and> y < of_int c * b}"
  proof (intro equalityI subsetI)
    fix y assume "y \<in> poly [:0, of_int c::real:] ` {x. a < x \<and> x < b}"
    then show "y \<in> {y. of_int c * a < y \<and> y < of_int c * b}"
      using cpos by (auto simp: mult_strict_left_mono)
  next
    fix y assume y: "y \<in> {y. of_int c * a < y \<and> y < of_int c * b}"
    hence "y / of_int c \<in> {x. a < x \<and> x < b}"
      using cpos by (auto simp: less_divide_eq divide_less_eq ac_simps)
    hence "poly [:0, of_int c::real:] (y / of_int c)
        \<in> poly [:0, of_int c::real:] ` {x. a < x \<and> x < b}" by (rule imageI)
    thus "y \<in> poly [:0, of_int c::real:] ` {x. a < x \<and> x < b}" using cne by simp
  qed
  also have "proots_count ?P {y. of_int c * a < y \<and> y < of_int c * b}
      = roots_in ?P (of_int c * a) (of_int c * b)"
    unfolding roots_in_def by simp
  finally show ?thesis .
qed

text \<open>\<open>dsc_pair_ok\<close> under a positive dilation, the same way.\<close>
lemma dsc_pair_ok_scale_poly_list:
  fixes xs :: "int list" and I :: "real \<times> real" and c :: int
  assumes P0: "Poly xs \<noteq> 0" and cpos: "0 < c"
  shows "dsc_pair_ok (map_poly of_int (Poly (scale_poly_list c xs)) :: real poly) I
       = dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) (of_int c * fst I, of_int c * snd I)"
proof -
  let ?P = "map_poly of_int (Poly xs) :: real poly"
  have ripoly_at: "\<And>y. poly (map_poly of_int (Poly (scale_poly_list c xs)) :: real poly) y
      = poly ?P (of_int c * y)"
  proof -
    fix y
    have "poly (map_poly of_int (Poly (scale_poly_list c xs)) :: real poly) y
        = poly (?P \<circ>\<^sub>p [:0, of_int c:]) y"
      by (simp add: Poly_scale_poly_list_eq_pcompose)
    also have "\<dots> = poly ?P (of_int c * y)" by (simp add: poly_pcompose ac_simps)
    finally show "poly (map_poly of_int (Poly (scale_poly_list c xs)) :: real poly) y
        = poly ?P (of_int c * y)" .
  qed
  have cpos': "(0::real) < of_int c" using cpos by simp
  show ?thesis
    unfolding dsc_pair_ok_def
    using ripoly_at roots_in_scale_poly_list[OF P0 cpos, of "fst I" "snd I"] cpos'
    by (auto simp: mult_less_cancel_left_pos mult_cancel_left)
qed

text \<open>\<open>real_to_rat_pair\<close> commutes with a RATIONAL dilation on any \<open>of_rat\<close>-image pair -- the
  dilation counterpart of the negate-and-swap lemma proven below for the reflection, needed to
  remap the carried capstone's unit-interval output back through the split's box scale.\<close>
lemma real_to_rat_pair_scale:
  assumes "K = (of_rat rx, of_rat ry)"
  shows "(of_rat (rc * fst (real_to_rat_pair K)), of_rat (rc * snd (real_to_rat_pair K)))
       = (of_rat rc * fst K, of_rat rc * snd K :: real)"
  using assms by (simp add: of_rat_mult)

section \<open>The AFP-free split all-roots isolator\<close>

text \<open>Per-box \<open>dsc_int\<close> correctness, AFP-free (re-derived from @{thm [source] dsc_int_eq_dsc}
  rather than going through a symmetric-box isolator that needs AFP
  \<open>Algebraic_Numbers.Cauchy_Root_Bound\<close>) -- keeping the Kioustelidis split path AFP-free end to
  end, matching \<open>Kiou_Bound_Spec.thy\<close>'s design.\<close>
lemma dsc_int_set_real_dsc':
  fixes P :: "int poly"
  assumes dom: "dsc_dom (degree P, of_rat a, of_rat b, map_poly of_int P :: real poly)"
    and P0: "P \<noteq> 0" and ab: "a < b"
  shows "set (dsc_int a b P) =
    real_to_rat_pair ` set (dsc (degree P) (of_rat a) (of_rat b)
        (map_poly of_int P :: real poly))"
  using dsc_int_eq_dsc[OF dom refl P0 ab] by (metis set_map set_rev)

lemma dsc_int_sound_real_image':
  fixes P :: "int poly"
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes dom: "dsc_dom (degree P, of_rat a, of_rat b, P_real)"
    and P0: "P \<noteq> 0" and ab: "a < b"
  shows "\<forall>I \<in> set (dsc_int a b P).
    \<exists>J \<in> set (dsc (degree P) (of_rat a) (of_rat b) P_real).
      I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
proof -
  have set_eq: "set (dsc_int a b P) =
      real_to_rat_pair ` set (dsc (degree P) (of_rat a) (of_rat b) P_real)"
    using dsc_int_set_real_dsc'[OF dom[unfolded P_real_def] P0 ab]
    unfolding P_real_def .
  have deg: "degree P_real \<le> degree P" unfolding P_real_def by (rule degree_map_poly_le)
  have P_real0: "P_real \<noteq> 0" using P0 unfolding P_real_def by simp
  have ab_real: "of_rat a < (of_rat b :: real)" using ab by (simp add: of_rat_less)
  have sound: "\<forall>J \<in> set (dsc (degree P) (of_rat a) (of_rat b) P_real). dsc_pair_ok P_real J"
    by (rule dsc_sound[OF dom deg P_real0 ab_real])
  show ?thesis using set_eq sound by auto
qed

lemma dsc_int_complete_real_image':
  fixes P :: "int poly"
  defines "P_real \<equiv> (map_poly of_int P :: real poly)"
  assumes dom: "dsc_dom (degree P, of_rat a, of_rat b, P_real)"
    and P0: "P \<noteq> 0"
    and root: "poly P_real x = 0"
    and ax: "of_rat a < x" and xb: "x < of_rat b"
  shows "\<exists>I \<in> set (dsc_int a b P).
    \<exists>J \<in> set (dsc (degree P) (of_rat a) (of_rat b) P_real).
      I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
proof -
  have ab: "a < b" using ax xb by (meson less_trans of_rat_less)
  have set_eq: "set (dsc_int a b P) =
      real_to_rat_pair ` set (dsc (degree P) (of_rat a) (of_rat b) P_real)"
    using dsc_int_set_real_dsc'[OF dom[unfolded P_real_def] P0 ab]
    unfolding P_real_def .
  have deg: "degree P_real \<le> degree P" unfolding P_real_def by (rule degree_map_poly_le)
  have P_real0: "P_real \<noteq> 0" using P0 unfolding P_real_def by simp
  obtain J where J_in: "J \<in> set (dsc (degree P) (of_rat a) (of_rat b) P_real)"
    and J_cover: "fst J \<le> x \<and> x \<le> snd J"
    using dsc_complete[OF dom deg P_real0 root ax xb] by blast
  then have "real_to_rat_pair J \<in> set (dsc_int a b P)" using set_eq by blast
  then show ?thesis using J_in J_cover by blast
qed

text \<open>Every element \<open>dsc\<close> returns, given \<open>of_rat\<close>-image bounds, is itself a pair of \<open>of_rat\<close> images:
  the bisection midpoint \<open>(a+b)/2\<close> of two \<open>of_rat\<close> images is again one (\<open>of_rat\<close> is a field
  homomorphism), so by induction on \<open>dsc\<close>'s recursion every returned pair is too. This lets
  \<open>real_to_rat_pair\<close> round-trip through negation below, which the split pipeline needs.\<close>
lemma dsc_elems_of_rat_image:
  assumes dom: "dsc_dom (p, a, b, P)"
    and a: "a = of_rat ra" and b: "b = of_rat rb"
  shows "\<forall>I \<in> set (dsc p a b P). \<exists>rx ry. I = (of_rat rx, of_rat ry)"
  using dom a b
proof (induction p a b P arbitrary: ra rb rule: dsc.pinduct)
  case (1 p a b P)
  have dsc_eq: "dsc p a b P =
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a,b)]
        else
          (let m = (a + b) / 2 in
             (if poly P m = 0 then [(m,m)] else []) @
             dsc p a m P @ dsc p m b P))"
    using "1.hyps" dsc.psimps by blast
  show ?case
  proof (cases "Bernstein_changes p a b P = 0")
    case True thus ?thesis using dsc_eq by simp
  next
    case v0: False
    show ?thesis
    proof (cases "Bernstein_changes p a b P = 1")
      case True
      thus ?thesis using dsc_eq "1.prems" by auto
    next
      case v_ge2: False
      let ?m = "(a + b) / 2"
      have m_rat: "?m = of_rat ((ra + rb) / 2)" using "1.prems" by (simp add: of_rat_add of_rat_divide)
      have mid: "\<forall>I \<in> set (if poly P ?m = 0 then [(?m,?m)] else []). \<exists>rx ry. I = (of_rat rx, of_rat ry)"
        using m_rat by (auto intro: exI[of _ "(ra + rb) / 2"])
      have left: "\<forall>I \<in> set (dsc p a ?m P). \<exists>rx ry. I = (of_rat rx, of_rat ry)"
        using "1.IH"(1)[OF refl v0 v_ge2 refl "1.prems"(1) m_rat] by blast
      have right: "\<forall>I \<in> set (dsc p ?m b P). \<exists>rx ry. I = (of_rat rx, of_rat ry)"
        using "1.IH"(2)[OF refl v0 v_ge2 refl m_rat "1.prems"(2)] by blast
      show ?thesis using dsc_eq v0 v_ge2 mid left right
        by (fastforce simp: Let_def)
    qed
  qed
qed

text \<open>\<open>real_to_rat_pair\<close> round-trips through \<open>of_rat\<close> on any \<open>of_rat\<close>-image pair, hence commutes
  with the negate-and-swap map used to remap the reflected half's roots back.\<close>
lemma real_to_rat_pair_neg_swap:
  assumes "K = (of_rat rx, of_rat ry)"
  shows "(- snd (real_to_rat_pair K), - fst (real_to_rat_pair K))
       = real_to_rat_pair (- snd K, - fst K)"
  using assms by (simp add: of_rat_minus[symmetric])

text \<open>The split isolator: positive roots of \<open>P\<close> on \<open>(0,2^kpos)\<close>, negated positive roots of the
  reflection \<open>Q = refl_list P\<close> on \<open>(0,2^kneg)\<close> (the negative roots of \<open>P\<close>), and the exact-zero case
  checked directly (\<open>P(0) = xs!0\<close>). Both searches use the strict Kioustelidis bounds directly as the
  box, since @{thm [source] kiou_k_sound} gives the strict containment \<open>x < 2^k\<close>.\<close>
definition dsc_isolate_all_split :: "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> (rat \<times> rat) list" where
  "dsc_isolate_all_split kpos kneg xs =
     dsc_int 0 (2 ^ kpos) (Poly xs)
     @ map (\<lambda>J. (- snd J, - fst J)) (dsc_int 0 (2 ^ kneg) (Poly (refl_list xs)))
     @ (if xs \<noteq> [] \<and> xs ! 0 = 0 then [(0, 0)] else [])"

text \<open>Soundness: every returned interval isolates a real root of \<open>P\<close> -- either directly (the
  positive-root half), or via the reflection's negation-invariance (the negative-root half), or
  trivially (the exact-zero singleton).\<close>
theorem dsc_isolate_all_split_sound:
  fixes xs :: "int list" and kpos kneg :: nat
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Q_real \<equiv> (map_poly of_int (Poly (refl_list xs)) :: real poly)"
  assumes P0: "Poly xs \<noteq> 0" and Q0: "Poly (refl_list xs) \<noteq> 0"
    and dom_pos: "dsc_dom (degree (Poly xs), 0, 2 ^ kpos, P_real)"
    and dom_neg: "dsc_dom (degree (Poly (refl_list xs)), 0, 2 ^ kneg, Q_real)"
  shows "\<forall>I \<in> set (dsc_isolate_all_split kpos kneg xs).
    \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
proof
  fix I assume I_in: "I \<in> set (dsc_isolate_all_split kpos kneg xs)"
  have dom_pos': "dsc_dom (degree (Poly xs), of_rat (0::rat), of_rat (2 ^ kpos :: rat), P_real)"
    using dom_pos by (simp add: of_rat_power)
  have dom_neg': "dsc_dom (degree (Poly (refl_list xs)), of_rat (0::rat), of_rat (2 ^ kneg :: rat), Q_real)"
    using dom_neg by (simp add: of_rat_power)
  have ab_pos: "(0::rat) < 2 ^ kpos" by simp
  have ab_neg: "(0::rat) < 2 ^ kneg" by simp
  show "\<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
  proof (cases "I \<in> set (dsc_int 0 (2 ^ kpos) (Poly xs))")
    case True
    obtain J where "J \<in> set (dsc (degree (Poly xs)) (of_rat 0) (of_rat (2 ^ kpos)) P_real)"
      and IJ: "I = real_to_rat_pair J" and ok: "dsc_pair_ok P_real J"
      using dsc_int_sound_real_image'[OF dom_pos'[unfolded P_real_def] P0 ab_pos]
        True unfolding P_real_def by fastforce
    thus ?thesis by blast
  next
    case False
    show ?thesis
    proof (cases "I \<in> set (map (\<lambda>J. (- snd J, - fst J)) (dsc_int 0 (2 ^ kneg) (Poly (refl_list xs))))")
      case True
      then obtain J' where J'_in: "J' \<in> set (dsc_int 0 (2 ^ kneg) (Poly (refl_list xs)))"
        and I_eq: "I = (- snd J', - fst J')" by auto
      obtain K where K_in: "K \<in> set (dsc (degree (Poly (refl_list xs))) (of_rat 0) (of_rat (2 ^ kneg)) Q_real)"
        and J'K: "J' = real_to_rat_pair K" and okQ: "dsc_pair_ok Q_real K"
        using dsc_int_sound_real_image'[OF dom_neg'[unfolded Q_real_def] Q0 ab_neg]
          J'_in unfolding Q_real_def by fastforce
      obtain rx ry where K_rat: "K = (of_rat rx, of_rat ry)"
        using dsc_elems_of_rat_image[OF dom_neg', of "0::rat" "2 ^ kneg :: rat"]
          K_in by auto
      let ?J = "(- snd K, - fst K)"
      have okP: "dsc_pair_ok P_real ?J"
        using dsc_pair_ok_refl_list[OF P0] okQ unfolding P_real_def Q_real_def by simp
      have I_eq2: "I = real_to_rat_pair ?J"
        using I_eq J'K real_to_rat_pair_neg_swap[OF K_rat] by simp
      show ?thesis using okP I_eq2 by blast
    next
      case False
      hence I0: "I = (0, 0)" using I_in \<open>I \<notin> set (dsc_int 0 (2 ^ kpos) (Poly xs))\<close>
        unfolding dsc_isolate_all_split_def by (auto split: if_splits)
      have xs0: "xs \<noteq> [] \<and> xs ! 0 = 0" using I_in \<open>I \<notin> set (dsc_int 0 (2 ^ kpos) (Poly xs))\<close>
        \<open>I \<notin> set (map (\<lambda>J. (- snd J, - fst J)) (dsc_int 0 (2 ^ kneg) (Poly (refl_list xs))))\<close>
        unfolding dsc_isolate_all_split_def by (auto split: if_splits)
      have "poly P_real 0 = 0"
        using xs0 unfolding P_real_def
        by (simp add: poly_0_coeff_0 coeff_Poly_eq nth_default_nth)
      hence ok0: "dsc_pair_ok P_real (0, 0)" unfolding dsc_pair_ok_def by simp
      have rtp0: "real_to_rat_pair (0::real, 0::real) = (0, 0)"
        using real_to_rat_pair_of_rat[of "0::rat" "0::rat"] by simp
      have "I = real_to_rat_pair (0, 0)" using I0 rtp0 by simp
      thus ?thesis using ok0 by blast
    qed
  qed
qed

text \<open>Completeness: every real root of \<open>P\<close> is covered by SOME returned interval, PROVIDED \<open>kpos\<close>/
  \<open>kneg\<close> genuinely bound the positive roots of \<open>P\<close>/\<open>Q\<close> (exactly @{thm [source]
  kiou_bound_k_monadic_sound}'s own conclusion shape -- the caller established fact this composes
  with). Mirrors @{thm [source] dsc_isolate_all_split_sound}'s case split via
  @{thm [source] real_roots_sign_split}.\<close>
theorem dsc_isolate_all_split_complete:
  fixes xs :: "int list" and kpos kneg :: nat and x :: real
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Q_real \<equiv> (map_poly of_int (Poly (refl_list xs)) :: real poly)"
  assumes P0: "Poly xs \<noteq> 0" and Q0: "Poly (refl_list xs) \<noteq> 0"
    and dom_pos: "dsc_dom (degree (Poly xs), 0, 2 ^ kpos, P_real)"
    and dom_neg: "dsc_dom (degree (Poly (refl_list xs)), 0, 2 ^ kneg, Q_real)"
    and bpos: "\<forall>y::real. 0 < y \<longrightarrow> ripoly (Poly xs) y = 0 \<longrightarrow> y < 2 ^ kpos"
    and bneg: "\<forall>y::real. 0 < y \<longrightarrow> ripoly (Poly (refl_list xs)) y = 0 \<longrightarrow> y < 2 ^ kneg"
    and root: "poly P_real x = 0"
  shows "\<exists>I \<in> set (dsc_isolate_all_split kpos kneg xs). \<exists>J. I = real_to_rat_pair J
    \<and> fst J \<le> x \<and> x \<le> snd J"
proof -
  have dom_pos': "dsc_dom (degree (Poly xs), of_rat (0::rat), of_rat (2 ^ kpos :: rat), P_real)"
    using dom_pos by (simp add: of_rat_power)
  have dom_neg': "dsc_dom (degree (Poly (refl_list xs)), of_rat (0::rat), of_rat (2 ^ kneg :: rat), Q_real)"
    using dom_neg by (simp add: of_rat_power)
  have rootP: "ripoly (Poly xs) x = 0" using root unfolding P_real_def by simp
  show ?thesis
  proof (cases "0 < x")
    case xpos: True
    have xb: "x < 2 ^ kpos" using bpos xpos rootP by blast
    have ax': "of_rat (0::rat) < x" using xpos by simp
    have xb': "x < of_rat (2 ^ kpos :: rat)" using xb by (simp add: of_rat_power)
    obtain I J where I_in: "I \<in> set (dsc_int 0 (2 ^ kpos) (Poly xs))"
      and IJ: "I = real_to_rat_pair J" and cov: "fst J \<le> x \<and> x \<le> snd J"
      using dsc_int_complete_real_image'[OF dom_pos'[unfolded P_real_def] P0
          root[unfolded P_real_def] ax' xb']
      by blast
    have I_split: "I \<in> set (dsc_isolate_all_split kpos kneg xs)"
      using I_in unfolding dsc_isolate_all_split_def by simp
    show ?thesis using I_split IJ cov by blast
  next
    case xnpos: False
    show ?thesis
    proof (cases "x = 0")
      case x0: True
      have xs0: "xs \<noteq> [] \<and> xs ! 0 = 0"
      proof -
        have xsne: "xs \<noteq> []" using P0 by auto
        moreover have "xs ! 0 = 0"
          using rootP x0 xsne by (simp add: poly_0_coeff_0 coeff_Poly_eq nth_default_nth)
        ultimately show ?thesis by blast
      qed
      have I_split: "(0, 0) \<in> set (dsc_isolate_all_split kpos kneg xs)"
        using xs0 unfolding dsc_isolate_all_split_def by simp
      have "(0, 0) = real_to_rat_pair (0::real, 0::real)"
        using real_to_rat_pair_of_rat[of "0::rat" "0::rat"] by simp
      thus ?thesis using I_split x0 by fastforce
    next
      case xneg0: False
      hence xneg: "x < 0" using xnpos by linarith
      let ?y = "- x"
      have ypos: "0 < ?y" using xneg by simp
      have rootQ: "ripoly (Poly (refl_list xs)) ?y = 0" using rootP by (simp add: ripoly_refl_list)
      have yb: "?y < 2 ^ kneg" using bneg ypos rootQ by blast
      have ay': "of_rat (0::rat) < ?y" using ypos by simp
      have yb': "?y < of_rat (2 ^ kneg :: rat)" using yb by (simp add: of_rat_power)
      obtain J' K where J'_in: "J' \<in> set (dsc_int 0 (2 ^ kneg) (Poly (refl_list xs)))"
        and K_in: "K \<in> set (dsc (degree (Poly (refl_list xs))) (of_rat 0) (of_rat (2 ^ kneg))
            (map_poly of_int (Poly (refl_list xs)) :: real poly))"
        and J'K: "J' = real_to_rat_pair K" and K_cov: "fst K \<le> ?y \<and> ?y \<le> snd K"
        using dsc_int_complete_real_image'[OF dom_neg'[unfolded Q_real_def] Q0
            rootQ[unfolded Q_real_def] ay' yb']
        by blast
      have K_in': "K \<in> set (dsc (degree (Poly (refl_list xs))) (of_rat 0) (of_rat (2 ^ kneg)) Q_real)"
        using K_in unfolding Q_real_def .
      obtain rx ry where K_rat: "K = (of_rat rx, of_rat ry)"
        using dsc_elems_of_rat_image[OF dom_neg', of "0::rat" "2 ^ kneg :: rat"]
          K_in' by auto
      let ?I = "(- snd J', - fst J')"
      have I_split: "?I \<in> set (dsc_isolate_all_split kpos kneg xs)"
        using J'_in unfolding dsc_isolate_all_split_def by simp
      let ?J = "(- snd K, - fst K)"
      have I_eq: "?I = real_to_rat_pair ?J"
        using J'K real_to_rat_pair_neg_swap[OF K_rat] by simp
      have J_cov: "fst ?J \<le> x \<and> x \<le> snd ?J" using K_cov by simp
      show ?thesis using I_split I_eq J_cov by blast
    qed
  qed
qed

text \<open>@{const kiou_headroom} depends only on \<open>length\<close> and per-index ABSOLUTE VALUES, both of
  which @{const refl_list} preserves (it only flips signs) -- so the bound kernel's headroom
  hypothesis transfers for free between \<open>xs\<close> and its reflection, needed when computing
  \<open>kneg\<close>.\<close>
lemma kiou_headroom_refl_list: "kiou_headroom (refl_list xs) = kiou_headroom xs"
  unfolding kiou_headroom_def by (simp add: nth_refl_list)

text \<open>Same transfer for the odd-degree negate-back step: \<open>map uminus\<close> only flips signs too.\<close>
lemma kiou_headroom_uminus: "kiou_headroom (map uminus ys) = kiou_headroom ys"
  unfolding kiou_headroom_def by simp


section \<open>Correctness capstone\<close>

text \<open>The raw output triple, read directly off the loop's @{const dyadic_interval_vec_triples}
  (i.e. @{const dyadic_interval_of_triple}), is \<open>r0\<close> times the SAME triple's count-frame
  projection @{const node_iv_of} at \<open>l0=0\<close> -- verified by unfolding both sides to \<open>dyadic_rat\<close>
  and cancelling the nonzero denominator \<open>r0\<close>. This is the bridge that lets the carried
  capstone's \<open>(0,1)\<close>-count-frame correctness theorem (@{thm bisection_main_list_spec})
  speak directly about the pipeline's actual \<open>(0,r0)\<close>-frame output, with NO new induction.\<close>
lemma dyadic_interval_of_triple_eq_r0_times_node_iv_of:
  fixes r0 :: int
  assumes r0: "r0 > 0"
  shows "dyadic_interval_of_triple t =
    (rat_of_int r0 * fst (node_iv_of 0 r0 0 t), rat_of_int r0 * snd (node_iv_of 0 r0 0 t))"
proof -
  obtain l r k where t_eq: "t = ((l, r), k)" by (metis surj_pair)
  have r0_ne: "(rat_of_int r0 :: rat) \<noteq> 0" using r0 by simp
  have niv: "node_iv_of 0 r0 0 t = (dyadic_rat l k / rat_of_int r0, dyadic_rat r k / rat_of_int r0)"
    unfolding t_eq node_iv_of_def node_iv_def dyadic_rat_def Let_def by simp
  have dit: "dyadic_interval_of_triple t = (dyadic_rat l k, dyadic_rat r k)"
    unfolding t_eq dyadic_interval_of_triple_def by simp
  show ?thesis unfolding dit niv using r0_ne by simp
qed

text \<open>A positive dilation of a nonzero polynomial stays nonzero. @{term c} is the box scale
  \<open>2^kpos\<close>/\<open>2^kneg\<close>, chosen by the pipeline rather than supplied by the caller, so this is derived rather
  than assumed.\<close>
lemma poly_scale_poly_list_nonzero:
  fixes xs :: "int list" and c :: int
  assumes P0: "Poly xs \<noteq> 0" and cne: "c \<noteq> 0"
  shows "Poly (scale_poly_list c xs) \<noteq> 0"
proof
  assume contra: "Poly (scale_poly_list c xs) = 0"
  have "(map_poly of_int (Poly (scale_poly_list c xs)) :: real poly) = 0"
    using contra by simp
  hence "(map_poly of_int (Poly xs) :: real poly) \<circ>\<^sub>p [:0, of_int c:] = 0"
    by (simp add: Poly_scale_poly_list_eq_pcompose)
  hence "(map_poly of_int (Poly xs) :: real poly) = 0"
    using cne by (subst (asm) pcompose_eq_0_iff) auto
  hence "Poly xs = 0" by simp
  thus False using P0 by contradiction
qed

text \<open>Soundness of the pipeline's POSITIVE half, at the pure-list level: given that the carried
  capstone's own SPEC holds of the returned vector (the caller supplies this via
  @{thm [source] bisection_main_list_spec} instantiated at \<open>l_num=0, r_num=rpos, k=0,
  P=Pinit\<close>), every raw output interval (@{const dyadic_interval_vec_to_list}, i.e. NO
  count-frame remap) is a @{const real_to_rat_pair} of a @{const dsc_pair_ok} witness against
  \<open>xs\<close>'s OWN real polynomial -- no negate-swap needed, since positive dilation preserves the
  output frame's orientation. Assembles the \<open>r0\<close>-bridge + the generic dilation-covariance lemmas
  + @{thm [source] dsc_elems_of_rat_image}.\<close>
lemma dsc_carried_et_pos_half_sound:
  fixes xs :: "int list" and rpos :: int
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and dom_init: "dsc_dom (degree (Poly Pinit), of_rat (0::rat), of_rat (1::rat),
        map_poly of_int (Poly Pinit) :: real poly)"
    and acc_spec: "dyadic_interval_vec_invar acc"
    and acc_eq: "mset (acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (dsc_int 0 1 (Poly Pinit))"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
    \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
proof
  fix I assume "I \<in> set (dyadic_interval_vec_to_list acc)"
  then obtain t where t_in: "t \<in> set (dyadic_interval_vec_triples acc)"
    and I_eq: "I = dyadic_interval_of_triple t"
    unfolding dyadic_interval_vec_to_list_def by auto
  have niv_in: "node_iv_of 0 rpos 0 t \<in> set (dsc_int 0 1 (Poly Pinit))"
    using t_in acc_eq unfolding acc_ivs_def
    by (metis (no_types, lifting) image_eqI mset_map mset_eq_setD set_map)
  have Pinit0: "Poly Pinit \<noteq> 0"
    unfolding Pinit_def using poly_scale_poly_list_nonzero[OF P0] rpos_pos by simp
  obtain J where J_in: "J \<in> set (dsc (degree (Poly Pinit)) (of_rat 0) (of_rat 1)
      (map_poly of_int (Poly Pinit) :: real poly))"
    and IJ: "node_iv_of 0 rpos 0 t = real_to_rat_pair J"
    and okPinit: "dsc_pair_ok (map_poly of_int (Poly Pinit) :: real poly) J"
    using dsc_int_sound_real_image'[OF dom_init Pinit0 zero_less_one] niv_in by fastforce
  obtain rx ry where J_rat: "J = (of_rat rx, of_rat ry)"
    using dsc_elems_of_rat_image[OF dom_init, of "0::rat" "1::rat"] J_in by auto
  have dit_eq: "I = (rat_of_int rpos * fst (node_iv_of 0 rpos 0 t),
                      rat_of_int rpos * snd (node_iv_of 0 rpos 0 t))"
    using I_eq dyadic_interval_of_triple_eq_r0_times_node_iv_of[OF rpos_pos] by simp
  have scale_eq: "(of_rat (rat_of_int rpos * fst (real_to_rat_pair J)),
                   of_rat (rat_of_int rpos * snd (real_to_rat_pair J)))
      = (of_rat (rat_of_int rpos) * fst J, of_rat (rat_of_int rpos) * snd J :: real)"
    using real_to_rat_pair_scale[OF J_rat, of "rat_of_int rpos"] .
  let ?J' = "(of_rat (rat_of_int rpos) * fst J, of_rat (rat_of_int rpos) * snd J :: real)"
  have I_real: "(of_rat (fst I), of_rat (snd I)) = ?J'"
    using dit_eq IJ scale_eq by simp
  have okP: "dsc_pair_ok P_real ?J'"
    using dsc_pair_ok_scale_poly_list[OF P0 rpos_pos, of J] okPinit
    unfolding P_real_def Pinit_def by (simp add: of_rat_of_int_eq)
  have I_eq_rtp: "I = real_to_rat_pair ?J'"
  proof -
    have "real_to_rat_pair ?J' = real_to_rat_pair (of_rat (fst I), of_rat (snd I))"
      using I_real by simp
    also have "\<dots> = (fst I, snd I)" by (rule real_to_rat_pair_of_rat)
    also have "\<dots> = I" by simp
    finally show ?thesis by simp
  qed
  show "\<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P_real J"
    using I_eq_rtp okP by blast
qed

text \<open>Completeness twin of @{thm [source] dsc_carried_et_pos_half_sound}: every real root of
  \<open>P\<close> in \<open>(0, rpos)\<close> is covered by SOME returned interval -- the direction \<open>dsc_pair_ok\<close> alone
  never gives (a pipeline that always returned the empty vector would vacuously satisfy pure
  soundness). Mirrors the abstract @{thm [source] dsc_isolate_all_split_complete}'s use of
  @{thm [source] dsc_int_complete_real_image'}, composed with the SAME scale-by-\<open>rpos\<close> algebra
  the soundness lemma above uses, run in the OTHER direction (root \<open>x\<close> \<rightarrow> its scaled-down image
  \<open>y = x/rpos\<close> is a root of \<open>Pinit\<close> in \<open>(0,1)\<close>, find its covering \<open>dsc_int\<close> element, pull it back
  through the mset equality to a concrete output triple, scale its bounds back up by \<open>rpos\<close>).\<close>
lemma dsc_carried_et_pos_half_complete:
  fixes xs :: "int list" and rpos :: int and x :: real
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and dom_init: "dsc_dom (degree (Poly Pinit), of_rat (0::rat), of_rat (1::rat),
        map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (dsc_int 0 1 (Poly Pinit))"
    and x_pos: "0 < x" and x_lt: "x < of_int rpos" and root: "poly P_real x = 0"
  shows "\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
    \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
proof -
  have Pinit0: "Poly Pinit \<noteq> 0"
    unfolding Pinit_def using poly_scale_poly_list_nonzero[OF P0] rpos_pos by simp
  define y where "y = x / of_int rpos"
  have y_pos: "0 < y" unfolding y_def using x_pos rpos_pos by simp
  have y_lt: "y < 1" unfolding y_def using x_lt rpos_pos by (simp add: pos_divide_less_eq)
  have rooty: "poly (map_poly of_int (Poly Pinit) :: real poly) y = 0"
  proof -
    have "(map_poly of_int (Poly Pinit) :: real poly) = P_real \<circ>\<^sub>p [:0, of_int rpos:]"
      unfolding Pinit_def P_real_def by (rule Poly_scale_poly_list_eq_pcompose)
    also have "poly \<dots> y = poly P_real (of_int rpos * y)" by (simp add: poly_pcompose mult.commute)
    also have "of_int rpos * y = x" unfolding y_def using rpos_pos by simp
    finally show ?thesis using root by simp
  qed
  have y_ax: "of_rat (0::rat) < y" using y_pos by simp
  have y_xb: "y < of_rat (1::rat)" using y_lt by simp
  have ex_step: "\<exists>I' \<in> set (dsc_int 0 1 (Poly Pinit)).
      \<exists>J' \<in> set (dsc (degree (Poly Pinit)) (of_rat 0) (of_rat 1)
        (map_poly of_int (Poly Pinit) :: real poly)).
      I' = real_to_rat_pair J' \<and> fst J' \<le> y \<and> y \<le> snd J'"
    using dsc_int_complete_real_image'[OF dom_init Pinit0 rooty y_ax y_xb] by blast
  obtain I' J' where I'_in: "I' \<in> set (dsc_int 0 1 (Poly Pinit))"
    and J'_in: "J' \<in> set (dsc (degree (Poly Pinit)) (of_rat 0) (of_rat 1)
        (map_poly of_int (Poly Pinit) :: real poly))"
    and I'J': "I' = real_to_rat_pair J'"
    and cov: "fst J' \<le> y \<and> y \<le> snd J'"
    using ex_step by blast
  have "I' \<in> set (acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))"
    using I'_in acc_eq by (metis mset_eq_setD)
  then obtain t where t_in: "t \<in> set (dyadic_interval_vec_triples acc)"
    and niv_eq: "node_iv_of 0 rpos 0 t = I'"
    unfolding acc_ivs_def by auto
  define I where "I = dyadic_interval_of_triple t"
  have I_in_list: "I \<in> set (dyadic_interval_vec_to_list acc)"
    using t_in unfolding dyadic_interval_vec_to_list_def I_def by auto
  have dit_eq: "I = (rat_of_int rpos * fst (node_iv_of 0 rpos 0 t),
                      rat_of_int rpos * snd (node_iv_of 0 rpos 0 t))"
    unfolding I_def using dyadic_interval_of_triple_eq_r0_times_node_iv_of[OF rpos_pos] .
  obtain rx ry where J'_rat: "J' = (of_rat rx, of_rat ry)"
    using dsc_elems_of_rat_image[OF dom_init, of "0::rat" "1::rat"] J'_in by fastforce
  have scale_eq: "(of_rat (rat_of_int rpos * fst (real_to_rat_pair J')),
                   of_rat (rat_of_int rpos * snd (real_to_rat_pair J')))
      = (of_rat (rat_of_int rpos) * fst J', of_rat (rat_of_int rpos) * snd J' :: real)"
    using real_to_rat_pair_scale[OF J'_rat, of "rat_of_int rpos"] .
  let ?J = "(of_rat (rat_of_int rpos) * fst J', of_rat (rat_of_int rpos) * snd J' :: real)"
  have I_real: "(of_rat (fst I), of_rat (snd I)) = ?J"
    using dit_eq niv_eq I'J' scale_eq by simp
  have I_eq_rtp: "I = real_to_rat_pair ?J"
  proof -
    have "real_to_rat_pair ?J = real_to_rat_pair (of_rat (fst I), of_rat (snd I))"
      using I_real by simp
    also have "\<dots> = (fst I, snd I)" by (rule real_to_rat_pair_of_rat)
    also have "\<dots> = I" by simp
    finally show ?thesis by simp
  qed
  have cov_x: "fst ?J \<le> x \<and> x \<le> snd ?J"
    using cov unfolding y_def using rpos_pos
    by (simp add: of_rat_mult mult_left_mono field_simps mult.commute)
  show ?thesis
    using I_in_list I_eq_rtp cov_x by blast
qed

text \<open>\<open>roots_in\<close>, hence \<open>dsc_pair_ok\<close>, is invariant under negating the whole polynomial (the
  pipeline's odd-degree negate-back step needs this: it flips \<open>Qb\<close>'s sign to make the leading
  coefficient positive for @{const kiou_bound_k_monadic}'s precondition, but must not change WHICH
  roots get isolated). @{thm [source] proots_count_smult} (\<open>Budan_Fourier/BF_Misc.thy\<close>, already a
  \<open>IsaRRI_Spec\<close> session dependency) gives this directly at \<open>c=-1\<close>.\<close>
lemma roots_in_uminus: "roots_in (- P) a b = roots_in P a b"
proof -
  have "- P = smult (-1) P" by simp
  thus ?thesis
    unfolding roots_in_def by (simp add: proots_count_smult)
qed

lemma dsc_pair_ok_uminus: "dsc_pair_ok (- P) I = dsc_pair_ok P I"
  unfolding dsc_pair_ok_def by (simp add: roots_in_uminus)

text \<open>The leading coefficient of the pipeline's negative-half input (@{term refl_list} of \<open>xs\<close>,
  negated back when the degree is odd so the leading sign matches \<open>xs\<close>'s) is exactly \<open>last xs\<close>
  -- checked by cases on the parity, using @{thm [source] nth_refl_list} at the top index and
  @{thm [source] last_map} for the negation.\<close>
lemma last_refl_list:
  assumes xsne: "xs \<noteq> []"
  shows "last (refl_list xs) = (if even (length xs - 1) then last xs else - last xs)"
proof -
  have rne: "refl_list xs \<noteq> []" using xsne by (simp add: refl_list_def)
  have "last (refl_list xs) = refl_list xs ! (length (refl_list xs) - 1)"
    using rne by (simp add: last_conv_nth)
  also have "\<dots> = refl_list xs ! (length xs - 1)" by simp
  also have "\<dots> = (if even (length xs - 1) then xs ! (length xs - 1) else - xs ! (length xs - 1))"
    using xsne by (simp add: nth_refl_list)
  also have "xs ! (length xs - 1) = last xs" using xsne by (simp add: last_conv_nth)
  finally show ?thesis .
qed

text \<open>The old \<open>last_split_neg_prep\<close> ("the odd-degree negate-back restores \<open>last xs\<close>") is GONE with
  the parity pre-pass it justified. The reflection's leading coefficient is now used AS IS, with
  whatever sign it has -- the sign-robust bound kernel needs only that it is NONZERO.\<close>
lemma last_refl_list_nz:
  assumes xsne: "xs \<noteq> []" and lastnz: "last xs \<noteq> 0"
  shows "last (refl_list xs) \<noteq> 0"
  using last_refl_list[OF xsne] lastnz by simp

text \<open>A canonical-coefficient-list characterization cheaper than re-deriving through
  @{thm [source] coeffs_scale_poly_list}: @{term "coeffs (Poly ys) = ys"} iff \<open>ys\<close> has no
  trailing zero, i.e. \<open>ys = []\<close> or \<open>last ys \<noteq> 0\<close>.\<close>
lemma coeffs_Poly_eq_self_of_last_nonzero:
  assumes "ys \<noteq> []" and "last ys \<noteq> 0"
  shows "coeffs (Poly ys) = ys"
  using assms by (simp add: strip_while_idem_iff no_trailing_unfold)

text \<open>Soundness of the pipeline's NEGATIVE half, mirroring @{thm [source]
  dsc_carried_et_pos_half_sound} exactly, EXCEPT the witness is stated against \<open>Q_real\<close> (the
  REFLECTED polynomial @{term "refl_list xs"}), not \<open>xs\<close> itself -- the negate-and-swap remap back
  to \<open>xs\<close>'s own frame is left to the caller.
  The possible odd-degree negate-back cancels via @{thm [source] dsc_pair_ok_uminus}.\<close>
lemma dsc_carried_et_neg_half_sound:
  fixes xs :: "int list" and rneg :: int
  defines "Q_real \<equiv> (map_poly of_int (Poly (refl_list xs)) :: real poly)"
    and "Qb \<equiv> (refl_list xs)"
    and "Qinit \<equiv> scale_poly_list rneg
        (refl_list xs)"
  assumes Q0: "Poly (refl_list xs) \<noteq> 0" and rneg_pos: "rneg > 0"
    and dom_init: "dsc_dom (degree (Poly Qinit), of_rat (0::rat), of_rat (1::rat),
        map_poly of_int (Poly Qinit) :: real poly)"
    and acc_spec: "dyadic_interval_vec_invar acc"
    and acc_eq: "mset (acc_ivs 0 rneg 0 (dyadic_interval_vec_triples acc))
        = mset (dsc_int 0 1 (Poly Qinit))"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
    \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok Q_real J"
proof -
  have Qb0: "Poly Qb \<noteq> 0"
    unfolding Qb_def using Q0 by (auto simp: Poly_map_uminus)
  \<comment> \<open>\<open>Qb = refl_list xs\<close> outright now (no odd-degree negate-back), so this is definitional --
      the @{thm [source] dsc_pair_ok_uminus} cancellation the parity pre-pass needed is gone.\<close>
  have Qb_Q: "\<And>I. dsc_pair_ok (map_poly of_int (Poly Qb) :: real poly) I = dsc_pair_ok Q_real I"
    unfolding Qb_def Q_real_def by simp
  have Qinit_Qb: "Qinit = scale_poly_list rneg Qb" unfolding Qinit_def Qb_def by simp
  show ?thesis
  proof
  fix I assume "I \<in> set (dyadic_interval_vec_to_list acc)"
  then obtain t where t_in: "t \<in> set (dyadic_interval_vec_triples acc)"
    and I_eq: "I = dyadic_interval_of_triple t"
    unfolding dyadic_interval_vec_to_list_def by auto
  have niv_in: "node_iv_of 0 rneg 0 t \<in> set (dsc_int 0 1 (Poly Qinit))"
    using t_in acc_eq unfolding acc_ivs_def
    by (metis (no_types, lifting) image_eqI mset_map mset_eq_setD set_map)
  have Qinit0: "Poly Qinit \<noteq> 0"
    unfolding Qinit_Qb using poly_scale_poly_list_nonzero[OF Qb0] rneg_pos by simp
  obtain J where J_in: "J \<in> set (dsc (degree (Poly Qinit)) (of_rat 0) (of_rat 1)
      (map_poly of_int (Poly Qinit) :: real poly))"
    and IJ: "node_iv_of 0 rneg 0 t = real_to_rat_pair J"
    and okQinit: "dsc_pair_ok (map_poly of_int (Poly Qinit) :: real poly) J"
    using dsc_int_sound_real_image'[OF dom_init Qinit0 zero_less_one] niv_in by fastforce
  obtain rx ry where J_rat: "J = (of_rat rx, of_rat ry)"
    using dsc_elems_of_rat_image[OF dom_init, of "0::rat" "1::rat"] J_in by auto
  have rneg_ne: "(rat_of_int rneg :: rat) \<noteq> 0" using rneg_pos by simp
  have dit_eq: "I = (rat_of_int rneg * fst (node_iv_of 0 rneg 0 t),
                      rat_of_int rneg * snd (node_iv_of 0 rneg 0 t))"
    using I_eq dyadic_interval_of_triple_eq_r0_times_node_iv_of[OF rneg_pos] by simp
  have scale_eq: "(of_rat (rat_of_int rneg * fst (real_to_rat_pair J)),
                   of_rat (rat_of_int rneg * snd (real_to_rat_pair J)))
      = (of_rat (rat_of_int rneg) * fst J, of_rat (rat_of_int rneg) * snd J :: real)"
    using real_to_rat_pair_scale[OF J_rat, of "rat_of_int rneg"] .
  let ?J' = "(of_rat (rat_of_int rneg) * fst J, of_rat (rat_of_int rneg) * snd J :: real)"
  have I_real: "(of_rat (fst I), of_rat (snd I)) = ?J'"
    using dit_eq IJ scale_eq by simp
  have okQb: "dsc_pair_ok (map_poly of_int (Poly Qb) :: real poly) ?J'"
    using dsc_pair_ok_scale_poly_list[OF Qb0 rneg_pos, of J] okQinit
    unfolding Qinit_Qb by (simp add: of_rat_of_int_eq)
  have okQ: "dsc_pair_ok Q_real ?J'" using okQb Qb_Q by simp
  have I_eq_rtp: "I = real_to_rat_pair ?J'"
  proof -
    have "real_to_rat_pair ?J' = real_to_rat_pair (of_rat (fst I), of_rat (snd I))"
      using I_real by simp
    also have "\<dots> = (fst I, snd I)" by (rule real_to_rat_pair_of_rat)
    also have "\<dots> = I" by simp
    finally show ?thesis by simp
  qed
  show "\<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok Q_real J"
    using I_eq_rtp okQ by blast
  qed
qed

text \<open>Completeness twin of @{thm [source] dsc_carried_et_neg_half_sound}, same rationale as
  @{thm [source] dsc_carried_et_pos_half_complete}: every real root of \<open>Q_real = refl_list xs\<close>
  in \<open>(0, rneg)\<close> is covered by some returned interval. The extra step versus the positive half:
  a root of \<open>Q_real\<close> is (up to sign, which doesn't matter for being a ROOT) also a root of
  \<open>Qb\<close>'s real polynomial, since negation doesn't introduce or remove roots.\<close>
lemma dsc_carried_et_neg_half_complete:
  fixes xs :: "int list" and rneg :: int and x :: real
  defines "Q_real \<equiv> (map_poly of_int (Poly (refl_list xs)) :: real poly)"
    and "Qb \<equiv> (refl_list xs)"
    and "Qinit \<equiv> scale_poly_list rneg
        (refl_list xs)"
  assumes Q0: "Poly (refl_list xs) \<noteq> 0" and rneg_pos: "rneg > 0"
    and dom_init: "dsc_dom (degree (Poly Qinit), of_rat (0::rat), of_rat (1::rat),
        map_poly of_int (Poly Qinit) :: real poly)"
    and acc_eq: "mset (acc_ivs 0 rneg 0 (dyadic_interval_vec_triples acc))
        = mset (dsc_int 0 1 (Poly Qinit))"
    and x_pos: "0 < x" and x_lt: "x < of_int rneg" and root: "poly Q_real x = 0"
  shows "\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
    \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
proof -
  have Qb0: "Poly Qb \<noteq> 0" unfolding Qb_def using Q0 by (auto simp: Poly_map_uminus)
  have Qinit_Qb: "Qinit = scale_poly_list rneg Qb" unfolding Qinit_def Qb_def by simp
  have rootQb: "poly (map_poly of_int (Poly Qb) :: real poly) x = 0"
    using root unfolding Qb_def Q_real_def by simp
  have Qinit0: "Poly Qinit \<noteq> 0"
    unfolding Qinit_Qb using poly_scale_poly_list_nonzero[OF Qb0] rneg_pos by simp
  define y where "y = x / of_int rneg"
  have y_pos: "0 < y" unfolding y_def using x_pos rneg_pos by simp
  have y_lt: "y < 1" unfolding y_def using x_lt rneg_pos by (simp add: pos_divide_less_eq)
  have rooty: "poly (map_poly of_int (Poly Qinit) :: real poly) y = 0"
  proof -
    have "(map_poly of_int (Poly Qinit) :: real poly)
        = (map_poly of_int (Poly Qb) :: real poly) \<circ>\<^sub>p [:0, of_int rneg:]"
      unfolding Qinit_Qb by (rule Poly_scale_poly_list_eq_pcompose)
    also have "poly \<dots> y = poly (map_poly of_int (Poly Qb) :: real poly) (of_int rneg * y)"
      by (simp add: poly_pcompose mult.commute)
    also have "of_int rneg * y = x" unfolding y_def using rneg_pos by simp
    finally show ?thesis using rootQb by simp
  qed
  have y_ax: "of_rat (0::rat) < y" using y_pos by simp
  have y_xb: "y < of_rat (1::rat)" using y_lt by simp
  have ex_step: "\<exists>I' \<in> set (dsc_int 0 1 (Poly Qinit)).
      \<exists>J' \<in> set (dsc (degree (Poly Qinit)) (of_rat 0) (of_rat 1)
        (map_poly of_int (Poly Qinit) :: real poly)).
      I' = real_to_rat_pair J' \<and> fst J' \<le> y \<and> y \<le> snd J'"
    using dsc_int_complete_real_image'[OF dom_init Qinit0 rooty y_ax y_xb] by blast
  obtain I' J' where I'_in: "I' \<in> set (dsc_int 0 1 (Poly Qinit))"
    and J'_in: "J' \<in> set (dsc (degree (Poly Qinit)) (of_rat 0) (of_rat 1)
        (map_poly of_int (Poly Qinit) :: real poly))"
    and I'J': "I' = real_to_rat_pair J'"
    and cov: "fst J' \<le> y \<and> y \<le> snd J'"
    using ex_step by blast
  have "I' \<in> set (acc_ivs 0 rneg 0 (dyadic_interval_vec_triples acc))"
    using I'_in acc_eq by (metis mset_eq_setD)
  then obtain t where t_in: "t \<in> set (dyadic_interval_vec_triples acc)"
    and niv_eq: "node_iv_of 0 rneg 0 t = I'"
    unfolding acc_ivs_def by auto
  define I where "I = dyadic_interval_of_triple t"
  have I_in_list: "I \<in> set (dyadic_interval_vec_to_list acc)"
    using t_in unfolding dyadic_interval_vec_to_list_def I_def by auto
  have dit_eq: "I = (rat_of_int rneg * fst (node_iv_of 0 rneg 0 t),
                      rat_of_int rneg * snd (node_iv_of 0 rneg 0 t))"
    unfolding I_def using dyadic_interval_of_triple_eq_r0_times_node_iv_of[OF rneg_pos] .
  obtain rx ry where J'_rat: "J' = (of_rat rx, of_rat ry)"
    using dsc_elems_of_rat_image[OF dom_init, of "0::rat" "1::rat"] J'_in by fastforce
  have scale_eq: "(of_rat (rat_of_int rneg * fst (real_to_rat_pair J')),
                   of_rat (rat_of_int rneg * snd (real_to_rat_pair J')))
      = (of_rat (rat_of_int rneg) * fst J', of_rat (rat_of_int rneg) * snd J' :: real)"
    using real_to_rat_pair_scale[OF J'_rat, of "rat_of_int rneg"] .
  let ?J = "(of_rat (rat_of_int rneg) * fst J', of_rat (rat_of_int rneg) * snd J' :: real)"
  have I_real: "(of_rat (fst I), of_rat (snd I)) = ?J"
    using dit_eq niv_eq I'J' scale_eq by simp
  have I_eq_rtp: "I = real_to_rat_pair ?J"
  proof -
    have "real_to_rat_pair ?J = real_to_rat_pair (of_rat (fst I), of_rat (snd I))"
      using I_real by simp
    also have "\<dots> = (fst I, snd I)" by (rule real_to_rat_pair_of_rat)
    also have "\<dots> = I" by simp
    finally show ?thesis by simp
  qed
  have cov_x: "fst ?J \<le> x \<and> x \<le> snd ?J"
    using cov unfolding y_def using rneg_pos
    by (simp add: of_rat_mult mult_left_mono field_simps mult.commute)
  show ?thesis
    using I_in_list I_eq_rtp cov_x by blast
qed

text \<open>@{thm [source] pcompose_linear_inverse}/@{thm [source] square_free_pcompose_linear}
  (\<open>dvd\<close>/\<open>square_free\<close> on \<open>real poly\<close> under a nonzero-linear-coefficient substitution) live in
  \<open>Square_Free_Pcompose.thy\<close>, in a minimal import context (see that file's header for the
  \<open>back\<close>-is-a-reserved-keyword gotcha that motivated splitting it out).\<close>

section \<open>Pipeline correctness capstone\<close>

text \<open>The pipeline's precondition: everything squarefreeness DOESN'T give for free. Squarefreeness
  of \<open>xs\<close> transfers to \<open>Pinit\<close>/\<open>Qinit\<close>
  automatically via @{thm [source] square_free_pcompose_linear} for ANY dilation -- but the
  machine-word snat-CAPACITY facts (\<open>bilr_dsc_squarefree_pre\<close>'s \<open>\<mu>\<close>-bound conjuncts, plus
  @{const split_init_pow2_l0_monadic}'s own \<open>kb * length xs < max_snat\<close> precondition) depend on
  \<open>Pinit\<close>/\<open>Qinit\<close>'s ACTUAL root separation, which is NOT derivable from squarefreeness alone --
  exactly like every other solver entry point in this codebase, they are a genuine caller
  obligation. Quantified over \<open>k\<close> since @{const kiou_bound_k_monadic} does not expose a pure,
  named function to state them against a single concrete value.\<close>
text \<open>\<^bold>\<open>The capacity predicate, at one \<open>k\<close>.\<close> It is stated at the one \<open>k\<close> the algorithm computes, not at
  every \<open>k\<close> that bounds the roots.

  \<^bold>\<open>Why not \<open>\<forall>k\<close>.\<close> The premise ``positive roots \<open>< 2 ^ k\<close>'' is monotone in \<open>k\<close> and the conclusion
  anti-monotone, with \<open>k\<close> ranging over all of \<open>nat\<close>, so instantiating at \<open>k := max k0 (max_snat \<dots>)\<close>
  refutes it: a precondition with that clause holds of no list, and every theorem conditional on it
  is vacuous (\<open>Pre_Vacuity_Probe\<close> keeps the refutation as a check). Bounding \<open>k < max_snat\<close> does not
  help: at \<open>k = max_snat - 1\<close> the premise still holds and \<open>k * length xs\<close> still overflows for
  \<open>2 \<le> length xs\<close>, and the \<open>\<mu>\<close> conjunct degrades on its own, because a larger \<open>k\<close> scales the roots
  towards the origin, shrinking \<open>\<delta>\<close> and growing \<open>\<mu>\<close> without bound. The bound has to come from what the
  algorithm computes.

  \<open>length (refl_list xs) = length xs\<close>, so one argument serves both halves.\<close>

definition split_cap :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"split_cap ys k \<longleftrightarrow>
  k * length ys < max_snat LENGTH(gmp_poly_len) \<and>
  (let Yinit = scale_poly_list (2 ^ k) ys;
       \<delta> = delta_P (map_poly of_int (Poly Yinit) :: real poly) in
     k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
     int (2 ^ Suc (rational_interval_mu \<delta> (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len)))"

text \<open>\<^bold>\<open>The precondition.\<close> The capacity clause is stated about the producer of \<open>k\<close>.
  @{const kiou_bound_k_monadic} is the only source of that exponent, and its specification
  (@{thm [source] kiou_bound_k_monadic_sound}) constrains it only from below: \<open>2 ^ k\<close> bounds the roots,
  not that \<open>k\<close> is small.

  \<open>\<le> SPEC\<close> is a plain \<open>bool\<close>, so every use site keeps its shape, and it is satisfiable, because the op
  is a deterministic \<open>O(n)\<close> pass. Determinism is not visible in the specification
  (@{const mpz_bitlen2_monadic} does not pin \<open>r\<close> for a zero coefficient), but a zero coefficient has
  sign \<open>0\<close>, so \<open>opp\<close> is \<open>False\<close> and @{const kiou_update_mop} returns \<open>k\<close> unchanged; only nonzero
  coefficients, whose bit lengths are pinned, can move \<open>k\<close>.

  A precondition definition needs a certified satisfiability witness,
  \<open>\<exists>xs. dsc_isolate_all_split_pre xs\<close>; it is \<open>dsc_isolate_all_split_pre_satisfiable\<close>
  (\<open>Split_Pre_Witness\<close>).\<close>

definition dsc_isolate_all_split_pre :: "int list \<Rightarrow> bool" where
"dsc_isolate_all_split_pre xs \<longleftrightarrow>
  2 \<le> length xs \<and> last xs \<noteq> 0 \<and> kiou_headroom xs \<and>
  coeffs (Poly xs) = xs \<and>
  square_free (map_poly of_int (Poly xs) :: real poly) \<and>
  kiou_bound_k_monadic xs \<le> SPEC (split_cap xs) \<and>
  kiou_bound_k_monadic (refl_list xs) \<le> SPEC (split_cap (refl_list xs))"

text \<open>Soundness: every raw output interval, in EITHER half's OWN frame (positive half: against
  \<open>xs\<close>; negative half: against \<open>Q_real = refl_list xs\<close>, per @{thm [source]
  dsc_carried_et_neg_half_sound} -- the negate-and-swap remap to \<open>xs\<close>'s frame is left to the caller),
  is a @{const real_to_rat_pair} of a @{const dsc_pair_ok} witness; \<open>xs0\<close> reports the exact-zero
  root correctly.\<close>
text \<open>Bridge: the pipeline's own precondition, instantiated at the (existentially-chosen-by-
  @{const kiou_bound_k_monadic}) \<open>kpos\<close>, implies the carried capstone's user-facing
  \<open>bilr_dsc_squarefree_pre\<close> for the positive half's \<open>(0, 2^kpos, 0, Pinit)\<close> call. Every conjunct
  traces to either the \<open>pre\<close> bundle's \<open>k\<close>-quantified capacity facts (instantiated at \<open>kpos\<close>) or
  @{thm [source] square_free_pcompose_linear} (squarefreeness/nonzero-ness/canonicity transfer
  under ANY dilation).\<close>
lemma bisection_isolate_all_split_pos_pre:
  fixes xs :: "int list" and kpos :: nat
  assumes pre: "dsc_isolate_all_split_pre xs"
    and kpos_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ kpos"
    \<comment> \<open>The capacity at THIS \<open>kpos\<close> is a hypothesis rather than an instantiation of a
       \<open>\<forall>k\<close> clause. The caller supplies it from \<open>kiou_bound_k_monadic_spec_capped\<close> (below),
       whose merged \<open>SPEC\<close> carries \<open>split_cap\<close> at the exponent the op actually returned.\<close>
    and cap_at: "split_cap xs kpos"
  shows "bilr_dsc_squarefree_pre
      (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ kpos) xs)) :: real poly))
      (((0, 2 ^ kpos), 0), scale_poly_list (2 ^ kpos) xs)"
proof -
  from pre have len2: "2 \<le> length xs" and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and canonxs: "coeffs (Poly xs) = xs" and hr: "kiou_headroom xs"
    unfolding dsc_isolate_all_split_pre_def by auto
  define Pinit where "Pinit = scale_poly_list (2 ^ kpos) xs"
  define d where "d = delta_P (map_poly of_int (Poly Pinit) :: real poly)"
  have cpos: "(2::int) ^ kpos \<noteq> 0" by simp
  have len_eq: "length Pinit = length xs" unfolding Pinit_def by (simp add: scale_poly_list_eq_map_upt)
  have sfPinit: "square_free (map_poly of_int (Poly Pinit) :: real poly)"
    unfolding Pinit_def
    using square_free_pcompose_linear[OF sfxs, of "2 ^ kpos"]
    by (simp add: Poly_scale_poly_list_eq_pcompose)
  have P0init: "Poly Pinit \<noteq> 0" using sfPinit unfolding square_free_def by simp
  have canonPinit: "coeffs (Poly Pinit) = Pinit"
    unfolding Pinit_def
    using coeffs_scale_poly_list[OF canonxs[symmetric], of "2 ^ kpos"] cpos
    by (simp add: scale_poly_list_correct[symmetric, of "2 ^ kpos" "Poly xs"] canonxs)
  have degne: "degree (Poly Pinit) \<noteq> 0"
  proof -
    have "length (coeffs (Poly Pinit)) = degree (Poly Pinit) + 1"
      using P0init by (rule length_coeffs)
    thus ?thesis using len2 len_eq canonPinit by simp
  qed
  have cap: "kpos * length xs < max_snat LENGTH(gmp_poly_len) \<and>
      kpos + rational_interval_mu d (0, 1) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      int (2 ^ Suc (rational_interval_mu d (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len))"
    using cap_at unfolding split_cap_def Pinit_def d_def by (simp add: Let_def)
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have Pinit_ne: "Pinit \<noteq> []" using len2 len_eq by auto
  show ?thesis
    unfolding bilr_dsc_squarefree_pre_def Pinit_def[symmetric]
    using cap sfPinit P0init canonPinit degne len_eq lenb d_def len2 Pinit_ne
    by (simp add: Let_def)
qed

text \<open>The negative-half twin of @{thm [source] bisection_isolate_all_split_pos_pre}: squarefreeness
  of \<open>Qb\<close> (the reflection, negated back at odd degree) transfers from \<open>xs\<close>'s squarefreeness via
  @{thm [source] square_free_pcompose_linear} (\<open>c=-1\<close>, the reflection) composed with
  @{thm [source] square_free_uminus} (the odd-degree negate-back); canonicity via
  @{thm [source] coeffs_Poly_eq_self_of_last_nonzero} + @{thm [source] last_refl_list_nz}
  (\<open>Qb = refl_list xs\<close>'s leading coefficient is nonzero, of either sign).\<close>
lemma bisection_isolate_all_split_neg_pre:
  fixes xs :: "int list" and kneg :: nat
  defines "Qb \<equiv> (refl_list xs)"
  assumes pre: "dsc_isolate_all_split_pre xs"
    and kneg_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ kneg"
    \<comment> \<open>Negative-half twin: at \<open>refl_list xs\<close>, which is exactly the list the
       negative half calls \<open>kiou_bound_k_monadic\<close> on. \<open>length (refl_list xs) = length xs\<close>, so
       the shared \<open>split_cap\<close> serves both halves with one argument.\<close>
    and cap_at: "split_cap (refl_list xs) kneg"
  shows "bilr_dsc_squarefree_pre
      (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ kneg) Qb)) :: real poly))
      (((0, 2 ^ kneg), 0), scale_poly_list (2 ^ kneg) Qb)"
proof -
  from pre have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and canonxs: "coeffs (Poly xs) = xs" and hr: "kiou_headroom xs"
    unfolding dsc_isolate_all_split_pre_def by auto
  have xsne: "xs \<noteq> []" using len2 by auto
  have sfrefl: "square_free (map_poly of_int (Poly (refl_list xs)) :: real poly)"
    using square_free_pcompose_linear[OF sfxs, of "-1"]
    by (simp add: refl_list_eq_scale_poly_list_neg1 Poly_scale_poly_list_eq_pcompose)
  \<comment> \<open>\<open>Qb = refl_list xs\<close>, so no @{thm [source] square_free_uminus} step for an odd-degree
      negate-back is needed.\<close>
  have sfQb: "square_free (map_poly of_int (Poly Qb) :: real poly)"
    using sfrefl unfolding Qb_def by simp
  have lastnzQb: "last Qb \<noteq> 0" unfolding Qb_def using last_refl_list_nz[OF xsne lastnz] by simp
  have Qb_ne: "Qb \<noteq> []" unfolding Qb_def using xsne by (simp add: refl_list_def)
  have canonQb: "coeffs (Poly Qb) = Qb"
    using coeffs_Poly_eq_self_of_last_nonzero[OF Qb_ne] lastnzQb by simp
  have len_Qb: "length Qb = length xs" unfolding Qb_def by (simp add: refl_list_def)
  define Qinit where "Qinit = scale_poly_list (2 ^ kneg) Qb"
  define d where "d = delta_P (map_poly of_int (Poly Qinit) :: real poly)"
  have cpos: "(2::int) ^ kneg \<noteq> 0" by simp
  have len_eq: "length Qinit = length xs" unfolding Qinit_def
    by (simp add: scale_poly_list_eq_map_upt len_Qb)
  have sfQinit: "square_free (map_poly of_int (Poly Qinit) :: real poly)"
    unfolding Qinit_def
    using square_free_pcompose_linear[OF sfQb, of "2 ^ kneg"]
    by (simp add: Poly_scale_poly_list_eq_pcompose)
  have P0init: "Poly Qinit \<noteq> 0" using sfQinit unfolding square_free_def by simp
  have canonQinit: "coeffs (Poly Qinit) = Qinit"
    unfolding Qinit_def
    using coeffs_scale_poly_list[OF canonQb[symmetric], of "2 ^ kneg"] cpos
    by (simp add: scale_poly_list_correct[symmetric, of "2 ^ kneg" "Poly Qb"] canonQb)
  have degne: "degree (Poly Qinit) \<noteq> 0"
  proof -
    have "length (coeffs (Poly Qinit)) = degree (Poly Qinit) + 1"
      using P0init by (rule length_coeffs)
    thus ?thesis using len2 len_eq canonQinit by simp
  qed
  have cap: "kneg * length xs < max_snat LENGTH(gmp_poly_len) \<and>
      kneg + rational_interval_mu d (0, 1) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      int (2 ^ Suc (rational_interval_mu d (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len))"
    \<comment> \<open>\<open>len_Qb\<close> is load-bearing here and NOT in the positive twin: \<open>split_cap\<close> is stated at
       \<open>length (refl_list xs)\<close> while the goal wants \<open>length xs\<close>.\<close>
    using cap_at len_Qb
    unfolding split_cap_def Qinit_def d_def Qb_def by (simp add: Let_def)
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have Qinit_ne: "Qinit \<noteq> []" using len2 len_eq by auto
  show ?thesis
    unfolding bilr_dsc_squarefree_pre_def Qinit_def[symmetric]
    using cap sfQinit P0init canonQinit degne len_eq lenb d_def len2 Qinit_ne
    by (simp add: Let_def)
qed

text \<open>Reusable for BOTH halves: @{const kiou_bound_k_monadic}'s returned \<open>k\<close> also satisfies
  \<open>k * length ys < max_snat\<close> (a hypothesis @{const dsc_isolate_all_split_pre}'s capacity bundle
  ALREADY supplies, quantified over any \<open>k\<close> satisfying the root-bound property) hence
  \<open>k < max_snat\<close> too (since \<open>length ys \<ge> 1\<close> gives \<open>k \<le> k * length ys\<close>) -- needed before
  @{const mpz_pow2_monadic}/@{const split_init_pow2_l0_monadic} can be called on it.\<close>
text \<open>\<^bold>\<open>Merging two \<open>\<le> SPEC\<close> facts about the SAME op.\<close> Only one \<open>\<le> SPEC\<close> fact fires per
  producer call, so a capacity must be merged into the op's SPEC rather than obtained by
  instantiating a \<open>\<forall>k\<close> clause at the returned \<open>k\<close>. Each vertical uses this again to fold in its
  OWN extra capacity predicate (hybrid's depth-quantified \<open>\<delta>\<close> bound, bail's potential bound).\<close>

lemma kiou_le_SPEC_conj:
  fixes f :: "'a nres"
  assumes P: "f \<le> SPEC P" and Q: "f \<le> SPEC Q"
  shows "f \<le> SPEC (\<lambda>x. P x \<and> Q x)"
  using P Q by (auto simp: pw_le_iff refine_pw_simps)

text \<open>\<open>capY\<close> is the producer-side clause carried by @{const dsc_isolate_all_split_pre}; the conclusion
  is stated so that downstream consumers depend only on the precondition and its \<open>_pos_/_neg_pre\<close>
  bridges.\<close>
lemma kiou_bound_k_monadic_spec_capped:
  fixes ys :: "int list"
  assumes len2: "2 \<le> length ys" and lastnz: "last ys \<noteq> 0"
    and hr: "kiou_headroom ys"
    and capY: "kiou_bound_k_monadic ys \<le> SPEC (split_cap ys)"
  shows "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k.
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k) \<and>
      k * length ys < max_snat LENGTH(gmp_poly_len) \<and> k < max_snat LENGTH(gmp_poly_len) \<and>
      split_cap ys k)"
proof -
  have len1: "1 \<le> length ys" using len2 by linarith
  have kcap: "\<And>k. k * length ys < max_snat LENGTH(gmp_poly_len) \<Longrightarrow>
      k < max_snat LENGTH(gmp_poly_len)"
  proof -
    fix k assume h: "k * length ys < max_snat LENGTH(gmp_poly_len)"
    have "k * 1 \<le> k * length ys" by (rule mult_le_mono2[OF len1])
    hence "k \<le> k * length ys" by linarith
    thus "k < max_snat LENGTH(gmp_poly_len)" using h by linarith
  qed
  have both: "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k.
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k) \<and> split_cap ys k)"
    by (rule kiou_le_SPEC_conj[OF kiou_bound_k_monadic_sound[OF len2 lastnz hr] capY])
  show ?thesis
    by (rule order_trans[OF both]) (use kcap in \<open>auto simp: split_cap_def\<close>)
qed

text \<open>The top-level soundness and completeness theorem \<open>bisection_isolate_all_split_main_correct\<close> (with
  its \<open>_terminates\<close> corollary) is assembled from stages. A single \<open>refine_vcg\<close> across the whole \<open>doN\<close>
  block produces one goal too large to work with, so the pipeline is staged into named intermediate
  fragments (as in @{thm [source] bisection_loop_monadic_seed_correct}):
  \<open>bisection_isolate_all_split_pos_half\<close> below proves the sub-block from
  \<open>kpos \<leftarrow> kiou_bound_k_monadic xs\<close> down to \<open>RETURN accP\<close> on its own, \<open>bisection_isolate_all_split_neg_half\<close>
  does the same for the \<open>Qb\<close> chain, and the top theorem composes the two halves with the exact-zero
  check.\<close>

text \<open>Stage 1 of the assembly: the pipeline's POSITIVE-half sub-block, in isolation. Syntactically
  identical to @{const bisection_isolate_all_split_main}'s own positive-half prefix, so \<open>order_trans\<close>
  plugs this fact directly into the top proof at that exact nested \<open>doN\<close> position.\<close>
text \<open>The positive-half body for a fixed \<open>kpos\<close> already satisfying the root bound and capacity
  conditions, as a top-level lemma rather than nested inside the \<open>kpos\<close> binder: a
  \<open>show \<dots> apply \<dots> done\<close> block nested three \<open>proof -\<close> levels deep can fail to close
  (``Failed to refine any pending goal'' with no subgoals left).\<close>
lemma bisection_isolate_all_split_pos_half_step:
  fixes xs :: "int list" and kpos :: nat
  assumes pre: "dsc_isolate_all_split_pre xs"
    and kpos_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ kpos"
    and kpos_cap: "kpos * length xs < max_snat LENGTH(gmp_poly_len)"
    and kpos_lt: "kpos < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>Threaded through to \<open>bisection_isolate_all_split_pos_pre\<close> below. Strictly
       stronger than \<open>kpos_cap\<close>, which is its first conjunct; both are kept so callers
       need no re-ordering.\<close>
    and cap_at: "split_cap xs kpos"
  shows "(doN {
      Pinit \<leftarrow> split_init_pow2_l0_monadic kpos xs;
      ASSERT (0 < length Pinit \<and> length Pinit + 1 < max_snat LENGTH(gmp_poly_len));
      zl \<leftarrow> RETURN (0::int);
      rpos \<leftarrow> mpz_pow2_monadic kpos;
      accP \<leftarrow> bisection_main_list zl rpos 0 Pinit;
      RETURN ();
      RETURN ();
      RETURN accP
    }) \<le> SPEC (\<lambda>accP. (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  from pre have sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and lenb0: "kiou_headroom xs"
    unfolding dsc_isolate_all_split_pre_def by auto
  have P0: "Poly xs \<noteq> 0" using sfxs unfolding square_free_def by simp
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF lenb0] by linarith
  define Pinit0 where "Pinit0 = scale_poly_list (2 ^ kpos) xs"
  have Pinit_eq: "carried_init_same_den 0 1 (2 ^ kpos) xs = Pinit0"
    unfolding Pinit0_def by (rule split_init_pow2_l0_eq_scale_poly_list)
  have pos_cl_pre: "bilr_dsc_squarefree_pre
      (delta_P (map_poly of_int (Poly Pinit0) :: real poly)) (((0, 2 ^ kpos), 0), Pinit0)"
    using bisection_isolate_all_split_pos_pre[OF pre kpos_sound cap_at] unfolding Pinit0_def by simp
  have int_pre: "bilr_dsc_int_pre
      (delta_P (map_poly of_int (Poly Pinit0) :: real poly)) (((0, 2 ^ kpos), 0), Pinit0)"
    using bilr_dsc_squarefree_pre_imp_int_pre[OF pos_cl_pre] .
  from int_pre have \<delta>_pos: "delta_P (map_poly of_int (Poly Pinit0) :: real poly) > 0"
    and lenPinit: "0 < length Pinit0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow>
        of_rat b - of_rat a \<le> delta_P (map_poly of_int (Poly Pinit0) :: real poly)
        \<Longrightarrow> descartes_list_int a b Pinit0 \<le> 1"
    and lenbPinit: "length Pinit0 + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "0 + rational_interval_mu (delta_P (map_poly of_int (Poly Pinit0) :: real poly))
        (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and cap: "int (2 ^ Suc (rational_interval_mu
        (delta_P (map_poly of_int (Poly Pinit0) :: real poly)) (0, 1))) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    and rpos_pos: "(0::int) < 2 ^ kpos"
    and dom_init: "dsc_dom (degree (Poly Pinit0), of_rat 0, of_rat 1,
        map_poly of_int (Poly Pinit0) :: real poly)"
    and P0init: "Poly Pinit0 \<noteq> 0" and canonPinit: "coeffs (Poly Pinit0) = Pinit0"
    unfolding bilr_dsc_int_pre_def by (auto simp: Let_def)
  have carried_init_direct: "split_init_pow2_l0_monadic kpos xs \<le> RETURN Pinit0"
    using split_init_pow2_l0_monadic_correct[OF lenb kpos_cap]
    by (simp add: Pinit_eq)
  show ?thesis
    unfolding PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg
        carried_init_direct[THEN order_trans]
        mpz_pow2_monadic_spec[OF kpos_lt, THEN order_trans]
        bisection_main_list_spec[OF
          \<delta>_pos lenPinit small_fast lenbPinit dcap cap rpos_pos dom_init P0init canonPinit,
          THEN order_trans])
    subgoal using lenPinit lenbPinit by simp
    subgoal using lenPinit lenbPinit by simp
    unfolding Pinit0_def
    subgoal
      apply (rule dsc_carried_et_pos_half_sound[OF P0 rpos_pos dom_init[unfolded Pinit0_def]])
      subgoal by simp
      subgoal by simp
      done
    subgoal premises prems for x xa
    proof -
      from prems have acc_eq: "mset (acc_ivs 0 (2 ^ kpos) 0 (dyadic_interval_vec_triples x))
          = mset (dsc_int 0 1 (Poly (scale_poly_list (2 ^ kpos) xs)))"
        and xa_pos: "0 < xa" and root: "ripoly (Poly xs) xa = 0" by auto
      have xa_lt: "xa < of_int ((2::int) ^ kpos)"
        using kpos_sound[rule_format, OF xa_pos] root by (simp add: of_int_power)
      show ?thesis
        using dsc_carried_et_pos_half_complete[OF P0 rpos_pos dom_init[unfolded Pinit0_def]
            acc_eq xa_pos xa_lt root]
        by simp
    qed
    done
qed

text \<open>Assembles \<open>bisection_isolate_all_split_pos_half_step\<close> under the existentially bound \<open>kpos\<close> that
  @{const kiou_bound_k_monadic} produces. After \<open>refine_vcg\<close> the remaining goal is
  \<open>\<And>kpos. (kpos_sound \<and> kpos_cap \<and> kpos_lt) \<Longrightarrow> split_init_pow2_l0_monadic kpos xs \<le> SPEC (\<lambda>Pinit. \<dots>)\<close>, which
  plain \<open>rule\<close> with the step lemma does not close; @{thm [source] bind_rule_complete} (the completeness
  half of the bind refinement rule) bridges the mismatch.\<close>
lemma bisection_isolate_all_split_pos_half:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_pre xs"
  shows "dsc_split_pos_solve_monadic xs
    \<le> SPEC (\<lambda>accP. (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  from pre have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs"
    and capY: "kiou_bound_k_monadic xs \<le> SPEC (split_cap xs)"
    unfolding dsc_isolate_all_split_pre_def by auto
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  show ?thesis
    unfolding dsc_split_pos_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg kiou_bound_k_monadic_spec_capped[OF len2 lastnz hr capY, THEN order_trans])
    subgoal using len2 lenb by (cases xs) auto
    subgoal using lenb by simp
    subgoal by blast
    subgoal by blast
    \<comment> \<open>FOUR premises (\<open>cap_at\<close>, \<open>kpos_sound\<close>, \<open>kpos_cap\<close>, \<open>kpos_lt\<close>); all four come from
       the merged \<open>SPEC\<close> that \<open>kiou_bound_k_monadic_spec_capped\<close> delivers, which is why each
       is a bare \<open>blast\<close>.\<close>
    apply (rule bisection_isolate_all_split_pos_half_step[OF pre,
        THEN bind_rule_complete[THEN iffD1]])
       apply blast
      apply blast
     apply blast
    apply blast
    done
qed

text \<open>Generic bind extension: if a program \<open>M\<close> meets \<open>SPEC \<Phi>\<close> and every continuation \<open>g\<close> meets
  \<open>SPEC \<Psi>\<close> on every \<open>\<Phi>\<close>-satisfying result, then \<open>M \<bind> g\<close> meets \<open>SPEC \<Psi>\<close>. Proved once, pointwise,
  with \<open>M\<close> atomic (so \<open>refine_pw_simps\<close> does not unfold a bind chain into the guarded-existential form
  on which \<open>auto\<close> stalls when \<open>M\<close> is a concrete pipeline). It composes a whole-fragment \<open>\<le> SPEC\<close> fact
  into a larger inlined bind chain; the split pipeline itself does not need it, since each stage call
  in @{const bisection_isolate_all_split_main} is atomic and \<open>refine_vcg\<close> with \<open>order_trans\<close> hints
  composes directly.\<close>
lemma nres_bind_SPEC_extend:
  fixes M :: "'b nres"
  assumes M: "M \<le> SPEC \<Phi>" and g: "\<And>x. \<Phi> x \<Longrightarrow> g x \<le> SPEC \<Psi>"
  shows "M \<bind> g \<le> SPEC \<Psi>"
  using assms by (auto simp: pw_le_iff refine_pw_simps)

text \<open>Stage 2b: the pipeline's negative-half body for a FIXED, ALREADY-CONSTRUCTED \<open>Qb\<close>
  (the reflection, negated back at odd degree) and a FIXED \<open>kneg\<close> already satisfying the root
  bound (against @{term "refl_list xs"}) + capacity conditions -- mirrors @{thm [source]
  bisection_isolate_all_split_pos_half_step} exactly: \<open>Qb\<close> is a GIVEN parameter here (tied to \<open>xs\<close> via
  \<open>Qb_eq\<close>), not reconstructed inline, since by the time this lemma is invoked (from the
  existential-\<open>kneg\<close> bridge below) the clone/scale/negate chain has ALREADY run.\<close>
lemma bisection_isolate_all_split_neg_half_step:
  fixes xs :: "int list" and Qb :: "int list" and kneg :: nat
  assumes pre: "dsc_isolate_all_split_pre xs"
    and Qb_eq: "Qb = (refl_list xs)"
    and kneg_sound_Qb: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly Qb) x = 0 \<longrightarrow> x < 2 ^ kneg"
    and kneg_cap: "kneg * length Qb < max_snat LENGTH(gmp_poly_len)"
    and kneg_lt: "kneg < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>Negative twin. Stated at \<open>refl_list xs\<close> (not at the parameter \<open>Qb\<close>) so it
       matches the clause the precondition carries; \<open>Qb_eq\<close> ties the two.\<close>
    and cap_at: "split_cap (refl_list xs) kneg"
  shows "(doN {
      Qinit \<leftarrow> split_init_pow2_l0_monadic kneg Qb;
      poly_free_monadic Qb;
      ASSERT (0 < length Qinit \<and> length Qinit + 1 < max_snat LENGTH(gmp_poly_len));
      zln \<leftarrow> RETURN (0::int);
      rneg \<leftarrow> mpz_pow2_monadic kneg;
      accQ \<leftarrow> bisection_main_list zln rneg 0 Qinit;
      RETURN ();
      RETURN ();
      RETURN accQ
    }) \<le> SPEC (\<lambda>accQ. (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. I = real_to_rat_pair J \<and>
            dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  have len_Qb: "length Qb = length xs" unfolding Qb_eq by simp
  have kneg_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ kneg"
  proof (intro allI impI)
    fix x :: real assume x0: "0 < x" and hx: "ripoly (Poly (refl_list xs)) x = 0"
    have "ripoly (Poly Qb) x = 0"
      unfolding Qb_eq using hx by (simp add: ripoly_map_uminus)
    thus "x < 2 ^ kneg" using kneg_sound_Qb x0 by simp
  qed
  have neg_cl_pre: "bilr_dsc_squarefree_pre
      (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ kneg) Qb)) :: real poly))
      (((0, 2 ^ kneg), 0), scale_poly_list (2 ^ kneg) Qb)"
    using bisection_isolate_all_split_neg_pre[OF pre kneg_sound cap_at] unfolding Qb_eq by simp
  define Qinit0 where "Qinit0 = scale_poly_list (2 ^ kneg) Qb"
  have Qinit_eq: "carried_init_same_den 0 1 (2 ^ kneg) Qb = Qinit0"
    unfolding Qinit0_def by (rule split_init_pow2_l0_eq_scale_poly_list)
  have int_pre: "bilr_dsc_int_pre
      (delta_P (map_poly of_int (Poly Qinit0) :: real poly)) (((0, 2 ^ kneg), 0), Qinit0)"
    using bilr_dsc_squarefree_pre_imp_int_pre[OF neg_cl_pre] unfolding Qinit0_def .
  from int_pre have \<delta>_pos: "delta_P (map_poly of_int (Poly Qinit0) :: real poly) > 0"
    and lenQinit: "0 < length Qinit0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow>
        of_rat b - of_rat a \<le> delta_P (map_poly of_int (Poly Qinit0) :: real poly)
        \<Longrightarrow> descartes_list_int a b Qinit0 \<le> 1"
    and lenbQinit: "length Qinit0 + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "0 + rational_interval_mu (delta_P (map_poly of_int (Poly Qinit0) :: real poly))
        (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and cap: "int (2 ^ Suc (rational_interval_mu
        (delta_P (map_poly of_int (Poly Qinit0) :: real poly)) (0, 1))) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    and rneg_pos: "(0::int) < 2 ^ kneg"
    and dom_init: "dsc_dom (degree (Poly Qinit0), of_rat 0, of_rat 1,
        map_poly of_int (Poly Qinit0) :: real poly)"
    and Q0init: "Poly Qinit0 \<noteq> 0" and canonQinit: "coeffs (Poly Qinit0) = Qinit0"
    unfolding bilr_dsc_int_pre_def by (auto simp: Let_def)
  have Q0: "Poly Qb \<noteq> 0"
  proof
    assume contra: "Poly Qb = 0"
    have "(map_poly of_int (Poly Qinit0) :: real poly)
        = (map_poly of_int (Poly Qb) :: real poly) \<circ>\<^sub>p [:0, of_int (2 ^ kneg):]"
      unfolding Qinit0_def by (rule Poly_scale_poly_list_eq_pcompose)
    also have "\<dots> = 0" using contra by simp
    finally have "(map_poly of_int (Poly Qinit0) :: real poly) = 0" .
    hence "Poly Qinit0 = 0" by simp
    thus False using Q0init by contradiction
  qed
  have Q0real: "Poly (refl_list xs) \<noteq> 0" using Q0 unfolding Qb_eq by simp
  have hr: "kiou_headroom xs" using pre unfolding dsc_isolate_all_split_pre_def by auto
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have lenbQb: "length Qb + 1 < max_snat LENGTH(gmp_poly_len)"
    using lenb unfolding len_Qb .
  have carried_init_direct: "split_init_pow2_l0_monadic kneg Qb \<le> RETURN Qinit0"
    using split_init_pow2_l0_monadic_correct[OF lenbQb kneg_cap]
    by (simp add: Qinit_eq)
  show ?thesis
    apply (refine_vcg
        carried_init_direct[THEN order_trans]
        mpz_pow2_monadic_spec[OF kneg_lt, THEN order_trans]
        bisection_main_list_spec[OF
          \<delta>_pos lenQinit small_fast lenbQinit dcap cap rneg_pos dom_init Q0init canonQinit,
          THEN order_trans])
    subgoal using lenQinit lenbQinit by simp
    subgoal using lenQinit lenbQinit by simp
    unfolding Qinit0_def
    subgoal
      apply (rule dsc_carried_et_neg_half_sound[OF Q0real
          rneg_pos dom_init[unfolded Qinit0_def Qb_eq]])
      subgoal by simp
      subgoal by (simp add: Qb_eq)
      done
    subgoal premises prems for x xa
    proof -
      from prems have acc_eq: "mset (acc_ivs 0 (2 ^ kneg) 0 (dyadic_interval_vec_triples x))
          = mset (dsc_int 0 1 (Poly (scale_poly_list (2 ^ kneg) Qb)))"
        and xa_pos: "0 < xa" and root: "ripoly (Poly (refl_list xs)) xa = 0" by auto
      have xa_lt: "xa < of_int ((2::int) ^ kneg)"
        using kneg_sound[rule_format, OF xa_pos] root by (simp add: of_int_power)
      show ?thesis
        using dsc_carried_et_neg_half_complete[OF Q0real rneg_pos
            dom_init[unfolded Qinit0_def Qb_eq] acc_eq[unfolded Qb_eq] xa_pos xa_lt root]
        by simp
    qed
    done
qed

text \<open>The existential-\<open>kneg\<close> bridge for the negative half, as a minimal top-level lemma (it fixes only
  \<open>xs\<close> and assumes only \<open>pre\<close>). Inside \<open>bisection_isolate_all_split_neg_half\<close>'s proof, the local
  context (\<open>lastnzQb\<close>, \<open>hrQb\<close>, \<open>capYQb\<close>, \<dots>, needed only to derive the properties of \<open>Qb_abs\<close>) enlarges
  \<open>force\<close>'s search space so much that the same \<open>bind_rule_complete\<close> and \<open>force\<close> step runs for minutes.\<close>
lemma bisection_isolate_all_split_neg_half_bridge:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_pre xs"
  shows "(doN {
      kneg \<leftarrow> kiou_bound_k_monadic (refl_list xs);
      ASSERT (kneg * length (refl_list xs) < max_snat LENGTH(gmp_poly_len) \<and>
        kneg < max_snat LENGTH(gmp_poly_len));
      Qinit \<leftarrow> split_init_pow2_l0_monadic kneg (refl_list xs);
      poly_free_monadic (refl_list xs);
      ASSERT (0 < length Qinit \<and> length Qinit + 1 < max_snat LENGTH(gmp_poly_len));
      zln \<leftarrow> RETURN (0::int);
      rneg \<leftarrow> mpz_pow2_monadic kneg;
      accQ \<leftarrow> bisection_main_list zln rneg 0 Qinit;
      RETURN ();
      RETURN ();
      RETURN accQ
    }) \<le> SPEC (\<lambda>accQ. (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. I = real_to_rat_pair J \<and>
            dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  \<comment> \<open>The \<open>Qb_abs\<close> abbreviation is GONE: the negative half now feeds \<open>refl_list xs\<close> straight to the
      sign-robust bound kernel, so there is no distinct \<open>negated-back\<close> list to name. (Folding it
      back in via \<open>Qb_abs_def[symmetric]\<close> would now also rewrite the SPEC's own
      \<open>Poly (refl_list xs)\<close>, breaking the match against \<open>bisection_isolate_all_split_neg_half_step\<close>.)\<close>
  from pre have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and xsne: "xs \<noteq> []"
    unfolding dsc_isolate_all_split_pre_def by auto
  have lastnzQb: "last (refl_list xs) \<noteq> 0" using last_refl_list_nz[OF xsne lastnz] .
  have hrQb: "kiou_headroom (refl_list xs)" using kiou_headroom_refl_list[of xs] hr by simp
  have len2Qb: "2 \<le> length (refl_list xs)" using len2 by simp
  \<comment> \<open>The precondition carries the negative capacity at exactly this list, so it is an
     extraction rather than a re-derivation from the \<open>\<forall>k\<close> clause.\<close>
  have capYQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (split_cap (refl_list xs))"
    using pre unfolding dsc_isolate_all_split_pre_def by auto
  show ?thesis
    apply (refine_vcg kiou_bound_k_monadic_spec_capped[OF len2Qb lastnzQb hrQb capYQb,
        THEN order_trans])
    subgoal by blast
    subgoal by blast
    apply (rule bisection_isolate_all_split_neg_half_step[OF pre refl,
        THEN bind_rule_complete[THEN iffD1]])
       apply blast
      apply blast
     apply blast
    apply blast
    done
qed

text \<open>Stage 2: assembles \<open>bisection_isolate_all_split_neg_half_step\<close> under the existentially-bound
  \<open>kneg\<close> that @{const kiou_bound_k_monadic} produces (on \<open>Qb\<close>, mirroring the positive half's
  \<open>kpos\<close>). Same closing pattern as @{thm [source] bisection_isolate_all_split_pos_half}: \<open>refine_vcg\<close>
  + @{thm [source] bisection_isolate_all_split_neg_half_bridge} discharges the whole existential-\<open>kneg\<close>
  obligation in one step.\<close>
lemma bisection_isolate_all_split_neg_half:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_pre xs"
  shows "dsc_split_neg_solve_monadic xs
    \<le> SPEC (\<lambda>accQ. (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. I = real_to_rat_pair J \<and>
            dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  \<comment> \<open>No \<open>Qb_abs\<close>, no \<open>if_negate_correct\<close>/\<open>cond_eq\<close>: with the sign-robust bound kernel the negative
      half feeds \<open>refl_list xs\<close> straight to the bound, whatever its leading sign.\<close>
  from pre have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and xsne: "xs \<noteq> []"
    unfolding dsc_isolate_all_split_pre_def by auto
  have lastnzQb: "last (refl_list xs) \<noteq> 0" using last_refl_list_nz[OF xsne lastnz] .
  have hrQb: "kiou_headroom (refl_list xs)" using kiou_headroom_refl_list[of xs] hr by simp
  have len2Qb: "2 \<le> length (refl_list xs)" using len2 by simp
  \<comment> \<open>Extraction, as in the bridge above.\<close>
  have capYQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (split_cap (refl_list xs))"
    using pre unfolding dsc_isolate_all_split_pre_def by auto
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have lenscaleQb: "length (refl_list xs) + 1 < max_snat LENGTH(gmp_poly_len)"
    using lenb by simp
  have Qbne: "refl_list xs \<noteq> []" using len2Qb by (cases "refl_list xs") auto
  have lenbQb: "length (refl_list xs) + 1 < max_snat LENGTH(gmp_poly_len)"
    using lenb by simp
  have poly_reflect_correct: "poly_reflect_in_place_monadic xs \<le> RETURN (refl_list xs)"
    using poly_reflect_in_place_correct[OF lenb] by (simp add: refl_list_def)
  show ?thesis
    unfolding dsc_split_neg_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def poly_length_monadic_def
    apply (refine_vcg
        poly_clone_monadic_correct[OF lenb, THEN order_trans]
        poly_reflect_correct[THEN order_trans])
    \<comment> \<open>THREE ASSERT side conditions now, not five: dropping the parity pre-pass removed both the
        \<open>nl \<leftarrow> poly_length Qb; ASSERT (1 \<le> nl)\<close> pair and the post-negate length ASSERT.\<close>
    subgoal using len2 len2Qb lenb lenscaleQb Qbne lenbQb by auto
    subgoal using len2 len2Qb lenb lenscaleQb Qbne lenbQb by auto
    subgoal using len2 len2Qb lenb lenscaleQb Qbne lenbQb by auto
    \<comment> \<open>Now that the parity pre-pass is gone, the residual goal is EXACTLY
        @{thm [source] bind_rule_complete}'s right-hand side for the bridge, so close it with the
        same \<open>rule\<close> the positive half uses (\<open>fastforce\<close> cannot do this higher-order match).\<close>
    apply (rule bisection_isolate_all_split_neg_half_bridge[OF pre,
        THEN bind_rule_complete[THEN iffD1]])
    done
qed

text \<open>Stage 3: the trivial exact-zero-root check -- \<open>ripoly (Poly xs) 0 = xs!0\<close>, no search needed.\<close>
lemma dsc_isolate_all_split_zero_check_correct:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_pre xs"
  shows "dsc_split_zero_check_monadic xs \<le> SPEC (\<lambda>xs0. xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  have len2: "2 \<le> length xs" using pre unfolding dsc_isolate_all_split_pre_def by auto
  show ?thesis
    unfolding dsc_split_zero_check_monadic_def
      PR_CONST_def poly_coeff_sgn_monadic_def
    apply refine_vcg
    using len2 by (auto simp: sgn_eq_0_iff)
qed

text \<open>The executable split pipeline is sound and complete against \<open>xs\<close> in each half's own frame, and
  the exact-zero flag is correct. Because the pipeline calls the three named stage ops (each atomic at
  this level), \<open>refine_vcg\<close> with \<open>order_trans\<close> hints composes directly.

  \<^bold>\<open>Completeness matters as well as soundness\<close>: a pipeline returning the empty vector for every input
  would satisfy soundness (\<open>\<forall>I\<in>output. valid I\<close> says nothing about whether every root appears); the
  second conjunct of each half rules that out by requiring every real root of \<open>xs\<close>/\<open>refl_list xs\<close> in
  \<open>(0,\<infinity>)\<close> to be covered by some returned interval (\<open>dsc_carried_et_pos_half_complete\<close>/
  @{thm [source] dsc_carried_et_neg_half_complete}, the executable counterpart of
  @{thm [source] dsc_isolate_all_split_complete}).\<close>
theorem bisection_isolate_all_split_main_correct:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_pre xs"
  shows "bisection_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accQ, xs0).
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)) \<and>
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)) \<and>
      xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  have len2: "2 \<le> length xs" using pre unfolding dsc_isolate_all_split_pre_def by auto
  show ?thesis
    unfolding bisection_isolate_all_split_main_def PR_CONST_def
    apply (refine_vcg
        bisection_isolate_all_split_pos_half[OF pre, THEN order_trans]
        bisection_isolate_all_split_neg_half[OF pre, THEN order_trans]
        dsc_isolate_all_split_zero_check_correct[OF pre, THEN order_trans])
    using len2 by auto
qed

text \<open>Explicit termination corollary. \<open>nofail\<close> alone is a weaker statement than it looks --
  \<open>nofail SUCCEED\<close> holds (the "no possible outcome" bottom value counts as \<open>nofail\<close>, and
  \<open>SUCCEED \<le> SPEC \<Phi>\<close> is trivially provable for ANY \<open>\<Phi>\<close>, by @{thm [source] SUCCEED_rule}) --
  so a bare \<open>\<le> SPEC\<close> proof does not, by itself, rule out non-termination. What actually excludes
  it here: EVERY loop in this pipeline (@{const kiou_bound_k_monadic}'s bound search,
  @{const bisection_main_list}'s carried loop, both certified elsewhere in
  \<open>Kiou_Bound.thy\<close>/\<open>Kiou_Bound_Refine.thy\<close>/\<open>Bisection_Loop_Refine.thy\<close>) is built via
  \<open>RECT\<close>/\<open>WHILET\<close> with an EXHIBITED well-founded relation, proved via @{thm [source]
  RECT_rule}'s WELL-FOUNDED INDUCTION -- a strictly stronger technique than the plain
  \<open>WHILE\<close>/\<open>WHILEI_rule\<close> path (no \<open>wf\<close> witness, could in principle admit \<open>SUCCEED\<close>). Well-founded
  induction genuinely cannot close on a non-terminating unfolding, so the deeper guarantee is
  real; this corollary just makes it visible as ITS OWN theorem for the split-isolator pipeline,
  rather than leaving it implicit inside the \<open>\<le> SPEC\<close> statement.\<close>
corollary bisection_isolate_all_split_main_terminates:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_pre xs"
  shows "nofail (bisection_isolate_all_split_main xs)"
  using bisection_isolate_all_split_main_correct[OF pre] by (rule SPEC_nofail)

end
