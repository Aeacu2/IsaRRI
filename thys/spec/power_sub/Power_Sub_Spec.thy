theory Power_Sub_Spec
  imports "IsaRRI_Spec.Dsc_Taylor"
begin

text \<open>Degree reduction \<open>P(x) = Q(x\<^sup>h)\<close>: the specification layer (coefficient lists, low to high, as in
  \<open>Dsc_Taylor\<close>).
  Main definitions: \<open>pow_sub_h\<close>, \<open>pow_sub_extract\<close>, \<open>pow_sub_roots_set\<close> (the detection, the reduced
  polynomial, and the root correspondence), joined by \<open>pow_sub_roots_of_list\<close>.

  \<^bold>\<open>The four obligations and where each is discharged\<close>:
  \<^item> \<^bold>\<open>\<open>P = Q \<circ> x\<^sup>h\<close> on the list representation\<close>: \<open>pow_sub_compose\<close>, with \<open>coeff_Poly_pow_sub_extract\<close> /
    \<open>nth_pow_sub_extract\<close> under it.
  \<^item> \<^bold>\<open>The root correspondence\<close>: \<open>pow_sub_roots_set\<close> (both directions, and \<open>pow_sub_roots_sound\<close> /
    \<open>pow_sub_roots_complete\<close> separately), with \<open>pow_sub_lift_pow\<close> / \<open>pow_sub_lift_mem\<close> as its two halves;
    squarefreeness transfers by \<open>pcompose_monom_squarefreeD\<close> / \<open>pow_sub_extract_squarefree\<close>.
  \<^item> \<^bold>\<open>The clamped preimage isolates\<close>: \<open>pow_sub_preimage_isolates\<close> and \<open>pow_sub_preimage_card\<close> (two
    \<open>x\<close>-roots for even \<open>h\<close>, one for odd).
  \<^item> \<^bold>\<open>The output ordering\<close>: \<open>pow_sub_lift_disjoint\<close> (disjointness) and \<open>pow_sub_lift_mono\<close> (the sort key,
    including the order reversal on the negative branch). Dyadicity of the emitted endpoints is a
    property of the back-map loop and is proved in \<open>Power_Sub_Backmap\<close>.
  \<^item> \<^bold>\<open>The join\<close>: \<open>pow_sub_roots_of_list\<close>; the first obligation is on \<open>int list\<close> and the others on
    \<open>real poly\<close>, and this is the statement the implementation uses.

  \<^bold>\<open>Boundary facts\<close> recorded below: \<open>pow_sub_extract_squarefree\<close> needs \<open>xs \<noteq> []\<close> and the support
  hypothesis; \<open>pow_sub_h\<close> returns \<open>0\<close>, not \<open>1\<close>, on a nonzero constant and on \<open>[]\<close> (\<open>pow_sub_h_const\<close>,
  \<open>pow_sub_h_Nil\<close>); clamping the lower endpoint to \<open>max a 0\<close> deletes a root at the origin
  (\<open>pow_sub_origin_never_selected\<close>), and \<open>pow_sub_squarefree_no_origin\<close> shows that root cannot exist when
  \<open>h \<ge> 2\<close> and \<open>P\<close> is squarefree.

  PARI's \<open>polrootsreal\<close> also performs this reduction when no interval is given. The back-map bisects in
  \<open>x\<close>-space and tests \<open>a < m\<^sup>h < b\<close> with exact integer powers, never extracting an \<open>h\<close>-th root, so it needs no new
  GMP primitive.\<close>

section \<open>Detection\<close>

text \<open>The substitution exponent: the gcd of the positions carrying a nonzero coefficient. \<open>h = 1\<close>
  means the transformation does not apply and the entry must be observably unchanged.\<close>

definition pow_sub_support :: "int list \<Rightarrow> nat set" where
  "pow_sub_support xs = {i. i < length xs \<and> xs ! i \<noteq> 0}"

definition pow_sub_h :: "int list \<Rightarrow> nat" where
  "pow_sub_h xs = Gcd (pow_sub_support xs)"

lemma pow_sub_h_dvd:
  "i \<in> pow_sub_support xs \<Longrightarrow> pow_sub_h xs dvd i"
  unfolding pow_sub_h_def by (rule Gcd_dvd)

text \<open>The form the extraction lemma actually consumes: every nonzero position is a multiple of
  \<open>h\<close>. This is \<open>pow_sub_h_dvd\<close> with the support unfolded, stated separately because
  \<open>pow_sub_compose\<close> takes it as a bare hypothesis (so the theorem stays usable for any \<open>h\<close>
  dividing the support, not only the maximal one).\<close>

lemma pow_sub_h_dvd_nonzero:
  "i < length xs \<Longrightarrow> xs ! i \<noteq> 0 \<Longrightarrow> pow_sub_h xs dvd i"
  by (rule pow_sub_h_dvd) (simp add: pow_sub_support_def)

text \<open>\<^bold>\<open>Detection can return \<open>h = 0\<close>, and \<open>0 < h\<close> is a hypothesis of every theorem below.\<close> \<open>Gcd {0} = 0\<close> in
  \<open>nat\<close>, so a polynomial whose only nonzero coefficient is at position \<open>0\<close> (any nonzero constant) gives \<open>h = 0\<close>,
  and so does the zero polynomial (empty support, \<open>Gcd {} = 0\<close>). \<open>h = 1\<close>, not \<open>h = 0\<close>, means ``does not
  apply''. The entry therefore clamps; an unclamped \<open>h\<close> would divide by zero in \<open>pow_sub_extract\<close> and
  falsify the \<open>0 < h\<close> premise of \<open>pow_sub_compose\<close>. The two facts below record this.\<close>

lemma pow_sub_h_Nil: "pow_sub_h ([] :: int list) = 0"
  by (simp add: pow_sub_h_def pow_sub_support_def)

lemma pow_sub_h_const: "c \<noteq> 0 \<Longrightarrow> pow_sub_h [c] = 0"
proof -
  assume "c \<noteq> 0"
  then have "pow_sub_support [c] = {0}" by (auto simp: pow_sub_support_def)
  then show ?thesis by (simp add: pow_sub_h_def)
qed

section \<open>Extraction\<close>

definition pow_sub_extract :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
  "pow_sub_extract h xs = map (\<lambda>j. xs ! (j * h)) [0..<Suc ((length xs - 1) div h)]"

lemma length_pow_sub_extract [simp]:
  "length (pow_sub_extract h xs) = Suc ((length xs - 1) div h)"
  by (simp add: pow_sub_extract_def)

lemma nth_pow_sub_extract:
  assumes "i < Suc ((length xs - 1) div h)"
  shows "pow_sub_extract h xs ! i = xs ! (i * h)"
proof -
  have "pow_sub_extract h xs ! i
          = (\<lambda>j. xs ! (j * h)) ([0..<Suc ((length xs - 1) div h)] ! i)"
    unfolding pow_sub_extract_def using assms by (subst nth_map) simp_all
  also have "\<dots> = xs ! (i * h)" using assms by (simp del: upt_Suc add: nth_upt)
  finally show ?thesis .
qed

text \<open>Coefficient of the reduced polynomial, in the total \<open>nth_default\<close> form the
  coefficientwise argument needs (so no side condition has to be carried around).\<close>

text \<open>\<open>xs \<noteq> []\<close> is required for \<open>pow_sub_compose\<close>. For \<open>xs = []\<close> the extraction is
  \<open>map (\<lambda>j. [] ! (j*h)) [0..<Suc ((0-1) div h)] = [[] ! 0]\<close>, a one-element list holding the undefined value
  \<open>[] ! 0\<close>, so \<open>Poly (pow_sub_extract h []) \<noteq> 0 = Poly []\<close> in general. Truncated subtraction (\<open>0 - 1 = 0\<close>) hides
  this.\<close>

lemma coeff_Poly_pow_sub_extract:
  assumes h: "0 < h" and ne: "xs \<noteq> []"
  shows "coeff (Poly (pow_sub_extract h xs)) i = nth_default 0 xs (i * h)"
proof (cases "i < Suc ((length xs - 1) div h)")
  case True
  then have "i * h \<le> ((length xs - 1) div h) * h" by simp
  also have "\<dots> \<le> length xs - 1" by (rule div_times_less_eq_dividend)
  finally have lt: "i * h < length xs" using ne by (cases xs) auto
  show ?thesis
    using True lt by (simp add: coeff_Poly nth_default_def nth_pow_sub_extract)
next
  case False
  \<comment> \<open>Past the end of \<open>Q\<close>: then \<open>i * h\<close> is past the end of \<open>xs\<close> and both sides are \<open>0\<close>.\<close>
  then have "(length xs - 1) div h < i" by simp
  then have "length xs - 1 < i * h"
    using h by (simp add: div_less_iff_less_mult mult.commute)
  then have "length xs \<le> i * h" by simp
  with False show ?thesis by (simp add: coeff_Poly nth_default_def)
qed

theorem pow_sub_compose:
  assumes h: "0 < h" and ne: "xs \<noteq> []"
    and supp: "\<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> h dvd i"
  shows "Poly xs = pcompose (Poly (pow_sub_extract h xs)) (monom 1 h)"
proof (rule poly_eqI)
  fix k :: nat
  have lt: "k mod h < h" using h by simp
  have decomp: "h * (k div h) + k mod h = k" by simp
  have rhs: "coeff (pcompose (Poly (pow_sub_extract h xs)) (monom 1 h)) k
               = (if k mod h = 0 then coeff (Poly (pow_sub_extract h xs)) (k div h) else 0)"
    using coeff_pcompose_monom[OF lt, of "Poly (pow_sub_extract h xs)" "k div h"] decomp
    by simp
  show "coeff (Poly xs) k = coeff (pcompose (Poly (pow_sub_extract h xs)) (monom 1 h)) k"
  proof (cases "k mod h = 0")
    case True
    then have "h dvd k" by (simp add: dvd_eq_mod_eq_0)
    then have kk: "k div h * h = k" by (rule dvd_div_mult_self)
    have "coeff (Poly (pow_sub_extract h xs)) (k div h) = nth_default 0 xs (k div h * h)"
      by (rule coeff_Poly_pow_sub_extract[OF h ne])
    then show ?thesis using True rhs kk by (simp add: coeff_Poly)
  next
    case False
    \<comment> \<open>\<open>h\<close> does not divide \<open>k\<close>, so the detection hypothesis forces position \<open>k\<close> of \<open>xs\<close> to be
       zero. This is the ONLY place \<open>supp\<close> is used, and it is what makes the theorem true.\<close>
    then have "\<not> h dvd k" by (simp add: dvd_eq_mod_eq_0)
    then have "nth_default 0 xs k = 0" using supp by (auto simp: nth_default_def)
    then show ?thesis using False rhs by (simp add: coeff_Poly)
  qed
qed
  \<comment> \<open>Coefficientwise: position \<open>i\<close> of the right-hand side is \<open>xs ! i\<close> when \<open>h dvd i\<close> and \<open>0\<close> otherwise, which
     the hypothesis makes exactly \<open>xs ! i\<close>. The facts used are \<open>Missing_Polynomial.coeff_pcompose_monom\<close>
     (\<open>j < n \<Longrightarrow> coeff (f \<circ>\<^sub>p monom 1 n) (n*i+j) = (if j = 0 then coeff f i else 0)\<close>) and its special case
     \<open>coeff_pcompose_x_pow_n\<close>.\<close>

text \<open>\<^bold>\<open>The support hypothesis is necessary.\<close> With only \<open>squarefree (Poly xs)\<close> and \<open>0 < h\<close>, nothing ties
  \<open>pow_sub_extract h xs\<close> to \<open>xs\<close>. Take \<open>xs = [0,1]\<close> (so \<open>Poly xs = x\<close>, squarefree) and \<open>h = 2\<close>: the extraction reads
  positions \<open>0, 2, \<dots>\<close> only, giving \<open>pow_sub_extract 2 [0,1] = [0]\<close>, hence \<open>Poly (pow_sub_extract 2 [0,1]) = 0\<close>,
  and \<open>\<not> squarefree 0\<close> (@{thm not_squarefree_0}). Without \<open>supp\<close>, the extractor discards nonzero coefficients
  instead of re-indexing them; \<open>supp\<close> is what makes extraction lossless, and the proof goes through
  \<open>pow_sub_compose\<close>.\<close>

text \<open>The polynomial-level fact is the reusable one; the list-level statement follows from it and
  \<open>pow_sub_compose\<close>. Two helpers first. \<open>is_unit_iff_degree\<close> holds only over a field and does not apply here
  (\<open>[:2:]\<close> has degree 0 and is not a unit of \<open>int poly\<close>), so the degree half is derived from
  \<open>degree_mult_eq\<close>.\<close>

lemma is_unit_imp_degree_0:
  fixes p :: "'a::idom_divide poly"
  assumes "is_unit p"
  shows "degree p = 0"
proof -
  from assms obtain r where r: "1 = p * r" by (elim dvdE)
  then have nz: "p \<noteq> 0" "r \<noteq> 0" by auto
  from r have "degree (p * r) = 0" by simp
  with degree_mult_eq[OF nz] show ?thesis by simp
qed

lemma pcompose_monom_is_unit:
  fixes q :: "'a::idom_divide poly"
  assumes h: "0 < h" and u: "is_unit (q \<circ>\<^sub>p monom 1 h)"
  shows "is_unit q"
proof -
  have dm: "degree (monom (1::'a) h) = h" by (simp add: degree_monom_eq)
  have d0: "degree (q \<circ>\<^sub>p monom (1::'a) h) = 0" using u by (rule is_unit_imp_degree_0)
  have "degree q * h = degree (q \<circ>\<^sub>p monom (1::'a) h)" by (simp add: degree_pcompose dm)
  also have "\<dots> = 0" by (rule d0)
  finally have "degree q * h = 0" .
  with h have "degree q = 0" by auto
  then obtain c where c: "q = [:c:]" by (rule degree_eq_zeroE)
  then have "q \<circ>\<^sub>p monom 1 h = q" by (simp add: pcompose_const)
  with u show ?thesis by simp
qed

text \<open>\<^bold>\<open>The reduced polynomial keeps squarefreeness\<close> — it cannot lose the
  caller's squarefree obligation. Contrapositive: a repeated factor of \<open>Q\<close> lifts through the
  composition, and composition with \<open>monom 1 h\<close> cannot turn a non-unit into a unit.\<close>

theorem pcompose_monom_squarefreeD:
  fixes Q :: "'a::idom_divide poly"
  assumes h: "0 < h" and sf: "squarefree (Q \<circ>\<^sub>p monom 1 h)"
  shows "squarefree Q"
proof (rule squarefreeI)
  fix q :: "'a poly"
  assume "q\<^sup>2 dvd Q"
  then obtain r where r: "Q = q\<^sup>2 * r" ..
  have "Q \<circ>\<^sub>p monom 1 h = (q \<circ>\<^sub>p monom 1 h)\<^sup>2 * (r \<circ>\<^sub>p monom 1 h)"
    by (simp add: r pcompose_mult pcompose_hom.hom_power)
  then have "(q \<circ>\<^sub>p monom 1 h)\<^sup>2 dvd (Q \<circ>\<^sub>p monom 1 h)" by simp
  with sf have "is_unit (q \<circ>\<^sub>p monom 1 h)" by (rule squarefreeD)
  with h show "is_unit q" by (rule pcompose_monom_is_unit)
qed

corollary pow_sub_extract_squarefree:
  assumes sf: "squarefree (Poly xs)" and h: "0 < h" and ne: "xs \<noteq> []"
    and supp: "\<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> h dvd i"
  shows "squarefree (Poly (pow_sub_extract h xs))"
proof -
  have "Poly xs = (Poly (pow_sub_extract h xs)) \<circ>\<^sub>p monom 1 h"
    by (rule pow_sub_compose[OF h ne supp])
  with sf have "squarefree ((Poly (pow_sub_extract h xs)) \<circ>\<^sub>p monom 1 h)" by simp
  with h show ?thesis by (rule pcompose_monom_squarefreeD)
qed
  \<comment> \<open>Squarefreeness is a caller obligation that is not checked at run time; if the reduced polynomial
     could lose it, the transformation would move the solver outside its own precondition.\<close>

text \<open>\<^bold>\<open>A root of \<open>Q\<close> at \<open>y = 0\<close> cannot arise under the precondition.\<close> If \<open>Q(0) = 0\<close> then \<open>x\<close> divides \<open>Q\<close>, so
  \<open>x\<^sup>h\<close> divides \<open>P\<close>, so for \<open>h \<ge> 2\<close> the square \<open>x\<^sup>2\<close> divides \<open>P\<close> and \<open>P\<close> is not squarefree. Since \<open>h \<ge> 2\<close> is
  exactly when the transformation applies, and squarefreeness of \<open>P\<close> is a caller obligation, \<open>Q(0) \<noteq> 0\<close>. No
  runtime origin test is needed: the root the clamp would delete does not exist.\<close>

lemma pow_sub_squarefree_no_origin:
  fixes Q :: "'a::idom_divide poly"
  assumes h: "2 \<le> h" and sf: "squarefree (Q \<circ>\<^sub>p monom 1 h)"
  shows "poly Q 0 \<noteq> 0"
proof
  assume "poly Q 0 = 0"
  then have "[:0,1:] dvd Q" by (simp add: poly_eq_0_iff_dvd)
  then obtain R where R: "Q = [:0,1:] * R" ..
  have idL: "[:0,1::'a:] \<circ>\<^sub>p monom 1 h = monom 1 h" by (simp add: pcompose_pCons)
  have "Q \<circ>\<^sub>p monom 1 h = monom (1::'a) h * (R \<circ>\<^sub>p monom 1 h)"
    by (simp add: R pcompose_mult idL)
  moreover have "([:0,1::'a:])\<^sup>2 dvd monom (1::'a) h"
    using h by (simp add: monom_altdef le_imp_power_dvd)
  ultimately have "([:0,1::'a:])\<^sup>2 dvd (Q \<circ>\<^sub>p monom 1 h)" by simp
  with sf have "is_unit ([:0,1::'a:])" by (rule squarefreeD)
  then have "degree ([:0,1::'a:]) = 0" by (rule is_unit_imp_degree_0)
  then show False by simp
qed

section \<open>The root correspondence\<close>

text \<open>The guarantee is a MULTISET equality against the abstract spec, so the correspondence must be
  stated that way too — not as a set equality, and not as "the counts agree".\<close>

text \<open>For \<open>y < 0\<close> the intended value is \<open>- ((- y) powr e)\<close>, written with explicit parentheses: \<open>- y powr e\<close>
  associates as \<open>- (y powr e)\<close>, and Isabelle's \<open>powr\<close> on a negative base is \<open>0\<close>.\<close>

definition pow_sub_lift :: "nat \<Rightarrow> real \<Rightarrow> real set" where
  "pow_sub_lift h y =
     (if y < 0 then (if even h then {} else { - ((- y) powr (1 / real h)) })
      else if even h \<and> 0 < y then { y powr (1 / real h), - (y powr (1 / real h)) }
      else { y powr (1 / real h) })"

text \<open>\<^bold>\<open>The set form.\<close> Under the squarefree obligation every real root of \<open>P\<close> is simple (and \<open>Q\<close> inherits
  squarefreeness, \<open>pcompose_monom_squarefreeD\<close>), so the set and multiset forms coincide, and the set form is
  what the isolation contract uses. \<open>pow_sub_roots_mset\<close> below restates it in multiset shape. A
  multiplicity-aware version would need \<open>order x P = order (x\<^sup>h) Q\<close> and has no consumer.

  No hypothesis \<open>Q \<noteq> 0\<close> is needed: for \<open>Q = 0\<close> both sides are \<open>UNIV\<close> (every \<open>x\<close> is a root of \<open>P = 0\<close>, and
  \<open>pow_sub_lift\<close> ranges over all \<open>y\<close>).\<close>

text \<open>The type is pinned. Left unconstrained, \<open>Q\<close> is inferred at sort \<open>comm_semiring_0\<close> (all \<open>pcompose\<close> needs),
  and \<open>poly_monom\<close>, which needs \<open>comm_semiring_1\<close>, does not apply, leaving \<open>poly (monom 1 h) x\<close> unrewritten.
  Everything from here on is about real roots, so the type is \<open>real poly\<close>.\<close>

lemma poly_pcompose_monom:
  fixes Q :: "real poly"
  shows "poly (Q \<circ>\<^sub>p monom 1 h) x = poly Q (x ^ h)"
  by (simp add: poly_pcompose poly_monom)

text \<open>The two \<open>powr\<close> facts the correspondence rests on. \<open>powr_root_pow\<close> needs the \<open>y = 0\<close> case
  handled separately: \<open>0 powr e = 0\<close> holds by \<open>powr_def\<close>, not by any of the mono/inverse lemmas.\<close>

lemma powr_root_pow:
  assumes y: "0 \<le> (y::real)" and h: "0 < h"
  shows "(y powr (1 / real h)) ^ h = y"
proof (cases "y = 0")
  case True
  with h show ?thesis by (simp add: powr_def)
next
  case False
  with y have y0: "0 < y" by simp
  then have "0 < y powr (1 / real h)" by simp
  then have "(y powr (1 / real h)) ^ h = (y powr (1 / real h)) powr real h"
    by (simp add: powr_realpow)
  also have "\<dots> = y powr ((1 / real h) * real h)" by (simp add: powr_powr)
  also have "\<dots> = y" using h y0 by simp
  finally show ?thesis .
qed

lemma powr_pow_root:
  assumes x: "0 < (x::real)" and h: "0 < h"
  shows "(x ^ h) powr (1 / real h) = x"
proof -
  have "(x ^ h) powr (1 / real h) = (x powr real h) powr (1 / real h)"
    using x by (simp add: powr_realpow)
  also have "\<dots> = x powr (real h * (1 / real h))" by (simp add: powr_powr)
  also have "\<dots> = x" using h x by simp
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>The lift is exactly the fibre of \<open>x \<mapsto> x\<^sup>h\<close>.\<close> The first lemma is soundness (nothing spurious is
  produced), the second completeness (nothing is missed); they are stated and proved separately. The boundary
  cases are in the case splits: \<open>y = 0\<close> (one root, no \<open>\<plusminus>\<close> pair), \<open>y < 0\<close> with \<open>h\<close> even (empty), and odd \<open>h\<close> (no
  pairing).\<close>

text \<open>The three branches of \<open>pow_sub_lift\<close>, each as its own equation. Selecting the branch by
  \<open>auto\<close> on the raw definition is unreliable — it splits the \<open>if\<close> before the sign facts are
  available and then cannot close the impossible branches.\<close>

lemma pow_sub_lift_neg_eq:
  "y < 0 \<Longrightarrow> pow_sub_lift h y
     = (if even h then {} else { - ((- y) powr (1 / real h)) })"
  by (simp add: pow_sub_lift_def)

lemma pow_sub_lift_zero_eq:
  "0 < h \<Longrightarrow> pow_sub_lift h 0 = {0}"
  by (simp add: pow_sub_lift_def powr_def)

lemma pow_sub_lift_pos_eq:
  "0 < y \<Longrightarrow> pow_sub_lift h y
     = (if even h then { y powr (1 / real h), - (y powr (1 / real h)) }
        else { y powr (1 / real h) })"
  by (simp add: pow_sub_lift_def)

lemma pow_sub_lift_pow:
  assumes h: "0 < h" and mem: "x \<in> pow_sub_lift h y"
  shows "x ^ h = y"
proof -
  consider (neg) "y < 0" | (zero) "y = 0" | (pos) "0 < y" by linarith
  then show ?thesis
  proof cases
    case neg
    show ?thesis
    proof (cases "even h")
      case True
      with neg mem show ?thesis by (simp add: pow_sub_lift_neg_eq)
    next
      case False
      with neg mem have x: "x = - ((- y) powr (1 / real h))"
        by (simp add: pow_sub_lift_neg_eq)
      have "x ^ h = - (((- y) powr (1 / real h)) ^ h)"
        unfolding x using False by (simp add: power_minus_odd)
      also have "\<dots> = - (- y)" using neg h by (simp add: powr_root_pow)
      finally show ?thesis by simp
    qed
  next
    case zero
    with h mem show ?thesis by (simp add: pow_sub_lift_zero_eq)
  next
    case pos
    with mem have "x = y powr (1 / real h) \<or> x = - (y powr (1 / real h))"
      by (auto simp: pow_sub_lift_pos_eq split: if_splits)
    then show ?thesis
    proof
      assume "x = y powr (1 / real h)"
      then show ?thesis using pos h by (simp add: powr_root_pow)
    next
      assume x: "x = - (y powr (1 / real h))"
      have "x ^ h = ((y powr (1 / real h)) ^ h) \<or> x ^ h = - ((y powr (1 / real h)) ^ h)"
        unfolding x by (cases "even h") (simp_all add: power_minus_even power_minus_odd)
      moreover have "(y powr (1 / real h)) ^ h = y" using pos h by (simp add: powr_root_pow)
      moreover have "even h"
      proof (rule ccontr)
        assume "\<not> even h"
        with pos mem x show False by (simp add: pow_sub_lift_pos_eq)
      qed
      ultimately show ?thesis unfolding x by (simp add: power_minus_even)
    qed
  qed
qed

lemma pow_sub_lift_mem:
  assumes h: "0 < h"
  shows "x \<in> pow_sub_lift h (x ^ h)"
proof -
  consider (zero) "x = 0" | (pos) "0 < x" | (neg) "x < 0" by linarith
  then show ?thesis
  proof cases
    case zero
    with h show ?thesis by (simp add: pow_sub_lift_zero_eq zero_power)
  next
    case pos
    then have y: "0 < x ^ h" by simp
    have r: "(x ^ h) powr (1 / real h) = x" using pos h by (rule powr_pow_root)
    show ?thesis by (simp add: pow_sub_lift_pos_eq[OF y] r)
  next
    case neg
    then have mx: "0 < - x" by simp
    have r: "((- x) ^ h) powr (1 / real h) = - x" using mx h by (rule powr_pow_root)
    have p: "0 < (- x) ^ h" using mx by simp
    \<comment> \<open>\<open>x\<^sup>h = (- x)\<^sup>h\<close> must not enter a simp set: \<open>power_minus\<close> rewrites \<open>(- x)\<^sup>h\<close> through \<open>(-1)\<^sup>h * x\<^sup>h\<close> and the
       pair loops. Both equations below are used only as one-shot \<open>unfolding\<close> steps on the goal.\<close>
    show ?thesis
    proof (cases "even h")
      case True
      then have xh: "x ^ h = (- x) ^ h" by (simp add: power_minus_even)
      have y: "0 < x ^ h" unfolding xh by (rule p)
      have r2: "(x ^ h) powr (1 / real h) = - x" unfolding xh by (rule r)
      show ?thesis using True by (simp add: pow_sub_lift_pos_eq[OF y] r2)
    next
      case False
      then have xh: "x ^ h = - ((- x) ^ h)" by (simp add: power_minus_odd)
      have y: "x ^ h < 0" unfolding xh using p by simp
      have r2: "(- (x ^ h)) powr (1 / real h) = - x" unfolding xh using r by simp
      show ?thesis using False by (simp add: pow_sub_lift_neg_eq[OF y] r2)
    qed
  qed
qed

theorem pow_sub_roots_set:
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h"
  shows "{x. poly P x = 0} = (\<Union>y \<in> {y. poly Q y = 0}. pow_sub_lift h y)"
proof (intro set_eqI iffI)
  fix x assume "x \<in> {x. poly P x = 0}"
  then have "poly Q (x ^ h) = 0" by (simp add: P poly_pcompose_monom)
  moreover have "x \<in> pow_sub_lift h (x ^ h)" using h by (rule pow_sub_lift_mem)
  ultimately show "x \<in> (\<Union>y \<in> {y. poly Q y = 0}. pow_sub_lift h y)" by auto
next
  fix x assume "x \<in> (\<Union>y \<in> {y. poly Q y = 0}. pow_sub_lift h y)"
  then obtain y where y: "poly Q y = 0" and mem: "x \<in> pow_sub_lift h y" by auto
  from h mem have "x ^ h = y" by (rule pow_sub_lift_pow)
  with y show "x \<in> {x. poly P x = 0}" by (simp add: P poly_pcompose_monom)
qed

corollary pow_sub_roots_sound:
  assumes "0 < h" and "P = Q \<circ>\<^sub>p monom 1 h" and "poly Q y = 0" and "x \<in> pow_sub_lift h y"
  shows "poly P x = 0"
  using assms pow_sub_roots_set[OF assms(1,2)] by auto

corollary pow_sub_roots_complete:
  assumes "0 < h" and "P = Q \<circ>\<^sub>p monom 1 h" and "poly P x = 0"
  shows "\<exists>y. poly Q y = 0 \<and> x \<in> pow_sub_lift h y"
  using assms pow_sub_roots_set[OF assms(1,2)] by auto

corollary pow_sub_roots_mset:
  assumes "0 < h" and "P = Q \<circ>\<^sub>p monom 1 h"
  shows "mset_set {x. poly P x = 0}
           = mset_set (\<Union>y \<in> {y. poly Q y = 0}. pow_sub_lift h y)"
  using pow_sub_roots_set[OF assms] by simp
  \<comment> \<open>The root correspondence in multiset wording. It carries NO content beyond
     \<open>pow_sub_roots_set\<close> — it is not evidence that multiplicities were checked. The
     multiplicity side is discharged by squarefreeness (\<open>pcompose_monom_squarefreeD\<close>), which makes
     every root simple on both sides.\<close>

section \<open>The int-list layer and the real-root layer, joined\<close>

text \<open>\<^bold>\<open>The first obligation is on \<open>int list\<close>; the others are on \<open>real poly\<close>.\<close> The bridge below joins them:
  composition commutes with the coefficient embedding because \<open>of_int\<close> is a ring homomorphism.\<close>

lemma of_int_poly_pcompose_monom:
  "real_of_int_poly (Q \<circ>\<^sub>p monom 1 h) = (real_of_int_poly Q) \<circ>\<^sub>p monom 1 h"
  by (simp add: of_int_hom.map_poly_pcompose of_int_hom.map_poly_hom_monom)

theorem pow_sub_roots_of_list:
  assumes h: "0 < h" and ne: "xs \<noteq> []"
    and supp: "\<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> h dvd i"
  shows "{x. poly (real_of_int_poly (Poly xs)) x = 0}
           = (\<Union>y \<in> {y. poly (real_of_int_poly (Poly (pow_sub_extract h xs))) y = 0}.
                pow_sub_lift h y)"
proof -
  have "real_of_int_poly (Poly xs)
          = (real_of_int_poly (Poly (pow_sub_extract h xs))) \<circ>\<^sub>p monom 1 h"
    by (simp add: pow_sub_compose[OF h ne supp] of_int_poly_pcompose_monom)
  from pow_sub_roots_set[OF h this] show ?thesis .
qed
  \<comment> \<open>\<^bold>\<open>The statement the implementation uses\<close>: detection gives \<open>h\<close> and the support fact, extraction gives
     the reduced coefficient list, and the real roots of the original are exactly the fibres of the reduced
     one's.\<close>

section \<open>Back-mapping without an h-th root (plan section 3, route B)\<close>

text \<open>Given an isolating interval \<open>(a, b)\<close> for a root of \<open>Q\<close>, the corresponding \<open>x\<close>-roots are
  isolated by ordinary bisection on the existing box, deciding side with the EXACT integer test
  \<open>a < m\<^sup>h < b\<close>. No root extraction, no new GMP binding, no new trust surface — the point of
  choosing this route.\<close>

definition pow_sub_in_preimage :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "pow_sub_in_preimage h a b m = (a < m ^ h \<and> m ^ h < b)"

text \<open>\<^bold>\<open>The isolation statement for the clamped preimage.\<close> Unfolding \<open>pow_sub_in_preimage\<close> in a naive
  statement gives \<open>a < m\<^sup>h \<and> m\<^sup>h < b \<longleftrightarrow> (\<exists>y. a < y \<and> y < b \<and> m\<^sup>h = y)\<close>, which is true for any \<open>h, a, b\<close> and uses none
  of the assumptions, so the statement below is phrased as an isolation property instead.

  \<^bold>\<open>The lower endpoint is clamped\<close> to \<open>max a 0\<close> in the statement: for even \<open>h\<close> and \<open>a < 0\<close>, \<open>{x. a < x\<^sup>2 < b}\<close> is
  the single interval \<open>(-\<surd>b, \<surd>b)\<close> containing both \<open>\<plusminus>\<surd>y\<close>, and no test of \<open>a < m\<^sup>2 < b\<close> separates them.

  \<^bold>\<open>The clamp deletes a root at the origin\<close> (\<open>pow_sub_origin_never_selected\<close>), but under the squarefree
  obligation that root cannot exist when \<open>h \<ge> 2\<close> (\<open>pow_sub_squarefree_no_origin\<close>), and \<open>h \<ge> 2\<close> is exactly when
  the transformation applies. So the clamp is sound, given the squarefree hypothesis.

  \<^bold>\<open>The statement\<close>: with \<open>a' = max a 0\<close>, the exact side test selects exactly the fibre of the unique \<open>Q\<close>-root in
  \<open>(a', b)\<close> (\<open>pow_sub_preimage_isolates\<close>), which has two elements for even \<open>h\<close> (negatives of each other) and one
  for odd \<open>h\<close> (\<open>pow_sub_preimage_card\<close>). Both directions of the set equality are proved.

  \<^bold>\<open>Two properties of the reduced solve's output the back-map must respect\<close>: the positive half is returned
  in descending order, and degenerate intervals \<open>[a,a]\<close> are emitted for exact dyadic roots, with a neighbouring
  interval starting at the same point, so a sort keyed on the lower endpoint alone mis-orders that pair.\<close>

lemma pow_sub_origin_never_selected:
  assumes h: "0 < h"
  shows "\<not> pow_sub_in_preimage h (max a 0) b 0"
  using h by (simp add: pow_sub_in_preimage_def zero_power)
  \<comment> \<open>The deletion, made explicit rather than left in prose: the clamped test rejects \<open>x = 0\<close> for
     EVERY \<open>a\<close> and \<open>b\<close>. Harmless only because \<open>pow_sub_squarefree_no_origin\<close> rules the root out.\<close>

theorem pow_sub_preimage_isolates:
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h"
    and uniq: "\<exists>!y. max a 0 < y \<and> y < b \<and> poly Q y = 0"
  shows "{x. poly P x = 0 \<and> pow_sub_in_preimage h (max a 0) b x}
           = pow_sub_lift h (THE y. max a 0 < y \<and> y < b \<and> poly Q y = 0)"
proof -
  from uniq obtain y0 where y0P: "max a 0 < y0" "y0 < b" "poly Q y0 = 0"
    and y0U: "\<And>w. max a 0 < w \<and> w < b \<and> poly Q w = 0 \<Longrightarrow> w = y0" by auto
  have the_eq: "(THE y. max a 0 < y \<and> y < b \<and> poly Q y = 0) = y0"
    using y0P y0U by blast
  show ?thesis unfolding the_eq
  proof (intro set_eqI iffI)
    fix x assume "x \<in> {x. poly P x = 0 \<and> pow_sub_in_preimage h (max a 0) b x}"
    then have A: "poly Q (x ^ h) = 0" "max a 0 < x ^ h" "x ^ h < b"
      by (auto simp: P poly_pcompose_monom pow_sub_in_preimage_def)
    then have "x ^ h = y0" using y0U by blast
    moreover have "x \<in> pow_sub_lift h (x ^ h)" using h by (rule pow_sub_lift_mem)
    ultimately show "x \<in> pow_sub_lift h y0" by simp
  next
    fix x assume "x \<in> pow_sub_lift h y0"
    with h have xh: "x ^ h = y0" by (rule pow_sub_lift_pow)
    with y0P show "x \<in> {x. poly P x = 0 \<and> pow_sub_in_preimage h (max a 0) b x}"
      by (simp add: P poly_pcompose_monom pow_sub_in_preimage_def)
  qed
qed

lemma pow_sub_lift_card_pos:
  assumes h: "0 < h" and y: "0 < y"
  shows "card (pow_sub_lift h y) = (if even h then 2 else 1)"
proof -
  have "0 < y powr (1 / real h)" using y by simp
  then have "y powr (1 / real h) \<noteq> - (y powr (1 / real h))" by simp
  then show ?thesis by (simp add: pow_sub_lift_pos_eq[OF y])
qed

corollary pow_sub_preimage_card:
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h"
    and uniq: "\<exists>!y. max a 0 < y \<and> y < b \<and> poly Q y = 0"
  shows "card {x. poly P x = 0 \<and> pow_sub_in_preimage h (max a 0) b x}
           = (if even h then 2 else 1)"
proof -
  from uniq obtain y0 where y0P: "max a 0 < y0" "y0 < b" "poly Q y0 = 0"
    and y0U: "\<And>w. max a 0 < w \<and> w < b \<and> poly Q w = 0 \<Longrightarrow> w = y0" by auto
  have the_eq: "(THE y. max a 0 < y \<and> y < b \<and> poly Q y = 0) = y0"
    using y0P y0U by blast
  have "(0::real) \<le> max a 0" by simp
  with y0P(1) have pos: "0 < y0" by linarith
  show ?thesis
    unfolding pow_sub_preimage_isolates[OF h P uniq] the_eq
    using h pos by (rule pow_sub_lift_card_pos)
qed
  \<comment> \<open>\<^bold>\<open>The clamp is what makes \<open>0 < y0\<close> free\<close>: \<open>y0 > max a 0 \<ge> 0\<close>. Without it \<open>y0\<close> could be
     negative, the even-\<open>h\<close> fibre would be EMPTY, and the count would be 0 rather than 2 — the
     straddling-window defect of the back-map, seen from the counting side.\<close>

section \<open>Plan section 4 obligation 4 — the spec-layer half of the output contract\<close>

text \<open>The ordering obligation (sorted, disjoint, dyadic) splits. Disjointness and the sort key are
  specification-level facts, proved here. Dyadicity is a property of the back-map, whose endpoints are dyadic by
  construction; it is proved in \<open>Power_Sub_Backmap\<close>.\<close>

lemma pow_sub_lift_disjoint:
  assumes h: "0 < h" and ne: "y1 \<noteq> y2"
  shows "pow_sub_lift h y1 \<inter> pow_sub_lift h y2 = {}"
proof (rule ccontr)
  assume "pow_sub_lift h y1 \<inter> pow_sub_lift h y2 \<noteq> {}"
  then obtain x where "x \<in> pow_sub_lift h y1" and "x \<in> pow_sub_lift h y2" by auto
  with h have "x ^ h = y1" "x ^ h = y2" by (auto intro: pow_sub_lift_pow)
  with ne show False by simp
qed
  \<comment> \<open>Distinct \<open>Q\<close>-roots therefore give disjoint \<open>x\<close>-fibres — no output interval can be produced
     twice, and no two back-mapped groups can overlap.\<close>

lemma pow_sub_lift_mono:
  assumes h: "0 < h" and y1: "0 \<le> y1" and lt: "y1 < y2"
  shows "y1 powr (1 / real h) < y2 powr (1 / real h)"
  using assms by (simp add: powr_less_mono2)
  \<comment> \<open>\<^bold>\<open>The sort key.\<close> On the positive branch the back-map is strictly increasing, so \<open>Q\<close>'s order is preserved;
     on the negative branch it is \<open>x \<mapsto> - x\<close> of the same map, hence strictly decreasing, so the negative half is
     emitted in reverse. No single key over the raw \<open>y\<close> values orders both halves.\<close>

section \<open>The obligation that is NOT about mathematics\<close>

text \<open>\<^bold>\<open>When \<open>h = 1\<close> the entry must be observably unchanged.\<close> 115 of the 135 record-suite cases
  have \<open>h = 1\<close>, and they are the regression test: their exported behaviour must be bit-identical,
  and the O(n) detection pass must not perturb the Kioustelidis bound, the initial frame, or any
  word-bound precondition. A preprocessing step that quietly changes the \<open>h = 1\<close> path would be the
  most expensive kind of bug this project has: invisible on the families it targets, and everywhere
  else at once.\<close>

end
