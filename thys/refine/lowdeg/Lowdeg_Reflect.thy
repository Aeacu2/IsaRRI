\<comment>\<open>Imports are session-qualified.\<close>
theory Lowdeg_Reflect
  imports
    "IsaRRI_Refine.Kiou_Bound_Reflect"
    "IsaRRI_LLVM.Lowdeg_Split"
    "IsaRRI_Spec.Lowdeg_Math"
begin

text \<open>The isolation theorem for the degree-2/3 closed forms, in the shape of
  @{thm [source] bisection_isolate_all_split_main_correct}: on the positive arm every emitted window
  satisfies \<open>dsc_pair_ok\<close> and every positive root is covered, and likewise on the reflected arm for
  \<open>refl_list xs\<close>.

  \<^bold>\<open>Three of its four pieces exist already\<close>:
  \<^item> the fall-through arm is @{thm [source] bisection_isolate_all_split_main_correct}: the dispatch hands
    the whole input to the bisection solve, so that branch needs no new argument;
  \<^item> the root bound is @{thm [source] kiou_bound_k_monadic_sound}: the emitted window's high endpoint is
    the Kioustelidis bound;
  \<^item> the mathematics is \<open>IsaRRI_Spec.Lowdeg_Math\<close>: \<open>cubic_neg_disc_unique\<close>,
    \<open>cubic_root_sign_pos\<close>/\<open>_neg\<close>, \<open>quad_no_real_root\<close>, \<open>quad_straddles_zero\<close>, \<open>quad_separator\<close>.

  What is new here is the bridge between them: that a set-theoretic root count becomes \<open>roots_in\<close>, and
  that the integer discriminants the implementation computes are the real ones the mathematics is
  stated about.

  \<^bold>\<open>Multiplicity.\<close> \<open>roots_in\<close> is \<open>proots_count\<close>, which counts with multiplicity, while the closed forms
  are about the set of real roots. The two agree because \<open>dsc_isolate_all_split_pre\<close> includes
  squarefreeness; the bridge is where that hypothesis is used.\<close>

section \<open>1. Counting: \<open>roots_in\<close> is a CARDINALITY under squarefreeness\<close>

text \<open>@{thm [source] proots_count_le_1} already contains this equality inside its proof, used
  once and discarded.  It is lifted out here because every emission lemma below needs it in its
  own right --- an INEQUALITY would only ever give \<open>\<le> 1\<close>, and \<open>dsc_pair_ok\<close> demands \<open>= 1\<close>.\<close>
lemma proots_count_eq_card:
  fixes p :: "'a::field_char_0 poly"
  assumes rsf: "rsquarefree p"
  shows "proots_count p S = card (proots_within p S)"
proof -
  from rsf have p0: "p \<noteq> 0" unfolding rsquarefree_def by auto
  have order_eq_1: "order z p = 1" if hz: "z \<in> proots_within p S" for z
  proof -
    from hz have "poly p z = 0" by (simp add: proots_within_def)
    from order_gt_0_iff[OF p0, of z] this have "order z p > 0" by simp
    moreover from rsf have "order z p = 0 \<or> order z p = 1"
      unfolding rsquarefree_def by blast
    ultimately show ?thesis by linarith
  qed
  have "proots_count p S = (\<Sum>z\<in>proots_within p S. order z p)"
    by (simp add: proots_count_def)
  also have "\<dots> = (\<Sum>z\<in>proots_within p S. 1)" using order_eq_1 by simp
  also have "\<dots> = card (proots_within p S)" by simp
  finally show ?thesis .
qed

lemma roots_in_eq_card:
  fixes P :: "real poly"
  assumes rsf: "rsquarefree P"
  shows "roots_in P a b = card {x. a < x \<and> x < b \<and> poly P x = 0}"
proof -
  have "proots_within P {x. a < x \<and> x < b} = {x. a < x \<and> x < b \<and> poly P x = 0}"
    by (auto simp: proots_within_def)
  thus ?thesis using proots_count_eq_card[OF rsf] by (simp add: roots_in_def)
qed

text \<open>The precondition's squarefreeness, in the form \<section>1 consumes.\<close>
lemma rsquarefree_of_pre:
  assumes sf: "square_free (map_poly of_int (Poly xs) :: real poly)"
  shows "rsquarefree (map_poly of_int (Poly xs) :: real poly)"
  using sf by (rule square_free_rsquarefree)

section \<open>2. The window the closed forms emit ISOLATES\<close>

text \<open>\<^bold>\<open>The workhorse.\<close>  When an arm has EXACTLY ONE positive root and the Kioustelidis bound
  \<open>2\<^sup>k\<close> lies above every positive root, the bound itself is the isolating window --- no
  subdivision, no separator.  Both the degree-3 \<open>\<Delta><0\<close> case and the degree-2 straddling case
  reduce to this lemma.\<close>
lemma lowdeg_bound_window_isolates:
  fixes xs :: "int list" and k :: nat
  assumes sf: "square_free (map_poly of_int (Poly xs) :: real poly)"
      and bound: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x = 0 \<Longrightarrow> x < 2 ^ k"
      and one: "\<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0"
  shows "dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) (0, 2 ^ k)"
proof -
  let ?P = "map_poly of_int (Poly xs) :: real poly"
  \<comment> \<open>\<^bold>\<open>\<open>ripoly\<close> is an abbreviation\<close>: \<open>ripoly p x\<close> is \<open>poly (map_poly of_int p) x\<close>, so there is no
     \<open>ripoly_def\<close> and no bridging step. A reflexive bridging lemma is useless as a rewrite and sends
     \<open>auto\<close> into a long search on the set equality below, so everything is written in one form,
     \<open>poly ?P\<close>.\<close>
  have setseq: "{x::real. 0 < x \<and> x < 2 ^ k \<and> poly ?P x = 0}
                  = {x::real. 0 < x \<and> poly ?P x = 0}"
    using bound by auto
  from one obtain r where r: "0 < r \<and> poly ?P r = 0"
    and uniq: "\<And>y::real. 0 < y \<and> poly ?P y = 0 \<Longrightarrow> y = r" by blast
  have "{x::real. 0 < x \<and> poly ?P x = 0} = {r}" using r uniq by blast
  hence "card {x::real. 0 < x \<and> x < 2 ^ k \<and> poly ?P x = 0} = 1" using setseq by simp
  hence "roots_in ?P 0 (2 ^ k) = 1"
    using roots_in_eq_card[OF rsquarefree_of_pre[OF sf]] by simp
  moreover have "(0::real) < 2 ^ k" by simp
  ultimately show ?thesis unfolding dsc_pair_ok_def by simp
qed

text \<open>And the empty case: an arm with NO positive root emits nothing, and the coverage clause is
  then vacuous.\<close>
lemma lowdeg_no_pos_root_covers:
  assumes none: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x \<noteq> 0"
  shows "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
          (\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
            \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)"
  using none by blast

text \<open>Coverage for the one-root case: the single positive root lies in the emitted window,
  because the bound is above it and \<open>0\<close> is below it.\<close>
lemma lowdeg_bound_window_covers:
  fixes k :: nat
  assumes bound: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x = 0 \<Longrightarrow> x < 2 ^ k"
  shows "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
           (fst ((0, 2 ^ k) :: real \<times> real) \<le> x \<and> x \<le> snd ((0, 2 ^ k) :: real \<times> real))"
  using bound by (auto intro: less_imp_le)

section \<open>3. The implementation's INTEGER discriminants are the mathematics' REAL ones\<close>

text \<open>\<open>Lowdeg_Math\<close> is stated over plain reals; the implementation computes over \<open>int\<close>.  These
  are the \<open>of_int\<close> homomorphism, and nothing more --- but they are what lets a sign test on an
  \<open>mpz\<close> stand in for a statement about real root counts.\<close>

lemma poly_of_int_Poly_deg2:
  fixes xs :: "int list"
  assumes len: "length xs = 3"
  shows "ripoly (Poly xs) (x::real)
           = of_int (xs!2) * x\<^sup>2 + of_int (xs!1) * x + of_int (xs!0)"
proof -
  \<comment> \<open>\<open>length_Suc_conv\<close> is the idiom for turning a known length into an explicit list; there is
     no \<open>list_3_cases\<close>.  \<open>eval_nat_numeral\<close> is what puts \<open>3\<close> into \<open>Suc\<close> form for it.\<close>
  from len obtain c b a where xs: "xs = [c, b, a]"
    by (auto simp: length_Suc_conv eval_nat_numeral)
  show ?thesis unfolding xs
    by (simp add: poly_altdef coeff_map_poly degree_Poly map_poly_degree_leq
                  power2_eq_square algebra_simps nth_default_def)
qed

lemma poly_of_int_Poly_deg3:
  fixes xs :: "int list"
  assumes len: "length xs = 4"
  shows "ripoly (Poly xs) (x::real)
           = cub (of_int (xs!3)) (of_int (xs!2)) (of_int (xs!1)) (of_int (xs!0)) x"
proof -
  from len obtain d c b a where xs: "xs = [d, c, b, a]"
    by (auto simp: length_Suc_conv eval_nat_numeral)
  show ?thesis unfolding xs
    by (simp add: poly_altdef coeff_map_poly degree_Poly map_poly_degree_leq
                  power2_eq_square power3_eq_cube algebra_simps nth_default_def)
qed

lemma disc3_of_int:
  fixes a b c d :: int
  shows "disc3 (of_int a) (of_int b) (of_int c) (of_int d)
           = of_int (lowdeg_disc3_int a b c d)"
  \<comment> \<open>\<open>disc3\<close> is written with POWERS and \<open>lowdeg_disc3_int\<close> with repeated multiplication --- the
     implementation has no \<open>mpz_pow\<close> and builds \<open>b\<^sup>3\<close> as \<open>b*b*b\<close> --- so the two normal forms only
     meet once the powers are expanded.\<close>
  by (simp add: disc3_def lowdeg_disc3_int_def power2_eq_square power3_eq_cube algebra_simps)

text \<open>\<open>of_int\<close> transports a strict sign; spelled out because \<open>simp\<close> otherwise pushes \<open>of_int\<close>
  through the products on one side only and then cannot match the integer hypothesis.\<close>
lemma of_int_neg_real: "(x::int) < 0 \<Longrightarrow> (of_int x :: real) < 0" by simp

lemma disc2_of_int:
  fixes a b c :: int
  shows "disc2 (of_int a) (of_int b) (of_int c) = of_int (b * b - 4 * (a * c))"
  by (simp add: disc2_def power2_eq_square algebra_simps)

section \<open>4. From a class code to a root structure\<close>

text \<open>Each emitting class of @{const lowdeg_class_monadic} asserts a root structure, and this
  section is what makes each such assertion true.  Every one is a consequence of \<open>Lowdeg_Math\<close>
  together with \<section>3's bridges --- no new analysis.\<close>

lemma lowdeg_deg3_one_pos_root:
  fixes xs :: "int list"
  assumes len: "length xs = 4" and a: "xs!3 \<noteq> 0"
      and D: "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0"
      and sg: "xs!3 * xs!0 < 0"
  shows "\<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0"
proof -
  let ?a = "of_int (xs!3) :: real" and ?b = "of_int (xs!2) :: real"
  let ?c = "of_int (xs!1) :: real" and ?d = "of_int (xs!0) :: real"
  have anz: "?a \<noteq> 0" using a by simp
  have Dr: "disc3 ?a ?b ?c ?d < 0" unfolding disc3_of_int by (rule of_int_neg_real[OF D])
  from cubic_neg_disc_unique[OF anz Dr] obtain r
    where r: "cub ?a ?b ?c ?d r = 0"
      and uq: "\<And>y. cub ?a ?b ?c ?d y = 0 \<Longrightarrow> y = r" by blast
  have adr: "?a * ?d < 0" using sg by (simp flip: of_int_mult)
  have rpos: "0 < r" by (rule cubic_root_sign_pos[OF anz Dr r adr])
  show ?thesis
  proof (rule ex1I[of _ r])
    show "0 < r \<and> ripoly (Poly xs) r = 0"
      using rpos r by (simp add: poly_of_int_Poly_deg3[OF len])
  next
    fix y :: real assume "0 < y \<and> ripoly (Poly xs) y = 0"
    thus "y = r" using uq by (simp add: poly_of_int_Poly_deg3[OF len])
  qed
qed

lemma lowdeg_deg3_no_pos_root:
  fixes xs :: "int list"
  assumes len: "length xs = 4" and a: "xs!3 \<noteq> 0"
      and D: "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0"
      and sg: "\<not> (xs!3 * xs!0 < 0)"
  shows "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x \<noteq> 0"
proof -
  fix x :: real assume xpos: "0 < x"
  let ?a = "of_int (xs!3) :: real" and ?b = "of_int (xs!2) :: real"
  let ?c = "of_int (xs!1) :: real" and ?d = "of_int (xs!0) :: real"
  have anz: "?a \<noteq> 0" using a by simp
  have Dr: "disc3 ?a ?b ?c ?d < 0" unfolding disc3_of_int by (rule of_int_neg_real[OF D])
  show "ripoly (Poly xs) x \<noteq> 0"
  proof
    assume z: "ripoly (Poly xs) x = 0"
    hence cz: "cub ?a ?b ?c ?d x = 0" by (simp add: poly_of_int_Poly_deg3[OF len])
    show False
    proof (cases "xs!0 = 0")
      case True
      hence "x = 0" using cubic_root_zero_of_zero_d[OF anz Dr cz] by simp
      thus False using xpos by simp
    next
      case False
      hence "0 < xs!3 * xs!0" using sg a by (simp add: not_less order_le_less)
      hence "0 < ?a * ?d" by (simp flip: of_int_mult)
      from cubic_root_sign_neg[OF anz Dr cz this] show False using xpos by simp
    qed
  qed
qed

lemma lowdeg_deg2_no_real_root:
  fixes xs :: "int list"
  assumes len: "length xs = 3" and a: "xs!2 \<noteq> 0"
      and D: "(xs!1) * (xs!1) - 4 * ((xs!2) * (xs!0)) < 0"
  shows "\<And>x::real. ripoly (Poly xs) x \<noteq> 0"
proof -
  fix x :: real
  let ?a = "of_int (xs!2) :: real" and ?b = "of_int (xs!1) :: real"
  let ?c = "of_int (xs!0) :: real"
  have anz: "?a \<noteq> 0" using a by simp
  have Dr: "disc2 ?a ?b ?c < 0" unfolding disc2_of_int by (rule of_int_neg_real[OF D])
  from quad_no_real_root[OF anz Dr, of x]
  show "ripoly (Poly xs) x \<noteq> 0" by (simp add: poly_of_int_Poly_deg2[OF len])
qed

text \<open>\<^bold>\<open>The degree-2 STRADDLING class (code \<open>4\<close>), and why it needs no reflection argument.\<close>
  \<open>refl_list\<close> negates the ODD-index coefficients, so a quadratic's \<open>a\<^sub>2\<close> and \<open>a\<^sub>0\<close> are untouched and
  \<open>a\<^sub>2*a\<^sub>0 < 0\<close> holds of \<open>refl_list xs\<close> exactly when it holds of \<open>xs\<close>.  The one lemma below
  therefore serves BOTH arms, applied to \<open>xs\<close> and to \<open>refl_list xs\<close> --- which is the formal
  counterpart of the implementation's decision to classify once for both arms.\<close>
lemma lowdeg_deg2_one_pos_root:
  fixes xs :: "int list"
  assumes len: "length xs = 3" and a: "xs!2 \<noteq> 0" and ac: "xs!2 * xs!0 < 0"
  shows "\<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0"
proof -
  let ?a = "of_int (xs!2) :: real" and ?b = "of_int (xs!1) :: real"
  let ?c = "of_int (xs!0) :: real"
  have anz: "?a \<noteq> 0" using a by simp
  have acr: "?a * ?c < 0" using ac by (simp flip: of_int_mult)
  have D: "0 < disc2 ?a ?b ?c" and prod: "qroot ?a ?b ?c True * qroot ?a ?b ?c False < 0"
    using quad_straddles_zero[OF anz acr] by auto
  have ev: "\<And>x::real. (ripoly (Poly xs) x = 0) = (?a * x\<^sup>2 + ?b * x + ?c = 0)"
    by (simp add: poly_of_int_Poly_deg2[OF len])
  \<comment> \<open>exactly one of the two roots is positive, and every root is one of the two\<close>
  from prod have "(0 < qroot ?a ?b ?c True \<and> qroot ?a ?b ?c False < 0)
                \<or> (qroot ?a ?b ?c True < 0 \<and> 0 < qroot ?a ?b ?c False)"
    by (simp add: mult_less_0_iff)
  then obtain rp rn where rp: "0 < rp" and rn: "rn < 0"
    and both: "{qroot ?a ?b ?c True, qroot ?a ?b ?c False} = {rp, rn}"
    by blast
  have rp_mem: "rp \<in> {qroot ?a ?b ?c True, qroot ?a ?b ?c False}" using both by auto
  have isroot: "?a * rp\<^sup>2 + ?b * rp + ?c = 0"
    using qroot_is_root[OF anz less_imp_le[OF D]] rp_mem by auto
  show ?thesis
  proof (rule ex1I[of _ rp])
    show "0 < rp \<and> ripoly (Poly xs) rp = 0" using rp isroot by (simp add: ev)
  next
    fix y :: real assume y: "0 < y \<and> ripoly (Poly xs) y = 0"
    hence "?a * y\<^sup>2 + ?b * y + ?c = 0" by (simp add: ev)
    from quad_root_is_qroot[OF anz less_imp_le[OF D] this]
    have "y \<in> {qroot ?a ?b ?c True, qroot ?a ?b ?c False}" by simp
    hence "y = rp \<or> y = rn" using both by blast
    thus "y = rp" using y rn by auto
  qed
qed

lemma lowdeg_deg2_refl_indices:
  fixes xs :: "int list"
  assumes len: "length xs = 3"
  shows "length (refl_list xs) = 3" and "refl_list xs ! 2 = xs ! 2"
    and "refl_list xs ! 0 = xs ! 0"
  using len by (simp_all add: nth_refl_list)

text \<open>\<^bold>\<open>The degree-2 SAME-SIGN class (codes \<open>5\<close>/\<open>6\<close>), stated over a REAL separator.\<close>  This is the
  only case emitting two windows.  The runtime check @{const lowdeg_sep_ok_monadic} establishes
  \<open>a * P t < 0\<close> for the dyadic \<open>t\<close> it computed, and \<open>quad_separator\<close> turns that into "\<open>t\<close> lies
  strictly between the two roots" --- so each half of the box then holds exactly one.  Keeping the
  statement over an arbitrary real \<open>t\<close> is deliberate: it makes the fact independent of HOW the
  implementation chose \<open>t\<close>, which is what lets the grid exponent stay a tunable constant.\<close>
lemma lowdeg_deg2_two_windows:
  fixes xs :: "int list" and t :: real and k :: nat
  assumes len: "length xs = 3" and a: "xs!2 \<noteq> 0"
      and sf: "square_free (map_poly of_int (Poly xs) :: real poly)"
      and sep: "of_int (xs!2) * (of_int (xs!2) * t\<^sup>2 + of_int (xs!1) * t + of_int (xs!0)) < (0::real)"
      \<comment> \<open>\<^bold>\<open>No \<open>0 < t\<close> hypothesis\<close>: \<open>pos\<close> puts the lower root above zero and the separator puts \<open>t\<close> above
         that. Requiring it would force the emission site to re-derive this from a \<open>q\<close> whose sign
         the runtime check says nothing about.\<close>
      and bound: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x = 0 \<Longrightarrow> x < 2 ^ k"
      and pos: "\<And>x::real. ripoly (Poly xs) x = 0 \<Longrightarrow> 0 < x"
  shows "dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) (0, t)"
    and "dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) (t, 2 ^ k)"
proof -
  let ?P = "map_poly of_int (Poly xs) :: real poly"
  let ?a = "of_int (xs!2) :: real" and ?b = "of_int (xs!1) :: real"
  let ?c = "of_int (xs!0) :: real"
  have anz: "?a \<noteq> 0" using a by simp
  have ev: "\<And>x::real. poly ?P x = ?a * x\<^sup>2 + ?b * x + ?c"
    using poly_of_int_Poly_deg2[OF len] by simp
  \<comment> \<open>the separator condition in the division-free coordinate\<close>
  have sq: "(2*?a*t + ?b)\<^sup>2 - disc2 ?a ?b ?c = 4*?a*(?a*t\<^sup>2 + ?b*t + ?c)"
    by (rule quad_square_id)
  have lt: "(2*?a*t + ?b)\<^sup>2 < disc2 ?a ?b ?c" using sq sep by simp
  from quad_separator[OF anz lt]
  have D: "0 < disc2 ?a ?b ?c"
    and betw: "(t - qroot ?a ?b ?c True) * (t - qroot ?a ?b ?c False) < 0" by auto
  from betw have "(qroot ?a ?b ?c True < t \<and> t < qroot ?a ?b ?c False)
                \<or> (qroot ?a ?b ?c False < t \<and> t < qroot ?a ?b ?c True)"
    by (auto simp: mult_less_0_iff)
  then obtain rlo rhi where lo: "rlo < t" and hi: "t < rhi"
    and both: "{qroot ?a ?b ?c True, qroot ?a ?b ?c False} = {rlo, rhi}" by blast
  have rootset: "\<And>y::real. (poly ?P y = 0) = (y = rlo \<or> y = rhi)"
  proof -
    fix y :: real
    show "(poly ?P y = 0) = (y = rlo \<or> y = rhi)"
    proof
      assume "poly ?P y = 0"
      hence "?a * y\<^sup>2 + ?b * y + ?c = 0" by (simp add: ev)
      from quad_root_is_qroot[OF anz less_imp_le[OF D] this] both show "y = rlo \<or> y = rhi"
        by blast
    next
      assume "y = rlo \<or> y = rhi"
      hence "y \<in> {qroot ?a ?b ?c True, qroot ?a ?b ?c False}" using both by blast
      thus "poly ?P y = 0"
        using qroot_is_root[OF anz less_imp_le[OF D]] by (auto simp: ev)
    qed
  qed
  have rlo_pos: "0 < rlo" using pos rootset by simp
  have rhi_lt: "rhi < 2 ^ k" using bound pos rootset by simp
  have rsf: "rsquarefree ?P" by (rule rsquarefree_of_pre[OF sf])
  show "dsc_pair_ok ?P (0, t)"
  proof -
    have "{x::real. 0 < x \<and> x < t \<and> poly ?P x = 0} = {rlo}"
      using rootset rlo_pos lo hi by auto
    hence "roots_in ?P 0 t = 1" using roots_in_eq_card[OF rsf] by simp
    thus ?thesis unfolding dsc_pair_ok_def using rlo_pos lo by simp
  qed
  show "dsc_pair_ok ?P (t, 2 ^ k)"
  proof -
    have "{x::real. t < x \<and> x < 2 ^ k \<and> poly ?P x = 0} = {rhi}"
      using rootset hi lo rhi_lt by auto
    hence "roots_in ?P t (2 ^ k) = 1" using roots_in_eq_card[OF rsf] by simp
    thus ?thesis unfolding dsc_pair_ok_def using hi rhi_lt by simp
  qed
qed

section \<open>4b. The reflected arm's data, in \<open>xs\<close>'s own vocabulary\<close>

text \<open>\<^bold>\<open>Why the implementation may classify ONCE for BOTH arms.\<close>  \<open>Lowdeg_Split.thy\<close> computes each
  discriminant a single time and reads both arms off it, and that is sound for exactly one
  reason: the discriminants are INVARIANT under \<open>x \<mapsto> -x\<close> while the SIGN PRODUCT that picks the
  arm FLIPS.  These lemmas are that statement.  Getting them wrong would not fail a build --- it
  would silently classify the reflected arm by the positive arm's root count.\<close>

lemma lowdeg_deg3_refl_indices:
  fixes xs :: "int list"
  assumes len: "length xs = 4"
  shows "length (refl_list xs) = 4"
    and "refl_list xs ! 3 = - (xs ! 3)"
    and "refl_list xs ! 2 = xs ! 2"
    and "refl_list xs ! 1 = - (xs ! 1)"
    and "refl_list xs ! 0 = xs ! 0"
  using len by (simp_all add: nth_refl_list)

text \<open>\<open>\<Delta>\<close> is invariant: \<open>(a,b,c,d) \<mapsto> (-a,b,-c,d)\<close> fixes every one of the five monomials
  (\<open>18abcd\<close>, \<open>-4b\<^sup>3d\<close>, \<open>b\<^sup>2c\<^sup>2\<close>, \<open>-4ac\<^sup>3\<close>, \<open>-27a\<^sup>2d\<^sup>2\<close>) --- each carries \<open>a\<close> and \<open>c\<close> at total
  even degree.\<close>
lemma lowdeg_disc3_int_refl:
  fixes a b c d :: int
  shows "lowdeg_disc3_int (- a) b (- c) d = lowdeg_disc3_int a b c d"
  by (simp add: lowdeg_disc3_int_def algebra_simps)

text \<open>Squarefreeness transfers through the reflection because \<open>x \<mapsto> -x\<close> is a degree-1 map ---
  the same @{thm [source] square_free_pcompose_linear} step the bisection solver's negative half
  uses, at \<open>c = -1\<close>.\<close>
lemma square_free_refl_list:
  fixes xs :: "int list"
  assumes sf: "square_free (map_poly of_int (Poly xs) :: real poly)"
  shows "square_free (map_poly of_int (Poly (refl_list xs)) :: real poly)"
  using square_free_pcompose_linear[OF sf, of "- 1"]
  by (simp add: Poly_refl_list_eq_pcompose)

text \<open>\<^bold>\<open>What the closed-form arms actually read off the precondition.\<close> Everything below
  except the bisection fall-through takes only this: the input's shape, squarefreeness, and that
  the exponent the root bound computes fits a machine word against the length. It is implied by
  @{const dsc_isolate_all_split_pre} and by the exported solver's weaker bundle, which lacks
  @{const split_cap}'s exponential clause, so both can reuse these lemmas.\<close>

definition lowdeg_basic_pre :: "int list \<Rightarrow> bool" where
"lowdeg_basic_pre xs \<longleftrightarrow>
  2 \<le> length xs \<and> last xs \<noteq> 0 \<and> kiou_headroom xs \<and>
  coeffs (Poly xs) = xs \<and>
  square_free (map_poly of_int (Poly xs) :: real poly) \<and>
  kiou_bound_k_monadic xs \<le> SPEC (\<lambda>k. k * length xs < max_snat LENGTH(gmp_poly_len)) \<and>
  kiou_bound_k_monadic (refl_list xs) \<le> SPEC (\<lambda>k. k * length (refl_list xs) < max_snat LENGTH(gmp_poly_len))"

lemma dsc_isolate_all_split_pre_basic:
  assumes "dsc_isolate_all_split_pre xs"
  shows "lowdeg_basic_pre xs"
  using assms unfolding dsc_isolate_all_split_pre_def lowdeg_basic_pre_def
  by (auto elim!: order_trans intro!: SPEC_rule simp: split_cap_def)

lemma kiou_bound_k_monadic_spec_kcap:
  fixes ys :: "int list"
  assumes len2: "2 \<le> length ys" and lastnz: "last ys \<noteq> 0"
    and hr: "kiou_headroom ys"
    and capK: "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k. k * length ys < max_snat LENGTH(gmp_poly_len))"
  shows "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k.
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k) \<and>
      k * length ys < max_snat LENGTH(gmp_poly_len) \<and> k < max_snat LENGTH(gmp_poly_len))"
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
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k)
      \<and> k * length ys < max_snat LENGTH(gmp_poly_len))"
    by (rule kiou_le_SPEC_conj[OF kiou_bound_k_monadic_sound[OF len2 lastnz hr] capK])
  show ?thesis
    by (rule order_trans[OF both]) (use kcap in auto)
qed

text \<open>The precondition, unpacked for BOTH arms at once.  Every conjunct on the reflected side is
  either already in the bundle (the \<open>split_cap\<close> clause) or transported by a named lemma; keeping
  them together is what lets \<section>5's two arms be literally the same lemma applied twice.\<close>
lemma lowdeg_arm_pre:
  fixes xs :: "int list"
  assumes pre: "lowdeg_basic_pre xs"
  shows "2 \<le> length xs" and "last xs \<noteq> 0" and "kiou_headroom xs"
    and "kiou_bound_k_monadic xs \<le> SPEC (\<lambda>k. k * length xs < max_snat LENGTH(gmp_poly_len))"
    and "square_free (map_poly of_int (Poly xs) :: real poly)"
    and "2 \<le> length (refl_list xs)" and "last (refl_list xs) \<noteq> 0"
    and "kiou_headroom (refl_list xs)"
    and "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (\<lambda>k. k * length (refl_list xs) < max_snat LENGTH(gmp_poly_len))"
    and "square_free (map_poly of_int (Poly (refl_list xs)) :: real poly)"
proof -
  from pre show len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0" and hr: "kiou_headroom xs"
    and capY: "kiou_bound_k_monadic xs \<le> SPEC (\<lambda>k. k * length xs < max_snat LENGTH(gmp_poly_len))"
    and sf: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (\<lambda>k. k * length (refl_list xs) < max_snat LENGTH(gmp_poly_len))"
    unfolding lowdeg_basic_pre_def by auto
  have xsne: "xs \<noteq> []" using len2 by (cases xs) auto
  show "2 \<le> length (refl_list xs)" using len2 by simp
  show "last (refl_list xs) \<noteq> 0" using last_refl_list_nz[OF xsne lastnz] .
  show "kiou_headroom (refl_list xs)" using kiou_headroom_refl_list[of xs] hr by simp
  show "square_free (map_poly of_int (Poly (refl_list xs)) :: real poly)"
    by (rule square_free_refl_list[OF sf])
qed
text \<open>Index \<open>1\<close> too --- the only coefficient the reflection actually moves at degree 2.\<close>
lemma lowdeg_deg2_refl_idx1:
  fixes xs :: "int list"
  assumes len: "length xs = 3"
  shows "refl_list xs ! 1 = - (xs ! 1)"
  using len by (simp add: nth_refl_list)


text \<open>\<^bold>\<open>The same-sign case's two root-structure facts, at the LIST level.\<close>  Both are
  @{thm [source] quad_both_pos} / @{thm [source] quad_both_neg} composed with \S3's bridges, in
  the same shape \S4's other classes use.  The emitting one is stated as "every root is
  positive", not "there are exactly two": that is what
  @{thm [source] lowdeg_deg2_two_windows} consumes, and it is also true when the two roots
  coincide --- which squarefreeness excludes, but the lemma need not know that.\<close>
lemma lowdeg_deg2_both_pos:
  fixes xs :: "int list"
  assumes len: "length xs = 3" and a: "xs!2 \<noteq> 0"
    and D: "0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)"
    and ac: "0 < xs!2 * xs!0" and ab: "xs!2 * xs!1 < 0"
  shows "\<And>x::real. ripoly (Poly xs) x = 0 \<Longrightarrow> 0 < x"
proof -
  fix x :: real assume rx: "ripoly (Poly xs) x = 0"
  let ?a = "of_int (xs!2) :: real" and ?b = "of_int (xs!1) :: real"
  let ?c = "of_int (xs!0) :: real"
  have anz: "?a \<noteq> 0" using a by simp
  \<comment> \<open>\<^bold>\<open>Cross into the reals with \<open>simp only:\<close>, never plain \<open>simp\<close>.\<close>  \<open>of_int_mult\<close>/\<open>of_int_diff\<close>
     are default simp rules, so a bare \<open>simp\<close> DISTRIBUTES \<open>of_int (b*b - 4*(a*c))\<close> into a real
     expression and then has no rule left to connect it to the integer premise --- the goal it
     leaves looks trivial and is not (it was the whole failure at this line).  Finishing the
     comparison in \<open>int\<close> first and crossing with a single-rule rewrite keeps both sides folded.\<close>
  have Dz: "(0::int) \<le> xs!1 * xs!1 - 4 * (xs!2 * xs!0)" using D by linarith
  have Dr: "0 \<le> disc2 ?a ?b ?c"
    unfolding disc2_of_int using Dz by (simp only: of_int_0_le_iff)
  have acr: "0 < ?a * ?c" using ac by (simp flip: of_int_mult)
  have abr: "?a * ?b < 0" using ab by (simp flip: of_int_mult)
  have "?a * x\<^sup>2 + ?b * x + ?c = 0" using rx by (simp add: poly_of_int_Poly_deg2[OF len])
  from quad_root_is_qroot[OF anz Dr this]
  have "x \<in> {qroot ?a ?b ?c True, qroot ?a ?b ?c False}" by simp
  thus "0 < x" using quad_both_pos[OF anz Dr acr abr] by auto
qed

lemma lowdeg_deg2_no_pos_root:
  fixes xs :: "int list"
  assumes len: "length xs = 3" and a: "xs!2 \<noteq> 0"
    and D: "0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)"
    and ac: "0 < xs!2 * xs!0" and ab: "0 < xs!2 * xs!1"
  shows "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x \<noteq> 0"
\<comment> \<open>\<^bold>\<open>The conclusion is a NEGATION and must be proved as one.\<close>  Assuming \<open>ripoly \<dots> = 0\<close> at the
   \<open>fix\<close>/\<open>assume\<close> level and deriving \<open>False\<close> proves nothing here: that premise is not part of the
   goal, so the \<open>thus False\<close> reports \<^bold>\<open>Failed to refine any pending goal\<close> --- an error that reads
   like a broken tactic and is a broken STATEMENT.  \<open>rule notI\<close> introduces it properly.\<close>
proof -
  fix x :: real assume xp: "0 < x"
  let ?a = "of_int (xs!2) :: real" and ?b = "of_int (xs!1) :: real"
  let ?c = "of_int (xs!0) :: real"
  have anz: "?a \<noteq> 0" using a by simp
  have Dz: "(0::int) \<le> xs!1 * xs!1 - 4 * (xs!2 * xs!0)" using D by linarith
  have Dr: "0 \<le> disc2 ?a ?b ?c"
    unfolding disc2_of_int using Dz by (simp only: of_int_0_le_iff)
  have acr: "0 < ?a * ?c" using ac by (simp flip: of_int_mult)
  have abr: "0 < ?a * ?b" using ab by (simp flip: of_int_mult)
  show "ripoly (Poly xs) x \<noteq> 0"
  proof (rule notI)
    assume rx: "ripoly (Poly xs) x = 0"
    have "?a * x\<^sup>2 + ?b * x + ?c = 0" using rx by (simp add: poly_of_int_Poly_deg2[OF len])
    from quad_root_is_qroot[OF anz Dr this]
    have "x \<in> {qroot ?a ?b ?c True, qroot ?a ?b ?c False}" by simp
    thus False using quad_both_neg[OF anz Dr acr abr] xp by auto
  qed
qed

text \<open>\<^bold>\<open>The \<open>rf\<close> flag IS the reflection.\<close>  The implementation runs the separator check on the
  ORIGINAL array with \<open>rf = True\<close> rather than cloning; the emitting arm then runs it on the
  CLONE with \<open>rf = False\<close>.  This says those two computations agree, so the class-6 branch may
  check one and emit from the other.  Both sides are the same integer expression once
  \<open>refl_list\<close>'s index-1 sign flip is unfolded.\<close>
lemma lowdeg_sep_ok_pure_refl:
  fixes xs :: "int list"
  assumes len: "length xs = 3"
  shows "lowdeg_sep_ok_pure True xs = lowdeg_sep_ok_pure False (refl_list xs)"
proof -
  note ri = lowdeg_deg2_refl_indices[OF len] lowdeg_deg2_refl_idx1[OF len]
  have q: "lowdeg_sep_q False lowdeg_sep_j (refl_list xs) = lowdeg_sep_q True lowdeg_sep_j xs"
    unfolding lowdeg_sep_q_def using ri by simp
  show ?thesis
    unfolding lowdeg_sep_ok_pure_def lowdeg_sep_W_def
    using ri q by simp
qed


section \<open>5. Emission: the single-window case\<close>

text \<open>When the arm has exactly one positive root the Kioustelidis bound IS the isolating
  window, so emission is one \<open>2\<^sup>k\<close> and one push.  When it has none it is the empty vector.
  The two lemmas below are the monadic counterpart of \<section>2's workhorse.

  \<^bold>\<open>The one place the rational/real frontier is crossed.\<close>  @{const dyadic_interval_vec_to_list}
  yields a pair of RATIONALS while @{const dsc_pair_ok} speaks of a pair of REALS, and the SPEC
  asks for a \<open>J\<close> with \<open>I = real_to_rat_pair J\<close>.  For the window this entry emits both sides are
  \<open>0\<close> and \<open>2\<^sup>k\<close>, so the crossing is exact and needs no approximation argument --- which is
  precisely why the emitted endpoints are a dyadic with exponent \<open>0\<close>.\<close>

lemma dyadic_triple_zero_pow2:
  fixes k :: nat
  shows "dyadic_interval_of_triple (((0::int), 2 ^ k), 0) = ((0, 2 ^ k) :: rat \<times> rat)"
  by (simp add: dyadic_interval_of_triple_def dyadic_rat_def)

lemma real_to_rat_pair_zero_pow2:
  fixes k :: nat
  shows "real_to_rat_pair ((0, 2 ^ k) :: real \<times> real) = ((0, 2 ^ k) :: rat \<times> rat)"
  \<comment> \<open>Normalise the FACT toward the goal, never the goal toward the fact: rewriting
     \<open>(0, 2\<^sup>k)\<close> into \<open>of_rat\<close> form leaves \<open>simp\<close> free to collapse \<open>of_rat 0\<close> straight
     back (\<open>2\<^sup>k = real_of_rat (2\<^sup>k)\<close>).\<close>
  using real_to_rat_pair_of_rat[of 0 "(2::rat) ^ k"]
  by (simp add: of_rat_power)

text \<open>An empty accumulator is pushable.  \<open>1 < max_snat\<close> comes from the caller's own length
  headroom rather than from a numeral fact about the word type, so this stays independent of
  \<open>gmp_poly_len\<close>.\<close>
lemma dyadic_vec_empty_pushable:
  assumes invar: "dyadic_interval_vec_invar acc"
    and empty: "dyadic_interval_vec_triples acc = []"
    and room: "(1::nat) < max_snat LENGTH(gmp_poly_len)"
  shows "dyadic_interval_vec_pushable acc"
proof -
  obtain lns rns ks where acc: "acc = (lns, rns, ks)" by (cases acc)
  from invar acc have eqlen: "length lns = length rns" "length lns = length ks"
    unfolding dyadic_interval_vec_invar_def by auto
  from empty acc have "zip (zip lns rns) ks = []"
    unfolding dyadic_interval_vec_triples_def by simp
  hence "lns = []" using eqlen by (cases lns; cases rns; cases ks) auto
  thus ?thesis using acc eqlen room unfolding dyadic_interval_vec_pushable_def by simp
qed

text \<open>The push, specialised to the one window this entry ever emits.\<close>
lemma lowdeg_push_one_window:
  fixes k :: nat
  assumes invar: "dyadic_interval_vec_invar acc"
    and push: "dyadic_interval_vec_pushable acc"
    and empty: "dyadic_interval_vec_to_list acc = []"
  shows "dyadic_interval_vec_push_monadic acc 0 (2 ^ k) 0
           \<le> SPEC (\<lambda>v. dyadic_interval_vec_to_list v
                          = [real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)])"
proof -
  obtain lns rns ks where acc: "acc = (lns, rns, ks)" by (cases acc)
  show ?thesis
    unfolding acc
    apply (rule order_trans[OF dyadic_interval_vec_push_monadic_spec])
    using invar push empty acc
    by (auto simp: dyadic_triple_zero_pow2 real_to_rat_pair_zero_pow2)
qed

text \<open>\<^bold>\<open>The emitted list MEETS the SPEC.\<close>  Both existential witnesses --- the \<open>J\<close> of the
  isolation clause and the \<open>I\<close>/\<open>J\<close> of the coverage clause --- are the same \<open>(0, 2\<^sup>k)\<close>, and
  supplying them here rather than hoping \<open>auto\<close> guesses them is what keeps the emission proof a
  one-line closer.  It also states the root bound in the \<open>\<forall>\<close>/\<open>\<longrightarrow>\<close> form the Kioustelidis
  \<open>SPEC\<close> actually delivers, rather than \<section>2's meta form.\<close>
lemma lowdeg_one_window_spec:
  fixes ys :: "int list" and k :: nat
  assumes sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and bound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k"
    and one: "\<exists>!x::real. 0 < x \<and> ripoly (Poly ys) x = 0"
    and lst: "dyadic_interval_vec_to_list acc
                = [real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)]"
  shows "(\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
            \<exists>J. I = real_to_rat_pair J \<and>
                dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) J) \<and>
         (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
               \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))"
proof (intro conjI ballI allI impI)
  fix I assume "I \<in> set (dyadic_interval_vec_to_list acc)"
  hence I: "I = real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)" using lst by simp
  have ok: "dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) (0, 2 ^ k)"
    using lowdeg_bound_window_isolates[OF sf _ one] bound by blast
  show "\<exists>J. I = real_to_rat_pair J \<and>
             dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) J"
    using I ok by blast
next
  fix x :: real assume xp: "0 < x" and xr: "ripoly (Poly ys) x = 0"
  have xlt: "x < 2 ^ k" using bound xp xr by blast
  have "real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)
          \<in> set (dyadic_interval_vec_to_list acc)" using lst by simp
  moreover have "fst ((0, 2 ^ k) :: real \<times> real) \<le> x
                 \<and> x \<le> snd ((0, 2 ^ k) :: real \<times> real)"
    using xp xlt by simp
  ultimately show "\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
                     \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J" by blast
qed

text \<open>\<^bold>\<open>The same fact in the two shapes \<open>refine_vcg\<close> actually asks for.\<close>  It splits the SPEC's
  conjunction into two goals, so a lemma proving the CONJUNCTION matches NEITHER half as an
  intro rule --- the coverage half was left open by exactly that.  The coverage form is stated
  POINTWISE (at the \<open>x\<close> the goal already fixed), not as the \<open>\<forall>x\<close> the SPEC carries.\<close>
lemma lowdeg_one_window_isolates_list:
  fixes ys :: "int list" and k :: nat
  assumes sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and bound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k"
    and one: "\<exists>!x::real. 0 < x \<and> ripoly (Poly ys) x = 0"
    and lst: "dyadic_interval_vec_to_list acc
                = [real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)]"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
            \<exists>J. I = real_to_rat_pair J \<and>
                dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) J"
  using lowdeg_one_window_spec[OF sf bound one lst] by blast

lemma lowdeg_one_window_covers_at:
  fixes ys :: "int list" and k :: nat and x :: real
  assumes bound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k"
    and lst: "dyadic_interval_vec_to_list acc
                = [real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)]"
    and xp: "0 < x" and xr: "ripoly (Poly ys) x = 0"
  shows "\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
           \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
proof -
  have xlt: "x < 2 ^ k" using bound xp xr by blast
  have "real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)
          \<in> set (dyadic_interval_vec_to_list acc)" using lst by simp
  moreover have "fst ((0, 2 ^ k) :: real \<times> real) \<le> x
                 \<and> x \<le> snd ((0, 2 ^ k) :: real \<times> real)" using xp xlt by simp
  ultimately show ?thesis by blast
qed

text \<open>\<^bold>\<open>The emitting arm.\<close>  Stated over a bare \<open>ys\<close> with the four bound-side hypotheses spelled
  out rather than over \<open>dsc_isolate_all_split_pre xs\<close>, because \<section>7 applies it TWICE --- once at
  \<open>xs\<close> and once at \<open>refl_list xs\<close> --- and only \<section>4b's transport makes the second application
  legal.  Taking the whole bundle instead would have forced a second, reflected bundle to exist.\<close>
lemma lowdeg_emit_pos_one_correct:
  fixes ys :: "int list"
  assumes len2: "2 \<le> length ys" and lastnz: "last ys \<noteq> 0"
    and hr: "kiou_headroom ys"
    and capY: "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k. k * length ys < max_snat LENGTH(gmp_poly_len))"
    and sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and one: "\<exists>!x::real. 0 < x \<and> ripoly (Poly ys) x = 0"
  shows "lowdeg_emit_pos_monadic True ys
           \<le> SPEC (\<lambda>acc.
                (\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
                   \<exists>J. I = real_to_rat_pair J \<and>
                       dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) J) \<and>
                (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow>
                   (\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
                      \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  have lenb: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have room: "(1::nat) < max_snat LENGTH(gmp_poly_len)" using len2 lenb by linarith
  have ysne: "ys \<noteq> []" using len2 by (cases ys) auto
  have len1: "1 \<le> length ys" using len2 by linarith
  show ?thesis
    unfolding lowdeg_emit_pos_monadic_def PR_CONST_def mpz_from_int_def
    apply (refine_vcg
        dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans]
        kiou_bound_k_monadic_spec_kcap[OF len2 lastnz hr capY, THEN order_trans]
        mpz_pow2_monadic_spec[THEN order_trans]
        lowdeg_push_one_window[THEN order_trans])
    \<comment> \<open>\<^bold>\<open>Order-INDEPENDENT closers.\<close>  \<open>refine_vcg\<close> emits these ASSERTs in an order the script
       cannot predict, so a positional \<open>subgoal\<close> chain is fragile.  Every closer below is
       wrapped in \<open>solves\<close>, so it fires only where it CLOSES a goal.\<close>
    apply (all \<open>(solves \<open>use len1 len2 lenb ysne room in auto\<close>)?\<close>)
    apply (all \<open>(solves \<open>use room in \<open>auto intro: dyadic_vec_empty_pushable\<close>\<close>)?\<close>)
    \<comment> \<open>Applied by \<open>rule\<close>, not offered to \<open>auto\<close> as \<open>intro!\<close>: \<open>auto\<close> first rewrites \<open>\<forall>I\<in>set [p]\<close> to
       \<open>P p\<close>, and would then have to guess the witness \<open>J = (0, 2\<^sup>k)\<close>.\<close>
    apply (all \<open>(solves \<open>rule lowdeg_one_window_isolates_list[OF sf _ one]; blast\<close>)?\<close>)
    apply (all \<open>(solves \<open>rule lowdeg_one_window_covers_at; blast\<close>)?\<close>)
    done
qed

text \<open>The non-emitting arm: the empty vector.  Both clauses are vacuous --- the first over an
  empty list, the second because the arm has no positive root at all.\<close>
lemma lowdeg_emit_pos_zero_correct:
  fixes ys :: "int list"
  assumes none: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly ys) x \<noteq> 0"
  shows "lowdeg_emit_pos_monadic False ys
           \<le> SPEC (\<lambda>acc.
                (\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
                   \<exists>J. I = real_to_rat_pair J \<and>
                       dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) J) \<and>
                (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow>
                   (\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
                      \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
  unfolding lowdeg_emit_pos_monadic_def PR_CONST_def
  apply (refine_vcg dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans]
      lowdeg_vec_empty_sz_monadic_spec[THEN order_trans])
  using none by auto

text \<open>\<^bold>\<open>The reflected arm is the positive arm, run on the clone.\<close>  \<open>lowdeg_emit_neg_monadic\<close>
  clones, reflects in place, and calls @{const lowdeg_emit_pos_monadic} --- so its correctness is
  @{thm [source] lowdeg_emit_pos_one_correct} at \<open>refl_list xs\<close>, with \<section>4b supplying the four
  bound-side hypotheses there.  The clone/reflect/free steps are discharged exactly as
  @{thm [source] bisection_isolate_all_split_neg_half} discharges its own.\<close>
lemma lowdeg_emit_neg_one_correct:
  fixes xs :: "int list"
  assumes pre: "lowdeg_basic_pre xs"
    and one: "\<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0"
  shows "lowdeg_emit_neg_monadic True xs
           \<le> SPEC (\<lambda>acc.
                (\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
                   \<exists>J. I = real_to_rat_pair J \<and>
                       dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
                (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
                   (\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
                      \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  note arm = lowdeg_arm_pre[OF pre]
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF arm(3)] by linarith
  have reflect: "poly_reflect_in_place_monadic xs \<le> RETURN (refl_list xs)"
    using poly_reflect_in_place_correct[OF lenb] by (simp add: refl_list_def)
  have body: "lowdeg_emit_pos_monadic True (refl_list xs)
      \<le> SPEC (\<lambda>acc.
           (\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
              \<exists>J. I = real_to_rat_pair J \<and>
                  dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
           (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
              (\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
                 \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
    by (rule lowdeg_emit_pos_one_correct[OF arm(6) arm(7) arm(8) arm(9) arm(10) one])
  show ?thesis
    unfolding lowdeg_emit_neg_monadic_def PR_CONST_def poly_free_monadic_def
    apply (refine_vcg
        poly_clone_monadic_correct[OF lenb, THEN order_trans]
        reflect[THEN order_trans]
        body[THEN order_trans])
    using lenb arm(1) by auto
qed

lemma lowdeg_emit_neg_zero_correct:
  fixes xs :: "int list"
  assumes pre: "lowdeg_basic_pre xs"
    and none: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
  shows "lowdeg_emit_neg_monadic False xs
           \<le> SPEC (\<lambda>acc.
                (\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
                   \<exists>J. I = real_to_rat_pair J \<and>
                       dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
                (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
                   (\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
                      \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
  unfolding lowdeg_emit_neg_monadic_def PR_CONST_def
  apply (refine_vcg dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans]
      lowdeg_vec_empty_sz_monadic_spec[THEN order_trans])
  using none by auto

section \<open>5b. Emission: the TWO-window case\<close>

text \<open>\<^bold>\<open>The one class that emits two windows.\<close>  Both roots are positive and the runtime check
  has certified a separator \<open>t = q/2\<^bsup>64\<^esup>\<close> strictly between them, so the arm returns \<open>[0, t]\<close> and
  \<open>[t, 2\<^sup>k]\<close>.  Everything analytic is already proved --- @{thm [source] lowdeg_deg2_two_windows}
  takes exactly the four facts the implementation has --- so this section is the MONADIC and
  RATIONAL bookkeeping: the push chain, and the dyadic triples at exponent \<open>64\<close>.

  \<^bold>\<open>Why the endpoints stay exact.\<close>  \S5's windows are \<open>0\<close> and \<open>2\<^sup>k\<close>, so its rational/real crossing
  is trivial.  Here the shared endpoint is \<open>q/2\<^bsup>64\<^esup>\<close>, still a DYADIC, so the crossing is still
  exact --- @{thm [source] real_to_rat_pair_of_rat} applies verbatim and no approximation
  argument appears anywhere in this file.\<close>

lemma dyadic_triple_zero_num:
  fixes q :: int and j :: nat
  shows "dyadic_interval_of_triple (((0::int), q), j) = ((0, rat_of_int q / 2 ^ j) :: rat \<times> rat)"
  by (simp add: dyadic_interval_of_triple_def dyadic_rat_def)

lemma dyadic_triple_num_pow2:
  fixes q :: int and j k :: nat
  shows "dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)
           = ((rat_of_int q / 2 ^ j, 2 ^ k) :: rat \<times> rat)"
  by (simp add: dyadic_interval_of_triple_def dyadic_rat_def power_add)

lemma real_to_rat_pair_zero_num:
  fixes q :: int and j :: nat
  shows "real_to_rat_pair ((0, of_int q / 2 ^ j) :: real \<times> real)
           = ((0, rat_of_int q / 2 ^ j) :: rat \<times> rat)"
  using real_to_rat_pair_of_rat[of 0 "rat_of_int q / 2 ^ j"]
  by (simp add: of_rat_divide of_rat_power)

lemma real_to_rat_pair_num_pow2:
  fixes q :: int and j k :: nat
  shows "real_to_rat_pair ((of_int q / 2 ^ j, 2 ^ k) :: real \<times> real)
           = ((rat_of_int q / 2 ^ j, 2 ^ k) :: rat \<times> rat)"
  using real_to_rat_pair_of_rat[of "rat_of_int q / 2 ^ j" "(2::rat) ^ k"]
  by (simp add: of_rat_divide of_rat_power)

text \<open>Pushability from the LENGTH alone.  \S5's @{thm [source] dyadic_vec_empty_pushable} is the
  \<open>0\<close> case of this; the two-window case pushes twice, so the second push needs it at length \<open>1\<close>.\<close>
lemma dyadic_vec_pushable_of_len:
  assumes invar: "dyadic_interval_vec_invar acc"
    and room: "length (dyadic_interval_vec_triples acc) + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "dyadic_interval_vec_pushable acc"
proof -
  obtain lns rns ks where acc: "acc = (lns, rns, ks)" by (cases acc)
  from invar acc have eqlen: "length lns = length rns" "length lns = length ks"
    unfolding dyadic_interval_vec_invar_def by auto
  have "length (dyadic_interval_vec_triples acc) = length lns"
    using acc eqlen unfolding dyadic_interval_vec_triples_def by simp
  thus ?thesis using room acc eqlen unfolding dyadic_interval_vec_pushable_def by simp
qed

text \<open>The push spec for an OPAQUE accumulator.  The library states it about an explicit
  \<open>(lns, rns, ks)\<close>, which \<open>refine_vcg\<close> cannot match against the schematic vector the first push
  returns; one \<open>cases\<close> here makes it usable twice in a row.\<close>
lemma dyadic_push_spec_any:
  assumes invar: "dyadic_interval_vec_invar acc" and push: "dyadic_interval_vec_pushable acc"
  shows "dyadic_interval_vec_push_monadic acc l r j
           \<le> SPEC (\<lambda>v. dyadic_interval_vec_invar v \<and>
                dyadic_interval_vec_triples v
                  = dyadic_interval_vec_triples acc @ [((l, r), j)] \<and>
                dyadic_interval_vec_to_list v
                  = dyadic_interval_vec_to_list acc @ [dyadic_interval_of_triple ((l, r), j)])"
proof -
  obtain lns rns ks where acc: "acc = (lns, rns, ks)" by (cases acc)
  show ?thesis unfolding acc
    using dyadic_interval_vec_push_monadic_spec[of lns rns ks l r j] invar push acc by simp
qed

text \<open>\<^bold>\<open>The integer check IS the real separator condition.\<close>  @{const lowdeg_sep_ok_pure} tests
  \<open>a * (a*q\<^sup>2 + b*q*2\<^bsup>j\<^esup> + c*2\<^bsup>2j\<^esup>) < 0\<close> over \<open>int\<close>; dividing by \<open>2\<^bsup>2j\<^esup> > 0\<close> is exactly
  \<open>a * P (q/2\<^bsup>j\<^esup>) < 0\<close> over \<open>real\<close>.  That is the whole bridge, and it is why the grid exponent may
  stay a tunable constant: nothing here says where \<open>q\<close> came from.\<close>
text \<open>\<^bold>\<open>COVERAGE for the two windows.\<close>  Isolation comes from
  @{thm [source] lowdeg_deg2_two_windows}; coverage does not, and \S5's single-window version
  does not generalise --- with two windows the root can be on either side of the separator, so
  the witness depends on a CASE SPLIT the emission proof's closers cannot guess.  Stated
  pointwise (at the \<open>x\<close> the goal already fixed), for the reason \S5's
  @{thm [source] lowdeg_one_window_covers_at} is: \<open>refine_vcg\<close> splits the SPEC's conjunction, so
  a lemma proving both halves matches neither.\<close>
lemma lowdeg_two_window_covers_at:
  fixes ys :: "int list" and q :: int and j k :: nat and x :: real
  assumes bound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k"
    \<comment> \<open>\<^bold>\<open>MEMBERSHIP, not the literal two-element list.\<close>  \<open>refine_vcg\<close> hands the accumulator's
       contents down as a CHAIN of append equations (\<open>to_list xc = to_list xb @ [t\<^sub>2]\<close>,
       \<open>to_list xb = \<dots> @ [t\<^sub>1]\<close>), never as \<open>[t\<^sub>1, t\<^sub>2]\<close>, so a hypothesis in list form does not
       match and the \<open>rule\<close> silently does not fire.  Membership is what the chain gives up
       easily, and it is all this proof needs.\<close>
    and mem1: "dyadic_interval_of_triple (((0::int), q), j)
                 \<in> set (dyadic_interval_vec_to_list acc)"
    and mem2: "dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)
                 \<in> set (dyadic_interval_vec_to_list acc)"
    and xp: "0 < x" and xr: "ripoly (Poly ys) x = 0"
  shows "\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
           \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
proof -
  let ?t = "(of_int q :: real) / 2 ^ j"
  have xlt: "x < 2 ^ k" using bound xp xr by blast
  show ?thesis
  proof (cases "x \<le> ?t")
    case True
    note mem = mem1
    have eq: "dyadic_interval_of_triple (((0::int), q), j)
                = real_to_rat_pair ((0, ?t) :: real \<times> real)"
      by (simp add: dyadic_triple_zero_num real_to_rat_pair_zero_num)
    show ?thesis using mem eq xp True by fastforce
  next
    case False
    hence tle: "?t \<le> x" by linarith
    note mem = mem2
    have eq: "dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)
                = real_to_rat_pair ((?t, 2 ^ k) :: real \<times> real)"
      by (simp add: dyadic_triple_num_pow2 real_to_rat_pair_num_pow2)
    show ?thesis using mem eq tle xlt by fastforce
  qed
qed

lemma dyadic_interval_vec_two_push:
  assumes "dyadic_interval_vec_to_list xa = []"
    and "dyadic_interval_vec_to_list xb = dyadic_interval_vec_to_list xa @ [t1]"
    and "dyadic_interval_vec_to_list xc = dyadic_interval_vec_to_list xb @ [t2]"
  shows "dyadic_interval_vec_to_list xc = [t1, t2]"
  using assms by simp

lemma lowdeg_two_window_isolates_list:
  fixes ys :: "int list" and q :: int and j k :: nat
  assumes sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and len3: "length ys = 3" and anz: "ys ! 2 \<noteq> 0"
    and sepr: "of_int (ys!2) *
               (of_int (ys!2) * ((of_int q :: real) / 2 ^ j)\<^sup>2 +
                of_int (ys!1) * ((of_int q :: real) / 2 ^ j) +
                of_int (ys!0)) < (0::real)"
    and bound: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly ys) x = 0 \<Longrightarrow> x < 2 ^ k"
    and pos: "\<And>x::real. ripoly (Poly ys) x = 0 \<Longrightarrow> 0 < x"
    and lst: "dyadic_interval_vec_to_list acc =
                [dyadic_interval_of_triple (((0::int), q), j),
                 dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)]"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
            \<exists>J. I = real_to_rat_pair J \<and>
                dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) J"
proof -
  have wins: "dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) (0, (of_int q :: real) / 2 ^ j)"
    "dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) ((of_int q :: real) / 2 ^ j, 2 ^ k)"
    using lowdeg_deg2_two_windows[OF len3 anz sf sepr bound pos] by blast+
  have eq1: "dyadic_interval_of_triple (((0::int), q), j) =
               real_to_rat_pair ((0, (of_int q :: real) / 2 ^ j) :: real \<times> real)"
    by (simp add: dyadic_triple_zero_num real_to_rat_pair_zero_num)
  have eq2: "dyadic_interval_of_triple ((q, 2 ^ (k + j)), j) =
               real_to_rat_pair (((of_int q :: real) / 2 ^ j, 2 ^ k) :: real \<times> real)"
    by (simp add: dyadic_triple_num_pow2 real_to_rat_pair_num_pow2)
  show ?thesis using lst wins eq1 eq2 by auto
qed

lemma lowdeg_two_window_isolates_chain:
  fixes ys :: "int list" and q :: int and j k :: nat and xa xb xc
  assumes sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and len3: "length ys = 3" and anz: "ys ! 2 \<noteq> 0"
    and sepr: "of_int (ys!2) *
               (of_int (ys!2) * ((of_int q :: real) / 2 ^ j)\<^sup>2 +
                of_int (ys!1) * ((of_int q :: real) / 2 ^ j) +
                of_int (ys!0)) < (0::real)"
    and bound: "\<forall>x::real. 0 < x \<longrightarrow> poly (real_of_int_poly (Poly ys)) x = 0 \<longrightarrow> x < 2 ^ k"
    and pos: "\<And>x::real. ripoly (Poly ys) x = 0 \<Longrightarrow> 0 < x"
    and xa: "dyadic_interval_vec_to_list xa = []"
    and xb: "dyadic_interval_vec_to_list xb =
               dyadic_interval_vec_to_list xa @ [dyadic_interval_of_triple (((0::int), q), j)]"
    and xc: "dyadic_interval_vec_to_list xc =
               dyadic_interval_vec_to_list xb @ [dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)]"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list xc).
            \<exists>J. I = real_to_rat_pair J \<and>
                dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) J"
proof -
  have lst: "dyadic_interval_vec_to_list xc =
               [dyadic_interval_of_triple (((0::int), q), j),
                dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)]"
    using xa xb xc by (auto intro: dyadic_interval_vec_two_push)
  have bound': "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly ys) x = 0 \<Longrightarrow> x < 2 ^ k"
    using bound by blast
  show ?thesis using lowdeg_two_window_isolates_list[OF sf len3 anz sepr bound' pos lst] .
qed

text \<open>\<^bold>\<open>Coverage over the push chain\<close>, the twin of @{thm [source] lowdeg_two_window_isolates_chain}.
  Applied in its membership form, the coverage rule leaves \<open>refine_vcg\<close>'s three append equations to be
  turned into two membership facts by the closer's \<open>auto\<close> on every remaining goal, which is slow. Doing
  the list collapse once here leaves the closer a \<open>rule\<close> whose premises are the facts in context.\<close>
lemma lowdeg_two_window_covers_chain:
  fixes ys :: "int list" and q :: int and j k :: nat and x :: real and xa xb xc
  assumes bound: "\<forall>x::real. 0 < x \<longrightarrow> poly (real_of_int_poly (Poly ys)) x = 0 \<longrightarrow> x < 2 ^ k"
    and xa: "dyadic_interval_vec_to_list xa = []"
    and xb: "dyadic_interval_vec_to_list xb =
               dyadic_interval_vec_to_list xa @ [dyadic_interval_of_triple (((0::int), q), j)]"
    and xc: "dyadic_interval_vec_to_list xc =
               dyadic_interval_vec_to_list xb @ [dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)]"
    and xp: "0 < x" and xr: "ripoly (Poly ys) x = 0"
  shows "\<exists>I \<in> set (dyadic_interval_vec_to_list xc).
           \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
proof -
  have lst: "dyadic_interval_vec_to_list xc =
               [dyadic_interval_of_triple (((0::int), q), j),
                dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)]"
    using xa xb xc by (auto intro: dyadic_interval_vec_two_push)
  have bound': "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k" using bound by blast
  have m1: "dyadic_interval_of_triple (((0::int), q), j)
              \<in> set (dyadic_interval_vec_to_list xc)" using lst by simp
  have m2: "dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)
              \<in> set (dyadic_interval_vec_to_list xc)" using lst by simp
  show ?thesis by (rule lowdeg_two_window_covers_at[OF bound' m1 m2 xp xr])
qed

text \<open>\<^bold>\<open>The scaling identity, over an opaque denominator.\<close> This is all of the bridge's algebra. It is a
  lemma rather than a step inside one because \<open>field_simps\<close> must not see \<open>2 ^ lowdeg_sep_j\<close>: on a
  symbolic exponent its power simproc does not terminate in reasonable time. With \<open>T\<close> a plain variable
  the same call is immediate, and the exponent enters only by instantiation.\<close>
lemma sep_scale_id:
  fixes a b c q T :: real
  assumes T: "T \<noteq> 0"
  shows "a * (a * (q / T)\<^sup>2 + b * (q / T) + c)
           = (a * (a * q\<^sup>2 + b * q * T + c * (T * T))) / (T * T)"
  using T by (simp add: power_divide power2_eq_square field_simps)

lemma lowdeg_sep_bridge:
  fixes ys :: "int list"
  assumes ok: "lowdeg_sep_ok_pure False ys"
  shows "of_int (ys!2) *
           (of_int (ys!2) * ((of_int (lowdeg_sep_q False lowdeg_sep_j ys) :: real) / 2 ^ lowdeg_sep_j)\<^sup>2
            + of_int (ys!1) * ((of_int (lowdeg_sep_q False lowdeg_sep_j ys) :: real) / 2 ^ lowdeg_sep_j)
            + of_int (ys!0)) < (0::real)"
\<comment> \<open>\<^bold>\<open>Three small steps, not one \<open>field_simps\<close>.\<close> With \<open>lowdeg_sep_W\<close> unfolded, \<open>field_simps\<close> would
     cross-multiply an \<open>of_int\<close> sum containing \<open>2\<^bsup>2j\<^esup>\<close> and two \<open>lowdeg_sep_q\<close> applications. Separating the
     \<open>of_int\<close> homomorphism (no division) from clearing one denominator (no \<open>of_int\<close>) keeps both halves
     small.\<close>
proof -
  let ?j = "lowdeg_sep_j"
  let ?q = "lowdeg_sep_q False ?j ys"
  let ?T = "(2::real) ^ ?j"
  let ?t = "(of_int ?q :: real) / ?T"
  let ?a = "of_int (ys!2) :: real" and ?b = "of_int (ys!1) :: real"
  let ?c = "of_int (ys!0) :: real"
  have Tpos: "0 < ?T" by simp
  have Tnz: "?T \<noteq> 0" by simp
  \<comment> \<open>(1) the integer expression, mapped into the reals --- pure homomorphism, no division.
     Stated about \<open>W\<close> ALONE, with the leading \<open>a\<close> kept outside: \<open>simp\<close> splits \<open>of_int (a * W)\<close>
     into a product of \<open>of_int\<close>s the moment it sees it (\<open>of_int_mult\<close> runs left to right), so a
     fact stated about the product never matches the goal it is meant to close.\<close>
  have ofint: "(of_int (lowdeg_sep_W False ?j ys) :: real)
                 = ?a * (of_int ?q)\<^sup>2 + ?b * of_int ?q * ?T + ?c * (?T * ?T)"
    unfolding lowdeg_sep_W_def
    by (simp add: power2_eq_square mult_2 power_add)
  \<comment> \<open>(2) the same expression over \<open>t = q/2\<^bsup>j\<^esup>\<close>, with the single denominator cleared by instantiating
     @{thm [source] sep_scale_id}, whose \<open>T\<close> is an opaque variable. Calling \<open>field_simps\<close> directly with
     \<open>2 ^ lowdeg_sep_j\<close> in the goal would expand the symbolic exponent.\<close>
  have expand: "?a * (?a * ?t\<^sup>2 + ?b * ?t + ?c)
                  = (?a * (?a * (of_int ?q)\<^sup>2 + ?b * of_int ?q * ?T + ?c * (?T * ?T)))
                    / (?T * ?T)"
    by (rule sep_scale_id[OF Tnz])
  \<comment> \<open>(3) a negative numerator over a positive denominator.\<close>
  have neg: "?a * (of_int (lowdeg_sep_W False ?j ys) :: real) < 0"
    using ok[unfolded lowdeg_sep_ok_pure_prod] by (simp flip: of_int_mult)
  show ?thesis
    unfolding expand ofint[symmetric]
    using divide_neg_pos[OF neg mult_pos_pos[OF Tpos Tpos]] by simp
qed

text \<open>\<^bold>\<open>The emitting arm, two-window case.\<close>  Stated over a bare \<open>ys\<close> exactly as
  @{thm [source] lowdeg_emit_pos_one_correct} is, and for the same reason: \S7 applies it twice,
  once at \<open>xs\<close> (class \<open>5\<close>) and once at \<open>refl_list xs\<close> (class \<open>6\<close>, through the clone).\<close>
lemma lowdeg_emit_two_pos_correct:
  fixes ys :: "int list"
  assumes len3: "length ys = 3" and lastnz: "last ys \<noteq> 0"
    and hr: "kiou_headroom ys"
    and capY: "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k. k * length ys < max_snat LENGTH(gmp_poly_len))"
    and sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and pos: "\<And>x::real. ripoly (Poly ys) x = 0 \<Longrightarrow> 0 < x"
    and sep: "lowdeg_sep_ok_pure False ys"
  shows "lowdeg_emit_two_pos_monadic ys
           \<le> SPEC (\<lambda>acc.
                (\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
                   \<exists>J. I = real_to_rat_pair J \<and>
                       dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) J) \<and>
                (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow>
                   (\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
                      \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  let ?j = "lowdeg_sep_j"
  let ?q = "lowdeg_sep_q False ?j ys"
  let ?t = "(of_int ?q :: real) / 2 ^ ?j"
  have len2: "2 \<le> length ys" using len3 by linarith
  have lenb: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have room: "(1::nat) < max_snat LENGTH(gmp_poly_len)" using len2 lenb by linarith
  have room2: "(2::nat) < max_snat LENGTH(gmp_poly_len)" using len2 lenb by linarith
  \<comment> \<open>\<^bold>\<open>The word-size numeral is evaluated once, here.\<close> Passing \<open>max_snat_def\<close> to the per-goal \<open>auto\<close>
     instead makes every \<open>refine_vcg\<close> ASSERT goal expand \<open>2\<^bsup>63\<^esup>\<close> and run numeral arithmetic on it.\<close>
  have mbig: "(96::nat) \<le> max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
  \<comment> \<open>\<open>k + 64\<close> is in range because the bound op's own cap gives \<open>k * length ys < max_snat\<close>
     and this arm has \<open>length ys = 3\<close>.\<close>
  have kroom: "k + 64 < max_snat LENGTH(gmp_poly_len)"
    if kc: "k * length ys < max_snat LENGTH(gmp_poly_len)" for k :: nat
  proof -
    have "3 * k < max_snat LENGTH(gmp_poly_len)" using kc len3 by (simp add: mult.commute)
    thus ?thesis using mbig by linarith
  qed
  have ysne: "ys \<noteq> []" using len2 by (cases ys) auto
  have anz: "ys ! 2 \<noteq> 0" using lastnz ysne len3 by (simp add: last_conv_nth)
  have j64: "?j = 64" by (simp add: lowdeg_sep_j_def)
  have sepr: "of_int (ys!2) * (of_int (ys!2) * ?t\<^sup>2 + of_int (ys!1) * ?t + of_int (ys!0)) < (0::real)"
    by (rule lowdeg_sep_bridge[OF sep])
  \<comment> \<open>\<^bold>\<open>The same fact with the exponent as the LITERAL the program carries.\<close>  Everything above
     is stated over \<open>lowdeg_sep_j\<close>; every goal \<open>refine_vcg\<close> produces says \<open>64\<close>, because the
     implementation passes the numeral (\<open>lowdeg_sep_num_monadic False 64\<close>, pushes at \<open>64\<close>).  An
     \<open>OF\<close> against the \<open>lowdeg_sep_j\<close> form therefore instantiates the isolation lemma's \<open>j\<close> to
     \<open>lowdeg_sep_j\<close> and its CONCLUSION then fails to match the goal's \<open>64\<close> --- \<open>rule\<close> does not
     fire, and the closer reports the untouched goal rather than a tactic failure.  Having
     \<open>j64\<close> merely present in the context does not help: the mismatch is in the RULE, so the
     rewrite has to be applied to the FACT.\<close>
  have sepr64: "of_int (ys!2) *
                  (of_int (ys!2) * ((of_int (lowdeg_sep_q False 64 ys) :: real) / 2 ^ 64)\<^sup>2
                   + of_int (ys!1) * ((of_int (lowdeg_sep_q False 64 ys) :: real) / 2 ^ 64)
                   + of_int (ys!0)) < (0::real)"
    using sepr[unfolded lowdeg_sep_j_def] .
  \<comment> \<open>The two windows, from the analytic lemma, at the \<open>k\<close> the bound op returns.\<close>
  have wins: "dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) (0, ?t)"
    "dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) (?t, 2 ^ k)"
    if bound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k" for k :: nat
    using lowdeg_deg2_two_windows[OF len3 anz sf sepr, of k] bound pos by blast+
  show ?thesis
    unfolding lowdeg_emit_two_pos_monadic_def PR_CONST_def mpz_from_int_def COPY_def
    apply (refine_vcg
        lowdeg_sep_num_monadic_correct[THEN order_trans]
        kiou_bound_k_monadic_spec_kcap[OF len2 lastnz hr capY, THEN order_trans]
        mpz_pow2_monadic_spec[THEN order_trans]
        dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans]
        dyadic_push_spec_any[THEN order_trans])
    apply (all \<open>(solves \<open>use len2 len3 lenb ysne room room2 anz j64 mbig in
                          \<open>auto dest: kroom\<close>\<close>)?\<close>)
    apply (all \<open>(solves \<open>use room room2 mbig in
                          \<open>auto intro: dyadic_vec_pushable_of_len dyadic_vec_empty_pushable simp: dyadic_interval_vec_triples_def max_snat_def\<close>\<close>)?\<close>)
    \<comment> \<open>\<^bold>\<open>Both halves close SEARCH-FREE, and that is deliberate.\<close>  Left to \<open>blast\<close>, the rule's five
       premises must be found among a dozen context facts --- three of them buried inside
       conjunctions, one a \<open>\<forall>\<close>/\<open>\<longrightarrow>\<close> bound and one a \<open>\<And>\<close>-rule --- and the search does not finish.
       \<open>elim conjE\<close> flattens the context, every premise the lemma cannot take by \<open>OF\<close> is then
       literally an assumption, and \<open>assumption\<close> cannot search.  A closer that runs on every
       remaining goal must be cheap on the goals it does NOT close.\<close>
    apply (all \<open>(solves \<open>elim conjE;
                          rule lowdeg_two_window_isolates_chain[OF sf len3 anz sepr64 _ pos];
                          assumption\<close>)?\<close>)
    \<comment> \<open>Coverage last, by \<open>rule\<close>: the witness is one of two windows and \<open>auto\<close> cannot guess which.\<close>
    apply (all \<open>(solves \<open>elim conjE; rule lowdeg_two_window_covers_chain; assumption\<close>)?\<close>)
    done
qed

text \<open>Class \<open>6\<close>: both roots negative, so the REFLECTED arm carries the two windows.  Same shape as
  @{thm [source] lowdeg_emit_neg_one_correct} --- clone, reflect, run the positive arm --- with
  \S4b supplying the reflected bundle.\<close>
lemma lowdeg_emit_two_neg_correct:
  fixes xs :: "int list"
  assumes pre: "lowdeg_basic_pre xs" and len3: "length xs = 3"
    and pos: "\<And>x::real. ripoly (Poly (refl_list xs)) x = 0 \<Longrightarrow> 0 < x"
    and sep: "lowdeg_sep_ok_pure False (refl_list xs)"
  shows "lowdeg_emit_two_neg_monadic xs
           \<le> SPEC (\<lambda>acc.
                (\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
                   \<exists>J. I = real_to_rat_pair J \<and>
                       dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
                (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
                   (\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
                      \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  note arm = lowdeg_arm_pre[OF pre]
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF arm(3)] by linarith
  have len3R: "length (refl_list xs) = 3" using len3 by simp
  have reflect: "poly_reflect_in_place_monadic xs \<le> RETURN (refl_list xs)"
    using poly_reflect_in_place_correct[OF lenb] by (simp add: refl_list_def)
  have body: "lowdeg_emit_two_pos_monadic (refl_list xs)
      \<le> SPEC (\<lambda>acc.
           (\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
              \<exists>J. I = real_to_rat_pair J \<and>
                  dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
           (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
              (\<exists>I \<in> set (dyadic_interval_vec_to_list acc).
                 \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
    by (rule lowdeg_emit_two_pos_correct[OF len3R arm(7) arm(8) arm(9) arm(10) pos sep])
  show ?thesis
    unfolding lowdeg_emit_two_neg_monadic_def PR_CONST_def poly_free_monadic_def
    apply (refine_vcg
        poly_clone_monadic_correct[OF lenb, THEN order_trans]
        reflect[THEN order_trans]
        body[THEN order_trans])
    using lenb arm(1) by auto
qed

section \<open>6. Classification: the class code tells the root structure\<close>

text \<open>The classifier returns \<open>0..6\<close>, and each code asserts a root structure on both arms. For \<open>5\<close> and
  \<open>6\<close> both roots share a sign, so the split at zero does not separate them and a checked separator does;
  their assertion is not a root count but ``every root is positive, and the check passed'', because
  that is what @{thm [source] lowdeg_deg2_two_windows} consumes. Each follows from the sections above
  together with the integer sign tests the implementation computes.

  \<^bold>\<open>The leading coefficient is nonzero by the precondition.\<close> \<open>last xs \<noteq> 0\<close> and the length the
  classifier has just tested give \<open>xs!2 \<noteq> 0\<close> / \<open>xs!3 \<noteq> 0\<close>, which every closed-form lemma needs and which
  the implementation does not check at run time.\<close>

text \<open>\<open>sgn\<close> compared against \<open>0\<close>, as a plain REWRITE.  Passing \<open>sgn_if\<close> to \<open>auto\<close> instead
  makes it case-split on \<open>z = 0\<close> and \<open>0 < z\<close> at every one of the classifier's branches, and the
  product of those splits with the SPEC's five implications is what the build watchdog killed
  (\<open>exception Interrupt_Breakdown\<close>).\<close>
lemma sgn_lt_zero_int[simp]: "(sgn (z::int) < 0) = (z < 0)" by (simp add: sgn_if)
lemma sgn_gt_zero_int[simp]: "(0 < sgn (z::int)) = (0 < z)" by (simp add: sgn_if)

text \<open>\<^bold>\<open>Name the sign product.\<close>  Every failure in this section traced to ONE shape: the
  classifier's branch condition reaching a PREMISE as a raw \<open>if\<close>-expression, where \<open>simp\<close> will
  not split it, \<open>split: if_splits\<close> multiplies against every other \<open>if\<close> in scope, and a \<open>dest\<close>
  rule stated with \<open>1\<close> misses the \<open>Suc 0\<close> the prover normalises to.  Giving the expression a
  NAME removes the shape instead of fighting it: the value the kernel op returns and the test
  the definition performs become the same term, and both sides match syntactically.\<close>
definition lowdeg_sp :: "int \<Rightarrow> int \<Rightarrow> nat" where
"lowdeg_sp a b = (if a * b < 0 then 1 else if 0 < a * b then 2 else 0)"

lemma lowdeg_sp_eq1[simp]: "(lowdeg_sp a b = 1) = (a * b < 0)"
  by (simp add: lowdeg_sp_def)

lemma lowdeg_sp_eq2[simp]: "(lowdeg_sp a b = 2) = (0 < a * b)"
proof (cases "a * b < 0")
  case True
  hence "\<not> (0 < a * b)" by linarith
  thus ?thesis using True by (simp add: lowdeg_sp_def)
next
  case False
  thus ?thesis by (simp add: lowdeg_sp_def)
qed

text \<open>\<^bold>\<open>Both in \<open>Suc 0\<close> shape.\<close> The prover normalises the nat literal \<open>1\<close> to \<open>Suc 0\<close> in premises, and a
  rule stated with \<open>1\<close> then does not fire; registering both shapes avoids that.\<close>
lemmas lowdeg_sp_eq1_Suc[simp] = lowdeg_sp_eq1[unfolded One_nat_def]

text \<open>The kernel op's spec, restated in that vocabulary.\<close>
lemma lowdeg_sgn_prod_value:
  assumes "i < length xs" and "j < length xs"
  shows "lowdeg_sgn_prod_monadic xs i j \<le> RETURN (lowdeg_sp (xs!i) (xs!j))"
  using lowdeg_sgn_prod_monadic_correct[OF assms] by (simp add: lowdeg_sp_def)

text \<open>The separator check's spec, in the same \<open>\<le> RETURN <pure value>\<close> vocabulary.  Its
  \<open>xs!2 \<noteq> 0\<close> premise is not decoration: @{const lowdeg_sep_ok_monadic} divides by \<open>2*a\<close>, and the
  division op ASSERTs a nonzero divisor, so without it the op FAILS and no value lemma could
  hold.  The classifier gets it from \<open>last xs \<noteq> 0\<close> plus the length it has just tested.\<close>
lemma lowdeg_sep_ok_value:
  fixes xs :: "int list"
  assumes len: "2 < length xs" and a: "xs!2 \<noteq> 0"
  shows "lowdeg_sep_ok_monadic rf xs \<le> RETURN (lowdeg_sep_ok_pure rf xs)"
  using lowdeg_sep_ok_monadic_correct[OF _ _ len a, of rf] len by simp

text \<open>\<^bold>\<open>The classifier as a PURE function.\<close>  Every kernel op in \<open>Lowdeg.thy\<close> is specified as
  \<open>\<le> RETURN <pure value>\<close> and the dispatch is specified the same way here, for the same reason:
  it keeps the monadic reasoning free of the property being proved.  This mirrors
  @{const lowdeg_class_monadic} branch for branch --- including that the disabled increment-2
  case (both roots the same sign) falls through to \<open>0\<close>.\<close>
definition lowdeg_class_pure :: "int list \<Rightarrow> nat" where
"lowdeg_class_pure xs =
  (if length xs = 3 then
     (if xs!1 * xs!1 - 4 * (xs!2 * xs!0) < 0 then 1
      else if 0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0) then
             (if lowdeg_sp (xs!2) (xs!0) = 1 then 4
              else if lowdeg_sp (xs!2) (xs!0) = 2 then
                     (if lowdeg_sp (xs!2) (xs!1) = 1 then
                        (if lowdeg_sep_ok_pure False xs then 5 else 0)
                      else if lowdeg_sp (xs!2) (xs!1) = 2 then
                        (if lowdeg_sep_ok_pure True xs then 6 else 0)
                      else 0)
              else 0)
      else 0)
   else if length xs = 4 then
     (if lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0 then
        (if lowdeg_sp (xs!3) (xs!0) = 1 then 2
         else if lowdeg_sp (xs!3) (xs!0) = 2 then 3 else 1)
      else 0)
   else 0)"

lemma lowdeg_class_monadic_value:
  fixes xs :: "int list"
  assumes len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
  shows "lowdeg_class_monadic xs \<le> RETURN (lowdeg_class_pure xs)"
  unfolding lowdeg_class_monadic_def PR_CONST_def poly_length_monadic_def
  apply (refine_vcg
      lowdeg_disc2_sgn_monadic_correct[THEN order_trans]
      lowdeg_disc3_sgn_monadic_correct[THEN order_trans]
      lowdeg_sgn_prod_value[THEN order_trans]
      lowdeg_sep_ok_value[THEN order_trans])
  \<comment> \<open>Small numeric goals only.  The definition stays FOLDED through \<open>refine_vcg\<close> and is
     unfolded per goal, so its nested \<open>if\<close>s land in conclusion position where \<open>simp\<close> splits
     them for free; the \<open>dest!\<close> rules above handle the premise side.\<close>
  \<comment> \<open>No \<open>One_nat_def\<close> here: with the sign product NAMED there is no \<open>Suc 0\<close>/\<open>1\<close> mismatch
     left to paper over, and normalising \<open>1\<close> away would instead stop @{thm [source]
     lowdeg_sp_eq1} matching the premises.\<close>
  \<comment> \<open>\<^bold>\<open>The leading coefficient, for the two-window case's division.\<close>  \<open>last xs \<noteq> 0\<close> and the
     branch's own \<open>length xs = 3\<close> give \<open>xs!2 \<noteq> 0\<close>; without it @{thm [source] lowdeg_sep_ok_value} does
     not apply and the \<open>fdiv\<close> ASSERT is unprovable.  It runs FIRST because those goals carry no
     \<open>lowdeg_class_pure\<close> and the later closers would spin on them.\<close>
  apply (all \<open>(solves \<open>use lastnz len2 in \<open>auto simp: last_conv_nth\<close>\<close>)?\<close>)
  apply (all \<open>(solves \<open>auto simp: lowdeg_class_pure_def\<close>)?\<close>)
  apply (all \<open>(solves \<open>simp add: lowdeg_class_pure_def\<close>)?\<close>)
  apply (all \<open>(solves \<open>auto simp: lowdeg_class_pure_def lowdeg_sp_def\<close>)?\<close>)
  \<comment> \<open>Whatever is left is a handful of branch-value goals, so \<open>if_splits\<close> --- unaffordable
     across the 100 goals the direct \<open>SPEC\<close> proof produced --- costs nothing here.  This is
     the payoff of routing through the pure classifier.\<close>
  done

lemma lowdeg_class_correct:
  fixes xs :: "int list"
  assumes pre: "lowdeg_basic_pre xs"
  shows "lowdeg_class_monadic xs
           \<le> SPEC (\<lambda>cl. cl \<in> {0,1,2,3,4,5,6} \<and>
              (cl = 1 \<longrightarrow> (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
                           (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0)) \<and>
              (cl = 2 \<longrightarrow> (\<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0) \<and>
                           (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0)) \<and>
              (cl = 3 \<longrightarrow> (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
                           (\<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0)) \<and>
              (cl = 4 \<longrightarrow> (\<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0) \<and>
                           (\<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0)) \<and>
              \<comment> \<open>\<^bold>\<open>The same-sign case's two codes assert a different SHAPE.\<close>  Classes \<open>1\<close>--\<open>4\<close> report a
                 root COUNT, which is all a single window needs.  Here the emitting arm returns
                 TWO windows, so what the emission consumes is \<open>every root is on this arm\<close> plus
                 the separator check --- @{thm [source] lowdeg_deg2_two_windows}'s \<open>pos\<close> and
                 \<open>sep\<close>.  The length is carried too: that lemma is degree-2 only.\<close>
              (cl = 5 \<longrightarrow> length xs = 3 \<and>
                           (\<forall>x::real. ripoly (Poly xs) x = 0 \<longrightarrow> 0 < x) \<and>
                           (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0) \<and>
                           lowdeg_sep_ok_pure False xs) \<and>
              (cl = 6 \<longrightarrow> length xs = 3 \<and>
                           (\<forall>x::real. ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> 0 < x) \<and>
                           (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
                           lowdeg_sep_ok_pure False (refl_list xs)))"
proof -
  from pre have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    unfolding lowdeg_basic_pre_def by auto
  have xsne: "xs \<noteq> []" using len2 by (cases xs) auto
  have lead3: "xs ! 2 \<noteq> 0" if len: "length xs = 3"
    using lastnz xsne len by (simp add: last_conv_nth)
  have lead4: "xs ! 3 \<noteq> 0" if len: "length xs = 4"
    using lastnz xsne len by (simp add: last_conv_nth)

  \<comment> \<open>\<^bold>\<open>Degree 2, \<open>\<Delta><0\<close>\<close> --- no real root at all, so neither arm has a positive one.  \<open>\<Delta>\<close> is
     literally the same integer on the reflection: only \<open>a\<^sub>1\<close> flips, and it enters squared.\<close>
  have d2_none: "(\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
                 (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0)"
    if len: "length xs = 3" and D: "xs!1 * xs!1 - 4 * (xs!2 * xs!0) < 0"
  proof -
    note ri = lowdeg_deg2_refl_indices[OF len]
    have aR: "refl_list xs ! 2 \<noteq> 0" using lead3[OF len] ri(2) by simp
    have DR: "refl_list xs ! 1 * refl_list xs ! 1
                - 4 * (refl_list xs ! 2 * refl_list xs ! 0) < 0"
      using D ri(2) ri(3) lowdeg_deg2_refl_idx1[OF len] by simp
    show ?thesis
      using lowdeg_deg2_no_real_root[OF len lead3[OF len] D]
            lowdeg_deg2_no_real_root[OF ri(1) aR DR] by blast
  qed

  \<comment> \<open>\<^bold>\<open>Degree 2, roots straddling zero\<close> --- \<open>a\<^sub>2*a\<^sub>0<0\<close> survives the reflection verbatim (both
     indices are EVEN), so ONE lemma serves both arms.  This is the formal counterpart of the
     implementation classifying once for both.\<close>
  have d2_two: "(\<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0) \<and>
                (\<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0)"
    if len: "length xs = 3" and ac: "xs!2 * xs!0 < 0"
  proof -
    note ri = lowdeg_deg2_refl_indices[OF len]
    have aR: "refl_list xs ! 2 \<noteq> 0" using lead3[OF len] ri(2) by simp
    have acR: "refl_list xs ! 2 * refl_list xs ! 0 < 0" using ac ri(2) ri(3) by simp
    show ?thesis
      using lowdeg_deg2_one_pos_root[OF len lead3[OF len] ac]
            lowdeg_deg2_one_pos_root[OF ri(1) aR acR] by blast
  qed

  \<comment> \<open>\<^bold>\<open>Degree 3, \<open>\<Delta><0\<close>\<close> --- exactly one real root, and \<open>sign(a\<^sub>3*a\<^sub>0)\<close> says which arm owns it.
     On the reflection \<open>\<Delta>\<close> is UNCHANGED while the sign product FLIPS, which is precisely why one
     discriminant computation decides two arms.\<close>
  \<comment> \<open>\<^bold>\<open>Three separate conditional facts, not one conjunction discharged by \<open>intro conjI impI\<close>.\<close>
     \<open>intro\<close> is repeated: after \<open>impI\<close> exposes each branch's conclusion it applies \<open>conjI\<close> again, which
     would leave six pending goals that no \<open>show\<close> matches.\<close>
  have d3neg: "(\<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0) \<and>
               (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0)"
    if len: "length xs = 4" and D: "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0"
      and h: "xs!3 * xs!0 < 0"
  proof -
    note ri = lowdeg_deg3_refl_indices[OF len]
    have aR: "refl_list xs ! 3 \<noteq> 0" using lead4[OF len] ri(2) by simp
    have DR: "lowdeg_disc3_int (refl_list xs ! 3) (refl_list xs ! 2)
                               (refl_list xs ! 1) (refl_list xs ! 0) < 0"
      using D ri(2) ri(3) ri(4) ri(5) by (simp add: lowdeg_disc3_int_refl)
    have prodR: "refl_list xs ! 3 * refl_list xs ! 0 = - (xs!3 * xs!0)"
      using ri(2) ri(5) by simp
    \<comment> \<open>\<open>linarith\<close>, not \<open>simp\<close>: \<open>simp\<close> normalises \<open>xs!3 * xs!0 = 0\<close> into the DISJUNCTION
       \<open>xs!3 = 0 \<or> xs!0 = 0\<close> and then cannot get back.  \<open>linarith\<close> abstracts the product as an
       atom, which is all these sign facts ever needed.\<close>
    have sgR: "\<not> (refl_list xs ! 3 * refl_list xs ! 0 < 0)" using prodR h by linarith
    show ?thesis
      using lowdeg_deg3_one_pos_root[OF len lead4[OF len] D h]
            lowdeg_deg3_no_pos_root[OF ri(1) aR DR sgR] by blast
  qed
  have d3pos: "(\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
               (\<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0)"
    if len: "length xs = 4" and D: "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0"
      and h: "0 < xs!3 * xs!0"
  proof -
    note ri = lowdeg_deg3_refl_indices[OF len]
    have aR: "refl_list xs ! 3 \<noteq> 0" using lead4[OF len] ri(2) by simp
    have DR: "lowdeg_disc3_int (refl_list xs ! 3) (refl_list xs ! 2)
                               (refl_list xs ! 1) (refl_list xs ! 0) < 0"
      using D ri(2) ri(3) ri(4) ri(5) by (simp add: lowdeg_disc3_int_refl)
    have prodR: "refl_list xs ! 3 * refl_list xs ! 0 = - (xs!3 * xs!0)"
      using ri(2) ri(5) by simp
    have sgX: "\<not> (xs!3 * xs!0 < 0)" using h by linarith
    have sgR: "refl_list xs ! 3 * refl_list xs ! 0 < 0" using prodR h by linarith
    show ?thesis
      using lowdeg_deg3_no_pos_root[OF len lead4[OF len] D sgX]
            lowdeg_deg3_one_pos_root[OF ri(1) aR DR sgR] by blast
  qed
  \<comment> \<open>Stated on the two NEGATIONS the classifier's \<open>else\<close> branch actually leaves in context,
     not on \<open>a\<^sub>3*a\<^sub>0 = 0\<close>, which \<open>simp\<close> would then have to derive from them.\<close>
  have d3zero: "(\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
                (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0)"
    if len: "length xs = 4" and D: "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0"
      and h1: "\<not> (xs!3 * xs!0 < 0)" and h2: "\<not> (0 < xs!3 * xs!0)"
  proof -
    have h: "xs!3 * xs!0 = 0" using h1 h2 by linarith
    note ri = lowdeg_deg3_refl_indices[OF len]
    have aR: "refl_list xs ! 3 \<noteq> 0" using lead4[OF len] ri(2) by simp
    have DR: "lowdeg_disc3_int (refl_list xs ! 3) (refl_list xs ! 2)
                               (refl_list xs ! 1) (refl_list xs ! 0) < 0"
      using D ri(2) ri(3) ri(4) ri(5) by (simp add: lowdeg_disc3_int_refl)
    have prodR: "refl_list xs ! 3 * refl_list xs ! 0 = - (xs!3 * xs!0)"
      using ri(2) ri(5) by simp
    have sgX: "\<not> (xs!3 * xs!0 < 0)" using h by linarith
    have sgR: "\<not> (refl_list xs ! 3 * refl_list xs ! 0 < 0)" using prodR h by linarith
    show ?thesis
      using lowdeg_deg3_no_pos_root[OF len lead4[OF len] D sgX]
            lowdeg_deg3_no_pos_root[OF ri(1) aR DR sgR] by blast
  qed

  \<comment> \<open>\<^bold>\<open>Routed through the PURE classifier.\<close>  Proving the \<open>SPEC\<close> directly against the monadic
     program made \<open>refine_vcg\<close> distribute the five implications over every branch --- 100
     goals, whose sheer volume (not any one hard step) exhausted the build watchdog, and whose
     branch conditions arrived as \<open>if\<close>s in PREMISE position where \<open>simp\<close> will not split them.
     Splitting the proof the way every kernel op in \<open>Lowdeg.thy\<close> is already split --- first
     \<open>\<le> RETURN <pure value>\<close>, then a pure fact about that value --- leaves the monadic step a
     handful of tiny numeric goals and puts the real content in ONE ordinary goal whose \<open>if\<close>s
     are in CONCLUSION position, where \<open>simp\<close> splits them for free.\<close>
  \<comment> \<open>\<^bold>\<open>One class code at a time.\<close>  Unfolding the definition into all FIVE implications at
     once let \<open>auto\<close> split every branch test against every other --- 48 goals mixing a
     degree-2 test with \<open>length xs = 4\<close>.  Each code is an independent, small obligation, and
     each needs exactly one of \<section>4's facts.\<close>
  have kmem: "lowdeg_class_pure xs \<in> {0,1,2,3,4,5,6}"
    by (simp add: lowdeg_class_pure_def)
  \<comment> \<open>\<^bold>\<open>Branch conditions first, polynomials second.\<close>  Each \<open>cases\<close> fact is PURELY NUMERIC, so
     \<open>if_splits\<close> over the definition costs nothing there; the root-structure step then runs with
     no splitting at all.  Doing both at once --- handing \<open>auto\<close> the \<open>\<Delta>\<close> facts WHILE it split
     the definition --- is what broke down.\<close>
  \<comment> \<open>\<^bold>\<open>\<open>h\<close> is UNFOLDED by the shape equation, never supplied alongside it.\<close>  Giving \<open>auto\<close>
     both \<open>lowdeg_class_pure xs = 1\<close> and \<open>lowdeg_class_pure xs = <if-term>\<close> lets \<open>simp\<close> combine
     them into \<open>1 = (if \<dots> then 1 \<dots>)\<close> and orient it LEFT to RIGHT --- so every \<open>1\<close> expands into
     a term containing \<open>1\<close>.  \<^bold>\<open>And there is no \<open>split: if_splits\<close>\<close>: on these goals it diverges.
     An explicit \<open>cases\<close> chain over the same three tests resolves every \<open>if\<close> before \<open>simp\<close> sees it,
     and cannot diverge.

     \<^bold>\<open>Resolve the LENGTH test before splitting anything.\<close>  \<open>split: if_splits\<close> over the whole
     nested definition diverges even on purely numeric goals.  Peeling the outer test first
     leaves a three-\<open>if\<close> term per degree, which splits in a handful of cases.\<close>
  have pure_deg2: "lowdeg_class_pure xs =
      (if xs!1 * xs!1 - 4 * (xs!2 * xs!0) < 0 then 1
       else if 0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)
              then (if lowdeg_sp (xs!2) (xs!0) = 1 then 4
                    else if lowdeg_sp (xs!2) (xs!0) = 2 then
                           (if lowdeg_sp (xs!2) (xs!1) = 1 then
                              (if lowdeg_sep_ok_pure False xs then 5 else 0)
                            else if lowdeg_sp (xs!2) (xs!1) = 2 then
                              (if lowdeg_sep_ok_pure True xs then 6 else 0)
                            else 0)
                    else 0)
              else 0)"
    if "length xs = 3"
    using that by (simp add: lowdeg_class_pure_def)
  have pure_deg3: "lowdeg_class_pure xs =
      (if lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0
       then (if lowdeg_sp (xs!3) (xs!0) = 1 then 2
             else if lowdeg_sp (xs!3) (xs!0) = 2 then 3 else 1)
       else 0)"
    if "length xs \<noteq> 3" and "length xs = 4"
    using that by (simp add: lowdeg_class_pure_def)
  have pure_other: "lowdeg_class_pure xs = 0"
    if "length xs \<noteq> 3" and "length xs \<noteq> 4"
    using that by (simp add: lowdeg_class_pure_def)

  have cases1: "(length xs = 3 \<and> xs!1 * xs!1 - 4 * (xs!2 * xs!0) < 0)
               \<or> (length xs = 4 \<and> lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0
                  \<and> \<not> (xs!3 * xs!0 < 0) \<and> \<not> (0 < xs!3 * xs!0))"
     if h: "lowdeg_class_pure xs = 1"
   proof (cases "length xs = 3")
     case True
     from h[unfolded pure_deg2[OF True]] True show ?thesis
       by (cases "xs!1 * xs!1 - 4 * (xs!2 * xs!0) < 0";
           cases "0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)";
           cases "xs!2 * xs!0 < 0"; cases "0 < xs!2 * xs!0";
           cases "xs!2 * xs!1 < 0"; cases "0 < xs!2 * xs!1";
           cases "lowdeg_sep_ok_pure False xs"; cases "lowdeg_sep_ok_pure True xs"; auto)
  next
    case n3: False
    show ?thesis
    proof (cases "length xs = 4")
      case True
      from h[unfolded pure_deg3[OF n3 True]] True show ?thesis
        by (cases "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0";
            cases "xs!3 * xs!0 < 0";
            cases "0 < xs!3 * xs!0"; simp)
    next
      case False
      from h[unfolded pure_other[OF n3 False]] show ?thesis by simp
    qed
  qed
  have cases2: "length xs = 4 \<and> lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0
               \<and> xs!3 * xs!0 < 0"
     if h: "lowdeg_class_pure xs = 2"
   proof (cases "length xs = 3")
     case True
     from h[unfolded pure_deg2[OF True]] True show ?thesis
       by (cases "xs!1 * xs!1 - 4 * (xs!2 * xs!0) < 0";
           cases "0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)";
           cases "xs!2 * xs!0 < 0"; cases "0 < xs!2 * xs!0";
           cases "xs!2 * xs!1 < 0"; cases "0 < xs!2 * xs!1";
           cases "lowdeg_sep_ok_pure False xs"; cases "lowdeg_sep_ok_pure True xs"; auto)
  next
    case n3: False
    show ?thesis
    proof (cases "length xs = 4")
      case True
      from h[unfolded pure_deg3[OF n3 True]] True show ?thesis
        by (cases "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0";
            cases "xs!3 * xs!0 < 0";
            cases "0 < xs!3 * xs!0"; simp)
    next
      case False
      from h[unfolded pure_other[OF n3 False]] show ?thesis by simp
    qed
  qed
  have cases3: "length xs = 4 \<and> lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0
               \<and> 0 < xs!3 * xs!0"
     if h: "lowdeg_class_pure xs = 3"
   proof (cases "length xs = 3")
     case True
     from h[unfolded pure_deg2[OF True]] True show ?thesis
       by (cases "xs!1 * xs!1 - 4 * (xs!2 * xs!0) < 0";
           cases "0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)";
           cases "xs!2 * xs!0 < 0"; cases "0 < xs!2 * xs!0";
           cases "xs!2 * xs!1 < 0"; cases "0 < xs!2 * xs!1";
           cases "lowdeg_sep_ok_pure False xs"; cases "lowdeg_sep_ok_pure True xs"; auto)
  next
    case n3: False
    show ?thesis
    proof (cases "length xs = 4")
      case True
      from h[unfolded pure_deg3[OF n3 True]] True show ?thesis
        by (cases "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0";
            cases "xs!3 * xs!0 < 0";
            cases "0 < xs!3 * xs!0"; simp)
    next
      case False
      from h[unfolded pure_other[OF n3 False]] show ?thesis by simp
    qed
  qed
  have cases4: "length xs = 3 \<and> xs!2 * xs!0 < 0"
     if h: "lowdeg_class_pure xs = 4"
   proof (cases "length xs = 3")
     case True
     from h[unfolded pure_deg2[OF True]] True show ?thesis
       by (cases "xs!1 * xs!1 - 4 * (xs!2 * xs!0) < 0";
           cases "0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)";
           cases "xs!2 * xs!0 < 0"; cases "0 < xs!2 * xs!0";
           cases "xs!2 * xs!1 < 0"; cases "0 < xs!2 * xs!1";
           cases "lowdeg_sep_ok_pure False xs"; cases "lowdeg_sep_ok_pure True xs"; auto)
  next
    case n3: False
    show ?thesis
    proof (cases "length xs = 4")
      case True
      from h[unfolded pure_deg3[OF n3 True]] True show ?thesis
        by (cases "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0";
            cases "xs!3 * xs!0 < 0";
            cases "0 < xs!3 * xs!0"; simp)
    next
      case False
      from h[unfolded pure_other[OF n3 False]] show ?thesis by simp
    qed
  qed

  have k1: "(\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
            (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0)"
    if h: "lowdeg_class_pure xs = 1"
    \<comment> \<open>\<open>1\<close> is reachable two ways: degree 2 with \<open>\<Delta><0\<close>, and degree 3 with \<open>\<Delta><0\<close> and the
       single root sitting AT the origin.  Both leave \<open>(0,\<infinity>)\<close> empty on either arm.\<close>
    using cases1[OF h] d2_none d3zero by auto
  have k2: "(\<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0) \<and>
            (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0)"
    if h: "lowdeg_class_pure xs = 2"
    using cases2[OF h] d3neg by auto
  have k3: "(\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
            (\<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0)"
    if h: "lowdeg_class_pure xs = 3"
    using cases3[OF h] d3pos by auto
  have k4: "(\<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0) \<and>
            (\<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0)"
    if h: "lowdeg_class_pure xs = 4"
    using cases4[OF h] d2_two by auto
  \<comment> \<open>\<^bold>\<open>The same-sign case's branch conditions.\<close>  Same extraction as \<open>cases1\<close>--\<open>cases4\<close>, one \<open>cases\<close>
     deeper: the degree-2 same-sign arm now tests \<open>sign (a\<^sub>2*a\<^sub>1)\<close> and then the separator, so the
     chain resolves five \<open>if\<close>s instead of three.  Only the DEGREE-2 shape can produce \<open>5\<close> or \<open>6\<close>,
     which is why the degree-3 and other-length branches close by \<open>simp\<close> alone.\<close>
  have cases5: "length xs = 3 \<and> 0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)
               \<and> 0 < xs!2 * xs!0 \<and> xs!2 * xs!1 < 0 \<and> lowdeg_sep_ok_pure False xs"
     if h: "lowdeg_class_pure xs = 5"
   proof (cases "length xs = 3")
     case True
     from h[unfolded pure_deg2[OF True]] True show ?thesis
       by (cases "xs!1 * xs!1 - 4 * (xs!2 * xs!0) < 0";
           cases "0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)";
           cases "xs!2 * xs!0 < 0"; cases "0 < xs!2 * xs!0";
           cases "xs!2 * xs!1 < 0"; cases "0 < xs!2 * xs!1";
           cases "lowdeg_sep_ok_pure False xs"; cases "lowdeg_sep_ok_pure True xs"; auto)
  next
    case n3: False
    show ?thesis
    proof (cases "length xs = 4")
      case True
      from h[unfolded pure_deg3[OF n3 True]] True show ?thesis
        by (cases "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0";
            cases "xs!3 * xs!0 < 0";
            cases "0 < xs!3 * xs!0"; simp)
    next
      case False
      from h[unfolded pure_other[OF n3 False]] show ?thesis by simp
    qed
  qed
  have cases6: "length xs = 3 \<and> 0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)
               \<and> 0 < xs!2 * xs!0 \<and> 0 < xs!2 * xs!1 \<and> lowdeg_sep_ok_pure True xs"
     if h: "lowdeg_class_pure xs = 6"
   proof (cases "length xs = 3")
     case True
     from h[unfolded pure_deg2[OF True]] True show ?thesis
       by (cases "xs!1 * xs!1 - 4 * (xs!2 * xs!0) < 0";
           cases "0 < xs!1 * xs!1 - 4 * (xs!2 * xs!0)";
           cases "xs!2 * xs!0 < 0"; cases "0 < xs!2 * xs!0";
           cases "xs!2 * xs!1 < 0"; cases "0 < xs!2 * xs!1";
           cases "lowdeg_sep_ok_pure False xs"; cases "lowdeg_sep_ok_pure True xs"; auto)
  next
    case n3: False
    show ?thesis
    proof (cases "length xs = 4")
      case True
      from h[unfolded pure_deg3[OF n3 True]] True show ?thesis
        by (cases "lowdeg_disc3_int (xs!3) (xs!2) (xs!1) (xs!0) < 0";
            cases "xs!3 * xs!0 < 0";
            cases "0 < xs!3 * xs!0"; simp)
    next
      case False
      from h[unfolded pure_other[OF n3 False]] show ?thesis by simp
    qed
  qed

  \<comment> \<open>\<^bold>\<open>The same-sign classes, on BOTH arms, from ONE discriminant.\<close>  \<open>a\<^sub>2\<close> and \<open>a\<^sub>0\<close> survive the
     reflection and \<open>a\<^sub>1\<close> flips, so \<open>\<Delta>\<close> and \<open>a\<^sub>2*a\<^sub>0\<close> are the same integers on \<open>refl_list xs\<close> while
     \<open>a\<^sub>2*a\<^sub>1\<close> NEGATES --- which is exactly why one check decides which arm emits.\<close>
  have d2_same: "(\<forall>x::real. ripoly (Poly ys) x = 0 \<longrightarrow> 0 < x) \<and>
                 (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list ys)) x \<noteq> 0)"
    if len: "length ys = 3" and lead: "ys!2 \<noteq> 0"
      and D: "0 < ys!1 * ys!1 - 4 * (ys!2 * ys!0)"
      and ac: "0 < ys!2 * ys!0" and ab: "ys!2 * ys!1 < 0"
    for ys :: "int list"
  proof -
    note ri = lowdeg_deg2_refl_indices[OF len] lowdeg_deg2_refl_idx1[OF len]
    have aR: "refl_list ys ! 2 \<noteq> 0" using lead ri(2) by simp
    have DR: "0 < refl_list ys ! 1 * refl_list ys ! 1
                - 4 * (refl_list ys ! 2 * refl_list ys ! 0)"
      using D ri(2) ri(3) ri(4) by simp
    have acR: "0 < refl_list ys ! 2 * refl_list ys ! 0" using ac ri(2) ri(3) by simp
    have abR: "0 < refl_list ys ! 2 * refl_list ys ! 1" using ab ri(2) ri(4) by simp
    show ?thesis
      using lowdeg_deg2_both_pos[OF len lead D ac ab]
            lowdeg_deg2_no_pos_root[OF ri(1) aR DR acR abR] by blast
  qed

  have k5: "length xs = 3 \<and>
            (\<forall>x::real. ripoly (Poly xs) x = 0 \<longrightarrow> 0 < x) \<and>
            (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0) \<and>
            lowdeg_sep_ok_pure False xs"
    if h: "lowdeg_class_pure xs = 5"
  proof -
    note c = cases5[OF h]
    have lead: "xs ! 2 \<noteq> 0" using lead3 c by simp
    show ?thesis using c d2_same[OF _ lead] by blast
  qed
  \<comment> \<open>Class \<open>6\<close> is class \<open>5\<close> AT \<open>refl_list xs\<close>, and the double reflection is what closes it:
     \<open>refl_list (refl_list xs)\<close> is \<open>xs\<close>, so the non-emitting arm of the transported fact is the
     original polynomial.  The separator moves by @{thm [source] lowdeg_sep_ok_pure_refl}.\<close>
  have k6: "length xs = 3 \<and>
            (\<forall>x::real. ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> 0 < x) \<and>
            (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
            lowdeg_sep_ok_pure False (refl_list xs)"
    if h: "lowdeg_class_pure xs = 6"
  proof -
    note c = cases6[OF h]
    have len: "length xs = 3" using c by simp
    have lead: "xs ! 2 \<noteq> 0" using lead3 len by simp
    note ri = lowdeg_deg2_refl_indices[OF len] lowdeg_deg2_refl_idx1[OF len]
    have lenR: "length (refl_list xs) = 3" using ri(1) .
    have aR: "refl_list xs ! 2 \<noteq> 0" using lead ri(2) by simp
    have DR: "0 < refl_list xs ! 1 * refl_list xs ! 1
                - 4 * (refl_list xs ! 2 * refl_list xs ! 0)"
      using c ri(2) ri(3) ri(4) by simp
    have acR: "0 < refl_list xs ! 2 * refl_list xs ! 0" using c ri(2) ri(3) by simp
    have abR: "refl_list xs ! 2 * refl_list xs ! 1 < 0" using c ri(2) ri(4) by simp
    have sep: "lowdeg_sep_ok_pure False (refl_list xs)"
      using c lowdeg_sep_ok_pure_refl[OF len] by simp
    show ?thesis
      using len sep
            lowdeg_deg2_both_pos[OF lenR aR DR acR abR]
            lowdeg_deg2_no_pos_root[OF len lead _ _ _] c by blast
  qed

  show ?thesis
    apply (rule order_trans[OF lowdeg_class_monadic_value[OF len2 lastnz]])
    apply (rule RETURN_rule)
    using kmem k1 k2 k3 k4 k5 k6 by blast
qed

section \<open>7. The capstone\<close>

text \<open>\<^bold>\<open>The shape is @{thm [source] bisection_isolate_all_split_main_correct}'s, one for one\<close>: the
  dispatch delivers the same pair of properties the bisection solve does, under the same
  precondition, so dispatching to it preserves the claim.

  \<^bold>\<open>The fall-through arm is free.\<close> On class \<open>0\<close> the program is
  @{const bisection_isolate_all_split_main}, so that branch closes by citing its capstone.\<close>

text \<open>The emitting branch, factored out of the capstone so that the \<open>cl\<close> case analysis happens once,
  in Isar, rather than inside a \<open>refine_vcg\<close> apply script. Classes \<open>5\<close> and \<open>6\<close> are reachable, so both
  \<open>if\<close>s below carry a real branch and each needs its own emission lemma.\<close>
text \<open>\<^bold>\<open>The rational/real pair, bound one way in the premises and the other in the goal.\<close>
  \<open>refine_vcg\<close> normalises the SPEC's triple pattern, which turns every \<open>\<exists>J\<close> in the CONCLUSION
  into \<open>\<exists>a b\<close> while the hypotheses keep \<open>\<exists>J\<close>.  A prover then has to synthesise
  \<open>J = (a, b)\<close> itself, and a bare \<open>blast\<close> does not.  As a rewrite it is one step.\<close>
lemma ex_rat_pair_split:
  "(\<exists>J. I = real_to_rat_pair J \<and> Q J)
     = (\<exists>a b. I = real_to_rat_pair (a, b) \<and> Q (a, b))"
  by (metis prod.collapse)

text \<open>\<^bold>\<open>The whole dispatch body, both arms of the class test.\<close> The \<open>cl\<close> case analysis is done here,
  in Isar: splitting on \<open>cl\<close> with \<open>apply (cases \<dots>)\<close> inside the capstone's \<open>refine_vcg\<close> script leaves
  the fall-through arm's \<open>\<le> SPEC\<close> fact unmatched by \<open>simp\<close>. Each arm is proved as two implications
  (\<open>P5\<close>/\<open>P04\<close>, \<open>Q6\<close>/\<open>Q34\<close>) and assembled by \<open>simp\<close>, because the two sides of the \<open>if\<close> are different
  programs and one \<open>show\<close> cannot match both.\<close>
lemma lowdeg_body_correct:
  fixes xs :: "int list" and cl :: nat
  assumes pre: "dsc_isolate_all_split_pre xs"
    and cls: "cl \<in> {0,1,2,3,4,5,6}"
    and posone: "cl = 2 \<or> cl = 4 \<Longrightarrow> \<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0"
    \<comment> \<open>\<^bold>\<open>Universally quantified, not stated about a fixed \<open>x\<close>.\<close>  A lemma-level free \<open>x\<close> makes
       this a fact about ONE point, and \<open>OF\<close> against the emission lemma's \<open>\<And>x\<close> premise then
       fails with \<open>OF: no unifiers\<close> --- textually identical terms, different binders.\<close>
    and posnone: "cl = 1 \<or> cl = 3 \<Longrightarrow> \<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0"
    and negone: "cl = 3 \<or> cl = 4 \<Longrightarrow> \<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0"
    and negnone: "cl = 1 \<or> cl = 2 \<Longrightarrow> \<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
    \<comment> \<open>\<^bold>\<open>The same-sign case's two, in exactly the shape @{thm [source] lowdeg_class_correct} delivers.\<close>
       Each bundles the EMITTING arm's root placement, the OTHER arm's emptiness, and the
       separator check --- the three things the two-window emission and its sibling need.\<close>
    and postwo: "cl = 5 \<Longrightarrow> length xs = 3 \<and>
                   (\<forall>x::real. ripoly (Poly xs) x = 0 \<longrightarrow> 0 < x) \<and>
                   (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0) \<and>
                   lowdeg_sep_ok_pure False xs"
    and negtwo: "cl = 6 \<Longrightarrow> length xs = 3 \<and>
                   (\<forall>x::real. ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> 0 < x) \<and>
                   (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
                   lowdeg_sep_ok_pure False (refl_list xs)"
  shows "(if cl = 0 then bisection_isolate_all_split_main xs
          else doN {
            accP \<leftarrow> (if cl = 5 then lowdeg_emit_two_pos_monadic xs
                               else lowdeg_emit_pos_monadic (cl = 2 \<or> cl = 4) xs);
            accQ \<leftarrow> (if cl = 6 then lowdeg_emit_two_neg_monadic xs
                               else lowdeg_emit_neg_monadic (cl = 3 \<or> cl = 4) xs);
            xs0 \<leftarrow> dsc_split_zero_check_monadic xs;
            RETURN (accP, accQ, xs0)
          }) \<le> SPEC (\<lambda>(accP, accQ, xs0).
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. (I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J)) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. (I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))) \<and>
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. (I = real_to_rat_pair J \<and>
             dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J)) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. (I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))) \<and>
      xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof (cases "cl = 0")
  \<comment> \<open>\<^bold>\<open>The fall-through arm is free\<close> --- the program IS the bisection solve, so this branch is
     its capstone verbatim, because the arm falls back to the certified solver instead of
     re-implementing it.\<close>
  case True
  thus ?thesis using bisection_isolate_all_split_main_correct[OF pre] by simp
next
  case False
  with cls have cls': "cl = 1 \<or> cl = 2 \<or> cl = 3 \<or> cl = 4 \<or> cl = 5 \<or> cl = 6" by auto
  have preB: "lowdeg_basic_pre xs" by (rule dsc_isolate_all_split_pre_basic[OF pre])
  note arm = lowdeg_arm_pre[OF preB]
  \<comment> \<open>\<^bold>\<open>Both arms' postconditions, named once.\<close>  They appear four times below (two arms x two
     shapes of emission) and writing them out each time is how the increment-1 version of this
     proof got long enough to hide its own case split.\<close>
  let ?PP = "\<lambda>accP.
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. I = real_to_rat_pair J \<and>
            dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))"
  let ?QQ = "\<lambda>accQ.
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. I = real_to_rat_pair J \<and>
            dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))"

  \<comment> \<open>\<^bold>\<open>The positive arm, by whether the two-window case fires.\<close>  Stated as two implications and
     assembled by \<open>simp\<close>, rather than as one \<open>cases\<close> on the \<open>if\<close>: the branches return DIFFERENT
     programs, so a single \<open>show ?thesis\<close> would have to match both.\<close>
  have P5: "lowdeg_emit_two_pos_monadic xs \<le> SPEC ?PP" if h: "cl = 5"
  proof -
    note c = postwo[OF h]
    have len3: "length xs = 3" using c by simp
    have lastnz: "last xs \<noteq> 0" using arm(2) .
    have pos: "\<And>x::real. ripoly (Poly xs) x = 0 \<Longrightarrow> 0 < x" using c by blast
    have sep: "lowdeg_sep_ok_pure False xs" using c by blast
    show ?thesis
      by (rule lowdeg_emit_two_pos_correct[OF len3 lastnz arm(3) arm(4) arm(5) pos sep])
  qed
  have P04: "lowdeg_emit_pos_monadic (cl = 2 \<or> cl = 4) xs \<le> SPEC ?PP" if n5: "cl \<noteq> 5"
  proof (cases "cl = 2 \<or> cl = 4")
    \<comment> \<open>\<open>b\<close> rewrites the GOAL's boolean argument to a literal, so \<open>rule\<close> matches the emission
       lemma directly; fed unrewritten, it does not.\<close>
    case True
    hence b: "(cl = 2 \<or> cl = 4) = True" by simp
    show ?thesis unfolding b
      by (rule lowdeg_emit_pos_one_correct[OF arm(1) arm(2) arm(3) arm(4) arm(5) posone[OF True]])
  next
    case n24: False
    from n24 have b: "(cl = 2 \<or> cl = 4) = False" by simp
    have nn: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x \<noteq> 0"
    proof (cases "cl = 6")
      case True
      show "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x \<noteq> 0" using negtwo[OF True] by blast
    next
      case n6: False
      with n24 n5 cls' have h: "cl = 1 \<or> cl = 3" by auto
      show "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x \<noteq> 0" using posnone[OF h] by blast
    qed
    show ?thesis unfolding b by (rule lowdeg_emit_pos_zero_correct[OF nn])
  qed
  have P: "(if cl = 5 then lowdeg_emit_two_pos_monadic xs
            else lowdeg_emit_pos_monadic (cl = 2 \<or> cl = 4) xs) \<le> SPEC ?PP"
    using P5 P04 by simp

  have Q6: "lowdeg_emit_two_neg_monadic xs \<le> SPEC ?QQ" if h: "cl = 6"
  proof -
    note c = negtwo[OF h]
    have len3: "length xs = 3" using c by simp
    have pos: "\<And>x::real. ripoly (Poly (refl_list xs)) x = 0 \<Longrightarrow> 0 < x" using c by blast
    have sep: "lowdeg_sep_ok_pure False (refl_list xs)" using c by blast
    show ?thesis by (rule lowdeg_emit_two_neg_correct[OF preB len3 pos sep])
  qed
  have Q34: "lowdeg_emit_neg_monadic (cl = 3 \<or> cl = 4) xs \<le> SPEC ?QQ" if n6: "cl \<noteq> 6"
  proof (cases "cl = 3 \<or> cl = 4")
    case True
    hence b: "(cl = 3 \<or> cl = 4) = True" by simp
    show ?thesis unfolding b by (rule lowdeg_emit_neg_one_correct[OF preB negone[OF True]])
  next
    case n34: False
    from n34 have b: "(cl = 3 \<or> cl = 4) = False" by simp
    have nn: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
    proof (cases "cl = 5")
      case True
      show "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
        using postwo[OF True] by blast
    next
      case n5: False
      with n34 n6 cls' have h: "cl = 1 \<or> cl = 2" by auto
      show "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
        using negnone[OF h] by blast
    qed
    show ?thesis unfolding b by (rule lowdeg_emit_neg_zero_correct[OF preB nn])
  qed
  have Q: "(if cl = 6 then lowdeg_emit_two_neg_monadic xs
            else lowdeg_emit_neg_monadic (cl = 3 \<or> cl = 4) xs) \<le> SPEC ?QQ"
    using Q6 Q34 by simp

  \<comment> \<open>\<^bold>\<open>Reduce the OUTER \<open>if\<close> only, and by \<open>unfolding\<close>, not \<open>simp\<close>.\<close>  Classes \<open>5\<close>/\<open>6\<close> are
     reachable, so the two inner \<open>if\<close>s stay, and \<open>simp\<close> would case-SPLIT them --- after which
     \<open>P\<close> and \<open>Q\<close>, which are stated ABOUT the \<open>if\<close>-expressions, no longer match syntactically and
     \<open>refine_vcg\<close> descends into a shape nothing closes.\<close>
  have c0: "(cl = 0) = False" using False by simp
  show ?thesis
    unfolding c0 if_False
    apply (refine_vcg P[THEN order_trans] Q[THEN order_trans]
        dsc_isolate_all_split_zero_check_correct[OF pre, THEN order_trans])
    apply (all \<open>(solves \<open>auto simp: ex_rat_pair_split\<close>)?\<close>)
    done
qed

theorem lowdeg_isolate_all_split_main_correct:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_pre xs"
  shows "lowdeg_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accQ, xs0).
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        \<exists>J. (I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J)) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
          \<exists>J. (I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))) \<and>
      (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
        \<exists>J. (I = real_to_rat_pair J \<and>
             dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J)) \<and>
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
          \<exists>J. (I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))) \<and>
      xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  from pre have len2: "2 \<le> length xs" unfolding dsc_isolate_all_split_pre_def by auto
  show ?thesis
    unfolding lowdeg_isolate_all_split_main_def PR_CONST_def
    \<comment> \<open>\<^bold>\<open>Composed by hand, not by \<open>refine_vcg\<close>.\<close>  \<open>refine_vcg\<close> SPLITS the \<open>if cl = 0\<close> before
       the body lemma can be applied, so the fall-through arm arrives already stripped of its
       \<open>if\<close> and \<open>rule\<close> cannot match.  @{thm [source] nres_bind_SPEC_extend} --- the codebase's
       own escape hatch for exactly this shape --- composes the classification's \<open>SPEC\<close> with
       the body lemma directly, leaving the \<open>if\<close> intact.\<close>
    apply (simp add: len2)
    apply (rule nres_bind_SPEC_extend[OF lowdeg_class_correct[OF dsc_isolate_all_split_pre_basic[OF pre]]])
    \<comment> \<open>\<^bold>\<open>\<open>weaken_SPEC\<close>, not \<open>rule\<close>.\<close> The \<open>simp\<close> above (which discharges the ASSERT) also normalises the
       postcondition (\<open>\<exists>J\<close> becomes \<open>\<exists>a b\<close> and the triple pattern splits into a nested \<open>case\<close>), so the
       pending goal and the body lemma are the same proposition in different form, which \<open>rule\<close> does
       not unify. \<open>weaken_SPEC\<close> leaves the difference as an implication between the postconditions.\<close>
    apply (rule weaken_SPEC[OF lowdeg_body_correct[OF pre]])
    \<comment> \<open>The postcondition implication \<open>weaken_SPEC\<close> leaves is precisely the \<open>\<exists>J\<close>-vs-\<open>\<exists>a b\<close>
       mismatch, so it needs @{thm [source] ex_rat_pair_split}; a bare \<open>blast\<close> cannot synthesise
       the pair.\<close>
    apply (all \<open>(solves \<open>simp\<close>)?\<close>)
    apply (all \<open>(solves \<open>auto simp: ex_rat_pair_split\<close>)?\<close>)
    done
qed


corollary lowdeg_isolate_all_split_main_terminates:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_pre xs"
  shows "nofail (lowdeg_isolate_all_split_main xs)"
  using lowdeg_isolate_all_split_main_correct[OF pre] by (rule SPEC_nofail)

end
