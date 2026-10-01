theory Power_Sub_Backmap
  imports Power_Sub_Spec "IsaRRI_Spec.NewDsc"
begin

text \<open>Back-mapping: the specification layer (real and rational intervals, as in \<open>Dsc_Misc\<close>).

  \<^bold>\<open>What this theory is for.\<close> The root correspondence (\<open>pow_sub_roots_set\<close>: the real roots of \<open>P\<close> are
  the fibres of \<open>Q\<close>'s under \<open>x \<mapsto> x\<^sup>h\<close>) is not enough to build the entry, because the solve returns isolating
  intervals, and its theorems are stated with @{const dsc_pair_ok}, i.e. with @{const roots_in}, i.e. with
  \<open>proots_count\<close>, a multiplicity-weighted count over an open interval. The back-map has to move that
  predicate across the substitution.

  \<^bold>\<open>The central theorem\<close> is \<open>pow_sub_roots_in_eq\<close>: for \<open>0 \<le> u\<close>, \<open>roots_in P u v = roots_in Q (u\<^sup>h) (v\<^sup>h)\<close>.
  The back-map's needs are corollaries: a window in \<open>x\<close>-space isolates a root of \<open>P\<close> exactly when its \<open>h\<close>-th
  power window isolates one of \<open>Q\<close>.

  \<^bold>\<open>The target\<close> is @{const dsc_pair_ok} plus completeness, not ``sorted, disjoint'': \<open>dsc_int\<close> conses
  onto an accumulator and emits degenerate \<open>(m,m)\<close> pairs adjacent to their neighbours. Nor can the
  composite meet a multiset equality against \<open>dsc_int\<close>'s own interval list, since it returns different
  intervals for the same polynomial; it gets the isolation property instead.

  \<^bold>\<open>Why the squarefree hypothesis is used rather than \<open>order_pcompose\<close>.\<close> Multiplicities do transfer in
  general (\<open>order x P = order (x\<^sup>h) Q\<close> for \<open>x \<noteq> 0\<close>, the extra factor in \<open>BF_Misc.order_pcompose\<close> being the
  multiplicity of \<open>x\<close> in \<open>t\<^sup>h - x\<^sup>h\<close>, which is 1 away from the origin). But squarefreeness is already a
  caller obligation, \<open>Q\<close> inherits it, and under it every order is 1, so the count collapses to a
  cardinality and the transfer is a bijection of finite sets.\<close>

section \<open>Under the squarefree contract, \<open>roots_in\<close> is a cardinality\<close>

lemma squarefree_order_eq_1:
  fixes p :: "real poly"
  assumes sf: "squarefree p" and root: "poly p x = 0"
  shows "order x p = 1"
proof -
  have pnz: "p \<noteq> 0" using sf by auto
  have ge1: "1 \<le> order x p" using root pnz by (simp add: order_root)
  moreover have "\<not> 2 \<le> order x p"
  proof
    assume "2 \<le> order x p"
    then have "[:- x, 1:] ^ 2 dvd p" using pnz by (simp add: order_divides)
    with sf have "is_unit ([:- x, 1:] :: real poly)" by (rule squarefreeD)
    then have "degree ([:- x, 1:] :: real poly) = 0" by (rule is_unit_imp_degree_0)
    then show False by simp
  qed
  ultimately show ?thesis by simp
qed

lemma roots_in_squarefree_card:
  fixes p :: "real poly"
  assumes sf: "squarefree p"
  shows "roots_in p a b = card {x. a < x \<and> x < b \<and> poly p x = 0}"
proof -
  have pnz: "p \<noteq> 0" using sf by auto
  have set_eq: "proots_within p {x. a < x \<and> x < b} = {x. a < x \<and> x < b \<and> poly p x = 0}"
    by (auto simp: proots_within_def)
  have "roots_in p a b = (\<Sum>r \<in> proots_within p {x. a < x \<and> x < b}. order r p)"
    by (simp add: roots_in_def proots_count_def)
  also have "\<dots> = (\<Sum>r \<in> proots_within p {x. a < x \<and> x < b}. 1)"
    by (rule sum.cong) (auto simp: proots_within_def squarefree_order_eq_1[OF sf])
  also have "\<dots> = card (proots_within p {x. a < x \<and> x < b})" by simp
  finally show ?thesis by (simp add: set_eq)
qed

text \<open>A zero count means an empty root set — needed because the impl tests a COUNT but the
  argument needs the absence of a witness. Finiteness is what turns one into the other.\<close>

lemma roots_in_zero_imp_no_root:
  fixes p :: "real poly"
  assumes sf: "squarefree p" and z: "roots_in p a b = 0"
  shows "\<not> (a < x \<and> x < b \<and> poly p x = 0)"
proof
  assume x: "a < x \<and> x < b \<and> poly p x = 0"
  have pnz: "p \<noteq> 0" using sf by auto
  have fin: "finite {x. a < x \<and> x < b \<and> poly p x = 0}"
    by (rule finite_subset[of _ "{x. poly p x = 0}"]) (auto simp: poly_roots_finite[OF pnz])
  have "{x. a < x \<and> x < b \<and> poly p x = 0} \<noteq> {}" using x by blast
  with fin have "0 < card {x. a < x \<and> x < b \<and> poly p x = 0}" by (simp add: card_gt_0_iff)
  with z roots_in_squarefree_card[OF sf] show False by simp
qed

section \<open>The crux: the substitution preserves the isolation COUNT\<close>

text \<open>The \<open>h\<close>-th power is a bijection from \<open>P\<close>'s roots in \<open>(u,v)\<close> onto \<open>Q\<close>'s roots in
  \<open>(u\<^sup>h, v\<^sup>h)\<close> whenever \<open>0 \<le> u\<close>. The window clamp is exactly what buys \<open>0 \<le> u\<close>, and this
  is where it earns its keep: without it the map is 2-to-1 on a straddling window and the count
  on the left would be twice the count on the right.\<close>

text \<open>\<open>u \<le> v\<close> is required: without it the statement is false for even \<open>h\<close>. Take \<open>u = 0\<close>, \<open>v = -2\<close>,
  \<open>h = 2\<close>: the \<open>x\<close>-window \<open>{x. 0 < x \<and> x < -2}\<close> is empty while the \<open>y\<close>-window \<open>{y. 0 < y \<and> y < 4}\<close> need not be,
  because \<open>v \<mapsto> v\<^sup>h\<close> discards the sign. Every call site has \<open>u < v\<close>.\<close>

lemma pow_sub_backmap_bij:
  fixes P Q :: "real poly" and u v :: real
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and u0: "0 \<le> u" and uv: "u \<le> v"
  shows "bij_betw (\<lambda>x. x ^ h)
           {x. u < x \<and> x < v \<and> poly P x = 0}
           {y. u ^ h < y \<and> y < v ^ h \<and> poly Q y = 0}"
proof (rule bij_betw_imageI)
  show "inj_on (\<lambda>x. x ^ h) {x. u < x \<and> x < v \<and> poly P x = 0}"
  proof (rule inj_onI)
    fix x y
    assume xin: "x \<in> {x. u < x \<and> x < v \<and> poly P x = 0}"
      and yin: "y \<in> {x. u < x \<and> x < v \<and> poly P x = 0}"
      and eq: "x ^ h = y ^ h"
    from xin have xu: "u < x" by simp
    from yin have yu: "u < y" by simp
    have nx: "0 \<le> x" using u0 xu by linarith
    have ny: "0 \<le> y" using u0 yu by linarith
    show "x = y" using eq nx ny h by (rule power_eq_imp_eq_base)
  qed
next
  show "(\<lambda>x. x ^ h) ` {x. u < x \<and> x < v \<and> poly P x = 0}
          = {y. u ^ h < y \<and> y < v ^ h \<and> poly Q y = 0}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> (\<lambda>x. x ^ h) ` {x. u < x \<and> x < v \<and> poly P x = 0}"
    then obtain x where x: "u < x" "x < v" "poly P x = 0" and yx: "y = x ^ h" by auto
    from u0 x(1) have "u ^ h < x ^ h" using h by (simp add: power_strict_mono)
    moreover from x(1) x(2) u0 have "x ^ h < v ^ h" using h by (simp add: power_strict_mono)
    moreover have "poly Q y = 0" using x(3) yx by (simp add: P poly_pcompose_monom)
    ultimately show "y \<in> {y. u ^ h < y \<and> y < v ^ h \<and> poly Q y = 0}" using yx by simp
  next
    fix y assume y: "y \<in> {y. u ^ h < y \<and> y < v ^ h \<and> poly Q y = 0}"
    then have ylo: "u ^ h < y" and yhi: "y < v ^ h" and yr: "poly Q y = 0" by auto
    have ypos: "0 < y" using ylo u0 by (meson le_less_trans zero_le_power)
    define x where "x = y powr (1 / real h)"
    have xpos: "0 < x" unfolding x_def using ypos by simp
    have xh: "x ^ h = y" unfolding x_def using ypos h by (simp add: powr_root_pow)
    have "u < x"
    proof (rule ccontr)
      assume "\<not> u < x"
      then have "x \<le> u" by simp
      with xpos have "x ^ h \<le> u ^ h" by (simp add: power_mono)
      with xh ylo show False by simp
    qed
    moreover have "x < v"
    proof (rule ccontr)
      assume "\<not> x < v"
      then have vx: "v \<le> x" by simp
      have "0 \<le> v" using u0 uv by linarith
      with vx have "v ^ h \<le> x ^ h" by (simp add: power_mono)
      with xh yhi show False by simp
    qed
    moreover have "poly P x = 0" using yr xh by (simp add: P poly_pcompose_monom)
    ultimately show "y \<in> (\<lambda>x. x ^ h) ` {x. u < x \<and> x < v \<and> poly P x = 0}"
      using xh by (auto simp: image_iff)
  qed
qed

theorem pow_sub_roots_in_eq:
  fixes P Q :: "real poly" and u v :: real
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and u0: "0 \<le> u" and uv: "u \<le> v"
  shows "roots_in P u v = roots_in Q (u ^ h) (v ^ h)"
proof -
  have sfQ: "squarefree Q" using h sf P by (simp add: pcompose_monom_squarefreeD)
  have "roots_in P u v = card {x. u < x \<and> x < v \<and> poly P x = 0}"
    by (rule roots_in_squarefree_card[OF sf])
  also have "\<dots> = card {y. u ^ h < y \<and> y < v ^ h \<and> poly Q y = 0}"
    using pow_sub_backmap_bij[OF h P u0 uv] by (rule bij_betw_same_card)
  also have "\<dots> = roots_in Q (u ^ h) (v ^ h)"
    by (rule roots_in_squarefree_card[OF sfQ, symmetric])
  finally show ?thesis .
qed
  \<comment> \<open>\<^bold>\<open>The theorem the precision loop is built on.\<close> It is an equality, so it transfers isolation in
     both directions; in particular a certificate computed on the reduced polynomial \<open>Q\<close> (degree \<open>n/h\<close>)
     certifies the emitted \<open>x\<close>-window.\<close>

section \<open>Transferring the isolation predicate the pipeline actually states\<close>

text \<open>@{const dsc_pair_ok}'s two arms do not transfer the same way. The interval arm moves by the count
  theorem above. The degenerate arm (\<open>fst I = snd I\<close>, an exactly representable root) transfers only when
  the \<open>h\<close>-th root of that point is itself representable, which is not automatic: \<open>Q(u) = 2u - 1\<close> has the
  exact dyadic root \<open>1/2\<close>, but \<open>P(x) = 2x\<^sup>2 - 1\<close> has roots \<open>\<plusminus>1/\<surd>2\<close>, which no dyadic pair pins. So a
  degenerate \<open>Q\<close>-interval with an irrational back-image must be emitted as a proper interval, and the
  theorem below keeps the two arms separate.\<close>

theorem pow_sub_pair_ok_interval:
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and u0: "0 \<le> u" and uv: "u < v"
    and iso: "roots_in Q (u ^ h) (v ^ h) = 1"
  shows "dsc_pair_ok P (u, v)"
  using uv pow_sub_roots_in_eq[OF h P sf u0 less_imp_le[OF uv]] iso
  by (simp add: dsc_pair_ok_def)

theorem pow_sub_pair_ok_degenerate:
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h"
    and root: "poly Q (u ^ h) = 0"
  shows "dsc_pair_ok P (u, u)"
  using root by (simp add: dsc_pair_ok_def P poly_pcompose_monom)

text \<open>\<^bold>\<open>A widening lemma.\<close> The implementation cannot compute \<open>u\<close> with \<open>u\<^sup>h\<close> exactly equal to a
  \<open>Q\<close>-endpoint. A widening back-map computes \<open>u\<close> with \<open>u\<^sup>h \<le> a\<close> and \<open>v\<close> with \<open>b \<le> v\<^sup>h\<close>, a wider window, and
  must certify that the widening swept in no extra root: the two shoulders are root-free.\<close>

theorem pow_sub_backmap_certificate:
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and u0: "0 \<le> u" and uv: "u < v"
    and lo: "u ^ h \<le> a" and hi: "b \<le> v ^ h"
    and ab: "a < b"
    and core: "roots_in Q a b = 1"
    and shoulder_lo: "roots_in Q (u ^ h) a = 0"
    and shoulder_hi: "roots_in Q b (v ^ h) = 0"
    and no_a: "poly Q a \<noteq> 0" and no_b: "poly Q b \<noteq> 0"
  shows "dsc_pair_ok P (u, v)"
proof -
  have sfQ: "squarefree Q" using h sf P by (simp add: pcompose_monom_squarefreeD)
  have set_eq: "{y. u ^ h < y \<and> y < v ^ h \<and> poly Q y = 0}
                  = {y. a < y \<and> y < b \<and> poly Q y = 0}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> {y. u ^ h < y \<and> y < v ^ h \<and> poly Q y = 0}"
    then have y1: "u ^ h < y" and y2: "y < v ^ h" and yr: "poly Q y = 0" by auto
    have "a < y"
    proof (rule ccontr)
      assume "\<not> a < y"
      then have "y \<le> a" by simp
      show False
      proof (cases "y = a")
        case True with no_a yr show False by simp
      next
        case False
        with \<open>y \<le> a\<close> have "y < a" by simp
        with y1 yr roots_in_zero_imp_no_root[OF sfQ shoulder_lo] show False by simp
      qed
    qed
    moreover have "y < b"
    proof (rule ccontr)
      assume "\<not> y < b"
      then have "b \<le> y" by simp
      show False
      proof (cases "y = b")
        case True with no_b yr show False by simp
      next
        case False
        with \<open>b \<le> y\<close> have "b < y" by simp
        with y2 yr roots_in_zero_imp_no_root[OF sfQ shoulder_hi] show False by simp
      qed
    qed
    ultimately show "y \<in> {y. a < y \<and> y < b \<and> poly Q y = 0}" using yr by simp
  next
    fix y assume "y \<in> {y. a < y \<and> y < b \<and> poly Q y = 0}"
    then show "y \<in> {y. u ^ h < y \<and> y < v ^ h \<and> poly Q y = 0}" using lo hi by auto
  qed
  have "roots_in Q (u ^ h) (v ^ h) = 1"
    using core roots_in_squarefree_card[OF sfQ] set_eq by simp
  with h P sf u0 uv show ?thesis by (rule pow_sub_pair_ok_interval)
qed
  \<comment> \<open>\<^bold>\<open>What a widening loop discharges\<close>: raise the precision until both shoulders test root-free on \<open>Q\<close>.
     It terminates because \<open>u\<^sup>h\<close> increases to \<open>a\<close> and \<open>v\<^sup>h\<close> decreases to \<open>b\<close> while the root-free margin
     around \<open>[a,b]\<close> has positive width, not because the shoulders shrink to nothing, which they do not
     when \<open>Q\<close>'s intervals touch.\<close>

section \<open>Termination: the root-free margin exists and is uniform\<close>

text \<open>Nothing so far says the widening loop stops. It does, and not because the shoulders shrink to
  nothing (when \<open>Q\<close>'s intervals touch they do not): the shoulders are eventually contained in a root-free
  neighbourhood of the endpoint, whose width depends on \<open>Q\<close> alone.

  The statement is uniform in the shoulder: one \<open>e\<close> works for every \<open>lo \<in> [a - e, a]\<close> and every
  \<open>hi \<in> [b, b + e]\<close>. A per-shoulder \<open>e\<close> would not discharge a loop, which does not choose its \<open>lo\<close> but
  gets whatever the integer \<open>h\<close>-th root produced.\<close>

lemma roots_in_mono_zero:
  fixes p :: "real poly"
  assumes sf: "squarefree p" and z: "roots_in p c d = 0" and lo: "c \<le> c'" and hi: "d' \<le> d"
  shows "roots_in p c' d' = 0"
proof -
  have pnz: "p \<noteq> 0" using sf by auto
  have sub: "{x. c' < x \<and> x < d' \<and> poly p x = 0} \<subseteq> {x. c < x \<and> x < d \<and> poly p x = 0}"
    using lo hi by auto
  have fin: "finite {x. c < x \<and> x < d \<and> poly p x = 0}"
    by (rule finite_subset[of _ "{x. poly p x = 0}"]) (auto simp: poly_roots_finite[OF pnz])
  from z have empty: "{x. c < x \<and> x < d \<and> poly p x = 0} = {}"
    using roots_in_squarefree_card[OF sf] fin by auto
  have emp: "{x. c' < x \<and> x < d' \<and> poly p x = 0} = {}" using sub empty by auto
  show ?thesis by (simp add: roots_in_squarefree_card[OF sf] emp)
qed

text \<open>These two have no \<open>poly p a \<noteq> 0\<close> hypothesis: the margin is \<open>Max\<close> of the roots strictly below \<open>a\<close>,
  which exists whether or not \<open>a\<close> is itself a root, and the degenerate case needs these lemmas at a
  root.\<close>

lemma roots_free_margin_below:
  fixes p :: "real poly"
  assumes sf: "squarefree p"
  shows "\<exists>e>0. roots_in p (a - e) a = 0"
proof -
  have pnz: "p \<noteq> 0" using sf by auto
  have finR: "finite {x. poly p x = 0}" by (rule poly_roots_finite[OF pnz])
  define S where "S = {x. poly p x = 0 \<and> x < a}"
  have finS: "finite S" unfolding S_def using finR by (auto intro: finite_subset)
  show ?thesis
  proof (cases "S = {}")
    case True
    have emp: "{x. a - 1 < x \<and> x < a \<and> poly p x = 0} = {}" using True by (auto simp: S_def)
    have "roots_in p (a - 1) a = 0" by (simp add: roots_in_squarefree_card[OF sf] emp)
    then show ?thesis by (intro exI[of _ 1]) simp
  next
    case False
    define r0 where "r0 = Max S"
    have r0S: "r0 \<in> S" unfolding r0_def using finS False by (rule Max_in)
    then have r0a: "r0 < a" by (simp add: S_def)
    have emp: "{x. r0 < x \<and> x < a \<and> poly p x = 0} = {}"
    proof (rule ccontr)
      assume "{x. r0 < x \<and> x < a \<and> poly p x = 0} \<noteq> {}"
      then obtain x where x: "r0 < x" "x < a" "poly p x = 0" by auto
      then have "x \<in> S" by (simp add: S_def)
      with finS have "x \<le> r0" unfolding r0_def by (rule Max_ge)
      with x show False by simp
    qed
    have z: "roots_in p r0 a = 0" by (simp add: roots_in_squarefree_card[OF sf] emp)
    have "a - (a - r0) = r0" by simp
    with z have "roots_in p (a - (a - r0)) a = 0" by simp
    then show ?thesis using r0a by (intro exI[of _ "a - r0"]) simp
  qed
qed

lemma roots_free_margin_above:
  fixes p :: "real poly"
  assumes sf: "squarefree p"
  shows "\<exists>e>0. roots_in p b (b + e) = 0"
proof -
  have pnz: "p \<noteq> 0" using sf by auto
  have finR: "finite {x. poly p x = 0}" by (rule poly_roots_finite[OF pnz])
  define S where "S = {x. poly p x = 0 \<and> b < x}"
  have finS: "finite S" unfolding S_def using finR by (auto intro: finite_subset)
  show ?thesis
  proof (cases "S = {}")
    case True
    have emp: "{x. b < x \<and> x < b + 1 \<and> poly p x = 0} = {}" using True by (auto simp: S_def)
    have "roots_in p b (b + 1) = 0" by (simp add: roots_in_squarefree_card[OF sf] emp)
    then show ?thesis by (intro exI[of _ 1]) simp
  next
    case False
    define r1 where "r1 = Min S"
    have r1S: "r1 \<in> S" unfolding r1_def using finS False by (rule Min_in)
    then have r1b: "b < r1" by (simp add: S_def)
    have emp: "{x. b < x \<and> x < r1 \<and> poly p x = 0} = {}"
    proof (rule ccontr)
      assume "{x. b < x \<and> x < r1 \<and> poly p x = 0} \<noteq> {}"
      then obtain x where x: "b < x" "x < r1" "poly p x = 0" by auto
      then have "x \<in> S" by (simp add: S_def)
      with finS have "r1 \<le> x" unfolding r1_def by (rule Min_le)
      with x show False by simp
    qed
    have z: "roots_in p b r1 = 0" by (simp add: roots_in_squarefree_card[OF sf] emp)
    have "b + (r1 - b) = r1" by simp
    with z have "roots_in p b (b + (r1 - b)) = 0" by simp
    then show ?thesis using r1b by (intro exI[of _ "r1 - b"]) simp
  qed
qed

theorem pow_sub_backmap_margin_uniform:
  fixes Q :: "real poly" and a b :: real
  assumes sf: "squarefree Q" and na: "poly Q a \<noteq> 0" and nb: "poly Q b \<noteq> 0"
  shows "\<exists>e>0. \<forall>lo hi. a - e \<le> lo \<and> lo \<le> a \<and> b \<le> hi \<and> hi \<le> b + e
                 \<longrightarrow> roots_in Q lo a = 0 \<and> roots_in Q b hi = 0"
proof -
  from roots_free_margin_below[OF sf] obtain e1 where e1: "0 < e1"
    and z1: "roots_in Q (a - e1) a = 0" by blast
  from roots_free_margin_above[OF sf] obtain e2 where e2: "0 < e2"
    and z2: "roots_in Q b (b + e2) = 0" by blast
  define e where "e = min e1 e2"
  have epos: "0 < e" unfolding e_def using e1 e2 by simp
  have "\<forall>lo hi. a - e \<le> lo \<and> lo \<le> a \<and> b \<le> hi \<and> hi \<le> b + e
          \<longrightarrow> roots_in Q lo a = 0 \<and> roots_in Q b hi = 0"
  proof (intro allI impI conjI)
    fix lo hi :: real
    assume A: "a - e \<le> lo \<and> lo \<le> a \<and> b \<le> hi \<and> hi \<le> b + e"
    have "a - e1 \<le> a - e" unfolding e_def by simp
    also have "\<dots> \<le> lo" using A by simp
    finally show "roots_in Q lo a = 0" by (rule roots_in_mono_zero[OF sf z1 _ order_refl])
  next
    fix lo hi :: real
    assume A: "a - e \<le> lo \<and> lo \<le> a \<and> b \<le> hi \<and> hi \<le> b + e"
    have "hi \<le> b + e" using A by simp
    also have "\<dots> \<le> b + e2" unfolding e_def by simp
    finally show "roots_in Q b hi = 0" by (rule roots_in_mono_zero[OF sf z2 order_refl])
  qed
  with epos show ?thesis by blast
qed
  \<comment> \<open>\<^bold>\<open>This makes the widening loop total.\<close> \<open>lo\<close> is the \<open>h\<close>-th power of a floored integer \<open>h\<close>-th root
     at precision \<open>m\<close>, so \<open>lo \<le> a\<close> always and \<open>a - lo\<close> tends to \<open>0\<close> as \<open>m\<close> grows; similarly for \<open>hi\<close> from
     above. So some precision puts both shoulders inside \<open>e\<close>, and then both certificates read 0. \<open>e\<close>
     depends on \<open>Q\<close>'s root separation, so this bounds the loop's existence, not its cost.\<close>

section \<open>The back-map at precision \<open>m\<close>, and that some precision works\<close>

text \<open>So far the back-map is characterised only by \<open>u\<^sup>h \<le> a\<close> and \<open>b \<le> v\<^sup>h\<close>. The loop needs a construction
  and a proof that raising \<open>m\<close> eventually satisfies the certificate.

  \<^bold>\<open>The specification-level construction is the floor of the scaled real root\<close>, not an integer \<open>h\<close>-th
  root. The two agree (the floor of \<open>a\<^sup>1\<^sup>/\<^sup>h * 2\<^sup>m\<close> is the largest \<open>n\<close> with \<open>(n/2\<^sup>m)\<^sup>h \<le> a\<close>), but the floor form
  needs no integer-root theory here, and the implementation's bisection refines to it
  (\<open>Power_Sub_Root_Impl\<close>).

  There is no a-priori bound on \<open>m\<close>: it would have to be computed from \<open>Q\<close>'s root separation, which is
  not required of callers. The loop is hybrid (test, double, retry), and its termination is the
  existence theorem below.\<close>

definition pow_sub_lo :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "pow_sub_lo h m a = real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor> / 2 ^ m"

definition pow_sub_hi :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "pow_sub_hi h m b = real_of_int \<lceil>(b powr (1 / real h)) * 2 ^ m\<rceil> / 2 ^ m"

lemma pow_sub_lo_bounds:
  fixes a :: real
  assumes a0: "0 \<le> a"
  shows "a powr (1 / real h) - 1 / 2 ^ m < pow_sub_lo h m a
         \<and> pow_sub_lo h m a \<le> a powr (1 / real h)"
proof -
  define r where "r = a powr (1 / real h)"
  have "real_of_int \<lfloor>r * 2 ^ m\<rfloor> \<le> r * 2 ^ m" by simp
  moreover have "r * 2 ^ m - 1 < real_of_int \<lfloor>r * 2 ^ m\<rfloor>" by simp
  ultimately show ?thesis
    unfolding pow_sub_lo_def r_def[symmetric] by (simp add: field_simps)
qed

lemma pow_sub_lo_nonneg:
  fixes a :: real
  assumes a0: "0 \<le> a"
  shows "0 \<le> pow_sub_lo h m a"
proof -
  have "0 \<le> a powr (1 / real h) * 2 ^ m" by simp
  then have "0 \<le> \<lfloor>a powr (1 / real h) * 2 ^ m\<rfloor>" by simp
  then show ?thesis unfolding pow_sub_lo_def by simp
qed

lemma pow_sub_lo_pow_le:
  fixes a :: real
  assumes a0: "0 \<le> a" and h: "0 < h"
  shows "(pow_sub_lo h m a) ^ h \<le> a"
proof -
  have "(pow_sub_lo h m a) ^ h \<le> (a powr (1 / real h)) ^ h"
    using pow_sub_lo_nonneg[OF a0] pow_sub_lo_bounds[OF a0] by (simp add: power_mono)
  also have "\<dots> = a" using a0 h by (rule powr_root_pow)
  finally show ?thesis .
qed

lemma pow_sub_hi_bounds:
  fixes b :: real
  shows "b powr (1 / real h) \<le> pow_sub_hi h m b"
proof -
  have "b powr (1 / real h) * 2 ^ m \<le> real_of_int \<lceil>b powr (1 / real h) * 2 ^ m\<rceil>" by simp
  then show ?thesis unfolding pow_sub_hi_def by (simp add: field_simps)
qed

lemma pow_sub_hi_nonneg:
  fixes b :: real
  shows "0 \<le> pow_sub_hi h m b"
  using pow_sub_hi_bounds[where b = b and h = h and m = m]
  by (meson order_trans powr_ge_zero)

lemma pow_sub_hi_pow_ge:
  fixes b :: real
  assumes b0: "0 \<le> b" and h: "0 < h"
  shows "b \<le> (pow_sub_hi h m b) ^ h"
proof -
  have "b = (b powr (1 / real h)) ^ h" using b0 h by (rule powr_root_pow[symmetric])
  also have "\<dots> \<le> (pow_sub_hi h m b) ^ h"
    using pow_sub_hi_bounds[where b = b and h = h and m = m] by (simp add: power_mono)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>Monotonicity in the precision.\<close> The two endpoints' precisions are obtained INDEPENDENTLY
  (each from its own continuity argument), but the dyadic output format carries ONE shared
  exponent per interval, so they must be merged into a single \<open>m\<close>. That is only sound if raising
  \<open>m\<close> never makes an endpoint worse — which is what these say. Without them the capstone below
  would need a per-endpoint exponent the ABI does not have.\<close>

lemma floor_scale_ge:
  fixes y :: real and k :: nat
  shows "int (2 ^ k) * \<lfloor>y\<rfloor> \<le> \<lfloor>y * 2 ^ k\<rfloor>"
proof -
  have "real_of_int (int (2 ^ k) * \<lfloor>y\<rfloor>) = 2 ^ k * real_of_int \<lfloor>y\<rfloor>" by simp
  also have "\<dots> \<le> 2 ^ k * y" by simp
  finally show ?thesis by (simp add: le_floor_iff mult.commute)
qed

lemma ceiling_scale_le:
  fixes y :: real and k :: nat
  shows "\<lceil>y * 2 ^ k\<rceil> \<le> int (2 ^ k) * \<lceil>y\<rceil>"
proof -
  have "y * 2 ^ k \<le> real_of_int \<lceil>y\<rceil> * 2 ^ k" by simp
  also have "\<dots> = real_of_int (int (2 ^ k) * \<lceil>y\<rceil>)" by (simp add: mult.commute)
  finally show ?thesis by (simp add: ceiling_le_iff)
qed

lemma pow_sub_lo_grid_mono:
  fixes a :: real
  assumes mm: "m \<le> m'"
  shows "pow_sub_lo h m a \<le> pow_sub_lo h m' a"
proof -
  define r where "r = a powr (1 / real h)"
  define k where "k = m' - m"
  have m': "m' = m + k" unfolding k_def using mm by simp
  have "int (2 ^ k) * \<lfloor>r * 2 ^ m\<rfloor> \<le> \<lfloor>r * 2 ^ m * 2 ^ k\<rfloor>"
    by (rule floor_scale_ge[where y = "r * 2 ^ m" and k = k])
  then have "real_of_int (int (2 ^ k) * \<lfloor>r * 2 ^ m\<rfloor>)
               \<le> real_of_int \<lfloor>r * 2 ^ m * 2 ^ k\<rfloor>"
    by (simp only: of_int_le_iff)
  then have "real_of_int \<lfloor>r * 2 ^ m\<rfloor> * 2 ^ k \<le> real_of_int \<lfloor>r * 2 ^ m * 2 ^ k\<rfloor>"
    by (simp add: mult.commute)
  then have "real_of_int \<lfloor>r * 2 ^ m\<rfloor> / 2 ^ m
               \<le> real_of_int \<lfloor>r * 2 ^ (m + k)\<rfloor> / 2 ^ (m + k)"
    by (simp add: field_simps power_add)
  then show ?thesis unfolding pow_sub_lo_def r_def[symmetric] m' .
qed

lemma pow_sub_hi_grid_mono:
  fixes b :: real
  assumes mm: "m \<le> m'"
  shows "pow_sub_hi h m' b \<le> pow_sub_hi h m b"
proof -
  define r where "r = b powr (1 / real h)"
  define k where "k = m' - m"
  have m': "m' = m + k" unfolding k_def using mm by simp
  have "\<lceil>r * 2 ^ m * 2 ^ k\<rceil> \<le> int (2 ^ k) * \<lceil>r * 2 ^ m\<rceil>"
    by (rule ceiling_scale_le[where y = "r * 2 ^ m" and k = k])
  then have "real_of_int \<lceil>r * 2 ^ m * 2 ^ k\<rceil>
               \<le> real_of_int (int (2 ^ k) * \<lceil>r * 2 ^ m\<rceil>)"
    by (simp only: of_int_le_iff)
  then have "real_of_int \<lceil>r * 2 ^ m * 2 ^ k\<rceil> \<le> real_of_int \<lceil>r * 2 ^ m\<rceil> * 2 ^ k"
    by (simp add: mult.commute)
  then have "real_of_int \<lceil>r * 2 ^ (m + k)\<rceil> / 2 ^ (m + k)
               \<le> real_of_int \<lceil>r * 2 ^ m\<rceil> / 2 ^ m"
    by (simp add: field_simps power_add)
  then show ?thesis unfolding pow_sub_hi_def r_def[symmetric] m' .
qed

text \<open>Convergence. Continuity of \<open>x \<mapsto> x\<^sup>h\<close> at the real root turns the \<open>2\<^sup>-\<^sup>m\<close> grid error into an \<open>e\<close>-error
  on the \<open>h\<close>-th power side, the side the certificate is tested on. \<open>dyadic_grid_below\<close> is spelled out (an
  Archimedean witness plus \<open>less_exp\<close>), since a \<open>metis\<close> call with \<open>real_arch_pow_inv\<close> does not terminate
  in reasonable time.\<close>

lemma dyadic_grid_below:
  fixes d :: real
  assumes d: "0 < d"
  obtains m :: nat where "1 / 2 ^ m < d"
proof -
  obtain n :: nat where n: "1 / d < real n" using reals_Archimedean2 by blast
  have "n < 2 ^ n" by (rule less_exp)
  then have "real n < real (2 ^ n)" by (simp only: of_nat_less_iff)
  then have n2: "real n < 2 ^ n" by simp
  have "1 / d < 2 ^ n" using n n2 by (rule less_trans)
  then have "1 < d * 2 ^ n" using d by (simp add: field_simps)
  then have "1 / 2 ^ n < d" by (simp add: field_simps)
  then show thesis by (rule that)
qed

lemma pow_sub_lo_converges:
  fixes a :: real
  assumes a0: "0 \<le> a" and h: "0 < h" and e: "0 < e"
  shows "\<exists>m. a - e \<le> (pow_sub_lo h m a) ^ h"
proof -
  define r where "r = a powr (1 / real h)"
  have rh: "r ^ h = a" unfolding r_def using a0 h by (rule powr_root_pow)
  have "isCont (\<lambda>x. x ^ h) r" by simp
  then have "(\<lambda>x. x ^ h) \<midarrow>r\<rightarrow> r ^ h" by (simp add: isCont_def)
  from LIM_D[OF this e] obtain d where d: "0 < d"
    and dd: "\<And>x. x \<noteq> r \<Longrightarrow> \<bar>x - r\<bar> < d \<Longrightarrow> \<bar>x ^ h - r ^ h\<bar> < e" by auto
  obtain m :: nat where m: "1 / 2 ^ m < d" using d by (rule dyadic_grid_below)
  have lo_le: "pow_sub_lo h m a \<le> r"
    using pow_sub_lo_bounds[OF a0] unfolding r_def by simp
  have lo_gt: "r - 1 / 2 ^ m < pow_sub_lo h m a"
    using pow_sub_lo_bounds[OF a0] unfolding r_def by simp
  show ?thesis
  proof (cases "pow_sub_lo h m a = r")
    case True
    then have "(pow_sub_lo h m a) ^ h = a" using rh by simp
    then show ?thesis using e by (intro exI[of _ m]) simp
  next
    case False
    have "\<bar>pow_sub_lo h m a - r\<bar> < d"
      using lo_le lo_gt m by (simp add: abs_real_def)
    from dd[OF False this] have "\<bar>(pow_sub_lo h m a) ^ h - a\<bar> < e" using rh by simp
    then show ?thesis by (intro exI[of _ m]) simp
  qed
qed

lemma pow_sub_hi_converges:
  fixes b :: real
  assumes b0: "0 \<le> b" and h: "0 < h" and e: "0 < e"
  shows "\<exists>m. (pow_sub_hi h m b) ^ h \<le> b + e"
proof -
  define r where "r = b powr (1 / real h)"
  have rh: "r ^ h = b" unfolding r_def using b0 h by (rule powr_root_pow)
  have "isCont (\<lambda>x. x ^ h) r" by simp
  then have "(\<lambda>x. x ^ h) \<midarrow>r\<rightarrow> r ^ h" by (simp add: isCont_def)
  from LIM_D[OF this e] obtain d where d: "0 < d"
    and dd: "\<And>x. x \<noteq> r \<Longrightarrow> \<bar>x - r\<bar> < d \<Longrightarrow> \<bar>x ^ h - r ^ h\<bar> < e" by auto
  obtain m :: nat where m: "1 / 2 ^ m < d" using d by (rule dyadic_grid_below)
  have hi_ge: "r \<le> pow_sub_hi h m b" using pow_sub_hi_bounds[where b = b and h = h and m = m] unfolding r_def by simp
  have hi_lt: "pow_sub_hi h m b < r + 1 / 2 ^ m"
  proof -
    have pos: "(0::real) < 2 ^ m" by simp
    have "real_of_int \<lceil>r * 2 ^ m\<rceil> < r * 2 ^ m + 1"
      using ceiling_correct[of "r * 2 ^ m"] by simp
    from divide_strict_right_mono[OF this pos]
    have "real_of_int \<lceil>r * 2 ^ m\<rceil> / 2 ^ m < (r * 2 ^ m + 1) / 2 ^ m" .
    also have "(r * 2 ^ m + 1) / 2 ^ m = r + 1 / 2 ^ m"
      using pos by (simp add: add_divide_distrib)
    finally show ?thesis unfolding pow_sub_hi_def r_def[symmetric] .
  qed
  show ?thesis
  proof (cases "pow_sub_hi h m b = r")
    case True
    then have "(pow_sub_hi h m b) ^ h = b" using rh by simp
    then show ?thesis using e by (intro exI[of _ m]) simp
  next
    case False
    have "\<bar>pow_sub_hi h m b - r\<bar> < d"
      using hi_ge hi_lt m by (simp add: abs_real_def)
    from dd[OF False this] have "\<bar>(pow_sub_hi h m b) ^ h - b\<bar> < e" using rh by simp
    then show ?thesis by (intro exI[of _ m]) simp
  qed
qed

text \<open>\<^bold>\<open>Some precision certifies.\<close> The loop's variant is built from this theorem: the hybrid
  test-and-double search cannot run forever.\<close>

theorem pow_sub_backmap_precision_exists:
  fixes P Q :: "real poly" and a b :: real
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and a0: "0 \<le> a" and ab: "a < b"
    and core: "roots_in Q a b = 1"
    and na: "poly Q a \<noteq> 0" and nb: "poly Q b \<noteq> 0"
  shows "\<exists>m. dsc_pair_ok P (pow_sub_lo h m a, pow_sub_hi h m b)"
proof -
  have sfQ: "squarefree Q" using h sf P by (simp add: pcompose_monom_squarefreeD)
  have b0: "0 \<le> b" using a0 ab by simp
  from pow_sub_backmap_margin_uniform[OF sfQ na nb] obtain e where e: "0 < e"
    and marg: "\<forall>lo hi. a - e \<le> lo \<and> lo \<le> a \<and> b \<le> hi \<and> hi \<le> b + e
                 \<longrightarrow> roots_in Q lo a = 0 \<and> roots_in Q b hi = 0" by blast
  from pow_sub_lo_converges[OF a0 h e] obtain m1 where m1: "a - e \<le> (pow_sub_lo h m1 a) ^ h" ..
  from pow_sub_hi_converges[OF b0 h e] obtain m2 where m2: "(pow_sub_hi h m2 b) ^ h \<le> b + e" ..
  define m where "m = max m1 m2"
  have lo_mono: "(pow_sub_lo h m1 a) ^ h \<le> (pow_sub_lo h m a) ^ h"
    using pow_sub_lo_grid_mono[where m = m1 and m' = m and h = h and a = a] pow_sub_lo_nonneg[OF a0] m_def
    by (simp add: power_mono)
  have hi_mono: "(pow_sub_hi h m b) ^ h \<le> (pow_sub_hi h m2 b) ^ h"
    using pow_sub_hi_grid_mono[where m = m2 and m' = m and h = h and b = b] pow_sub_hi_nonneg[where b = b and h = h and m = m] m_def
    by (simp add: power_mono)
  have lo_lo: "a - e \<le> (pow_sub_lo h m a) ^ h" using m1 lo_mono by simp
  have hi_hi: "(pow_sub_hi h m b) ^ h \<le> b + e" using m2 hi_mono by simp
  have lo_le: "(pow_sub_lo h m a) ^ h \<le> a" by (rule pow_sub_lo_pow_le[OF a0 h])
  have hi_ge: "b \<le> (pow_sub_hi h m b) ^ h" by (rule pow_sub_hi_pow_ge[OF b0 h])
  from marg lo_lo lo_le hi_ge hi_hi
  have sh_lo: "roots_in Q ((pow_sub_lo h m a) ^ h) a = 0"
    and sh_hi: "roots_in Q b ((pow_sub_hi h m b) ^ h) = 0" by blast+
  have uv: "pow_sub_lo h m a < pow_sub_hi h m b"
  proof (rule ccontr)
    assume "\<not> pow_sub_lo h m a < pow_sub_hi h m b"
    then have le: "pow_sub_hi h m b \<le> pow_sub_lo h m a" by simp
    have "(pow_sub_hi h m b) ^ h \<le> (pow_sub_lo h m a) ^ h"
      using le pow_sub_hi_nonneg[where b = b and h = h and m = m] by (simp add: power_mono)
    with lo_le hi_ge ab show False by simp
  qed
  have "dsc_pair_ok P (pow_sub_lo h m a, pow_sub_hi h m b)"
    by (rule pow_sub_backmap_certificate[OF h P sf pow_sub_lo_nonneg[OF a0] uv
             lo_le hi_ge ab core sh_lo sh_hi na nb])
  then show ?thesis ..
qed

section \<open>Dyadicity, and the negative half\<close>

text \<open>\<^bold>\<open>Dyadicity.\<close> The emitted endpoints are dyadic by construction (floor and ceiling at precision
  \<open>m\<close>), one line each. The exponent is the shared \<open>m\<close>, which is what the emitted \<open>(lna, rnb, k)\<close> triple
  needs.\<close>

lemma pow_sub_lo_dyadic: "\<exists>k::int. pow_sub_lo h m a = real_of_int k / 2 ^ m"
  unfolding pow_sub_lo_def by (rule exI[of _ "\<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>"]) simp

lemma pow_sub_hi_dyadic: "\<exists>k::int. pow_sub_hi h m b = real_of_int k / 2 ^ m"
  unfolding pow_sub_hi_def by (rule exI[of _ "\<lceil>(b powr (1 / real h)) * 2 ^ m\<rceil>"]) simp

text \<open>\<^bold>\<open>The negative half is a completeness obligation.\<close> Everything above assumes \<open>0 \<le> u\<close>, so it
  certifies only the positive back-image. For even \<open>h\<close> each positive root \<open>y\<close> of \<open>Q\<close> lifts to two roots
  \<open>\<plusminus>y\<^sup>1\<^sup>/\<^sup>h\<close> of \<open>P\<close> (\<open>pow_sub_preimage_card\<close>), so an entry that emits only the positive window drops half the
  real roots. Mirroring needs no new precision loop: \<open>P(-x) = P(x)\<close> for even \<open>h\<close>, so it reuses the same
  \<open>m\<close>.\<close>

lemma pow_sub_poly_even_sym:
  fixes P Q :: "real poly" and x :: real
  assumes P: "P = Q \<circ>\<^sub>p monom 1 h" and ev: "even h"
  shows "poly P (- x) = poly P x"
proof -
  have pm: "(- x) ^ h = x ^ h" using ev by (rule power_minus_even)
  have "poly P (- x) = poly Q ((- x) ^ h)" by (simp add: P poly_pcompose_monom)
  also have "\<dots> = poly Q (x ^ h)" using pm by simp
  also have "\<dots> = poly P x" by (simp add: P poly_pcompose_monom)
  finally show ?thesis .
qed

lemma pow_sub_roots_in_mirror:
  fixes P Q :: "real poly" and u v :: real
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and ev: "even h" and u0: "0 \<le> u" and uv: "u \<le> v"
  shows "roots_in P (- v) (- u) = roots_in Q (u ^ h) (v ^ h)"
proof -
  have sym: "\<And>x. poly P (- x) = poly P x" by (rule pow_sub_poly_even_sym[OF P ev])
  have set_eq: "{x. - v < x \<and> x < - u \<and> poly P x = 0}
                  = uminus ` {x. u < x \<and> x < v \<and> poly P x = 0}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> {x. - v < x \<and> x < - u \<and> poly P x = 0}"
    then have "u < - x" and "- x < v" and "poly P (- x) = 0" using sym by auto
    then show "x \<in> uminus ` {x. u < x \<and> x < v \<and> poly P x = 0}"
      by (intro image_eqI[where x = "- x"]) auto
  next
    fix x assume "x \<in> uminus ` {x. u < x \<and> x < v \<and> poly P x = 0}"
    then obtain y where y: "x = - y" "u < y" "y < v" "poly P y = 0" by auto
    then show "x \<in> {x. - v < x \<and> x < - u \<and> poly P x = 0}" using sym[of y] by simp
  qed
  have "roots_in P (- v) (- u) = card {x. - v < x \<and> x < - u \<and> poly P x = 0}"
    by (rule roots_in_squarefree_card[OF sf])
  also have "\<dots> = card {x. u < x \<and> x < v \<and> poly P x = 0}"
    unfolding set_eq by (rule card_image) (auto intro: inj_onI)
  also have "\<dots> = roots_in P u v" by (rule roots_in_squarefree_card[OF sf, symmetric])
  also have "\<dots> = roots_in Q (u ^ h) (v ^ h)" by (rule pow_sub_roots_in_eq[OF h P sf u0 uv])
  finally show ?thesis .
qed

theorem pow_sub_pair_ok_mirror:
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P" and ev: "even h"
    and u0: "0 \<le> u" and uv: "u < v"
    and iso: "roots_in Q (u ^ h) (v ^ h) = 1"
  shows "dsc_pair_ok P (- v, - u)"
  using uv pow_sub_roots_in_mirror[OF h P sf ev u0 less_imp_le[OF uv]] iso
  by (simp add: dsc_pair_ok_def)

text \<open>The back-map window is strictly ordered at EVERY precision — it does not need the margin
  argument, only \<open>a < b\<close> and the two power bounds. Stated separately because the mirror capstone
  needs it after the existential above has discarded it.\<close>

lemma pow_sub_lo_less_hi:
  fixes a b :: real
  assumes h: "0 < h" and a0: "0 \<le> a" and ab: "a < b"
  shows "pow_sub_lo h m a < pow_sub_hi h m b"
proof (rule ccontr)
  assume "\<not> pow_sub_lo h m a < pow_sub_hi h m b"
  then have le: "pow_sub_hi h m b \<le> pow_sub_lo h m a" by simp
  have b0: "0 \<le> b" using a0 ab by simp
  have "(pow_sub_hi h m b) ^ h \<le> (pow_sub_lo h m a) ^ h"
    using le pow_sub_hi_nonneg[where b = b and h = h and m = m] by (simp add: power_mono)
  moreover have "(pow_sub_lo h m a) ^ h \<le> a" by (rule pow_sub_lo_pow_le[OF a0 h])
  moreover have "b \<le> (pow_sub_hi h m b) ^ h" by (rule pow_sub_hi_pow_ge[OF b0 h])
  ultimately show False using ab by simp
qed

text \<open>\<^bold>\<open>The mirror.\<close> The same \<open>m\<close>, no second precision loop: the negative window is the reflection of
  the positive one, and for even \<open>h\<close> it is emitted alongside the positive window.\<close>

theorem pow_sub_backmap_precision_exists_mirror:
  fixes P Q :: "real poly" and a b :: real
  assumes h: "0 < h" and ev: "even h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and a0: "0 \<le> a" and ab: "a < b"
    and core: "roots_in Q a b = 1"
    and na: "poly Q a \<noteq> 0" and nb: "poly Q b \<noteq> 0"
  shows "\<exists>m. dsc_pair_ok P (pow_sub_lo h m a, pow_sub_hi h m b)
             \<and> dsc_pair_ok P (- pow_sub_hi h m b, - pow_sub_lo h m a)"
proof -
  from pow_sub_backmap_precision_exists[OF h P sf a0 ab core na nb]
  obtain m where pk: "dsc_pair_ok P (pow_sub_lo h m a, pow_sub_hi h m b)" ..
  have uv: "pow_sub_lo h m a < pow_sub_hi h m b" by (rule pow_sub_lo_less_hi[OF h a0 ab])
  from pk uv have "roots_in P (pow_sub_lo h m a) (pow_sub_hi h m b) = 1"
    by (simp add: dsc_pair_ok_def)
  then have "roots_in Q ((pow_sub_lo h m a) ^ h) ((pow_sub_hi h m b) ^ h) = 1"
    using pow_sub_roots_in_eq[OF h P sf pow_sub_lo_nonneg[OF a0] less_imp_le[OF uv]] by simp
  then have "dsc_pair_ok P (- pow_sub_hi h m b, - pow_sub_lo h m a)"
    by (rule pow_sub_pair_ok_mirror[OF h P sf ev pow_sub_lo_nonneg[OF a0] uv])
  with pk show ?thesis by blast
qed

text \<open>\<^bold>\<open>What these results do not cover.\<close>
  \<^item> \<^bold>\<open>Endpoint roots.\<close> The hypotheses \<open>na\<close>/\<open>nb\<close> are not supplied by the reduced solve's output
    specification. @{const dsc_pair_ok} is \<open>(fst = snd \<and> poly P (fst I) = 0) \<or> (fst < snd \<and> roots_in P .. = 1)\<close>,
    and @{const roots_in} counts an open interval, so an emitted \<open>Q\<close>-interval may carry a root on an
    endpoint. The shrinking back-map of \<open>Power_Sub_Loop\<close> needs no such hypothesis.
  \<^item> \<^bold>\<open>Odd \<open>h\<close>.\<close> For odd \<open>h\<close> the negative roots of \<open>Q\<close> lift and there is no mirror: the map is injective and
    order-preserving through the origin. It is not treated here; the entry substitutes only for even
    \<open>h \<ge> 2\<close>.\<close>

end
