theory Power_Sub_Loop
  imports Power_Sub_Backmap
begin

text \<open>Back-mapping: the abstract content of the precision loop.

  \<^bold>\<open>The emitted window shrinks rather than widens.\<close> A widening back-map emits, per \<open>Q\<close>-interval
  \<open>[a,b]\<close>, a window \<open>[lo,hi]\<close> with \<open>lo\<^sup>h \<le> a\<close> and \<open>b \<le> hi\<^sup>h\<close>, and certifies that no extra root was swept
  in by testing both shoulders root-free. That form is proved (\<open>pow_sub_backmap_certificate\<close>,
  \<open>..._precision_exists\<close>), but only under \<open>poly Q a \<noteq> 0\<close> and \<open>poly Q b \<noteq> 0\<close>, and the reduced solve
  does not supply those: @{const dsc_pair_ok} counts an open interval, so an emitted \<open>Q\<close>-interval may
  carry a root on an endpoint, which \<open>dsc_int\<close> produces when a bisection midpoint is a root (it emits
  the degenerate pair \<open>(m,m)\<close> and the two neighbours touching it). In that case a widening loop does
  not terminate: \<open>lo\<^sup>h < a\<close> at every precision, so the window always contains the endpoint root.

  Emitting \<open>lo = pow_sub_hi h m a\<close> and \<open>hi = pow_sub_lo h m b\<close> (the ceiling below, the floor above)
  gives \<open>a \<le> lo\<^sup>h\<close> and \<open>hi\<^sup>h \<le> b\<close>, so the window is a subinterval of \<open>(a,b)\<close>. Then:

  \<^item> \<^bold>\<open>soundness is unconditional\<close>: a subinterval of \<open>(a,b)\<close> cannot contain a root that \<open>(a,b)\<close> does
    not, so no endpoint hypothesis is needed. It follows from \<open>pow_sub_pair_ok_interval\<close> alone;
  \<^item> \<^bold>\<open>termination needs no margin\<close>: \<open>lo\<^sup>h\<close> decreases to \<open>a\<close> and \<open>hi\<^sup>h\<close> increases to \<open>b\<close>, and the root \<open>r\<close>
    lies strictly inside \<open>(a,b)\<close>, so some precision has \<open>lo\<^sup>h < r < hi\<^sup>h\<close>. (The uniform margin is still
    needed for the degenerate case below.)

  \<^bold>\<open>The degenerate case\<close>, a \<open>Q\<close>-pair \<open>(a,a)\<close> with \<open>poly Q a = 0\<close>, cannot shrink (the window would be
  empty), so it is the one case that widens. It needs no runtime branch: the emitted pair is
  \<open>(pow_sub_lo h m a, pow_sub_hi h m a)\<close> in both sub-cases, because when \<open>a\<^sup>1\<^sup>/\<^sup>h\<close> is exactly
  representable at precision \<open>m\<close> the floor and the ceiling coincide and the pair is degenerate, which
  is @{const dsc_pair_ok}'s other arm. For \<open>Q(u) = 2u - 1\<close>, \<open>P(x) = 2x\<^sup>2 - 1\<close>, the irrational back-image
  need not be pinned; it needs to be isolated, and the floor/ceiling pair isolates it.\<close>

section \<open>Two facts about a count of exactly one\<close>

lemma roots_in_one_witness:
  fixes p :: "real poly"
  assumes sf: "squarefree p" and one: "roots_in p a b = 1"
  shows "\<exists>r. a < r \<and> r < b \<and> poly p r = 0"
proof -
  have "card {x. a < x \<and> x < b \<and> poly p x = 0} = 1"
    using one roots_in_squarefree_card[OF sf] by simp
  then obtain w where "{x. a < x \<and> x < b \<and> poly p x = 0} = {w}"
    by (rule card_1_singletonE)
  then have "w \<in> {x. a < x \<and> x < b \<and> poly p x = 0}" by simp
  then show ?thesis by blast
qed

text \<open>A subinterval that still contains the witness still isolates it. This is the whole
  soundness argument of the shrinking loop, and it mentions no endpoint.\<close>

lemma roots_in_sub_one:
  fixes p :: "real poly"
  assumes sf: "squarefree p" and one: "roots_in p a b = 1"
    and le1: "a \<le> a'" and le2: "b' \<le> b"
    and r1: "a' < r" and r2: "r < b'" and rr: "poly p r = 0"
  shows "roots_in p a' b' = 1"
proof -
  have pnz: "p \<noteq> 0" using sf by auto
  have finB: "finite {x. a < x \<and> x < b \<and> poly p x = 0}"
    by (rule finite_subset[of _ "{x. poly p x = 0}"]) (auto simp: poly_roots_finite[OF pnz])
  have sub: "{x. a' < x \<and> x < b' \<and> poly p x = 0} \<subseteq> {x. a < x \<and> x < b \<and> poly p x = 0}"
    using le1 le2 by auto
  have mem: "r \<in> {x. a' < x \<and> x < b' \<and> poly p x = 0}" using r1 r2 rr by simp
  have cardB: "card {x. a < x \<and> x < b \<and> poly p x = 0} = 1"
    using one roots_in_squarefree_card[OF sf] by simp
  have finA: "finite {x. a' < x \<and> x < b' \<and> poly p x = 0}"
    by (rule finite_subset[OF sub finB])
  have "0 < card {x. a' < x \<and> x < b' \<and> poly p x = 0}"
    using finA mem by (auto simp: card_gt_0_iff)
  moreover have "card {x. a' < x \<and> x < b' \<and> poly p x = 0} \<le> 1"
    using card_mono[OF finB sub] cardB by simp
  ultimately have "card {x. a' < x \<and> x < b' \<and> poly p x = 0} = 1" by simp
  then show ?thesis by (simp add: roots_in_squarefree_card[OF sf])
qed

section \<open>Proper intervals: the shrinking back-map\<close>

text \<open>No endpoint hypotheses, no margin. Compare \<open>pow_sub_backmap_precision_exists\<close>, which needs
  both \<open>poly Q a \<noteq> 0\<close> and \<open>poly Q b \<noteq> 0\<close>.\<close>

theorem pow_sub_shrink_exists:
  fixes P Q :: "real poly" and a b :: real
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and a0: "0 \<le> a" and ab: "a < b"
    and core: "roots_in Q a b = 1"
  shows "\<exists>m. pow_sub_hi h m a < pow_sub_lo h m b
           \<and> dsc_pair_ok P (pow_sub_hi h m a, pow_sub_lo h m b)"
proof -
  have sfQ: "squarefree Q" using h sf P by (simp add: pcompose_monom_squarefreeD)
  have b0: "0 \<le> b" using a0 ab by simp
  from roots_in_one_witness[OF sfQ core] obtain r
    where r1: "a < r" and r2: "r < b" and rr: "poly Q r = 0" by blast
  define e1 where "e1 = (r - a) / 2"
  define e2 where "e2 = (b - r) / 2"
  have e1pos: "0 < e1" unfolding e1_def using r1 by simp
  have e2pos: "0 < e2" unfolding e2_def using r2 by simp
  from pow_sub_hi_converges[OF a0 h e1pos] obtain m1
    where m1: "(pow_sub_hi h m1 a) ^ h \<le> a + e1" ..
  from pow_sub_lo_converges[OF b0 h e2pos] obtain m2
    where m2: "b - e2 \<le> (pow_sub_lo h m2 b) ^ h" ..
  define m where "m = max m1 m2"
  \<comment> \<open>merge the two precisions onto the ABI's single shared exponent, as in the widening capstone\<close>
  have hi_mono: "(pow_sub_hi h m a) ^ h \<le> (pow_sub_hi h m1 a) ^ h"
    using pow_sub_hi_grid_mono[where m = m1 and m' = m and h = h and b = a]
          pow_sub_hi_nonneg[where b = a and h = h and m = m] m_def
    by (simp add: power_mono)
  have lo_mono: "(pow_sub_lo h m2 b) ^ h \<le> (pow_sub_lo h m b) ^ h"
    using pow_sub_lo_grid_mono[where m = m2 and m' = m and h = h and a = b]
          pow_sub_lo_nonneg[OF b0] m_def
    by (simp add: power_mono)
  have lo_lt: "(pow_sub_hi h m a) ^ h < r"
  proof -
    have "(pow_sub_hi h m a) ^ h \<le> a + e1" using hi_mono m1 by simp
    also have "a + e1 < r" using r1 by (simp add: e1_def field_simps)
    finally show ?thesis .
  qed
  have hi_gt: "r < (pow_sub_lo h m b) ^ h"
  proof -
    have "r < b - e2" using r2 by (simp add: e2_def field_simps)
    also have "b - e2 \<le> (pow_sub_lo h m b) ^ h" using lo_mono m2 by simp
    finally show ?thesis .
  qed
  have lo_ge: "a \<le> (pow_sub_hi h m a) ^ h" by (rule pow_sub_hi_pow_ge[OF a0 h])
  have hi_le: "(pow_sub_lo h m b) ^ h \<le> b" by (rule pow_sub_lo_pow_le[OF b0 h])
  have iso: "roots_in Q ((pow_sub_hi h m a) ^ h) ((pow_sub_lo h m b) ^ h) = 1"
    by (rule roots_in_sub_one[OF sfQ core lo_ge hi_le lo_lt hi_gt rr])
  have uv: "pow_sub_hi h m a < pow_sub_lo h m b"
  proof (rule ccontr)
    assume "\<not> pow_sub_hi h m a < pow_sub_lo h m b"
    then have le: "pow_sub_lo h m b \<le> pow_sub_hi h m a" by simp
    have "(pow_sub_lo h m b) ^ h \<le> (pow_sub_hi h m a) ^ h"
      using le pow_sub_lo_nonneg[OF b0] by (simp add: power_mono)
    with lo_lt hi_gt show False by simp
  qed
  have "dsc_pair_ok P (pow_sub_hi h m a, pow_sub_lo h m b)"
    by (rule pow_sub_pair_ok_interval[OF h P sf
             pow_sub_hi_nonneg[where b = a and h = h and m = m] uv iso])
  with uv show ?thesis by blast
qed

section \<open>Degenerate \<open>Q\<close>-pairs: the one case that widens\<close>

text \<open>Floor and ceiling coincide exactly when the scaled root is an integer, and then the emitted
  pair is degenerate and exact. Split out because both branches of the capstone need it.\<close>

lemma pow_sub_lo_of_exact:
  fixes a :: real
  assumes z: "real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor> = (a powr (1 / real h)) * 2 ^ m"
  shows "pow_sub_lo h m a = a powr (1 / real h)"
proof -
  have "pow_sub_lo h m a = ((a powr (1 / real h)) * 2 ^ m) / 2 ^ m"
    unfolding pow_sub_lo_def by (simp only: z)
  also have "\<dots> = a powr (1 / real h)" by simp
  finally show ?thesis .
qed
  \<comment> \<open>\<open>simp\<close> must NOT see the hypothesis: it rewrites \<open>real_of_int \<lfloor>y\<rfloor> = y\<close> into
     \<open>y \<in> \<int>\<close> and then unfolds that to \<open>\<exists>n. y = real_of_int n\<close>, losing the
     witness. \<open>simp only: z\<close> uses it as a rewrite instead.\<close>

lemma pow_sub_lo_eq_hi_iff_exact:
  fixes a :: real
  assumes a0: "0 \<le> a" and h: "0 < h"
  shows "pow_sub_lo h m a = pow_sub_hi h m a
           \<longleftrightarrow> pow_sub_lo h m a = a powr (1 / real h)"
proof
  assume e: "pow_sub_lo h m a = pow_sub_hi h m a"
  have "real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>
          = real_of_int \<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil>"
    using e unfolding pow_sub_lo_def pow_sub_hi_def by simp
  then have fl: "real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>
                   = (a powr (1 / real h)) * 2 ^ m"
    using floor_correct[of "(a powr (1 / real h)) * 2 ^ m"]
          ceiling_correct[of "(a powr (1 / real h)) * 2 ^ m"] by linarith
  show "pow_sub_lo h m a = a powr (1 / real h)" by (rule pow_sub_lo_of_exact[OF fl])
next
  assume e: "pow_sub_lo h m a = a powr (1 / real h)"
  from e have "real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor> / 2 ^ m = a powr (1 / real h)"
    unfolding pow_sub_lo_def .
  then have fl: "real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>
                   = (a powr (1 / real h)) * 2 ^ m"
    by (simp add: divide_eq_eq)
  have c1: "\<lceil>real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>\<rceil>
              = \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>" by (rule ceiling_of_int)
  have c2: "\<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil>
              = \<lceil>real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>\<rceil>"
    by (simp only: fl)
  from c2 c1 have "\<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil>
                     = \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>" by simp
  then show "pow_sub_lo h m a = pow_sub_hi h m a"
    unfolding pow_sub_lo_def pow_sub_hi_def by simp
qed

lemma pow_sub_exact_root:
  fixes a :: real
  assumes a0: "0 \<le> a" and h: "0 < h"
    and eq: "pow_sub_lo h m a = a powr (1 / real h)"
  shows "(pow_sub_lo h m a) ^ h = a"
  using eq powr_root_pow[OF a0 h] by simp

text \<open>Strictness in the other branch: if the two differ, the scaled root is not an integer, so the
  floor is strictly below it and the ceiling strictly above, which puts \<open>a\<close> strictly inside the
  emitted window.\<close>

lemma pow_sub_strict_below:
  fixes a :: real
  assumes a0: "0 \<le> a" and h: "0 < h"
    and ne: "pow_sub_lo h m a \<noteq> pow_sub_hi h m a"
  shows "(pow_sub_lo h m a) ^ h < a \<and> a < (pow_sub_hi h m a) ^ h"
proof -
  have pos: "(0::real) < 2 ^ m" by simp
  have fc_ne: "\<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>
                 \<noteq> \<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil>"
  proof
    assume "\<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>
              = \<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil>"
    then have "pow_sub_lo h m a = pow_sub_hi h m a"
      unfolding pow_sub_lo_def pow_sub_hi_def by simp
    with ne show False by simp
  qed
  have lt: "\<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>
              < \<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil>"
    using fc_ne floor_le_ceiling[of "(a powr (1 / real h)) * 2 ^ m"]
    by (simp add: order_less_le)
  have ceil_eq: "\<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil>
                   = \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor> + 1"
    using lt ceiling_diff_floor_le_1[of "(a powr (1 / real h)) * 2 ^ m"] by linarith
    \<comment> \<open>the ONE integrality step: \<open>linarith\<close> cannot get strictness out of
       \<open>floor_correct\<close>/\<open>ceiling_correct\<close> alone (both are compatible with \<open>z\<close> being an integer),
       so the gap is closed on the INTEGERS, where \<open>\<lceil>z\<rceil> - \<lfloor>z\<rfloor> \<le> 1\<close> plus
       \<open><\<close> forces the successor.\<close>
  have lo_lt: "pow_sub_lo h m a < a powr (1 / real h)"
  proof -
    have "real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor> < (a powr (1 / real h)) * 2 ^ m"
      using ceiling_correct[of "(a powr (1 / real h)) * 2 ^ m"] by (simp add: ceil_eq)
    from divide_strict_right_mono[OF this pos] show ?thesis
      unfolding pow_sub_lo_def by simp
  qed
  have hi_gt: "a powr (1 / real h) < pow_sub_hi h m a"
  proof -
    have "(a powr (1 / real h)) * 2 ^ m < real_of_int \<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil>"
      using floor_correct[of "(a powr (1 / real h)) * 2 ^ m"] by (simp add: ceil_eq)
    from divide_strict_right_mono[OF this pos] show ?thesis
      unfolding pow_sub_hi_def by simp
  qed
  have rh: "(a powr (1 / real h)) ^ h = a" by (rule powr_root_pow[OF a0 h])
  have "(pow_sub_lo h m a) ^ h < (a powr (1 / real h)) ^ h"
    using lo_lt pow_sub_lo_nonneg[OF a0] h by (rule power_strict_mono)
  moreover have "(a powr (1 / real h)) ^ h < (pow_sub_hi h m a) ^ h"
    using hi_gt powr_ge_zero h by (rule power_strict_mono)
  ultimately show ?thesis using rh by simp
qed

theorem pow_sub_degenerate_exists:
  fixes P Q :: "real poly" and a :: real
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and a0: "0 \<le> a" and root: "poly Q a = 0"
  shows "\<exists>m. dsc_pair_ok P (pow_sub_lo h m a, pow_sub_hi h m a)"
proof -
  have sfQ: "squarefree Q" using h sf P by (simp add: pcompose_monom_squarefreeD)
  from roots_free_margin_below[OF sfQ, of a] obtain e1 where e1: "0 < e1"
    and z1: "roots_in Q (a - e1) a = 0" by blast
  from roots_free_margin_above[OF sfQ, of a] obtain e2 where e2: "0 < e2"
    and z2: "roots_in Q a (a + e2) = 0" by blast
  from pow_sub_lo_converges[OF a0 h e1] obtain m1
    where m1: "a - e1 \<le> (pow_sub_lo h m1 a) ^ h" ..
  from pow_sub_hi_converges[OF a0 h e2] obtain m2
    where m2: "(pow_sub_hi h m2 a) ^ h \<le> a + e2" ..
  define m where "m = max m1 m2"
  have lo_mono: "(pow_sub_lo h m1 a) ^ h \<le> (pow_sub_lo h m a) ^ h"
    using pow_sub_lo_grid_mono[where m = m1 and m' = m and h = h and a = a]
          pow_sub_lo_nonneg[OF a0] m_def
    by (simp add: power_mono)
  have hi_mono: "(pow_sub_hi h m a) ^ h \<le> (pow_sub_hi h m2 a) ^ h"
    using pow_sub_hi_grid_mono[where m = m2 and m' = m and h = h and b = a]
          pow_sub_hi_nonneg[where b = a and h = h and m = m] m_def
    by (simp add: power_mono)
  have lo_in: "a - e1 \<le> (pow_sub_lo h m a) ^ h" using m1 lo_mono by simp
  have hi_in: "(pow_sub_hi h m a) ^ h \<le> a + e2" using m2 hi_mono by simp
  show ?thesis
  proof (cases "pow_sub_lo h m a = pow_sub_hi h m a")
    case True
    then have "pow_sub_lo h m a = a powr (1 / real h)"
      using pow_sub_lo_eq_hi_iff_exact[OF a0 h] by simp
    then have "(pow_sub_lo h m a) ^ h = a" by (rule pow_sub_exact_root[OF a0 h])
    then have "poly Q ((pow_sub_lo h m a) ^ h) = 0" using root by simp
    then have "dsc_pair_ok P (pow_sub_lo h m a, pow_sub_lo h m a)"
      by (rule pow_sub_pair_ok_degenerate[OF h P])
    then have "dsc_pair_ok P (pow_sub_lo h m a, pow_sub_hi h m a)" using True by simp
    then show ?thesis ..
  next
    case False
    from pow_sub_strict_below[OF a0 h False]
    have lo_lt: "(pow_sub_lo h m a) ^ h < a" and hi_gt: "a < (pow_sub_hi h m a) ^ h" by simp_all
    have zl: "roots_in Q ((pow_sub_lo h m a) ^ h) a = 0"
      by (rule roots_in_mono_zero[OF sfQ z1 lo_in order_refl])
    have zr: "roots_in Q a ((pow_sub_hi h m a) ^ h) = 0"
      by (rule roots_in_mono_zero[OF sfQ z2 order_refl hi_in])
    have set_eq: "{x. (pow_sub_lo h m a) ^ h < x \<and> x < (pow_sub_hi h m a) ^ h \<and> poly Q x = 0}
                    = {a}"
    proof (rule set_eqI, rule iffI)
      fix x assume xin: "x \<in> {x. (pow_sub_lo h m a) ^ h < x \<and> x < (pow_sub_hi h m a) ^ h
                                 \<and> poly Q x = 0}"
      then have x1: "(pow_sub_lo h m a) ^ h < x" and x2: "x < (pow_sub_hi h m a) ^ h"
        and xr: "poly Q x = 0" by auto
      have "\<not> x < a" using x1 xr roots_in_zero_imp_no_root[OF sfQ zl] by blast
      moreover have "\<not> a < x" using x2 xr roots_in_zero_imp_no_root[OF sfQ zr] by blast
      ultimately show "x \<in> {a}" by simp
    next
      fix x assume "x \<in> {a}"
      then show "x \<in> {x. (pow_sub_lo h m a) ^ h < x \<and> x < (pow_sub_hi h m a) ^ h
                         \<and> poly Q x = 0}"
        using lo_lt hi_gt root by simp
    qed
    have iso: "roots_in Q ((pow_sub_lo h m a) ^ h) ((pow_sub_hi h m a) ^ h) = 1"
      by (simp add: roots_in_squarefree_card[OF sfQ] set_eq)
    have uv: "pow_sub_lo h m a < pow_sub_hi h m a"
    proof (rule ccontr)
      assume "\<not> pow_sub_lo h m a < pow_sub_hi h m a"
      then have le: "pow_sub_hi h m a \<le> pow_sub_lo h m a" by simp
      have "(pow_sub_hi h m a) ^ h \<le> (pow_sub_lo h m a) ^ h"
        using le pow_sub_hi_nonneg[where b = a and h = h and m = m] by (simp add: power_mono)
      with lo_lt hi_gt show False by simp
    qed
    have "dsc_pair_ok P (pow_sub_lo h m a, pow_sub_hi h m a)"
      by (rule pow_sub_pair_ok_interval[OF h P sf pow_sub_lo_nonneg[OF a0] uv iso])
    then show ?thesis ..
  qed
qed

section \<open>The per-interval obligation the implementation meets\<close>

text \<open>\<^bold>\<open>One statement covering both shapes of \<open>Q\<close>-output.\<close> The reduced arm returns a list of
  @{const dsc_pair_ok}-satisfying pairs, each of which is EITHER degenerate (an exact root) or a
  proper isolating interval; this says each shape has a back-map at some precision, and names the
  emitted pair for each. \<^bold>\<open>The impl branches on \<open>fst = snd\<close>, which it already knows\<close> — it does not
  have to test whether an endpoint is a root, which was the operand the widening route needed and
  could not get.\<close>

theorem pow_sub_backmap_pair_exists:
  fixes P Q :: "real poly" and I :: "real \<times> real"
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and a0: "0 \<le> fst I"
    and ok: "dsc_pair_ok Q I"
  shows "\<exists>m. (fst I = snd I \<longrightarrow> dsc_pair_ok P (pow_sub_lo h m (fst I), pow_sub_hi h m (fst I)))
           \<and> (fst I < snd I \<longrightarrow> dsc_pair_ok P (pow_sub_hi h m (fst I), pow_sub_lo h m (snd I)))"
proof (cases "fst I = snd I")
  case True
  then have root: "poly Q (fst I) = 0" using ok by (simp add: dsc_pair_ok_def)
  from pow_sub_degenerate_exists[OF h P sf a0 root] obtain m
    where "dsc_pair_ok P (pow_sub_lo h m (fst I), pow_sub_hi h m (fst I))" ..
  then show ?thesis using True by (intro exI[of _ m]) simp
next
  case False
  then have lt: "fst I < snd I" and core: "roots_in Q (fst I) (snd I) = 1"
    using ok by (auto simp: dsc_pair_ok_def)
  from pow_sub_shrink_exists[OF h P sf a0 lt core] obtain m
    where "pow_sub_hi h m (fst I) < pow_sub_lo h m (snd I)
           \<and> dsc_pair_ok P (pow_sub_hi h m (fst I), pow_sub_lo h m (snd I))" ..
  then show ?thesis using False by (intro exI[of _ m]) simp
qed

text \<open>\<^bold>\<open>The mirror, for even \<open>h\<close>.\<close> The reflection transfers @{const dsc_pair_ok}; here it is stated on
  the shrinking window, the one the loop emits. Both windows come from the same \<open>m\<close>, so the
  implementation runs one precision loop per \<open>Q\<close>-interval and emits two \<open>P\<close>-intervals from it.\<close>

theorem pow_sub_shrink_exists_mirror:
  fixes P Q :: "real poly" and a b :: real
  assumes h: "0 < h" and ev: "even h" and P: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and a0: "0 \<le> a" and ab: "a < b"
    and core: "roots_in Q a b = 1"
  shows "\<exists>m. dsc_pair_ok P (pow_sub_hi h m a, pow_sub_lo h m b)
           \<and> dsc_pair_ok P (- pow_sub_lo h m b, - pow_sub_hi h m a)"
proof -
  from pow_sub_shrink_exists[OF h P sf a0 ab core] obtain m
    where uv: "pow_sub_hi h m a < pow_sub_lo h m b"
      and pk: "dsc_pair_ok P (pow_sub_hi h m a, pow_sub_lo h m b)" by blast
  have b0: "0 \<le> b" using a0 ab by simp
    \<comment> \<open>\<open>uv\<close> must be EXPORTED by the shrink theorem, not recovered from \<open>pk\<close>: @{const dsc_pair_ok}
       has a degenerate arm, so it does NOT imply \<open>fst < snd\<close> (memory:
       exported-atom-must-be-conclusion-indexable)\<close>
  from pk uv have "roots_in P (pow_sub_hi h m a) (pow_sub_lo h m b) = 1"
    by (simp add: dsc_pair_ok_def)
  then have "roots_in Q ((pow_sub_hi h m a) ^ h) ((pow_sub_lo h m b) ^ h) = 1"
    using pow_sub_roots_in_eq[OF h P sf
            pow_sub_hi_nonneg[where b = a and h = h and m = m] less_imp_le[OF uv]]
    by simp
  then have "dsc_pair_ok P (- pow_sub_lo h m b, - pow_sub_hi h m a)"
    by (rule pow_sub_pair_ok_mirror[OF h P sf ev
             pow_sub_hi_nonneg[where b = a and h = h and m = m] uv])
  with pk show ?thesis by blast
qed

section \<open>The bridge for the integer root floor\<close>

text \<open>\<^bold>\<open>This keeps @{const powr} out of the implementation.\<close> Nothing above implies it, so it is proved
  here rather than assumed.

  The specification says \<open>pow_sub_lo h m a = \<lfloor>a\<^sup>1\<^sup>/\<^sup>h \<cdot> 2\<^sup>m\<rfloor> / 2\<^sup>m\<close>, which no machine can evaluate. The
  implementation computes the same integer by bisection on a predicate that is pure integer
  arithmetic, and the lemmas below say the predicate is the right one:

  \<^item> \<open>pow_sub_root_test\<close>: for \<open>0 \<le> n\<close>, testing \<open>n \<le> a\<^sup>1\<^sup>/\<^sup>h \<cdot> 2\<^sup>m\<close> is the same as testing
    \<open>n\<^sup>h \<le> a \<cdot> 2\<^sup>h\<^sup>m\<close>: no root is taken, only an \<open>h\<close>-th power;
  \<^item> \<open>pow_sub_root_test_dyadic\<close>: on the dyadic endpoints the pipeline carries (\<open>a = A / 2\<^sup>k\<close>), the test
    is \<open>n\<^sup>h \<cdot> 2\<^sup>k \<le> A \<cdot> 2\<^sup>h\<^sup>m\<close>, entirely in \<open>int\<close>: multiplications, two shifts and one comparison, with no new
    GMP primitive;
  \<^item> \<open>pow_sub_lo_num_char\<close>: the bisection's answer is the floor, because the predicate is downward
    closed in \<open>n\<close>, so the greatest \<open>n\<close> passing it is \<open>\<lfloor>a\<^sup>1\<^sup>/\<^sup>h \<cdot> 2\<^sup>m\<rfloor>\<close>.\<close>

lemma pow_sub_root_test:
  fixes a :: real and n :: int
  assumes a0: "0 \<le> a" and h: "0 < h" and n0: "0 \<le> n"
  shows "real_of_int n \<le> (a powr (1 / real h)) * 2 ^ m
           \<longleftrightarrow> (real_of_int n) ^ h \<le> a * 2 ^ (h * m)"
proof -
  have y0: "0 \<le> (a powr (1 / real h)) * 2 ^ m" by simp
  have pw: "((a powr (1 / real h)) * 2 ^ m) ^ h = a * 2 ^ (h * m)"
  proof -
    have e1: "(a powr (1 / real h)) ^ h = a" by (rule powr_root_pow[OF a0 h])
    have e2: "((2::real) ^ m) ^ h = 2 ^ (h * m)"
    proof -
      have "((2::real) ^ m) ^ h = 2 ^ (m * h)" by (simp add: power_mult)
      then show ?thesis by (simp add: mult.commute)
    qed
    show ?thesis by (simp add: power_mult_distrib e1 e2)
  qed
  show ?thesis
  proof
    assume "real_of_int n \<le> (a powr (1 / real h)) * 2 ^ m"
    then have "(real_of_int n) ^ h \<le> ((a powr (1 / real h)) * 2 ^ m) ^ h"
      using n0 by (simp add: power_mono)
    then show "(real_of_int n) ^ h \<le> a * 2 ^ (h * m)" using pw by simp
  next
    assume le: "(real_of_int n) ^ h \<le> a * 2 ^ (h * m)"
    show "real_of_int n \<le> (a powr (1 / real h)) * 2 ^ m"
    proof (rule ccontr)
      assume "\<not> real_of_int n \<le> (a powr (1 / real h)) * 2 ^ m"
      then have "(a powr (1 / real h)) * 2 ^ m < real_of_int n" by simp
      then have "((a powr (1 / real h)) * 2 ^ m) ^ h < (real_of_int n) ^ h"
        using y0 h by (rule power_strict_mono)
      with le pw show False by simp
    qed
  qed
qed

lemma pow_sub_root_test_dyadic:
  fixes A :: int and n :: int
  assumes h: "0 < h" and n0: "0 \<le> n" and A0: "0 \<le> A"
    and adef: "a = real_of_int A / 2 ^ k"
  shows "real_of_int n \<le> (a powr (1 / real h)) * 2 ^ m
           \<longleftrightarrow> n ^ h * 2 ^ k \<le> A * 2 ^ (h * m)"
proof -
  have a0: "0 \<le> a" unfolding adef using A0 by simp
  have pos: "(0::real) < 2 ^ k" by simp
  have "real_of_int n \<le> (a powr (1 / real h)) * 2 ^ m
          \<longleftrightarrow> (real_of_int n) ^ h \<le> a * 2 ^ (h * m)"
    by (rule pow_sub_root_test[OF a0 h n0])
  also have "\<dots> \<longleftrightarrow> (real_of_int n) ^ h * 2 ^ k \<le> a * 2 ^ (h * m) * 2 ^ k"
    using pos by simp
  also have "a * 2 ^ (h * m) * 2 ^ k = real_of_int A * 2 ^ (h * m)"
    unfolding adef by simp
  also have "((real_of_int n) ^ h * 2 ^ k \<le> real_of_int A * 2 ^ (h * m))
               \<longleftrightarrow> (n ^ h * 2 ^ k \<le> A * 2 ^ (h * m))"
  proof -
    have l: "(real_of_int n) ^ h * 2 ^ k = real_of_int (n ^ h * 2 ^ k)" by simp
    have r: "real_of_int A * 2 ^ (h * m) = real_of_int (A * 2 ^ (h * m))" by simp
    show ?thesis by (simp only: l r of_int_le_iff)
  qed
  finally show ?thesis .
qed
  \<comment> \<open>\<^bold>\<open>The whole inner loop, in one inequality.\<close> \<open>n\<^sup>h\<close> is repeated multiplication; the two \<open>2\<^sup>\<cdot>\<close>
     factors are \<open>mpz_mul_2exp\<close>; the test is a comparison. Everything is exact, so the certificate
     the loop reports is exact.\<close>

lemma pow_sub_root_test_mono:
  fixes a :: real
  assumes a0: "0 \<le> a" and h: "0 < h" and n0: "0 \<le> n'" and le: "n' \<le> n"
    and pass: "(real_of_int n) ^ h \<le> a * 2 ^ (h * m)"
  shows "(real_of_int n') ^ h \<le> a * 2 ^ (h * m)"
proof -
  have nn: "0 \<le> n" using n0 le by simp
  have "real_of_int n \<le> (a powr (1 / real h)) * 2 ^ m"
    using pow_sub_root_test[OF a0 h nn] pass by simp
  then have "real_of_int n' \<le> (a powr (1 / real h)) * 2 ^ m" using le by simp
  then show ?thesis using pow_sub_root_test[OF a0 h n0] by simp
qed
  \<comment> \<open>downward closure — the bisection's search invariant\<close>

lemma pow_sub_lo_num_char:
  fixes a :: real and n :: int
  assumes a0: "0 \<le> a" and h: "0 < h" and n0: "0 \<le> n"
  shows "n \<le> \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>
           \<longleftrightarrow> (real_of_int n) ^ h \<le> a * 2 ^ (h * m)"
proof -
  have "n \<le> \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>
          \<longleftrightarrow> real_of_int n \<le> (a powr (1 / real h)) * 2 ^ m"
    by (simp add: le_floor_iff)
  also have "\<dots> \<longleftrightarrow> (real_of_int n) ^ h \<le> a * 2 ^ (h * m)"
    by (rule pow_sub_root_test[OF a0 h n0])
  finally show ?thesis .
qed
lemma pow_sub_lo_num_unique:
  fixes a :: real and n :: int
  assumes a0: "0 \<le> a" and h: "0 < h" and n0: "0 \<le> n"
    and test: "(real_of_int n) ^ h \<le> a * 2 ^ (h * m)"
    and ntest: "\<not> (real_of_int (n + 1)) ^ h \<le> a * 2 ^ (h * m)"
  shows "n = \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>"
proof -
  have le: "n \<le> \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>"
    using pow_sub_lo_num_char[OF a0 h n0] test by simp
  have n1: "0 \<le> n + 1" using n0 by simp
  have "\<not> n + 1 \<le> \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>"
    using pow_sub_lo_num_char[OF a0 h n1] ntest by simp
  with le show ?thesis by simp
qed
  \<comment> \<open>\<^bold>\<open>The implementation's postcondition, in full.\<close> Two exact integer comparisons pin the answer,
     so the bisection needs no invariant beyond \<open>the test passes at n and fails at n+1\<close> and does
     not reason about \<open>powr\<close>.\<close>

  \<comment> \<open>\<^bold>\<open>So the greatest \<open>n\<close> passing the integer test IS the numerator of\<close> @{const pow_sub_lo}.
     \<open>pow_sub_hi\<close>'s numerator is then \<open>\<lfloor>\<cdot>\<rfloor>\<close> or \<open>\<lfloor>\<cdot>\<rfloor> + 1\<close> according to
     whether the test is TIGHT at that \<open>n\<close> (\<open>ceiling_altdef\<close>), which is one extra exact
     comparison — the same one the degenerate branch of \<open>pow_sub_degenerate_exists\<close> reads.\<close>

subsection \<open>The HIGH endpoint's numerator — one extra exact comparison\<close>

text \<open>\<^bold>\<open>The per-interval emission needs both endpoints, and only the low one has a search.\<close>
  \<open>root_floor_gmp2\<close> returns \<open>\<lfloor>a\<^sup>1\<^sup>/\<^sup>h \<cdot> 2\<^sup>m\<rfloor>\<close>; the high endpoint is \<open>\<lceil>\<cdot>\<rceil>\<close> at the same \<open>m\<close>, and by
  @{thm ceiling_altdef} it differs from the floor only when the scaled root is exactly an integer.
  That is decided by the exact integer identity the search already evaluates,
  \<open>n\<^sup>h \<cdot> 2\<^sup>k = A \<cdot> 2\<^sup>h\<^sup>\<cdot>\<^sup>m\<close> (@{thm pow_sub_root_test_dyadic} with \<open>\<le>\<close> tightened to \<open>=\<close>), so the high
  endpoint costs one comparison rather than a second bisection.\<close>

lemma pow_sub_root_exact_iff:
  fixes A :: int and n :: int
  assumes h: "0 < h" and n0: "0 \<le> n" and A0: "0 \<le> A"
    and adef: "a = real_of_int A / 2 ^ k"
  shows "real_of_int n = (a powr (1 / real h)) * 2 ^ m
           \<longleftrightarrow> n ^ h * 2 ^ k = A * 2 ^ (h * m)"
proof -
  have a0: "0 \<le> a" unfolding adef using A0 by simp
  have rn0: "0 \<le> real_of_int n" using n0 by simp
  have x0: "0 \<le> (a powr (1 / real h)) * 2 ^ m" using a0 by simp
  have pw: "((a powr (1 / real h)) * 2 ^ m) ^ h = a * 2 ^ (h * m)"
  proof -
    have e1: "(a powr (1 / real h)) ^ h = a" by (rule powr_root_pow[OF a0 h])
    have e2: "((2::real) ^ m) ^ h = 2 ^ (h * m)"
    proof -
      have "((2::real) ^ m) ^ h = 2 ^ (m * h)" by (simp add: power_mult)
      then show ?thesis by (simp add: mult.commute)
    qed
    show ?thesis by (simp add: power_mult_distrib e1 e2)
  qed
  show ?thesis
  proof
    assume e: "real_of_int n = (a powr (1 / real h)) * 2 ^ m"
    have "(real_of_int n) ^ h * 2 ^ k = a * 2 ^ (h * m) * 2 ^ k"
      using e pw by simp
    also have "a * 2 ^ (h * m) * 2 ^ k = real_of_int A * 2 ^ (h * m)"
      unfolding adef by simp
    finally have "real_of_int (n ^ h * 2 ^ k) = real_of_int (A * 2 ^ (h * m))" by simp
    then show "n ^ h * 2 ^ k = A * 2 ^ (h * m)" by (simp only: of_int_eq_iff)
  next
    assume e: "n ^ h * 2 ^ k = A * 2 ^ (h * m)"
    then have "real_of_int (n ^ h * 2 ^ k) = real_of_int (A * 2 ^ (h * m))" by simp
    then have r: "(real_of_int n) ^ h * 2 ^ k = real_of_int A * 2 ^ (h * m)" by simp
    have "real_of_int A * 2 ^ (h * m) = a * 2 ^ (h * m) * 2 ^ k"
      unfolding adef by simp
    with r have "(real_of_int n) ^ h * 2 ^ k = a * 2 ^ (h * m) * 2 ^ k" by simp
    then have "(real_of_int n) ^ h = a * 2 ^ (h * m)" by simp
    then have "(real_of_int n) ^ h = ((a powr (1 / real h)) * 2 ^ m) ^ h"
      using pw by simp
    then show "real_of_int n = (a powr (1 / real h)) * 2 ^ m"
      by (rule power_eq_imp_eq_base[OF _ rn0 x0 h])
  qed
qed

text \<open>\<^bold>\<open>The emit op's postcondition\<close>, stated on the low endpoint in the shape
  \<open>root_floor_gmp2_is_pow_sub_lo\<close> delivers, so the two chain without a \<open>\<lfloor>\<cdot>\<rfloor>\<close> appearing in the
  implementation.\<close>

lemma pow_sub_hi_of_num:
  fixes A :: int and n :: int
  assumes h: "0 < h" and A0: "0 \<le> A"
    and adef: "a = real_of_int A / 2 ^ k"
    and ndef: "pow_sub_lo h m a = real_of_int n / 2 ^ m"
  shows "pow_sub_hi h m a
           = real_of_int (if n ^ h * 2 ^ k = A * 2 ^ (h * m) then n else n + 1) / 2 ^ m"
proof -
  have a0: "0 \<le> a" unfolding adef using A0 by simp
  have x0: "0 \<le> (a powr (1 / real h)) * 2 ^ m" using a0 by simp
  \<comment> \<open>\<open>n\<close> IS the floor: the two dyadics agree and \<open>2\<^sup>m \<noteq> 0\<close>\<close>
  have nfl: "n = \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>"
  proof -
    have "real_of_int n / 2 ^ m
            = real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor> / 2 ^ m"
      using ndef unfolding pow_sub_lo_def by simp
    then have "real_of_int n = real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>"
      by (simp add: divide_eq_eq)
    then show ?thesis by (simp only: of_int_eq_iff)
  qed
  have n0: "0 \<le> n" unfolding nfl using x0 by simp
  show ?thesis
  proof (cases "n ^ h * 2 ^ k = A * 2 ^ (h * m)")
    case True
    then have "real_of_int n = (a powr (1 / real h)) * 2 ^ m"
      using pow_sub_root_exact_iff[OF h n0 A0 adef] by simp
    then have "\<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil> = n"
      by (metis ceiling_of_int)
    then show ?thesis using True unfolding pow_sub_hi_def by simp
  next
    case False
    then have "real_of_int n \<noteq> (a powr (1 / real h)) * 2 ^ m"
      using pow_sub_root_exact_iff[OF h n0 A0 adef] by simp
    then have "(a powr (1 / real h)) * 2 ^ m
                 \<noteq> real_of_int \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>"
      using nfl by simp
    then have "\<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil>
                 = \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor> + 1"
      by (simp add: ceiling_altdef)
    then show ?thesis using False nfl unfolding pow_sub_hi_def by simp
  qed
qed

text \<open>\<^bold>\<open>What this theory does not provide.\<close> Everything above is an existence statement about the
  precision \<open>m\<close>: the hybrid test-and-double search cannot run forever. It does not bound \<open>m\<close> (see
  \<open>Power_Sub_Backmap\<close>). The rest is refinement: the integer root floor is refined in
  \<open>Power_Sub_Root_Impl\<close>; the loop's certification test is decidable (a sign test, or the Descartes
  count on the reduced polynomial); and odd \<open>h\<close>, which has no mirror, is excluded by the entry, which
  substitutes only for even \<open>h \<ge> 2\<close>.\<close>

end
