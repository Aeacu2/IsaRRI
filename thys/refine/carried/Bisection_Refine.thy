theory Bisection_Refine
  imports Bisection_Solver
begin

text \<open>The functional correctness of the carried algorithm against \<open>dsc_int\<close>: the root-anchoring,
  homothety, transform and count bridge (see the section text below).\<close>

section \<open>GAP 2: carried main-solver semantic correctness (refine to dsc_int)\<close>

text \<open>We data-refine the carried loop to the
  representation-agnostic endpoint abstract worklist \<open>rational_queue_main_int\<close>
  (which is already proven @{text "= mset (dsc_int ...)"} in
  \<open>Rational_Refine\<close>) using the functional bridge below. The bridge
  reduces, near-definitionally, to "the carried poly Q for interval [a,b] satisfies
  @{text "rev Q = p3"}" where p3 is the polynomial @{const descartes_list_int}
  counts (after its final @{text "taylor_shift_list 1"}).\<close>

subsection \<open>The fast-descartes intermediate polynomial p3\<close>

definition fast_descartes_p3 :: "rat \<Rightarrow> rat \<Rightarrow> int list \<Rightarrow> int list" where
  "fast_descartes_p3 a b xs =
    (let (na, da) = quotient_of a;
         p1 = fractional_taylor_shift a xs;
         (nw, dw) = quotient_of ((b - a) * of_int da)
     in scale_for_fractional_shift dw 1 (rev (scale_poly_list nw p1)))"

lemma fast_descartes_list_int_via_p3:
  "descartes_list_int a b xs
     = sign_changes_fold (taylor_shift_list 1 (fast_descartes_p3 a b xs))"
  by (simp add: descartes_list_int_def fast_descartes_p3_def Let_def split: prod.splits)

subsection \<open>B3 -- the count bridge (PROVEN)\<close>

text \<open>A carried poly whose reverse is exactly p3 has the same Descartes count as
  @{const descartes_list_int} for that interval. This is the count half of the
  bridge; the geometric half (that the carried transforms actually maintain
  @{text "rev Q = p3"}) is B0/B1/B2 below.\<close>
lemma carried_count_eq_fast_descartes:
  assumes "rev Q = fast_descartes_p3 a b xs"
  shows "carried_descartes_count Q = descartes_list_int a b xs"
  by (simp add: carried_descartes_count_def assms fast_descartes_list_int_via_p3)

subsection \<open>The carried representation invariant\<close>

definition carried_repr :: "int list \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> int list \<Rightarrow> bool" where
  "carried_repr P a b Q \<longleftrightarrow> (rev Q = fast_descartes_p3 a b P)"

lemma carried_repr_count:
  "carried_repr P a b Q \<Longrightarrow> carried_descartes_count Q = descartes_list_int a b P"
  by (simp add: carried_repr_def carried_count_eq_fast_descartes)

subsection \<open>B0/B1/B2 -- the geometric bridge (PROVEN)\<close>

text \<open>B1 (left child): the carried left transform = bisecting to the left half.
  @{const carried_left} is the homothety x -> x/2 applied from the high-degree
  end (@{text "rev (scale_for_fractional_shift 2 1 (rev xs))"}); proving it maintains
  @{const carried_repr} for @{text "[a, (a+b)/2]"} is the heart of the bridge.\<close>
text \<open>Crux: halving a rational with odd (normalized) numerator just doubles the
  denominator -- no further cancellation. This is exactly what the left homothety needs.\<close>
lemma quotient_of_half:
  assumes qW: "quotient_of W = (nw, dw)" and odd_nw: "odd nw"
  shows "quotient_of (W / 2) = (nw, 2 * dw)"
proof -
  note cop = quotient_of_coprime[OF qW]
  note pos = quotient_of_denom_pos[OF qW]
  from qW have "W = of_int nw / of_int dw" by (rule quotient_of_div)
  hence "W / 2 = Rat.Fract nw (2 * dw)" by (simp add: Fract_of_int_quotient)
  hence "quotient_of (W / 2) = Rat.normalize (nw, 2 * dw)" by (simp add: quotient_of_Fract)
  also have "\<dots> = (nw, 2 * dw)" using pos cop odd_nw by simp
  finally show ?thesis .
qed

lemma carried_repr_left:
  assumes Q: "carried_repr P a b Q"
    and odd_nw: "odd (fst (quotient_of ((b - a) * of_int (snd (quotient_of a)))))"
  shows "carried_repr P a ((a + b) / 2) (carried_left Q)"
proof -
  let ?da = "snd (quotient_of a)"
  let ?W = "(b - a) * of_int ?da"
  let ?p1 = "fractional_taylor_shift a P"
  obtain nw dw where qw: "quotient_of ?W = (nw, dw)" by (metis surj_pair)
  from odd_nw qw have odd_nw': "odd nw" by simp
  have half: "((a + b) / 2 - a) * of_int ?da = ?W / 2" by (simp add: field_simps)
  have qw2: "quotient_of (((a + b) / 2 - a) * of_int ?da) = (nw, 2 * dw)"
    unfolding half using qw odd_nw' by (rule quotient_of_half)
  have p3ab: "fast_descartes_p3 a b P
      = scale_for_fractional_shift dw 1 (rev (scale_poly_list nw ?p1))"
    by (simp add: fast_descartes_p3_def Let_def case_prod_beta qw)
  have p3am: "fast_descartes_p3 a ((a + b) / 2) P
      = scale_for_fractional_shift (2 * dw) 1 (rev (scale_poly_list nw ?p1))"
    by (simp add: fast_descartes_p3_def Let_def case_prod_beta qw2)
  have "rev (carried_left Q) = scale_for_fractional_shift 2 1 (rev Q)"
    by (simp add: carried_left_def)
  also have "\<dots> = scale_for_fractional_shift 2 1 (fast_descartes_p3 a b P)"
    using Q by (simp add: carried_repr_def)
  also have "\<dots> = scale_poly_list 2 (scale_poly_list dw (rev (scale_poly_list nw ?p1)))"
    by (simp add: p3ab scale_for_fractional_shift_eq_scale_poly_list)
  also have "\<dots> = scale_poly_list (2 * dw) (rev (scale_poly_list nw ?p1))"
    by (simp add: scale_poly_list_scale_poly_list)
  also have "\<dots> = fast_descartes_p3 a ((a + b) / 2) P"
    by (simp add: p3am scale_for_fractional_shift_eq_scale_poly_list)
  finally show ?thesis by (simp add: carried_repr_def)
qed

text \<open>B2 (right child): @{const carried_right} = left then shift-by-1.
  The scalar-free geometric core: shifting the left half by 1 lands on the right half
  (both equal @{term "pcompose (Poly Pr) [:m, m - a:]"} when @{term "b - m = m - a"}).\<close>
lemma taylor_shift_list_add:
  fixes c d :: "'a::comm_ring_1"
  shows "taylor_shift_list c (taylor_shift_list d xs) = taylor_shift_list (c + d) xs"
proof (rule poly_eq_same_length)
  show "length (taylor_shift_list c (taylor_shift_list d xs)) = length (taylor_shift_list (c + d) xs)"
    by simp
  have comp: "pcompose ([:d, 1:]::'a poly) [:c, 1:] = [:c + d, 1:]"
    by (simp add: pcompose_pCons add.commute)
  have "Poly (taylor_shift_list c (taylor_shift_list d xs))
      = pcompose (pcompose (Poly xs) [:d, 1:]) [:c, 1:]"
    by (simp add: Poly_taylor_shift_list)
  also have "\<dots> = pcompose (Poly xs) [:c + d, 1:]"
    by (simp add: comp add.commute flip: pcompose_assoc)
  also have "\<dots> = Poly (taylor_shift_list (c + d) xs)" by (simp add: Poly_taylor_shift_list)
  finally show "Poly (taylor_shift_list c (taylor_shift_list d xs)) = Poly (taylor_shift_list (c + d) xs)" .
qed

lemma ts1_scale_taylor_bisect:
  fixes a m b :: rat
  assumes mab: "b - m = m - a"
  shows "taylor_shift_list 1 (scale_poly_list (m - a) (taylor_shift_list a Pr))
       = scale_poly_list (b - m) (taylor_shift_list m Pr)"
proof -
  have "taylor_shift_list 1 (scale_poly_list (m - a) (taylor_shift_list a Pr))
      = scale_poly_list (m - a) (taylor_shift_list (m - a) (taylor_shift_list a Pr))"
    by (simp add: taylor_scale_commute_rat)
  also have "\<dots> = scale_poly_list (m - a) (taylor_shift_list ((m - a) + a) Pr)"
    by (simp add: taylor_shift_list_add)
  also have "\<dots> = scale_poly_list (b - m) (taylor_shift_list m Pr)"
    using mab by simp
  finally show ?thesis .
qed

text \<open>Scalar equality via least-common-denominator theory: the clearing factor
  \<open>da * dw\<close> equals \<open>lcm (denom x) (denom width)\<close>, the same for both halves.\<close>

lemma quotient_of_denom_minus [simp]:
  "snd (quotient_of (- w)) = snd (quotient_of w)"
  by (simp add: rat_uminus_code split: prod.splits)

text \<open>Two atomic int facts (sledgehammer-discharged).\<close>
lemma denom_lcm_aux:
  assumes "(0::int) < n" and "0 < q"
  shows "n * (q div gcd n q) = lcm n q"
proof -
  have "n * (q div gcd n q) = n * q div gcd n q"
    using gcd_dvd2 by (simp add: div_mult_swap)
  also have "\<dots> = lcm n q" using assms by (simp add: lcm_altdef_int)
  finally show ?thesis .
qed

lemma div_bigger_divisor_dvd: "(g1::int) dvd g2 \<Longrightarrow> g2 dvd n \<Longrightarrow> n div g2 dvd n div g1"
  by fastforce

text \<open>\<open>clear x w = denom x * denom (w * denom x) = lcm (denom x) (denom w)\<close>.\<close>
lemma clear_eq_lcm:
  fixes x w :: rat
  shows "snd (quotient_of x) * snd (quotient_of (w * of_int (snd (quotient_of x))))
       = lcm (snd (quotient_of x)) (snd (quotient_of w))"
proof -
  obtain pw qw where w: "quotient_of w = (pw, qw)" by (cases "quotient_of w")
  let ?n = "snd (quotient_of x)"
  have npos: "0 < ?n" by (simp add: quotient_of_denom_pos')
  have qpos: "0 < qw" using w quotient_of_denom_pos by blast
  note cop = quotient_of_coprime[OF w]
  have "w = of_int pw / of_int qw" using w by (rule quotient_of_div)
  hence "w * of_int ?n = Rat.Fract (pw * ?n) qw"
    using qpos by (simp add: Fract_of_int_quotient)
  hence "quotient_of (w * of_int ?n) = Rat.normalize (pw * ?n, qw)" by (simp add: quotient_of_Fract)
  hence dwn: "snd (quotient_of (w * of_int ?n)) = qw div gcd (pw * ?n) qw"
    using qpos by (simp add: Rat.normalize_def Let_def)
  have g: "gcd (pw * ?n) qw = gcd ?n qw"
    apply (rule gcd_mult_left_left_cancel)
    using cop by (simp add: coprime_iff_gcd_eq_1 gcd.commute)
  have "?n * (qw div gcd ?n qw) = lcm ?n qw"
    using npos qpos by (rule denom_lcm_aux)
  thus ?thesis using dwn g w by simp
qed

lemma denom_add_dvd_lcm:
  "snd (quotient_of (x + y)) dvd lcm (snd (quotient_of x)) (snd (quotient_of y))"
proof -
  obtain a c where x: "quotient_of x = (a, c)" by (cases "quotient_of x")
  obtain b d where y: "quotient_of y = (b, d)" by (cases "quotient_of y")
  have cpos: "0 < c" and dpos: "0 < d" using x y quotient_of_denom_pos by blast+
  have snd_xy: "snd (quotient_of (x + y)) = (c * d) div gcd (a * d + b * c) (c * d)"
    using x y cpos dpos by (simp add: rat_plus_code Rat.normalize_def Let_def)
  have g1: "gcd c d dvd gcd (a * d + b * c) (c * d)"
  proof (rule gcd_greatest)
    have "gcd c d dvd a * d" using gcd_dvd2 dvd_mult by blast
    moreover have "gcd c d dvd b * c" using gcd_dvd1 dvd_mult by blast
    ultimately show "gcd c d dvd a * d + b * c" by (rule dvd_add)
    show "gcd c d dvd c * d" using gcd_dvd1 dvd_mult2 by blast
  qed
  have "(c * d) div gcd (a * d + b * c) (c * d) dvd (c * d) div gcd c d"
    by (rule div_bigger_divisor_dvd[OF g1 gcd_dvd2])
  also have "(c * d) div gcd c d = lcm c d" using cpos dpos by (simp add: lcm_altdef_int)
  finally show ?thesis using snd_xy x y by simp
qed

lemma lcm_denom_shift_eq:
  fixes a w :: rat
  shows "lcm (snd (quotient_of a)) (snd (quotient_of w))
       = lcm (snd (quotient_of (a + w))) (snd (quotient_of w))"
proof (rule zdvd_antisym_nonneg)
  show "0 \<le> lcm (snd (quotient_of a)) (snd (quotient_of w))" by simp
  show "0 \<le> lcm (snd (quotient_of (a + w))) (snd (quotient_of w))" by simp
  show "lcm (snd (quotient_of a)) (snd (quotient_of w))
        dvd lcm (snd (quotient_of (a + w))) (snd (quotient_of w))"
  proof (rule lcm_least)
    have "snd (quotient_of ((a + w) + (- w))) dvd lcm (snd (quotient_of (a + w))) (snd (quotient_of (- w)))"
      by (rule denom_add_dvd_lcm)
    thus "snd (quotient_of a) dvd lcm (snd (quotient_of (a + w))) (snd (quotient_of w))" by simp
  qed simp
  show "lcm (snd (quotient_of (a + w))) (snd (quotient_of w))
        dvd lcm (snd (quotient_of a)) (snd (quotient_of w))"
    by (rule lcm_least) (rule denom_add_dvd_lcm, simp)
qed

lemma p3_scalar_bisect_eq:
  fixes a b :: rat
  defines "m \<equiv> (a + b) / 2"
  shows "snd (quotient_of a) * snd (quotient_of ((m - a) * of_int (snd (quotient_of a))))
       = snd (quotient_of m) * snd (quotient_of ((b - m) * of_int (snd (quotient_of m))))"
proof -
  have bm: "b - m = m - a" by (simp add: m_def)
  have ma: "a + (m - a) = m" by simp
  have "snd (quotient_of a) * snd (quotient_of ((m - a) * of_int (snd (quotient_of a))))
      = lcm (snd (quotient_of a)) (snd (quotient_of (m - a)))" by (rule clear_eq_lcm)
  also have "\<dots> = lcm (snd (quotient_of m)) (snd (quotient_of (m - a)))"
    using lcm_denom_shift_eq[of a "m - a"] by (simp add: ma)
  also have "\<dots> = snd (quotient_of m) * snd (quotient_of ((b - m) * of_int (snd (quotient_of m))))"
    using clear_eq_lcm[of m "b - m"] by (simp add: bm)
  finally show ?thesis .
qed

lemma map_rat_of_int_inj:
  "map rat_of_int xs = map rat_of_int ys \<Longrightarrow> xs = ys"
  by (metis list.inj_map_strong of_int_eq_iff)

lemma carried_repr_right:
  assumes Q: "carried_repr P a b Q"
    and len: "0 < length P"
    and ab: "a < b"
    and odd_nw: "odd (fst (quotient_of ((b - a) * of_int (snd (quotient_of a)))))"
  shows "carried_repr P ((a + b) / 2) b (carried_right Q)"
proof -
  define m where "m = (a + b) / 2"
  have ne_am: "a \<noteq> m" and ne_mb: "m \<noteq> b" using ab by (auto simp: m_def)
  have mab: "b - m = m - a" by (simp add: m_def)
  let ?Pr = "map rat_of_int P"
  define k where "k = length P - 1"
  have p3_unfold: "\<And>x y. fast_descartes_p3 x y P =
      scale_for_fractional_shift (snd (quotient_of ((y - x) * of_int (snd (quotient_of x))))) 1
        (rev (scale_poly_list (fst (quotient_of ((y - x) * of_int (snd (quotient_of x)))))
               (fractional_taylor_shift x P)))"
    by (simp add: fast_descartes_p3_def Let_def case_prod_beta)
  define Sl where "Sl = (rat_of_int (snd (quotient_of a))
      * rat_of_int (snd (quotient_of ((m - a) * of_int (snd (quotient_of a)))))) ^ k"
  define Sr where "Sr = (rat_of_int (snd (quotient_of m))
      * rat_of_int (snd (quotient_of ((b - m) * of_int (snd (quotient_of m)))))) ^ k"
  have rat_am: "map rat_of_int (fast_descartes_p3 a m P)
      = smult_list Sl (rev (scale_poly_list (m - a) (taylor_shift_list a ?Pr)))"
    unfolding p3_unfold Sl_def k_def using p3_rat_equiv[OF len ne_am] by simp
  have rat_mb: "map rat_of_int (fast_descartes_p3 m b P)
      = smult_list Sr (rev (scale_poly_list (b - m) (taylor_shift_list m ?Pr)))"
    unfolding p3_unfold Sr_def k_def using p3_rat_equiv[OF len ne_mb] by simp
  have SlSr: "Sl = Sr"
  proof -
    have "rat_of_int (snd (quotient_of a))
          * rat_of_int (snd (quotient_of ((m - a) * of_int (snd (quotient_of a)))))
        = rat_of_int (snd (quotient_of m))
          * rat_of_int (snd (quotient_of ((b - m) * of_int (snd (quotient_of m)))))"
      using p3_scalar_bisect_eq[of a b] by (simp add: m_def flip: of_int_mult)
    thus ?thesis unfolding Sl_def Sr_def by simp
  qed
  from carried_repr_left[OF Q odd_nw]
  have "rev (carried_left Q) = fast_descartes_p3 a m P"
    by (simp add: carried_repr_def m_def)
  hence Lrev: "carried_left Q = rev (fast_descartes_p3 a m P)" by (metis rev_rev_ident)
  have "map rat_of_int (rev (carried_right Q)) = map rat_of_int (fast_descartes_p3 m b P)"
  proof -
    have "map rat_of_int (rev (carried_right Q))
        = rev (taylor_shift_list 1 (rev (map rat_of_int (fast_descartes_p3 a m P))))"
      by (simp del: rev_map
          add: carried_right_def Lrev map_rat_of_int_taylor_shift_list rev_map[symmetric])
    also have "\<dots> = rev (taylor_shift_list 1 (smult_list Sl (scale_poly_list (m - a) (taylor_shift_list a ?Pr))))"
      by (simp add: rat_am rev_smult_list)
    also have "\<dots> = smult_list Sl (rev (taylor_shift_list 1 (scale_poly_list (m - a) (taylor_shift_list a ?Pr))))"
      by (simp add: taylor_shift_list_smult rev_smult_list)
    also have "\<dots> = smult_list Sl (rev (scale_poly_list (b - m) (taylor_shift_list m ?Pr)))"
      by (simp add: ts1_scale_taylor_bisect[OF mab])
    also have "\<dots> = smult_list Sr (rev (scale_poly_list (b - m) (taylor_shift_list m ?Pr)))"
      using SlSr by simp
    also have "\<dots> = map rat_of_int (fast_descartes_p3 m b P)" using rat_mb by simp
    finally show ?thesis .
  qed
  hence "rev (carried_right Q) = fast_descartes_p3 m b P" by (rule map_rat_of_int_inj)
  thus ?thesis by (simp add: carried_repr_def m_def)
qed

text \<open>B0 (init/base): the canonical root interval is @{text "[0,1]"} with the literal
  input poly @{term P} (the carried main solver pushes @{term P} verbatim; the dyadic triple
  @{text "(l,r,k)"} is output bookkeeping only). Here @{term "fast_descartes_p3 0 1 P = rev P"}
  exactly, so @{term "carried_repr P 0 1 P"} holds; bisecting @{text "[0,1]"} via B1/B2
  generates every dyadic @{text "[l/2^k, r/2^k]"}.\<close>

lemma ruffini_step_zero[simp]:
  "ruffini_step 0 a xs = a # xs"
  by (induction xs arbitrary: a) simp_all

lemma taylor_shift_list_zero[simp]:
  "taylor_shift_list (0::'a::comm_ring_1) xs = xs"
  by (induction xs) simp_all

lemma scale_for_fractional_shift_one_one[simp]:
  "scale_for_fractional_shift 1 1 xs = xs"
  by (induction xs) simp_all

lemma scale_poly_list_one[simp]:
  "scale_poly_list 1 xs = xs"
  unfolding scale_poly_list_def by (induction xs) simp_all

lemma fractional_taylor_shift_zero[simp]:
  "fractional_taylor_shift 0 xs = xs"
proof -
  \<comment> \<open>@{thm [source] quotient_of_number} rather than \<open>by eval\<close>, so that the code generator does not
     enter the trusted base of these two ground facts.\<close>
  have "quotient_of (0::rat) = (0, 1)" by (simp add: quotient_of_number)
  thus ?thesis by (simp add: fractional_taylor_shift_def)
qed

lemma fast_descartes_p3_zero_one:
  "fast_descartes_p3 0 1 xs = rev xs"
proof -
  have q: "quotient_of (0::rat) = (0, 1)" "quotient_of (1::rat) = (1, 1)" by eval+
  show ?thesis by (simp add: fast_descartes_p3_def q)
qed

lemma carried_repr_init:
  "carried_repr P 0 1 P"
  by (simp add: carried_repr_def fast_descartes_p3_zero_one)

subsection \<open>The carried_init_same_den bisection identity\<close>

text \<open>@{const carried_left}/@{const carried_right} of an initialised node equal the direct
  @{const carried_init_same_den} of the corresponding child box. Semantics (over \<open>\<rat>\<close>):
  \<open>init(l,d,r,P)(x) = d^(n-1) \<cdot> P((l + (r-l)x)/d)\<close>; both child identities hold exactly, with the
  same scalar \<open>(2d)^(n-1)\<close> on both sides. The proof maps to \<open>\<rat>\<close> (injectively, via
  @{thm [source] map_rat_of_int_inj}), characterises the \<open>rev \<circ> scale \<circ> rev\<close> diagonal as
  \<open>smult \<circ> dilation\<close>, and collapses both sides' \<open>pcompose\<close> towers to the same affine composite.\<close>

text \<open>\<open>Poly\<close> of a constant-multiplied coefficient list is \<open>smult\<close>.\<close>
lemma cdlr_Poly_map_mult:
  fixes c :: "'a::comm_semiring_0"
  shows "Poly (map ((*) c) ys) = smult c (Poly ys)"
  by (induction ys) auto

text \<open>The \<open>rev \<circ> scale \<circ> rev\<close> diagonal (= @{const carried_left}'s core at scalar 2),
  reflection-free: it is the \<open>x \<mapsto> x/c\<close> dilation times the constant \<open>c^(n-1)\<close>.\<close>
lemma cdlr_rev_scale_rev:
  fixes c :: rat
  assumes c0: "c \<noteq> 0"
  shows "rev (scale_poly_list c (rev Y))
       = map ((*) (c ^ (length Y - 1))) (scale_poly_list (1/c) Y)"
proof (rule nth_equalityI)
  show "length (rev (scale_poly_list c (rev Y)))
      = length (map ((*) (c ^ (length Y - 1))) (scale_poly_list (1/c) Y))"
    by (simp add: length_scale_poly_list)
  fix j assume "j < length (rev (scale_poly_list c (rev Y)))"
  hence j: "j < length Y" by (simp add: length_scale_poly_list)
  have len_srev: "length (scale_poly_list c (rev Y)) = length Y"
    by (simp add: length_scale_poly_list)
  have idx: "length Y - Suc (length Y - Suc j) = j" using j by arith
  have "rev (scale_poly_list c (rev Y)) ! j
      = scale_poly_list c (rev Y) ! (length Y - Suc j)"
    using j by (simp add: rev_nth len_srev)
  also have "\<dots> = rev Y ! (length Y - Suc j) * c ^ (length Y - Suc j)"
    using j by (simp add: length_scale_poly_list)
  also have "\<dots> = Y ! j * c ^ (length Y - Suc j)"
    using j by (simp add: rev_nth idx)
  finally have lhs: "rev (scale_poly_list c (rev Y)) ! j = Y ! j * c ^ (length Y - Suc j)" .
  have pow: "c ^ (length Y - 1) * (1/c) ^ j = c ^ (length Y - Suc j)"
  proof -
    have "c ^ (length Y - 1) * (1/c) ^ j = c ^ (length Y - 1) / c ^ j"
      by (simp add: power_one_over)
    also have "\<dots> = c ^ (length Y - 1 - j)"
      using c0 j by (simp add: power_diff)
    finally show ?thesis by simp
  qed
  have "map ((*) (c ^ (length Y - 1))) (scale_poly_list (1/c) Y) ! j
      = c ^ (length Y - 1) * (Y ! j * (1/c) ^ j)"
    using j by (simp add: length_scale_poly_list)
  also have "\<dots> = Y ! j * (c ^ (length Y - 1) * (1/c) ^ j)"
    by (simp add: algebra_simps)
  also have "\<dots> = Y ! j * c ^ (length Y - Suc j)"
    by (metis pow)
  finally show "rev (scale_poly_list c (rev Y)) ! j
      = map ((*) (c ^ (length Y - 1))) (scale_poly_list (1/c) Y) ! j"
    by (simp add: lhs)
qed

lemma cdlr_Poly_rev_scale_rev:
  fixes c :: rat
  assumes c0: "c \<noteq> 0"
  shows "Poly (rev (scale_poly_list c (rev Y)))
       = smult (c ^ (length Y - 1)) (pcompose (Poly Y) [:0, 1/c:])"
  by (simp add: cdlr_rev_scale_rev[OF c0] cdlr_Poly_map_mult Poly_scale_poly_list)

text \<open>The LEFT-child core, over \<rat>: dilating the initialized node = initializing the
  dilated node. Both sides' \<open>pcompose\<close> towers collapse to
  \<open>smult ((2d)^(n-1)) (P \<circ> [:l/d, c/(2d):])\<close>.\<close>
lemma cdlr_left_rat:
  fixes Pm :: "rat list" and lq cq dq :: rat
  assumes d0: "dq \<noteq> 0"
  shows "rev (scale_poly_list 2 (rev
           (scale_poly_list cq (taylor_shift_list lq (rev (scale_poly_list dq (rev Pm)))))))
       = scale_poly_list cq (taylor_shift_list (2 * lq) (rev (scale_poly_list (2 * dq) (rev Pm))))"
proof (rule poly_eq_same_length)
  show "length (rev (scale_poly_list 2 (rev
           (scale_poly_list cq (taylor_shift_list lq (rev (scale_poly_list dq (rev Pm))))))))
      = length (scale_poly_list cq (taylor_shift_list (2 * lq)
           (rev (scale_poly_list (2 * dq) (rev Pm)))))"
    by (simp add: length_scale_poly_list)
  define n where "n = length Pm"
  have twod0: "2 * dq \<noteq> 0" using d0 by simp
  have lenW: "length (rev (scale_poly_list dq (rev Pm))) = n"
    by (simp add: length_scale_poly_list n_def)
  have lenW2: "length (rev (scale_poly_list (2 * dq) (rev Pm))) = n"
    by (simp add: length_scale_poly_list n_def)
  have len_inner: "length (scale_poly_list cq (taylor_shift_list lq
        (rev (scale_poly_list dq (rev Pm))))) = n"
    by (simp add: length_scale_poly_list lenW n_def)
  have W: "Poly (rev (scale_poly_list dq (rev Pm)))
      = smult (dq ^ (n - 1)) (pcompose (Poly Pm) [:0, 1/dq:])"
    using cdlr_Poly_rev_scale_rev[OF d0, of Pm] by (simp add: n_def)
  have W2: "Poly (rev (scale_poly_list (2 * dq) (rev Pm)))
      = smult ((2 * dq) ^ (n - 1)) (pcompose (Poly Pm) [:0, 1/(2 * dq):])"
    using cdlr_Poly_rev_scale_rev[OF twod0, of Pm] by (simp add: n_def)
  have scal: "(2 :: rat) ^ (n - 1) * dq ^ (n - 1) = (2 * dq) ^ (n - 1)"
    by (simp add: power_mult_distrib)
  have aff: "\<And>p :: rat poly.
      p \<circ>\<^sub>p [:0, 1/dq:] \<circ>\<^sub>p [:lq, 1:] \<circ>\<^sub>p [:0, cq:] \<circ>\<^sub>p [:0, 1/2:]
    = p \<circ>\<^sub>p [:0, 1/(dq * 2):] \<circ>\<^sub>p [:lq * 2, 1:] \<circ>\<^sub>p [:0, cq:]"
    using d0
    by (simp add: pcompose_pCons field_simps flip: pcompose_assoc)
  show "Poly (rev (scale_poly_list 2 (rev
        (scale_poly_list cq (taylor_shift_list lq (rev (scale_poly_list dq (rev Pm))))))))
      = Poly (scale_poly_list cq (taylor_shift_list (2 * lq)
        (rev (scale_poly_list (2 * dq) (rev Pm)))))"
    using d0
    by (simp add: cdlr_Poly_rev_scale_rev len_inner n_def
        Poly_scale_poly_list Poly_taylor_shift_list
        pcompose_smult smult_smult pcompose_assoc
        scal[unfolded n_def] aff mult.commute)
qed

lemma carried_init_child_left:
  fixes d :: int
  assumes d0: "d \<noteq> 0"
  shows "carried_left (carried_init_same_den l d r P)
       = carried_init_same_den (l + l) (2 * d) (l + r) P"
proof (rule map_rat_of_int_inj)
  have d0': "rat_of_int d \<noteq> 0" using d0 by simp
  have "map rat_of_int (carried_left (carried_init_same_den l d r P))
      = rev (scale_poly_list 2 (rev
          (scale_poly_list (rat_of_int (r - l)) (taylor_shift_list (rat_of_int l)
            (rev (scale_poly_list (rat_of_int d) (rev (map rat_of_int P))))))))"
    by (simp add: carried_left_def carried_init_same_den_def
        scale_for_fractional_shift_eq_scale_poly_list rev_map[symmetric]
        map_rat_of_int_scale_poly_list map_rat_of_int_taylor_shift_list)
  also have "\<dots> = scale_poly_list (rat_of_int (r - l)) (taylor_shift_list (2 * rat_of_int l)
          (rev (scale_poly_list (2 * rat_of_int d) (rev (map rat_of_int P)))))"
    by (rule cdlr_left_rat[OF d0'])
  also have "\<dots> = map rat_of_int (carried_init_same_den (l + l) (2 * d) (l + r) P)"
    by (simp add: carried_init_same_den_def
        scale_for_fractional_shift_eq_scale_poly_list rev_map[symmetric]
        map_rat_of_int_scale_poly_list map_rat_of_int_taylor_shift_list)
  finally show "map rat_of_int (carried_left (carried_init_same_den l d r P))
      = map rat_of_int (carried_init_same_den (l + l) (2 * d) (l + r) P)" .
qed

lemma carried_init_child_right:
  fixes d :: int
  assumes d0: "d \<noteq> 0"
  shows "carried_right (carried_init_same_den l d r P)
       = carried_init_same_den (l + r) (2 * d) (r + r) P"
proof (rule map_rat_of_int_inj)
  have "map rat_of_int (carried_right (carried_init_same_den l d r P))
      = taylor_shift_list 1 (map rat_of_int (carried_left (carried_init_same_den l d r P)))"
    by (simp add: carried_right_def map_rat_of_int_taylor_shift_list)
  also have "\<dots> = taylor_shift_list 1 (map rat_of_int
          (carried_init_same_den (l + l) (2 * d) (l + r) P))"
    by (simp add: carried_init_child_left[OF d0])
  also have "\<dots> = taylor_shift_list 1
          (scale_poly_list (rat_of_int (r - l)) (taylor_shift_list (rat_of_int (l + l))
            (rev (scale_poly_list (rat_of_int (2 * d)) (rev (map rat_of_int P))))))"
    by (simp add: carried_init_same_den_def
        scale_for_fractional_shift_eq_scale_poly_list rev_map[symmetric]
        map_rat_of_int_scale_poly_list map_rat_of_int_taylor_shift_list)
  also have "\<dots> = scale_poly_list (rat_of_int (r - l)) (taylor_shift_list
          (rat_of_int (r - l) + rat_of_int (l + l))
          (rev (scale_poly_list (rat_of_int (2 * d)) (rev (map rat_of_int P)))))"
    by (simp add: taylor_scale_commute_rat taylor_shift_list_add)
  also have "\<dots> = map rat_of_int (carried_init_same_den (l + r) (2 * d) (r + r) P)"
    by (simp add: carried_init_same_den_def
        scale_for_fractional_shift_eq_scale_poly_list rev_map[symmetric]
        map_rat_of_int_scale_poly_list map_rat_of_int_taylor_shift_list algebra_simps)
  finally show "map rat_of_int (carried_right (carried_init_same_den l d r P))
      = map rat_of_int (carried_init_same_den (l + r) (2 * d) (r + r) P)" .
qed

text \<open>The instance the truncating loop's keystone consumes. Unconditional except for
  \<open>2^k \<noteq> 0\<close>, which is automatic.\<close>
lemma carried_left_right_reconstruct:
  shows "carried_left (carried_init_same_den l_num (2 ^ k) r_num P)
       = carried_init_same_den (l_num + l_num) (2 ^ (k + 1)) (l_num + r_num) P"
    and "carried_right (carried_init_same_den l_num (2 ^ k) r_num P)
       = carried_init_same_den (l_num + r_num) (2 ^ (k + 1)) (r_num + r_num) P"
  using carried_init_child_left[of "2 ^ k" l_num r_num P]
        carried_init_child_right[of "2 ^ k" l_num r_num P]
  by simp_all

text \<open>NEXT (separate theory, importing Rational_Refine): the data-refinement
  relation carried_state_rel, the loop-body refinement to \<open>rational_queue_step_int\<close>
  (using @{thm carried_repr_count} + @{thm carried_left_right_monadic_correct} = B1/B2 +
  @{thm carried_descartes_count_monadic_classify}), the loop + main-list lift to
  \<open>rational_queue_main_int\<close>, chaining to @{text "= mset (dsc_int ...)"}, then
  HNR packaging mirroring dsc_rational_main_list_dsc_int_{spec,refine}.\<close>

end
