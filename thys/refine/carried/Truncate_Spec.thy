theory Truncate_Spec
  imports Count_Spec
begin

text \<open>Abstract layer of carried shift truncation: the one-sided error frame carried through the
  bisection recursion, its propagation through the two child maps (dilation, unit Taylor shift),
  and the \<open>g\<close>-widened generalisations of the trusted-sign and guarded-count theorems. No GMP or
  Sepref content.

  The frame: \<open>gframe s g X Y\<close> says the carried coefficient list \<open>Y\<close> is the exact list \<open>X\<close>
  floor-truncated by \<open>s\<close> bits plus at most \<open>g\<close> bits of accumulated one-sided slack
  (\<open>0 \<le> X!i - 2^s * Y!i < 2^(s+g)\<close>). The node state carries only \<open>g\<close>; \<open>s\<close> is existential in the
  refinement relation. Fresh truncation is the instance \<open>gframe t 0 X (trunc_list t X)\<close>, and the
  \<open>trusted_sgn\<close>/\<open>trunc_changes\<close> machinery is recovered at \<open>g = 0\<close>.

  Main results (consumed by \<open>Truncate\<close>'s guarded ops): \<open>gframe\<close> and the propagation lemmas
  (\<open>gframe_trunc*\<close>, \<open>gframe_dilate\<close>, \<open>gframe_shift1\<close>, \<open>gframe_bisect_right\<close>),
  \<open>trusted_sgn_g\<close>/\<open>trunc_changes_g\<close> with the two count directions (\<open>trunc_changes_g_ge2_sound\<close>,
  \<open>trunc_changes_g_decisive_exact\<close>), the midpoint-evaluation guard (\<open>gframe_hom_eval2_sound\<close>), and
  the \<open>node_frame\<close> \<open>g = 0\<close> sentinel bookkeeping.\<close>

section \<open>The one-sided g-frame\<close>

text \<open>\<open>X\<close> = exact node coefficients, \<open>Y\<close> = carried (truncated) coefficients.
  One-sidedness (\<open>0 \<le> err\<close>) is what floor division provides:
  every POSITIVE carried value is sign-trusted for free, at every consumer.\<close>
definition gframe :: "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
  "gframe s g X Y \<longleftrightarrow> length X = length Y \<and>
     (\<forall>i < length Y. 0 \<le> X ! i - 2 ^ s * Y ! i \<and> X ! i - 2 ^ s * Y ! i < 2 ^ (s + g))"

lemma gframe_length: "gframe s g X Y \<Longrightarrow> length X = length Y"
  by (simp add: gframe_def)

text \<open>A never-truncated node is exact: integer error \<open>< 2^0 = 1\<close> forces error \<open>= 0\<close>.
  All child maps below preserve \<open>(s,g) = (0,0)\<close>, so untruncated lineages behave
  bit-identically to the untruncated solver.\<close>
lemma gframe_exact: "gframe 0 0 X X"
  by (simp add: gframe_def)

lemma gframe_mono:
  assumes "gframe s g X Y" and "g \<le> g'"
  shows "gframe s g' X Y"
  using assms
  unfolding gframe_def
  by (auto intro: less_le_trans power_increasing)

text \<open>Counts run on the REVERSED node poly (\<open>carried_descartes_count\<close> reverses);
  the frame is index-uniform so it commutes with \<open>rev\<close>. Route: \<open>rev_nth\<close>.\<close>
lemma gframe_rev:
  assumes "gframe s g X Y"
  shows "gframe s g (rev X) (rev Y)"
  using assms
  unfolding gframe_def
  by (auto simp: rev_nth)

subsection \<open>Fresh truncation of the carried list\<close>

text \<open>Truncating an EXACT-frame list keeps \<open>g = 0\<close>: the new error is
  \<open>2^s * (Y!i mod 2^t) + old \<le> 2^s*(2^t - 1) + (2^s - 1) = 2^(s+t) - 1\<close>.
  Route: \<open>trunc_decomp_nth\<close>/\<open>div_mult_mod_eq\<close> pointwise.\<close>
lemma gframe_trunc_exact:
  assumes "gframe s 0 X Y"
  shows "gframe (s + t) 0 X (trunc_list t Y)"
proof -
  have len: "length X = length Y" using assms unfolding gframe_def by simp
  { fix i assume i: "i < length Y"
    from assms i have lb: "0 \<le> X ! i - 2 ^ s * Y ! i"
      and ub: "X ! i - 2 ^ s * Y ! i < 2 ^ s"
      unfolding gframe_def by auto
    have decomp: "Y ! i = 2 ^ t * (trunc_list t Y ! i) + trunc_resid_list t Y ! i"
      using trunc_decomp_nth[OF i] .
    have resid_lb: "0 \<le> trunc_resid_list t Y ! i" using trunc_resid_nth_lb[OF i] .
    have resid_ub: "trunc_resid_list t Y ! i < 2 ^ t" using trunc_resid_nth_ub[OF i] .
    have resid_ub': "trunc_resid_list t Y ! i \<le> 2 ^ t - 1" using resid_ub by simp
    have resid_mult: "(2::int) ^ s * trunc_resid_list t Y ! i \<le> 2 ^ s * (2 ^ t - 1)"
      using mult_left_mono[OF resid_ub', of "2 ^ s"] by simp
    have eq: "X ! i - 2 ^ (s + t) * (trunc_list t Y ! i)
        = (X ! i - 2 ^ s * Y ! i) + 2 ^ s * trunc_resid_list t Y ! i"
      using decomp by (simp add: power_add algebra_simps)
    have lb': "0 \<le> X ! i - 2 ^ (s + t) * (trunc_list t Y ! i)"
      unfolding eq using lb resid_lb by simp
    have "X ! i - 2 ^ s * Y ! i + 2 ^ s * trunc_resid_list t Y ! i < 2 ^ s + 2 ^ s * (2 ^ t - 1)"
      using ub resid_mult by linarith
    also have "\<dots> = 2 ^ (s + t)" by (simp add: power_add algebra_simps)
    finally have ub': "X ! i - 2 ^ (s + t) * (trunc_list t Y ! i) < 2 ^ (s + t)"
      unfolding eq .
    from lb' ub' have "0 \<le> X ! i - 2 ^ (s + t) * (trunc_list t Y ! i) \<and>
      X ! i - 2 ^ (s + t) * (trunc_list t Y ! i) < 2 ^ (s + t + 0)" by simp
  }
  then show ?thesis using len unfolding gframe_def by (simp add: length_trunc_list)
qed

text \<open>Re-truncating an error-carrying list resets \<open>g\<close> to 1, provided the truncation
  budget dominates the accumulated slack (\<open>g \<le> t\<close> — the impl's nb-gate enforces
  this, plan D-c): new error \<open>< 2^(s+t) + 2^(s+g) \<le> 2^(s+t+1)\<close>.
  \<open>Suc 0\<close> (not \<open>1\<close>) — the printed normal form (proof-iteration cheat sheet).\<close>
lemma gframe_trunc:
  assumes "gframe s g X Y" and "g \<le> t"
  shows "gframe (s + t) (Suc 0) X (trunc_list t Y)"
proof -
  have len: "length X = length Y" using assms unfolding gframe_def by simp
  { fix i assume i: "i < length Y"
    from assms i have lb: "0 \<le> X ! i - 2 ^ s * Y ! i"
      and ub: "X ! i - 2 ^ s * Y ! i < 2 ^ (s + g)"
      unfolding gframe_def by auto
    have decomp: "Y ! i = 2 ^ t * (trunc_list t Y ! i) + trunc_resid_list t Y ! i"
      using trunc_decomp_nth[OF i] .
    have resid_lb: "0 \<le> trunc_resid_list t Y ! i" using trunc_resid_nth_lb[OF i] .
    have resid_ub: "trunc_resid_list t Y ! i < 2 ^ t" using trunc_resid_nth_ub[OF i] .
    have eq: "X ! i - 2 ^ (s + t) * (trunc_list t Y ! i)
        = (X ! i - 2 ^ s * Y ! i) + 2 ^ s * trunc_resid_list t Y ! i"
      using decomp by (simp add: power_add algebra_simps)
    have lb': "0 \<le> X ! i - 2 ^ (s + t) * (trunc_list t Y ! i)"
      unfolding eq using lb resid_lb by simp
    have gpow: "(2::int) ^ (s + g) \<le> 2 ^ (s + t)"
      using \<open>g \<le> t\<close> by (intro power_increasing) auto
    have resid_ub': "trunc_resid_list t Y ! i \<le> 2 ^ t - 1" using resid_ub by simp
    have resid_mult: "(2::int) ^ s * trunc_resid_list t Y ! i \<le> 2 ^ s * (2 ^ t - 1)"
      using mult_left_mono[OF resid_ub', of "2 ^ s"] by simp
    have "X ! i - 2 ^ s * Y ! i + 2 ^ s * trunc_resid_list t Y ! i
        < 2 ^ (s + g) + 2 ^ s * (2 ^ t - 1)"
      using ub resid_mult by linarith
    also have "\<dots> \<le> 2 ^ (s + t) + 2 ^ s * (2 ^ t - 1)"
      using gpow by simp
    also have "\<dots> = 2 ^ (s + t + Suc 0) - 2 ^ s"
      by (simp add: power_add algebra_simps)
    also have "\<dots> < 2 ^ (s + t + Suc 0)" by simp
    finally have ub': "X ! i - 2 ^ (s + t) * (trunc_list t Y ! i) < 2 ^ (s + t + Suc 0)"
      unfolding eq .
    from lb' ub' have "0 \<le> X ! i - 2 ^ (s + t) * (trunc_list t Y ! i) \<and>
      X ! i - 2 ^ (s + t) * (trunc_list t Y ! i) < 2 ^ (s + t + Suc 0)" by simp
  }
  then show ?thesis using len unfolding gframe_def by (simp add: length_trunc_list)
qed

text \<open>Re-truncating when the BUDGET \<open>t\<close> is SMALLER than the accumulated slack \<open>g\<close> (the
  complementary case to \<open>gframe_trunc\<close>'s \<open>g \<le> t\<close>, needed for \<open>retrunc_reset_mop\<close>'s own
  general two-branch reset formula \<open>g' = g - t + 1\<close> when \<open>t < g\<close>): new error
  \<open>< 2^(s+g) + 2^(s+t) - 2^s \<le> 2^(s+t+(g-t+1))\<close>, using \<open>2^t \<le> 2^g\<close> from \<open>t \<le> g\<close> to fold
  \<open>2^g + 2^t - 1 \<le> 2^(g+1)\<close>. Route: mirrors \<open>gframe_trunc\<close>'s pointwise proof with the
  dominance direction flipped.\<close>
lemma gframe_retrunc_dom:
  assumes "gframe s g X Y" and "t \<le> g"
  shows "gframe (s + t) (g - t + 1) X (trunc_list t Y)"
proof -
  have len: "length X = length Y" using assms unfolding gframe_def by simp
  { fix i assume i: "i < length Y"
    from assms i have lb: "0 \<le> X ! i - 2 ^ s * Y ! i"
      and ub: "X ! i - 2 ^ s * Y ! i < 2 ^ (s + g)"
      unfolding gframe_def by auto
    have decomp: "Y ! i = 2 ^ t * (trunc_list t Y ! i) + trunc_resid_list t Y ! i"
      using trunc_decomp_nth[OF i] .
    have resid_lb: "0 \<le> trunc_resid_list t Y ! i" using trunc_resid_nth_lb[OF i] .
    have resid_ub: "trunc_resid_list t Y ! i < 2 ^ t" using trunc_resid_nth_ub[OF i] .
    have eq: "X ! i - 2 ^ (s + t) * (trunc_list t Y ! i)
        = (X ! i - 2 ^ s * Y ! i) + 2 ^ s * trunc_resid_list t Y ! i"
      using decomp by (simp add: power_add algebra_simps)
    have lb': "0 \<le> X ! i - 2 ^ (s + t) * (trunc_list t Y ! i)"
      unfolding eq using lb resid_lb by simp
    have resid_ub': "trunc_resid_list t Y ! i \<le> 2 ^ t - 1" using resid_ub by simp
    have resid_mult: "(2::int) ^ s * trunc_resid_list t Y ! i \<le> 2 ^ s * (2 ^ t - 1)"
      using mult_left_mono[OF resid_ub', of "2 ^ s"] by simp
    have tg: "(2::int) ^ t \<le> 2 ^ g" using \<open>t \<le> g\<close> by (intro power_increasing) auto
    have gpow: "(2::int) ^ (g + 1) = 2 ^ g + 2 ^ g" by (simp add: power_add)
    have fold: "(2::int) ^ g + 2 ^ t - 1 \<le> 2 ^ (g + 1)"
      using tg gpow by linarith
    have "X ! i - 2 ^ s * Y ! i + 2 ^ s * trunc_resid_list t Y ! i
        < 2 ^ (s + g) + 2 ^ s * (2 ^ t - 1)"
      using ub resid_mult by linarith
    also have "\<dots> = 2 ^ s * (2 ^ g + 2 ^ t - 1)" by (simp add: power_add algebra_simps)
    also have "\<dots> \<le> 2 ^ s * 2 ^ (g + 1)" using fold by simp
    also have "\<dots> = 2 ^ (s + t + (g - t + 1))"
      using \<open>t \<le> g\<close> by (simp add: power_add)
    finally have ub': "X ! i - 2 ^ (s + t) * (trunc_list t Y ! i) < 2 ^ (s + t + (g - t + 1))"
      unfolding eq .
    from lb' ub' have "0 \<le> X ! i - 2 ^ (s + t) * (trunc_list t Y ! i) \<and>
      X ! i - 2 ^ (s + t) * (trunc_list t Y ! i) < 2 ^ (s + t + (g - t + 1))" by simp
  }
  then show ?thesis using len unfolding gframe_def by (simp add: length_trunc_list)
qed

subsection \<open>The two bisection child maps\<close>

text \<open>The left-child dilation, coefficient \<open>i \<mapsto> 2^(len-1-i) * c_i\<close> — the abstract
  form of \<open>poly_shift_pow_in_place_monadic\<close>'s \<open>j = 1\<close> instance
  (\<open>Dyadic_Interval.thy\<close>), related to it through that op's \<open>_correct\<close> lemma.\<close>
definition dilate_list :: "int list \<Rightarrow> int list" where
  "dilate_list Y = map (\<lambda>i. Y ! i * 2 ^ (length Y - Suc i)) [0..<length Y]"

lemma length_dilate_list[simp]: "length (dilate_list Y) = length Y"
  by (simp add: dilate_list_def)

lemma dilate_list_nth:
  assumes "i < length Y"
  shows "dilate_list Y ! i = Y ! i * 2 ^ (length Y - Suc i)"
  using assms unfolding dilate_list_def by simp

text \<open>Dilation is per-coefficient multiplication by a positive power \<open>\<le> 2^(len-1)\<close>:
  one-sidedness preserved, slack grows by \<open>len - 1\<close> bits. Route: pointwise;
  \<open>mult_left_mono\<close> on the error, exponent arithmetic.\<close>
lemma gframe_dilate:
  assumes "gframe s g X Y"
  shows "gframe s (g + (length Y - Suc 0)) (dilate_list X) (dilate_list Y)"
proof -
  have lenXY: "length X = length Y" using assms unfolding gframe_def by simp
  { fix i assume i: "i < length Y"
    then have iX: "i < length X" using lenXY by simp
    from assms i have lb: "0 \<le> X ! i - 2 ^ s * Y ! i"
      and ub: "X ! i - 2 ^ s * Y ! i < 2 ^ (s + g)"
      unfolding gframe_def by auto
    have eq: "dilate_list X ! i - 2 ^ s * dilate_list Y ! i
        = (X ! i - 2 ^ s * Y ! i) * 2 ^ (length Y - Suc i)"
      using dilate_list_nth[OF iX] dilate_list_nth[OF i]
      by (simp add: lenXY algebra_simps)
    have lb': "0 \<le> dilate_list X ! i - 2 ^ s * dilate_list Y ! i"
      unfolding eq using lb by simp
    have expmono: "(2::int) ^ (length Y - Suc i) \<le> 2 ^ (length Y - Suc 0)"
      by (intro power_increasing) auto
    have "(X ! i - 2 ^ s * Y ! i) * 2 ^ (length Y - Suc i)
        < 2 ^ (s + g) * 2 ^ (length Y - Suc i)"
      using ub by (intro mult_strict_right_mono) auto
    also have "\<dots> \<le> 2 ^ (s + g) * 2 ^ (length Y - Suc 0)"
      using expmono by (intro mult_left_mono) auto
    also have "\<dots> = 2 ^ (s + (g + (length Y - Suc 0)))"
      by (simp add: power_add)
    finally have ub': "dilate_list X ! i - 2 ^ s * dilate_list Y ! i
        < 2 ^ (s + (g + (length Y - Suc 0)))"
      unfolding eq .
    from lb' ub' have "0 \<le> dilate_list X ! i - 2 ^ s * dilate_list Y ! i \<and>
      dilate_list X ! i - 2 ^ s * dilate_list Y ! i < 2 ^ (s + (g + (length Y - Suc 0)))" by simp
  }
  then show ?thesis using lenXY unfolding gframe_def by simp
qed

text \<open>The unit Taylor shift adds \<open>len\<close> bits of slack: the shifted error at position
  \<open>i\<close> is bounded by \<open>C(len, i+1) * 2^(s+g) \<le> 2^(s+g+len)\<close>. Route: express
  \<open>X = map2 (+) (map ((*) (2^s)) Y) E\<close> with \<open>E\<close> the pointwise error list, then
  @{thm [source] taylor_shift_list_map2_add} and @{thm [source]
  taylor_shift_list_map_smult} (linearity), @{thm [source]
  taylor_shift_list_one_mono} against the scaled all-ones list, and @{thm [source]
  taylor_shift_list_one_replicate_ones} with @{thm [source] shift1_err_bound_le_len}
  (\<open>= binomial_le_pow2\<close>) for the bound.\<close>
lemma gframe_shift1:
  assumes "gframe s g X Y"
  shows "gframe s (g + length Y) (taylor_shift_list 1 X) (taylor_shift_list 1 Y)"
proof -
  define len where "len = length Y"
  define E where "E = map2 (-) X (map ((*) (2 ^ s)) Y)"
  have lenXY: "length X = length Y" using assms unfolding gframe_def by simp
  have lenE: "length E = len" unfolding E_def len_def using lenXY by simp
  have Ei: "\<And>i. i < len \<Longrightarrow> E ! i = X ! i - 2 ^ s * Y ! i"
    unfolding E_def len_def using lenXY by simp
  have Elb: "\<And>i. i < len \<Longrightarrow> 0 \<le> E ! i"
    and Eub: "\<And>i. i < len \<Longrightarrow> E ! i < 2 ^ (s + g)"
    using assms Ei unfolding gframe_def len_def by auto
  have Xdecomp: "X = map2 (+) (map ((*) (2 ^ s)) Y) E"
    unfolding E_def using lenXY by (intro nth_equalityI) simp_all
  have len_eq1: "length (map ((*) (2 ^ s)) Y) = length E"
    using lenE len_def by simp
  have shift_eq: "taylor_shift_list 1 X
      = map2 (+) (map ((*) (2 ^ s)) (taylor_shift_list 1 Y)) (taylor_shift_list 1 E)"
    using Xdecomp taylor_shift_list_map2_add[OF len_eq1]
    by (simp add: taylor_shift_list_map_smult)
  have shift_len: "length (taylor_shift_list 1 X) = len"
    using lenXY len_def by simp
  { fix i assume i: "i < len"
    have Xi: "taylor_shift_list 1 X ! i
        = 2 ^ s * taylor_shift_list 1 Y ! i + taylor_shift_list 1 E ! i"
      using shift_eq i shift_len len_def by simp
    text \<open>Lower bound: shift of a nonneg list is nonneg (monotone against the zero list).\<close>
    have E_ge_zero: "\<forall>j < length (replicate len (0::int)). 0 \<le> replicate len (0::int) ! j
        \<and> replicate len (0::int) ! j \<le> E ! j"
      using Elb by simp
    have E_len0: "length (replicate len (0::int)) = length E" using lenE by simp
    have shiftE_lb: "0 \<le> taylor_shift_list 1 E ! i"
      using taylor_shift_list_one_mono[OF E_len0 E_ge_zero[rule_format]] i lenE
        taylor_shift_list_replicate_zero[of "1::int" len]
      by simp
    text \<open>Upper bound: shift of \<open>E\<close> against the constant \<open>2^(s+g)-1\<close> list.\<close>
    have E_le_const: "\<forall>j < length E. 0 \<le> E ! j \<and> E ! j \<le> replicate len (2 ^ (s + g) - 1 :: int) ! j"
      using Elb Eub lenE by auto
    have E_len1: "length E = length (replicate len (2 ^ (s + g) - 1 :: int))" using lenE by simp
    have shiftE_mono: "taylor_shift_list 1 E ! i
        \<le> taylor_shift_list 1 (replicate len (2 ^ (s + g) - 1 :: int)) ! i"
      using taylor_shift_list_one_mono[OF E_len1 E_le_const[rule_format]] i lenE by simp
    have const_shift: "taylor_shift_list 1 (replicate len (2 ^ (s + g) - 1 :: int)) ! i
        = (2 ^ (s + g) - 1) * shift1_err_bound len i"
    proof -
      have "replicate len (2 ^ (s + g) - 1 :: int) = map ((*) (2 ^ (s + g) - 1)) (replicate len 1)"
        by (simp add: map_replicate)
      also have "taylor_shift_list 1 \<dots>
          = map ((*) (2 ^ (s + g) - 1)) (taylor_shift_list 1 (replicate len (1::int)))"
        by (rule taylor_shift_list_map_smult)
      finally show ?thesis
        using taylor_shift_list_one_replicate_ones[of i len] i by (simp add: nth_map)
    qed
    have bge1: "1 \<le> shift1_err_bound len i"
      unfolding shift1_err_bound_def using i by (simp add: Suc_leI zero_less_binomial)
    have blen: "shift1_err_bound len i \<le> 2 ^ len"
      using shift1_err_bound_le_len .
    have shiftE_ub: "taylor_shift_list 1 E ! i < 2 ^ (s + g + len)"
    proof -
      have "taylor_shift_list 1 E ! i \<le> (2 ^ (s + g) - 1) * shift1_err_bound len i"
        using shiftE_mono const_shift by simp
      also have "\<dots> < shift1_err_bound len i * 2 ^ (s + g)"
        using bge1 by (simp add: mult_strict_right_mono mult.commute)
      also have "\<dots> \<le> 2 ^ len * 2 ^ (s + g)"
        using blen bge1 by (intro mult_right_mono) auto
      also have "\<dots> = 2 ^ (s + g + len)" by (simp add: power_add algebra_simps)
      finally show ?thesis .
    qed
    have "0 \<le> taylor_shift_list 1 X ! i - 2 ^ s * taylor_shift_list 1 Y ! i \<and>
      taylor_shift_list 1 X ! i - 2 ^ s * taylor_shift_list 1 Y ! i < 2 ^ (s + (g + len))"
      using Xi shiftE_lb shiftE_ub by (simp add: add.assoc)
  }
  then show ?thesis
    using shift_len lenXY len_def unfolding gframe_def by simp
qed

text \<open>Per-position refinement of @{thm [source] gframe_shift1}'s bound, exposing the
  UNCAPPED \<open>shift1_err_bound\<close> form (rather than its \<open>2^len\<close> cap) so a caller can apply
  a tighter position-dependent cap (\<open>shift1_err_bound_le_thresh\<close>) instead. Proof is
  the same construction as \<open>gframe_shift1\<close> stopped one step earlier.\<close>
lemma gframe_shift1_nth:
  assumes "gframe s g X Y" and "i < length Y"
  shows "0 \<le> taylor_shift_list 1 X ! i - 2 ^ s * taylor_shift_list 1 Y ! i \<and>
    taylor_shift_list 1 X ! i - 2 ^ s * taylor_shift_list 1 Y ! i
      < shift1_err_bound (length Y) i * 2 ^ (s + g)"
proof -
  define len where "len = length Y"
  define E where "E = map2 (-) X (map ((*) (2 ^ s)) Y)"
  have lenXY: "length X = length Y" using assms(1) unfolding gframe_def by simp
  have lenE: "length E = len" unfolding E_def len_def using lenXY by simp
  have Ei: "\<And>j. j < len \<Longrightarrow> E ! j = X ! j - 2 ^ s * Y ! j"
    unfolding E_def len_def using lenXY by simp
  have Elb: "\<And>j. j < len \<Longrightarrow> 0 \<le> E ! j"
    and Eub: "\<And>j. j < len \<Longrightarrow> E ! j < 2 ^ (s + g)"
    using assms(1) Ei unfolding gframe_def len_def by auto
  have Xdecomp: "X = map2 (+) (map ((*) (2 ^ s)) Y) E"
    unfolding E_def using lenXY by (intro nth_equalityI) simp_all
  have len_eq1: "length (map ((*) (2 ^ s)) Y) = length E"
    using lenE len_def by simp
  have shift_eq: "taylor_shift_list 1 X
      = map2 (+) (map ((*) (2 ^ s)) (taylor_shift_list 1 Y)) (taylor_shift_list 1 E)"
    using Xdecomp taylor_shift_list_map2_add[OF len_eq1]
    by (simp add: taylor_shift_list_map_smult)
  have shift_len: "length (taylor_shift_list 1 X) = len"
    using lenXY len_def by simp
  have i: "i < len" using assms(2) len_def by simp
  have Xi: "taylor_shift_list 1 X ! i
      = 2 ^ s * taylor_shift_list 1 Y ! i + taylor_shift_list 1 E ! i"
    using shift_eq i shift_len len_def by simp
  have E_ge_zero: "\<forall>j < length (replicate len (0::int)). 0 \<le> replicate len (0::int) ! j
      \<and> replicate len (0::int) ! j \<le> E ! j"
    using Elb by simp
  have E_len0: "length (replicate len (0::int)) = length E" using lenE by simp
  have shiftE_lb: "0 \<le> taylor_shift_list 1 E ! i"
    using taylor_shift_list_one_mono[OF E_len0 E_ge_zero[rule_format]] i lenE
      taylor_shift_list_replicate_zero[of "1::int" len]
    by simp
  have E_le_const: "\<forall>j < length E. 0 \<le> E ! j \<and> E ! j \<le> replicate len (2 ^ (s + g) - 1 :: int) ! j"
    using Elb Eub lenE by auto
  have E_len1: "length E = length (replicate len (2 ^ (s + g) - 1 :: int))" using lenE by simp
  have shiftE_mono: "taylor_shift_list 1 E ! i
      \<le> taylor_shift_list 1 (replicate len (2 ^ (s + g) - 1 :: int)) ! i"
    using taylor_shift_list_one_mono[OF E_len1 E_le_const[rule_format]] i lenE by simp
  have const_shift: "taylor_shift_list 1 (replicate len (2 ^ (s + g) - 1 :: int)) ! i
      = (2 ^ (s + g) - 1) * shift1_err_bound len i"
  proof -
    have "replicate len (2 ^ (s + g) - 1 :: int) = map ((*) (2 ^ (s + g) - 1)) (replicate len 1)"
      by (simp add: map_replicate)
    also have "taylor_shift_list 1 \<dots>
        = map ((*) (2 ^ (s + g) - 1)) (taylor_shift_list 1 (replicate len (1::int)))"
      by (rule taylor_shift_list_map_smult)
    finally show ?thesis
      using taylor_shift_list_one_replicate_ones[of i len] i by (simp add: nth_map)
  qed
  have bge1: "1 \<le> shift1_err_bound len i"
    unfolding shift1_err_bound_def using i by (simp add: Suc_leI zero_less_binomial)
  have shiftE_ub: "taylor_shift_list 1 E ! i < shift1_err_bound len i * 2 ^ (s + g)"
  proof -
    have "taylor_shift_list 1 E ! i \<le> (2 ^ (s + g) - 1) * shift1_err_bound len i"
      using shiftE_mono const_shift by simp
    also have "\<dots> < shift1_err_bound len i * 2 ^ (s + g)"
      using bge1 by (simp add: mult_strict_right_mono mult.commute)
    finally show ?thesis .
  qed
  show ?thesis using Xi shiftE_lb shiftE_ub len_def by simp
qed

text \<open>The right bisection child = dilation then unit shift: \<open>g += 2*len - 1\<close>.\<close>
corollary gframe_bisect_right:
  assumes "gframe s g X Y"
  shows "gframe s (g + (2 * length Y - Suc 0))
           (taylor_shift_list 1 (dilate_list X)) (taylor_shift_list 1 (dilate_list Y))"
proof -
  have step1: "gframe s (g + (length Y - Suc 0)) (dilate_list X) (dilate_list Y)"
    using gframe_dilate[OF assms] .
  have step2: "gframe s ((g + (length Y - Suc 0)) + length (dilate_list Y))
      (taylor_shift_list 1 (dilate_list X)) (taylor_shift_list 1 (dilate_list Y))"
    using gframe_shift1[OF step1] .
  have step2': "gframe s (g + (length Y - Suc 0) + length Y)
      (taylor_shift_list 1 (dilate_list X)) (taylor_shift_list 1 (dilate_list Y))"
    using step2 by (simp add: length_dilate_list)
  have eq: "g + (length Y - Suc 0) + length Y = g + (2 * length Y - Suc 0)"
    by simp
  show ?thesis using step2' unfolding eq .
qed

section \<open>g-widened trusted signs\<close>

text \<open>\<open>trusted_sgn\<close> of the plain truncated count, with the negative-branch threshold widened by the node's
  carried slack \<open>g\<close>: the count's own (virtual) shift contributes
  \<open>trunc_thresh len i\<close> bits on top of the \<open>g\<close> bits already in the node — no double
  counting. At \<open>g = 0\<close> this IS \<open>trusted_sgn\<close>.\<close>
definition trusted_sgn_g :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int option" where
  "trusted_sgn_g g len i x =
     (if 0 < x then Some 1
      else if x \<le> - (2 ^ (g + trunc_thresh len i)) then Some (-1)
      else None)"

lemma trusted_sgn_g_zero: "trusted_sgn_g 0 len i x = trusted_sgn len i x"
  by (simp add: trusted_sgn_g_def trusted_sgn_def)

text \<open>A trusted sign of the shifted CARRIED list is the exact sign of the shifted
  EXACT list. Positive branch: free (one-sided, \<open>X'!i \<ge> 2^s * Y'!i > 0\<close>).
  Negative branch: shifted error at \<open>i\<close> is \<open>< C(len,i+1) * 2^(s+g)
  \<le> 2^(s + g + trunc_thresh len i)\<close> (@{thm [source] shift1_err_bound_le_thresh}),
  so \<open>Y'!i \<le> -2^(g+thresh)\<close> forces \<open>X'!i < 0\<close> strictly. Route: the per-position
  refinement of \<open>gframe_shift1\<close>'s bound (keep it as a separate \<open>_nth\<close> helper if the
  uniform lemma loses the position).\<close>
lemma trusted_sgn_g_sound:
  assumes "gframe s g X Y" and "i < length Y"
    and "trusted_sgn_g g (length Y) i (taylor_shift_list 1 Y ! i) = Some sg"
  shows "sgn (taylor_shift_list 1 X ! i) = sg"
proof -
  let ?len = "length Y"
  define Yp where "Yp = taylor_shift_list 1 Y ! i"
  define Xp where "Xp = taylor_shift_list 1 X ! i"
  have bnd: "0 \<le> Xp - 2 ^ s * Yp \<and> Xp - 2 ^ s * Yp < shift1_err_bound ?len i * 2 ^ (s + g)"
    using gframe_shift1_nth[OF assms(1) assms(2)] unfolding Xp_def Yp_def by simp
  have thresh: "shift1_err_bound ?len i \<le> 2 ^ trunc_thresh ?len i"
    using shift1_err_bound_le_thresh[of i ?len] assms(2) by simp
  have cases_sg: "(0 < Yp \<and> sg = 1) \<or> (Yp \<le> -(2 ^ (g + trunc_thresh ?len i)) \<and> sg = -1)"
    using assms(3) unfolding trusted_sgn_g_def Yp_def
    by (auto split: if_splits)
  from cases_sg show ?thesis
  proof
    assume "0 < Yp \<and> sg = 1"
    then have Yp_pos: "0 < Yp" and sg1: "sg = 1" by auto
    have "0 < 2 ^ s * Yp" using Yp_pos by simp
    then have "0 < Xp" using bnd by linarith
    then show ?thesis unfolding Xp_def sg1 by simp
  next
    assume "Yp \<le> -(2 ^ (g + trunc_thresh ?len i)) \<and> sg = -1"
    then have Yp_neg: "Yp \<le> -(2 ^ (g + trunc_thresh ?len i))" and sgm1: "sg = -1" by auto
    have h1: "2 ^ s * Yp \<le> 2 ^ s * (- (2 ^ (g + trunc_thresh ?len i)))"
      by (intro mult_left_mono Yp_neg) simp
    have h1': "(2::int) ^ s * (- (2 ^ (g + trunc_thresh ?len i))) = - (2 ^ (s + (g + trunc_thresh ?len i)))"
      by (simp add: power_add)
    have h2: "Xp - 2 ^ s * Yp < shift1_err_bound ?len i * 2 ^ (s + g)"
      using bnd by simp
    have h3: "shift1_err_bound ?len i * 2 ^ (s + g) \<le> 2 ^ trunc_thresh ?len i * 2 ^ (s + g)"
      using thresh by (intro mult_right_mono) auto
    have h4: "(2::int) ^ trunc_thresh ?len i * 2 ^ (s + g) = 2 ^ (s + (g + trunc_thresh ?len i))"
      by (simp add: power_add algebra_simps)
    have "Xp < 2 ^ s * Yp + 2 ^ (s + (g + trunc_thresh ?len i))"
      using h2 h3 h4 by simp
    also have "\<dots> \<le> - (2 ^ (s + (g + trunc_thresh ?len i))) + 2 ^ (s + (g + trunc_thresh ?len i))"
      using h1 h1' by simp
    also have "\<dots> = 0" by simp
    finally have "Xp < 0" .
    then show ?thesis unfolding Xp_def sgm1 by simp
  qed
qed

section \<open>The g-widened guarded sign-variation fold\<close>

text \<open>Same fold as \<open>trunc_changes\<close> (state: last trusted sign, count of trusted
  changes, ambiguity flag) with \<open>trusted_sgn_g\<close> plugged in. The impl kernel is the
  plain truncated count kernel with its per-position threshold widened by \<open>g\<close> and NO truncation
  pre-pass (the node poly is already the truncation).\<close>
definition trunc_changes_g :: "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> nat \<times> bool" where
  "trunc_changes_g g len ys =
     (case fold (\<lambda>(i, x). tsign_step (trusted_sgn_g g len i x))
            (zip [0..<length ys] ys) (0, 0, False)
      of (_, cnt, amb) \<Rightarrow> (cnt, amb))"

lemma trunc_changes_g_zero: "trunc_changes_g 0 len ys = trunc_changes len ys"
proof -
  have feq: "(\<lambda>(i, x). tsign_step (trusted_sgn_g 0 len i x))
      = (\<lambda>(i, x). tsign_step (trusted_sgn len i x))"
    by (rule ext) (auto simp: trusted_sgn_g_zero split: prod.splits)
  show ?thesis unfolding trunc_changes_g_def trunc_changes_def feq by simp
qed

subsection \<open>The \<open>g\<close>-widened fold\<close>

text \<open>Clone of \<open>Count_Spec.thy\<close>'s \<open>tsign_*\<close> machinery (lines 704-1029),
  \<open>trusted_sgn\<close> replaced throughout by \<open>trusted_sgn_g g\<close>. Each proof is mechanically
  the same case split on \<open>trusted_sgn_g\<close>'s definition (same if-then-else SHAPE as
  \<open>trusted_sgn\<close>, only the threshold expression differs), so this is a direct
  substitution clone, not a re-derivation.\<close>
definition tsign_repr_g :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "tsign_repr_g g len i x = (case trusted_sgn_g g len i x of Some s \<Rightarrow> s | None \<Rightarrow> 0)"

lemma tsign_step_eq_sign_step_g:
  assumes "last_s = 0 \<longrightarrow> cnt = 0"
  shows "(\<lambda>(a,b,c). (a,b)) (tsign_step (trusted_sgn_g g len i x) (last_s, cnt, amb))
       = sign_step (tsign_repr_g g len i x) (last_s, cnt)"
  using assms
  unfolding tsign_repr_g_def trusted_sgn_g_def
  by (cases "0 < x"; cases "x \<le> - (2 ^ (g + trunc_thresh len i))") auto

lemma tsign_step_invar_g:
  assumes "last_s = 0 \<longrightarrow> cnt = 0"
    and "tsign_step (trusted_sgn_g g len i x) (last_s, cnt, amb) = (last_s', cnt', amb')"
  shows "last_s' = 0 \<longrightarrow> cnt' = 0"
  using assms
  unfolding trusted_sgn_g_def
  by (cases "0 < x"; cases "x \<le> - (2 ^ (g + trunc_thresh len i))") auto

fun tsign_fold_idx_g :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int \<times> nat \<times> bool \<Rightarrow> int \<times> nat \<times> bool" where
  "tsign_fold_idx_g g len i0 [] st = st"
| "tsign_fold_idx_g g len i0 (x # xs) st =
     tsign_fold_idx_g g len (Suc i0) xs (tsign_step (trusted_sgn_g g len i0 x) st)"

lemma fold_tsign_eq_idx_g:
  "fold (\<lambda>(i, x). tsign_step (trusted_sgn_g g len i x)) (zip [i0..<i0 + length xs] xs) st
     = tsign_fold_idx_g g len i0 xs st"
proof (induction xs arbitrary: i0 st)
  case Nil
  then show ?case by simp
next
  case (Cons x xs')
  have "[i0..<i0 + length (x # xs')] = i0 # [Suc i0..<i0 + length (x # xs')]"
    by (rule upt_conv_Cons) simp
  then have "[i0..<i0 + length (x # xs')] = i0 # [Suc i0..<Suc i0 + length xs']"
    by simp
  then show ?case
    using Cons.IH[of "Suc i0" "tsign_step (trusted_sgn_g g len i0 x) st"]
    by simp
qed

definition tsign_Z_g :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list" where
  "tsign_Z_g g len i0 xs = map (\<lambda>j. tsign_repr_g g len (i0 + j) (xs ! j)) [0..<length xs]"

lemma length_tsign_Z_g[simp]: "length (tsign_Z_g g len i0 xs) = length xs"
  by (simp add: tsign_Z_g_def)

lemma tsign_fold_idx_eq_sign_step_g:
  assumes "last_s = 0 \<longrightarrow> cnt = 0"
  shows "(\<lambda>(a,b,c). (a,b)) (tsign_fold_idx_g g len i0 xs (last_s, cnt, amb))
       = fold sign_step (tsign_Z_g g len i0 xs) (last_s, cnt)"
  using assms
proof (induction xs arbitrary: i0 last_s cnt amb)
  case Nil
  then show ?case by (simp add: tsign_Z_g_def)
next
  case (Cons x xs')
  obtain ls1 cnt1 amb1 where step1:
    "tsign_step (trusted_sgn_g g len i0 x) (last_s, cnt, amb) = (ls1, cnt1, amb1)"
    by (cases "tsign_step (trusted_sgn_g g len i0 x) (last_s, cnt, amb)")
  have eq1: "(ls1, cnt1) = sign_step (tsign_repr_g g len i0 x) (last_s, cnt)"
    using tsign_step_eq_sign_step_g[OF Cons.prems, of g len i0 x amb] step1 by simp
  have invar1: "ls1 = 0 \<longrightarrow> cnt1 = 0"
    using tsign_step_invar_g[OF Cons.prems step1] .
  have "(\<lambda>(a,b,c). (a,b)) (tsign_fold_idx_g g len i0 (x # xs') (last_s, cnt, amb))
      = (\<lambda>(a,b,c). (a,b)) (tsign_fold_idx_g g len (Suc i0) xs' (ls1, cnt1, amb1))"
    using step1 by simp
  also have "\<dots> = fold sign_step (tsign_Z_g g len (Suc i0) xs') (ls1, cnt1)"
    using Cons.IH[OF invar1] by simp
  also have "\<dots> = fold sign_step (tsign_Z_g g len (Suc i0) xs')
      (sign_step (tsign_repr_g g len i0 x) (last_s, cnt))"
    using eq1 by simp
  also have "\<dots> = fold sign_step (tsign_repr_g g len i0 x # tsign_Z_g g len (Suc i0) xs') (last_s, cnt)"
    by simp
  also have "tsign_repr_g g len i0 x # tsign_Z_g g len (Suc i0) xs' = tsign_Z_g g len i0 (x # xs')"
    unfolding tsign_Z_g_def
    by (simp add: map_upt_Suc del: upt_Suc)
  finally show ?case .
qed

lemma tsign_fold_idx_amb_iff_g:
  "(\<lambda>(a, b, c). c) (tsign_fold_idx_g g len i0 xs (last_s, cnt, amb0))
     \<longleftrightarrow> (amb0 \<or> (\<exists>j < length xs. trusted_sgn_g g len (i0 + j) (xs ! j) = None))"
proof (induction xs arbitrary: i0 last_s cnt amb0)
  case Nil
  then show ?case by simp
next
  case (Cons x xs')
  obtain ls1 cnt1 amb1 where step1:
    "tsign_step (trusted_sgn_g g len i0 x) (last_s, cnt, amb0) = (ls1, cnt1, amb1)"
    by (cases "tsign_step (trusted_sgn_g g len i0 x) (last_s, cnt, amb0)")
  have amb1_eq: "amb1 = (amb0 \<or> trusted_sgn_g g len i0 x = None)"
    using step1 by (cases "trusted_sgn_g g len i0 x") auto
  have "(\<lambda>(a, b, c). c) (tsign_fold_idx_g g len i0 (x # xs') (last_s, cnt, amb0))
      = (\<lambda>(a, b, c). c) (tsign_fold_idx_g g len (Suc i0) xs' (ls1, cnt1, amb1))"
    using step1 by simp
  also have "\<dots> \<longleftrightarrow> (amb1 \<or> (\<exists>j < length xs'. trusted_sgn_g g len (Suc i0 + j) (xs' ! j) = None))"
    using Cons.IH by simp
  also have "\<dots> \<longleftrightarrow>
      (amb0 \<or> trusted_sgn_g g len i0 x = None
       \<or> (\<exists>j < length xs'. trusted_sgn_g g len (Suc i0 + j) (xs' ! j) = None))"
    using amb1_eq by simp
  also have "\<dots> \<longleftrightarrow>
      (amb0 \<or> (\<exists>j < length (x # xs'). trusted_sgn_g g len (i0 + j) ((x # xs') ! j) = None))"
    by (auto simp: less_Suc_eq_0_disj)
  finally show ?case .
qed

lemma trunc_changes_g_conv_fold_idx:
  "trunc_changes_g g len xs
     = (case tsign_fold_idx_g g len 0 xs (0, 0, False) of (_, cnt, amb) \<Rightarrow> (cnt, amb))"
  unfolding trunc_changes_g_def
  using fold_tsign_eq_idx_g[of g len 0 xs "(0, 0, False)"]
  by (simp add: id_def cong: prod.case_cong)

text \<open>Direction 1 (usable WITH ambiguity — powers the early-abort-at-2 branch):
  trusted signs are exact signs of a subsequence of the exact shifted list; a
  subsequence never has more sign changes. Clone of \<open>trunc_changes_ge2_sound\<close>
  (\<open>Count_Spec.thy\<close>) over the \<open>_g\<close> fold above, with
  \<open>trusted_sgn_g_sound\<close> in place of \<open>trusted_sgn_sound\<close>.\<close>
lemma trunc_changes_g_ge2_sound:
  assumes "gframe s g X Y"
    and "2 \<le> fst (trunc_changes_g g (length Y) (taylor_shift_list 1 Y))"
  shows "2 \<le> sign_changes_fold (taylor_shift_list 1 X)"
proof -
  let ?len = "length Y"
  let ?xs = "taylor_shift_list 1 Y"
  let ?T = "taylor_shift_list 1 X"
  have len_xs: "length ?xs = ?len" using assms(1) unfolding gframe_def by simp
  have lenT: "length ?T = ?len" using assms(1) unfolding gframe_def by simp
  have tc_eq: "trunc_changes_g g ?len ?xs
      = (case tsign_fold_idx_g g ?len 0 ?xs (0, 0, False) of (_, cnt, amb) \<Rightarrow> (cnt, amb))"
    using trunc_changes_g_conv_fold_idx[of g ?len ?xs] .
  obtain ls1 cnt1 amb1 where st1: "tsign_fold_idx_g g ?len 0 ?xs (0, 0, False) = (ls1, cnt1, amb1)"
    by (cases "tsign_fold_idx_g g ?len 0 ?xs (0, 0, False)") auto
  have cnt_eq: "fst (trunc_changes_g g ?len ?xs) = cnt1"
    using tc_eq st1 by simp
  have corr: "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx_g g ?len 0 ?xs (0, 0, False))
      = fold sign_step (tsign_Z_g g ?len 0 ?xs) (0, 0)"
    using tsign_fold_idx_eq_sign_step_g[of 0 0 g ?len 0 ?xs False] by simp
  have cnt1_eq: "cnt1 = sign_changes_fold (tsign_Z_g g ?len 0 ?xs)"
    using corr st1 unfolding sign_changes_fold_def by (metis snd_conv split_conv)
  have pw: "\<forall>j < length (tsign_Z_g g ?len 0 ?xs).
      tsign_Z_g g ?len 0 ?xs ! j = 0 \<or> tsign_Z_g g ?len 0 ?xs ! j = (map sgn ?T) ! j"
  proof (intro allI impI)
    fix j assume j: "j < length (tsign_Z_g g ?len 0 ?xs)"
    then have jlen: "j < ?len" by simp
    then have jxlen: "j < length ?xs" using len_xs by simp
    show "tsign_Z_g g ?len 0 ?xs ! j = 0 \<or> tsign_Z_g g ?len 0 ?xs ! j = (map sgn ?T) ! j"
    proof (cases "trusted_sgn_g g ?len j (?xs ! j)")
      case None
      then have "tsign_Z_g g ?len 0 ?xs ! j = 0"
        unfolding tsign_Z_g_def tsign_repr_g_def using jxlen by simp
      then show ?thesis by simp
    next
      case (Some sgv)
      then have z_eq: "tsign_Z_g g ?len 0 ?xs ! j = sgv"
        unfolding tsign_Z_g_def tsign_repr_g_def using jxlen by simp
      have Teq: "sgn (?T ! j) = sgv"
        using trusted_sgn_g_sound[OF assms(1) jlen] Some jlen by simp
      have "map sgn ?T ! j = sgn (?T ! j)" using jlen lenT by simp
      then show ?thesis using z_eq Teq by simp
    qed
  qed
  have lens: "length (tsign_Z_g g ?len 0 ?xs) = length (map sgn ?T)"
    using len_xs lenT by simp
  have mask_le: "changes (tsign_Z_g g ?len 0 ?xs) \<le> changes (map sgn ?T)"
    using changes_mask_le[OF lens] pw by simp
  have lhs_eq: "changes (tsign_Z_g g ?len 0 ?xs) = int cnt1"
    using changes_eq_sign_changes_fold[of "tsign_Z_g g ?len 0 ?xs"] cnt1_eq by simp
  have rhs_eq: "changes (map sgn ?T) = int (sign_changes_fold ?T)"
    using changes_map_sgn_eq[of ?T] changes_eq_sign_changes_fold[of ?T] by simp
  have "cnt1 \<le> sign_changes_fold ?T"
    using mask_le lhs_eq rhs_eq by simp
  then show ?thesis
    using assms(2) cnt_eq by simp
qed

text \<open>Direction 2 (the decisive case): no ambiguity \<Longrightarrow> every exact shifted
  coefficient is nonzero with sign equal to its trusted sign \<Longrightarrow> counts agree
  EXACTLY (so the classify trichotomy transfers). Route: clone
  @{thm [source] trunc_changes_decisive_exact} with \<open>trusted_sgn_g_sound\<close>.\<close>
lemma trunc_changes_g_decisive_exact:
  assumes "gframe s g X Y"
    and "\<not> snd (trunc_changes_g g (length Y) (taylor_shift_list 1 Y))"
  shows "fst (trunc_changes_g g (length Y) (taylor_shift_list 1 Y))
       = sign_changes_fold (taylor_shift_list 1 X)"
proof -
  let ?len = "length Y"
  let ?xs = "taylor_shift_list 1 Y"
  let ?T = "taylor_shift_list 1 X"
  have len_xs: "length ?xs = ?len" using assms(1) unfolding gframe_def by simp
  have lenT: "length ?T = ?len" using assms(1) unfolding gframe_def by simp
  have tc_eq: "trunc_changes_g g ?len ?xs
      = (case tsign_fold_idx_g g ?len 0 ?xs (0, 0, False) of (_, cnt, amb) \<Rightarrow> (cnt, amb))"
    using trunc_changes_g_conv_fold_idx[of g ?len ?xs] .
  obtain ls1 cnt1 amb1 where st1: "tsign_fold_idx_g g ?len 0 ?xs (0, 0, False) = (ls1, cnt1, amb1)"
    by (cases "tsign_fold_idx_g g ?len 0 ?xs (0, 0, False)") auto
  have cnt_eq: "fst (trunc_changes_g g ?len ?xs) = cnt1"
    using tc_eq st1 by simp
  have amb_eq: "snd (trunc_changes_g g ?len ?xs) = amb1"
    using tc_eq st1 by simp
  have no_none: "\<forall>j < length ?xs. trusted_sgn_g g ?len j (?xs ! j) \<noteq> None"
    using tsign_fold_idx_amb_iff_g[of g ?len 0 ?xs 0 0 False] st1 amb_eq assms(2) by auto
  have corr: "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx_g g ?len 0 ?xs (0, 0, False))
      = fold sign_step (tsign_Z_g g ?len 0 ?xs) (0, 0)"
    using tsign_fold_idx_eq_sign_step_g[of 0 0 g ?len 0 ?xs False] by simp
  have cnt1_eq: "cnt1 = sign_changes_fold (tsign_Z_g g ?len 0 ?xs)"
    using corr st1 unfolding sign_changes_fold_def by (metis snd_conv split_conv)
  have exact: "tsign_Z_g g ?len 0 ?xs = map sgn ?T"
  proof (rule nth_equalityI)
    show "length (tsign_Z_g g ?len 0 ?xs) = length (map sgn ?T)" using len_xs lenT by simp
    fix j assume "j < length (tsign_Z_g g ?len 0 ?xs)"
    then have jlen: "j < ?len" by simp
    then have jxlen: "j < length ?xs" using len_xs by simp
    obtain sgv where some_sgv: "trusted_sgn_g g ?len j (?xs ! j) = Some sgv"
      using no_none jxlen by (cases "trusted_sgn_g g ?len j (?xs ! j)") auto
    have z_eq: "tsign_Z_g g ?len 0 ?xs ! j = sgv"
      unfolding tsign_Z_g_def tsign_repr_g_def using jxlen some_sgv by simp
    have "sgn (?T ! j) = sgv"
      using trusted_sgn_g_sound[OF assms(1) jlen] some_sgv jlen by simp
    then show "tsign_Z_g g ?len 0 ?xs ! j = map sgn ?T ! j"
      using z_eq jxlen jlen lenT by simp
  qed
  have lhs_eq: "changes (tsign_Z_g g ?len 0 ?xs) = int cnt1"
    using changes_eq_sign_changes_fold[of "tsign_Z_g g ?len 0 ?xs"] cnt1_eq by simp
  have rhs_eq: "changes (map sgn ?T) = int (sign_changes_fold ?T)"
    using changes_map_sgn_eq[of ?T] changes_eq_sign_changes_fold[of ?T] by simp
  have "cnt1 = sign_changes_fold ?T"
    using exact lhs_eq rhs_eq by simp
  then show ?thesis
    using cnt_eq by simp
qed

subsection \<open>g-widened fold combinators (needed by the impl-layer WHILET clone)\<close>

text \<open>Clones of \<open>Count_Spec.thy\<close>'s later combinator batch
  (\<open>tsign_fold_idx_append\<close> through \<open>trusted_sgn_last\<close>, lines 953-1139), over
  \<open>tsign_fold_idx_g\<close>/\<open>trusted_sgn_g\<close>. \<open>tsign_step_fst_snd_cong\<close> and
  \<open>tsign_step_cnt_mono\<close> are already fully generic in the trust ORACLE (they take
  \<open>os :: int option\<close> as a bare parameter, never unfolding \<open>trusted_sgn\<close>) and are
  reused verbatim from the imported \<open>Count_Spec\<close> session — only the
  FOLD-level wrappers need a \<open>_g\<close> clone.\<close>

lemma tsign_fold_idx_append_g:
  "tsign_fold_idx_g g len i0 (xs @ ys) st
     = tsign_fold_idx_g g len (i0 + length xs) ys (tsign_fold_idx_g g len i0 xs st)"
  by (induction xs arbitrary: i0 st) simp_all

lemma tsign_fold_idx_take_Suc_g:
  assumes "i < length xs"
  shows "tsign_fold_idx_g g len i0 (take (Suc i) xs) st
       = tsign_step (trusted_sgn_g g len (i0 + i) (xs ! i)) (tsign_fold_idx_g g len i0 (take i xs) st)"
proof -
  have "take (Suc i) xs = take i xs @ [xs ! i]"
    using assms by (rule take_Suc_conv_app_nth)
  then have "tsign_fold_idx_g g len i0 (take (Suc i) xs) st
      = tsign_fold_idx_g g len (i0 + length (take i xs)) [xs ! i] (tsign_fold_idx_g g len i0 (take i xs) st)"
    by (simp add: tsign_fold_idx_append_g)
  also have "length (take i xs) = i" using assms by simp
  finally show ?thesis by simp
qed

lemma tsign_fold_idx_fst_snd_cong_g:
  assumes "(\<lambda>(a, b, c). (a, b)) st = (\<lambda>(a, b, c). (a, b)) st'"
  shows "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx_g g len i0 xs st)
       = (\<lambda>(a, b, c). (a, b)) (tsign_fold_idx_g g len i0 xs st')"
  using assms
proof (induction xs arbitrary: i0 st st')
  case Nil
  then show ?case by simp
next
  case (Cons x xs')
  show ?case
    using Cons.IH[OF tsign_step_fst_snd_cong[OF Cons.prems]] by simp
qed

lemma tsign_fold_idx_amb_or_g:
  "(\<lambda>(a, b, c). c) (tsign_fold_idx_g g len i0 xs (ls, cnt, amb0))
     = (amb0 \<or> (\<lambda>(a, b, c). c) (tsign_fold_idx_g g len i0 xs (ls, cnt, False)))"
  using tsign_fold_idx_amb_iff_g[of g len i0 xs ls cnt amb0]
        tsign_fold_idx_amb_iff_g[of g len i0 xs ls cnt False]
  by simp

lemma tsign_fold_idx_cnt_mono_g:
  "(\<lambda>(a, b, c). b) st \<le> (\<lambda>(a, b, c). b) (tsign_fold_idx_g g len i0 xs st)"
proof (induction xs arbitrary: i0 st)
  case Nil
  then show ?case by simp
next
  case (Cons x xs')
  have "(\<lambda>(a, b, c). b) st \<le> (\<lambda>(a, b, c). b) (tsign_step (trusted_sgn_g g len i0 x) st)"
    by (rule tsign_step_cnt_mono)
  also have "\<dots> \<le> (\<lambda>(a, b, c). b) (tsign_fold_idx_g g len (Suc i0) xs'
      (tsign_step (trusted_sgn_g g len i0 x) st))"
    by (rule Cons.IH)
  finally show ?case by simp
qed

text \<open>Boundary split, the \<open>_g\<close> twin of @{thm [source] trunc_changes_split_last}.\<close>
lemma trunc_changes_g_split_last:
  assumes "xs \<noteq> []"
  shows "trunc_changes_g g len xs
    = (case tsign_step (trusted_sgn_g g len (length xs - 1) (last xs))
             (tsign_fold_idx_g g len 0 (butlast xs) (0, 0, False))
       of (_, cnt, amb) \<Rightarrow> (cnt, amb))"
proof -
  have split: "xs = butlast xs @ [last xs]"
    using assms by simp
  have "tsign_fold_idx_g g len 0 xs (0, 0, False)
      = tsign_fold_idx_g g len (0 + length (butlast xs)) [last xs]
          (tsign_fold_idx_g g len 0 (butlast xs) (0, 0, False))"
    by (subst split) (rule tsign_fold_idx_append_g)
  also have "length (butlast xs) = length xs - 1" by simp
  finally have "tsign_fold_idx_g g len 0 xs (0, 0, False)
      = tsign_step (trusted_sgn_g g len (length xs - 1) (last xs))
          (tsign_fold_idx_g g len 0 (butlast xs) (0, 0, False))"
    by simp
  then show ?thesis
    unfolding trunc_changes_g_conv_fold_idx
    by (simp add: id_def cong: prod.case_cong)
qed

text \<open>Early-abort lower bound, the \<open>_g\<close> twin of @{thm [source] trunc_changes_cnt_ge_prefix}.\<close>
lemma trunc_changes_g_cnt_ge_prefix:
  assumes "tsign_fold_idx_g g len 0 (take i xs) (0, 0, False) = (ls, cnt, amb)"
  shows "cnt \<le> fst (trunc_changes_g g len xs)"
proof -
  have "tsign_fold_idx_g g len 0 xs (0, 0, False)
      = tsign_fold_idx_g g len 0 (take i xs @ drop i xs) (0, 0, False)" by simp
  also have "\<dots> = tsign_fold_idx_g g len (0 + length (take i xs)) (drop i xs)
                    (tsign_fold_idx_g g len 0 (take i xs) (0, 0, False))"
    by (rule tsign_fold_idx_append_g)
  also have "\<dots> = tsign_fold_idx_g g len (0 + length (take i xs)) (drop i xs) (ls, cnt, amb)"
    by (simp add: assms)
  finally have full: "tsign_fold_idx_g g len 0 xs (0, 0, False)
      = tsign_fold_idx_g g len (0 + length (take i xs)) (drop i xs) (ls, cnt, amb)" .
  have "cnt \<le> (\<lambda>(a, b, c). b) (tsign_fold_idx_g g len (0 + length (take i xs)) (drop i xs) (ls, cnt, amb))"
    using tsign_fold_idx_cnt_mono_g[of "(ls, cnt, amb)"] by simp
  then have "cnt \<le> (\<lambda>(a, b, c). b) (tsign_fold_idx_g g len 0 xs (0, 0, False))"
    using full by simp
  then show ?thesis
    unfolding trunc_changes_g_conv_fold_idx
    by (cases "tsign_fold_idx_g g len 0 xs (0, 0, False)") auto
qed

text \<open>Operational (sign+bitlen-comparison) form of \<open>trusted_sgn_g\<close>, the \<open>_g\<close> twin of
  @{thm [source] trusted_sgn_bitlen_test} — same case split on \<open>x\<close>, threshold widened
  by \<open>g\<close> throughout.\<close>
lemma trusted_sgn_g_bitlen_test:
  fixes x :: int
  assumes ub: "\<bar>x\<bar> < 2 ^ bl"
    and lb: "x \<noteq> 0 \<Longrightarrow> 2 ^ (bl - 1) \<le> \<bar>x\<bar>"
  shows "trusted_sgn_g g len i x
       = (if 0 < sgn x then Some 1
          else if sgn x < 0 \<and> g + trunc_thresh len i < bl then Some (-1)
          else None)"
proof (cases x "0::int" rule: linorder_cases)
  case less
  have xne: "x \<noteq> 0" using less by simp
  have blpos: "0 < bl"
  proof (rule ccontr)
    assume "\<not> 0 < bl"
    then have "bl = 0" by simp
    then have "\<bar>x\<bar> < 1" using ub by simp
    then show False using xne by simp
  qed
  have iff: "x \<le> - (2 ^ (g + trunc_thresh len i)) \<longleftrightarrow> g + trunc_thresh len i < bl"
  proof
    assume "g + trunc_thresh len i < bl"
    then have "g + trunc_thresh len i \<le> bl - 1" by simp
    then have "(2::int) ^ (g + trunc_thresh len i) \<le> 2 ^ (bl - 1)"
      by (simp add: power_increasing)
    also have "\<dots> \<le> \<bar>x\<bar>" using lb xne by simp
    finally show "x \<le> - (2 ^ (g + trunc_thresh len i))" using less by simp
  next
    assume "x \<le> - (2 ^ (g + trunc_thresh len i))"
    then have "(2::int) ^ (g + trunc_thresh len i) \<le> \<bar>x\<bar>" using less by simp
    also have "\<dots> < 2 ^ bl" using ub .
    finally show "g + trunc_thresh len i < bl"
      using power_less_imp_less_exp[of "2::int" "g + trunc_thresh len i" bl] by simp
  qed
  show ?thesis
    unfolding trusted_sgn_g_def using less iff by auto
next
  case equal
  then show ?thesis
    unfolding trusted_sgn_g_def by auto
next
  case greater
  then show ?thesis
    unfolding trusted_sgn_g_def by auto
qed

subsection \<open>The masked-coefficient device (guarded-bitlen repair), \<open>_g\<close> twin\<close>

text \<open>The masked-coefficient device of \<open>Count_Spec\<close>, over the \<open>_g\<close> definitions: the bit-length
  specification's upper bound is guarded by \<open>size_t\<close>-representability, so the kernel's
  per-coefficient decision is proved equal to @{const trusted_sgn_g} of the coefficient masked to
  \<open>0\<close> on distrust, and the loop invariant carries the mask. Only the unconditional lower bound is
  used.\<close>
lemma trusted_sgn_g_bitlen_test_masked:
  fixes x :: int
  assumes lb: "x \<noteq> 0 \<Longrightarrow> 2 ^ (bl - 1) \<le> \<bar>x\<bar>"
  shows "trusted_sgn_g g len i
           (if 0 < sgn x \<or> sgn x < 0 \<and> g + trunc_thresh len i < bl then x else 0)
       = (if 0 < sgn x \<or> sgn x < 0 \<and> g + trunc_thresh len i < bl then Some (sgn x) else None)"
proof (cases x "0::int" rule: linorder_cases)
  case less
  show ?thesis
  proof (cases "g + trunc_thresh len i < bl")
    case True
    have "g + trunc_thresh len i \<le> bl - 1" using True by simp
    then have "(2::int) ^ (g + trunc_thresh len i) \<le> 2 ^ (bl - 1)"
      by (simp add: power_increasing)
    also have "\<dots> \<le> \<bar>x\<bar>" using lb less by simp
    finally have "(2::int) ^ (g + trunc_thresh len i) \<le> \<bar>x\<bar>" .
    then have le: "x \<le> - (2 ^ (g + trunc_thresh len i))" using less by simp
    show ?thesis unfolding trusted_sgn_g_def using less True le by auto
  next
    case False
    have pos: "(0::int) < 2 ^ (g + trunc_thresh len i)" by simp
    show ?thesis unfolding trusted_sgn_g_def using less False pos by auto
  qed
next
  case equal
  then show ?thesis unfolding trusted_sgn_g_def by auto
next
  case greater
  then show ?thesis unfolding trusted_sgn_g_def by auto
qed

lemma tsign_fold_idx_mask_not_amb_g:
  assumes len_eq: "length zs = length ts"
    and mask: "\<forall>j<length zs. zs ! j = 0 \<or> zs ! j = ts ! j"
    and noamb: "\<not> (\<lambda>(a, b, c). c) (tsign_fold_idx_g g len i0 zs st)"
  shows "zs = ts"
  using assms
proof (induction zs ts arbitrary: i0 st rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons z zs' t ts')
  obtain ls cnt amb where stq: "st = (ls, cnt, amb)" by (cases st)
  have z_case: "z = 0 \<or> z = t"
    using Cons.prems(1) by (metis length_greater_0_conv list.discI nth_Cons_0)
  have pw': "\<forall>j<length zs'. zs' ! j = 0 \<or> zs' ! j = ts' ! j"
    using Cons.prems(1) by fastforce
  show ?case
  proof (cases "z = t")
    case True
    have tail: "\<not> (\<lambda>(a, b, c). c)
        (tsign_fold_idx_g g len (Suc i0) zs' (tsign_step (trusted_sgn_g g len i0 z) st))"
      using Cons.prems(2) by simp
    show ?thesis using Cons.IH[OF pw' tail] True by simp
  next
    case False
    then have z0: "z = 0" using z_case by simp
    have none: "trusted_sgn_g g len i0 z = None"
      unfolding z0 trusted_sgn_g_def
      using zero_less_power[of "2::int" "g + trunc_thresh len i0"] by simp
    have "tsign_step (trusted_sgn_g g len i0 z) st = (ls, cnt, True)"
      unfolding none stq by simp
    then have "(\<lambda>(a, b, c). c) (tsign_fold_idx_g g len i0 (z # zs') st)
        = (\<lambda>(a, b, c). c) (tsign_fold_idx_g g len (Suc i0) zs' (ls, cnt, True))"
      by simp
    also have "\<dots> = True"
      using tsign_fold_idx_amb_or_g[of g len "Suc i0" zs' ls cnt True] by simp
    finally show ?thesis using Cons.prems(2) by simp
  qed
qed

lemma tsign_mask_cnt_le_full_g:
  assumes fr: "gframe s g X Y"
    and lenws: "length ws = length Y"
    and mask: "\<forall>j<length ws. ws ! j = 0 \<or> ws ! j = taylor_shift_list 1 Y ! j"
  shows "(\<lambda>(a, b, c). b) (tsign_fold_idx_g g (length Y) 0 ws (0, 0, b0))
       \<le> sign_changes_fold (taylor_shift_list 1 X)"
proof -
  let ?len = "length Y"
  let ?xs = "taylor_shift_list 1 Y"
  let ?T = "taylor_shift_list 1 X"
  have lenT: "length ?T = ?len" using fr unfolding gframe_def by simp
  obtain ls1 cnt1 amb1 where st1: "tsign_fold_idx_g g ?len 0 ws (0, 0, b0) = (ls1, cnt1, amb1)"
    by (cases "tsign_fold_idx_g g ?len 0 ws (0, 0, b0)") auto
  have corr: "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx_g g ?len 0 ws (0, 0, b0))
      = fold sign_step (tsign_Z_g g ?len 0 ws) (0, 0)"
    using tsign_fold_idx_eq_sign_step_g[of 0 0 g ?len 0 ws b0] by simp
  have cnt1_eq: "cnt1 = sign_changes_fold (tsign_Z_g g ?len 0 ws)"
    using corr st1 unfolding sign_changes_fold_def by (metis snd_conv split_conv)
  have pw: "\<forall>j < length (tsign_Z_g g ?len 0 ws).
      tsign_Z_g g ?len 0 ws ! j = 0 \<or> tsign_Z_g g ?len 0 ws ! j = (map sgn ?T) ! j"
  proof (intro allI impI)
    fix j assume j: "j < length (tsign_Z_g g ?len 0 ws)"
    then have jws: "j < length ws" by simp
    then have jlen: "j < ?len" using lenws by simp
    show "tsign_Z_g g ?len 0 ws ! j = 0 \<or> tsign_Z_g g ?len 0 ws ! j = (map sgn ?T) ! j"
    proof (cases "trusted_sgn_g g ?len j (ws ! j)")
      case None
      then have "tsign_Z_g g ?len 0 ws ! j = 0"
        unfolding tsign_Z_g_def tsign_repr_g_def using jws by simp
      then show ?thesis by simp
    next
      case (Some sgv)
      then have z_eq: "tsign_Z_g g ?len 0 ws ! j = sgv"
        unfolding tsign_Z_g_def tsign_repr_g_def using jws by simp
      have wsj: "ws ! j = ?xs ! j"
      proof (rule ccontr)
        assume "ws ! j \<noteq> ?xs ! j"
        then have "ws ! j = 0" using mask jws by blast
        then show False using Some
          unfolding trusted_sgn_g_def
          using zero_less_power[of "2::int" "g + trunc_thresh ?len j"] by simp
      qed
      have "sgn (?T ! j) = sgv"
        using trusted_sgn_g_sound[OF fr jlen] Some wsj jlen by simp
      then show ?thesis using z_eq jlen lenT by simp
    qed
  qed
  have lens: "length (tsign_Z_g g ?len 0 ws) = length (map sgn ?T)"
    using lenws lenT by simp
  have mask_le: "changes (tsign_Z_g g ?len 0 ws) \<le> changes (map sgn ?T)"
    using changes_mask_le[OF lens] pw by simp
  have lhs_eq: "changes (tsign_Z_g g ?len 0 ws) = int cnt1"
    using changes_eq_sign_changes_fold[of "tsign_Z_g g ?len 0 ws"] cnt1_eq by simp
  have rhs_eq: "changes (map sgn ?T) = int (sign_changes_fold ?T)"
    using changes_map_sgn_eq[of ?T] changes_eq_sign_changes_fold[of ?T] by simp
  have "cnt1 \<le> sign_changes_fold ?T"
    using mask_le lhs_eq rhs_eq by simp
  then show ?thesis using st1 by simp
qed

lemma tsign_mask_cnt_le_prefix_g:
  assumes fr: "gframe s g X Y"
    and lenzs: "length zs \<le> length Y"
    and mask: "\<forall>j<length zs. zs ! j = 0 \<or> zs ! j = taylor_shift_list 1 Y ! j"
  shows "(\<lambda>(a, b, c). b) (tsign_fold_idx_g g (length Y) 0 zs (0, 0, b0))
       \<le> sign_changes_fold (taylor_shift_list 1 X)"
proof -
  let ?len = "length Y"
  let ?xs = "taylor_shift_list 1 Y"
  define ws where "ws = zs @ drop (length zs) ?xs"
  have lenxs: "length ?xs = ?len" by simp
  have lenws: "length ws = ?len" unfolding ws_def using lenzs lenxs by simp
  have maskws: "\<forall>j<length ws. ws ! j = 0 \<or> ws ! j = ?xs ! j"
  proof (intro allI impI)
    fix j assume j: "j < length ws"
    show "ws ! j = 0 \<or> ws ! j = ?xs ! j"
    proof (cases "j < length zs")
      case True
      then have "ws ! j = zs ! j" unfolding ws_def by (simp add: nth_append)
      then show ?thesis using mask True by simp
    next
      case False
      then have "ws ! j = drop (length zs) ?xs ! (j - length zs)"
        unfolding ws_def by (simp add: nth_append)
      also have "\<dots> = ?xs ! j" using False j lenws lenxs by simp
      finally show ?thesis by simp
    qed
  qed
  have split: "tsign_fold_idx_g g ?len 0 ws (0, 0, b0)
      = tsign_fold_idx_g g ?len (0 + length zs) (drop (length zs) ?xs)
          (tsign_fold_idx_g g ?len 0 zs (0, 0, b0))"
    unfolding ws_def by (rule tsign_fold_idx_append_g)
  have "(\<lambda>(a, b, c). b) (tsign_fold_idx_g g ?len 0 zs (0, 0, b0))
      \<le> (\<lambda>(a, b, c). b) (tsign_fold_idx_g g ?len 0 ws (0, 0, b0))"
    unfolding split by (rule tsign_fold_idx_cnt_mono_g)
  also have "\<dots> \<le> sign_changes_fold (taylor_shift_list 1 X)"
    using tsign_mask_cnt_le_full_g[OF fr lenws maskws] .
  finally show ?thesis .
qed

text \<open>The \<open>_g\<close> kernel loop's sign-accounting invariant (\<open>_g\<close> twin of
  @{const tmask_state}).\<close>
definition tmask_state_g :: "nat \<Rightarrow> int list \<Rightarrow> bool \<Rightarrow> int \<times> nat \<times> bool \<Rightarrow> nat \<Rightarrow> bool" where
  "tmask_state_g g Y amb0 st i \<equiv>
     (\<exists>zs. length zs = i
           \<and> (\<forall>j<i. zs ! j = 0 \<or> zs ! j = taylor_shift_list 1 Y ! j)
           \<and> st = tsign_fold_idx_g g (length Y) 0 zs (0, 0, amb0))"

lemma tmask_state_g_init: "tmask_state_g g Y amb0 (0, 0, amb0) 0"
  unfolding tmask_state_g_def by (rule exI[where x="[]"]) simp

lemma tmask_state_g_cnt_le:
  assumes st: "tmask_state_g g Y amb0 (ls, cnt, amb) i"
    and fr: "gframe s g X Y"
    and ile: "i \<le> length Y"
  shows "cnt \<le> sign_changes_fold (taylor_shift_list 1 X)"
proof -
  from st obtain zs where zs: "length zs = i"
    "\<forall>j<i. zs ! j = 0 \<or> zs ! j = taylor_shift_list 1 Y ! j"
    "(ls, cnt, amb) = tsign_fold_idx_g g (length Y) 0 zs (0, 0, amb0)"
    unfolding tmask_state_g_def by blast
  have bnd: "(\<lambda>(a, b, c). b) (tsign_fold_idx_g g (length Y) 0 zs (0, 0, amb0))
      \<le> sign_changes_fold (taylor_shift_list 1 X)"
    using tsign_mask_cnt_le_prefix_g[OF fr] zs(1,2) ile by simp
  have z3: "tsign_fold_idx_g g (length Y) 0 zs (0, 0, amb0) = (ls, cnt, amb)"
    using zs(3) by simp
  show ?thesis using bnd unfolding z3 by simp
qed

lemma tmask_state_g_not_amb:
  assumes st: "tmask_state_g g Y amb0 (ls, cnt, amb) i"
    and noamb: "\<not> amb"
    and ile: "i \<le> length Y"
  shows "(ls, cnt, amb) = tsign_fold_idx_g g (length Y) 0
           (take i (taylor_shift_list 1 Y)) (0, 0, amb0)"
proof -
  from st obtain zs where zs: "length zs = i"
    "\<forall>j<i. zs ! j = 0 \<or> zs ! j = taylor_shift_list 1 Y ! j"
    "(ls, cnt, amb) = tsign_fold_idx_g g (length Y) 0 zs (0, 0, amb0)"
    unfolding tmask_state_g_def by blast
  let ?T = "taylor_shift_list 1 Y"
  have lenT: "length ?T = length Y" by simp
  have len_eq: "length zs = length (take i ?T)" using zs(1) ile lenT by simp
  have mask: "\<forall>j<length zs. zs ! j = 0 \<or> zs ! j = take i ?T ! j"
    using zs(1,2) ile lenT by simp
  have z3: "tsign_fold_idx_g g (length Y) 0 zs (0, 0, amb0) = (ls, cnt, amb)"
    using zs(3) by simp
  have "\<not> (\<lambda>(a, b, c). c) (tsign_fold_idx_g g (length Y) 0 zs (0, 0, amb0))"
    unfolding z3 using noamb by simp
  from tsign_fold_idx_mask_not_amb_g[OF len_eq mask this] have "zs = take i ?T" .
  then show ?thesis using zs(3) by simp
qed

text \<open>At the leading position \<open>trunc_thresh\<close> is 0, so the trust test degenerates to a
  bare comparison against \<open>2^g\<close> — the \<open>_g\<close> twin of @{thm [source] trusted_sgn_last}
  (which degenerates further to plain nonzero-ness at \<open>g = 0\<close>). This is exactly the
  impl kernel's \<open>lead_trust_mop\<close> test.\<close>
lemma trusted_sgn_g_last:
  fixes x :: int
  shows "trusted_sgn_g g len (len - 1) x
       = (if 0 < x then Some 1 else if x \<le> - (2 ^ g) then Some (-1) else None)"
proof -
  have "trunc_thresh len (len - 1) = 0"
    unfolding trunc_thresh_def by (cases len) auto
  then show ?thesis
    unfolding trusted_sgn_g_def by auto
qed

section \<open>The midpoint-evaluation guard\<close>

text \<open>The homogeneous evaluation at \<open>(1, 2)\<close> — the abstract form of the midpoint
  test \<open>poly_hom_eval_zero_nd_monadic 1 2\<close> (\<open>Interval_Eval.thy\<close>), related to it through
  that op's \<open>_correct\<close> lemma, as with \<open>dilate_list\<close>.\<close>
definition trunc_eval2_spec :: "int list \<Rightarrow> int" where
  "trunc_eval2_spec Y = (\<Sum>i < length Y. Y ! i * 2 ^ (length Y - Suc i))"

text \<open>Sign transfer for the midpoint test: positive carried evaluation is free
  (one-sided error sum \<open>\<ge> 0\<close>); negative is trusted past \<open>g + (len-1) +
  bitlen(len)\<close> bits (error sum \<open>< len * 2^(s+g+len-1) < 2^(s+g+len-1+bitlen len)\<close>
  via @{thm [source] nat_bitlen_lt}). Ambiguity admits a zero \<Longrightarrow> the impl
  ESCALATES (exact rebuild from the root), so a true midpoint root is always
  detected exactly. Route: \<open>sum_mono\<close> pointwise over the frame; strictness from
  the strict pointwise bound.\<close>
text \<open>\<open>trunc_eval2_spec\<close> IS the dilation sum: position \<open>i\<close> of its summand is exactly
  \<open>dilate_list\<close>'s \<open>i\<close>-th entry, so the whole bound reduces to @{thm [source]
  gframe_dilate}'s per-position frame summed over the index range — no fresh error
  decomposition needed.\<close>
lemma hom_eval2_spec_eq_dilate_sum:
  "trunc_eval2_spec Z = (\<Sum>i < length Z. dilate_list Z ! i)"
  unfolding trunc_eval2_spec_def
  by (rule sum.cong) (auto simp: dilate_list_nth)

lemma gframe_hom_eval2_sound:
  assumes "gframe s g X Y"
    and "0 < trunc_eval2_spec Y \<or>
         trunc_eval2_spec Y \<le> - (2 ^ (g + (length Y - Suc 0) + nat_bitlen (length Y)))"
  shows "sgn (trunc_eval2_spec X) = sgn (trunc_eval2_spec Y)" and "trunc_eval2_spec X \<noteq> 0"
proof -
  let ?len = "length Y"
  have lenXY: "length X = ?len" using assms(1) unfolding gframe_def by simp
  have hY: "trunc_eval2_spec Y = (\<Sum>i < ?len. dilate_list Y ! i)"
    using hom_eval2_spec_eq_dilate_sum[of Y] by simp
  have hX: "trunc_eval2_spec X = (\<Sum>i < ?len. dilate_list X ! i)"
    using hom_eval2_spec_eq_dilate_sum[of X] lenXY by simp
  have DXDY: "gframe s (g + (?len - Suc 0)) (dilate_list X) (dilate_list Y)"
    using gframe_dilate[OF assms(1)] .
  have DXi_lb: "\<And>i. i < ?len \<Longrightarrow> 0 \<le> dilate_list X ! i - 2 ^ s * dilate_list Y ! i"
    and DXi_ub: "\<And>i. i < ?len \<Longrightarrow>
        dilate_list X ! i - 2 ^ s * dilate_list Y ! i < 2 ^ (s + (g + (?len - Suc 0)))"
    using DXDY unfolding gframe_def by (auto simp: length_dilate_list)
  have main_eq: "trunc_eval2_spec X - 2 ^ s * trunc_eval2_spec Y
      = (\<Sum>i < ?len. dilate_list X ! i - 2 ^ s * dilate_list Y ! i)"
    using hX hY by (simp add: sum_subtractf sum_distrib_left)
  have main_lb: "0 \<le> trunc_eval2_spec X - 2 ^ s * trunc_eval2_spec Y"
    unfolding main_eq
  proof (rule sum_nonneg)
    fix x assume "x \<in> {..< ?len}"
    then show "0 \<le> dilate_list X ! x - 2 ^ s * dilate_list Y ! x"
      using DXi_lb by simp
  qed
  have len_pos: "?len \<noteq> 0"
  proof
    assume "?len = 0"
    then have "trunc_eval2_spec Y = 0" unfolding trunc_eval2_spec_def by simp
    with assms(2) show False by simp
  qed
  obtain len' where len_eq: "?len = Suc len'"
    using len_pos by (cases ?len) auto
  have main_ub: "trunc_eval2_spec X - 2 ^ s * trunc_eval2_spec Y
      < 2 ^ (s + (g + (?len - Suc 0) + nat_bitlen ?len))"
  proof -
    have exp_eq: "s + (g + (?len - Suc 0)) = s + g + len'"
      using len_eq by simp
    have "(\<Sum>i < ?len. dilate_list X ! i - 2 ^ s * dilate_list Y ! i)
        < (\<Sum>i < ?len. 2 ^ (s + g + len'))"
    proof (rule sum_strict_mono)
      show "finite {..< ?len}" by simp
      have "0 \<in> {..< ?len}" using len_eq by simp
      then show "{..< ?len} \<noteq> {}" by blast
      fix x assume "x \<in> {..< ?len}"
      then show "dilate_list X ! x - 2 ^ s * dilate_list Y ! x < 2 ^ (s + g + len')"
        using DXi_ub exp_eq by simp
    qed
    also have "\<dots> = int (?len * 2 ^ (s + g + len'))"
      by simp
    also have "\<dots> < 2 ^ nat_bitlen ?len * 2 ^ (s + g + len')"
    proof -
      have castlt: "(int ?len :: int) < 2 ^ nat_bitlen ?len"
        using nat_bitlen_lt[of ?len] by simp
      have "int (?len * 2 ^ (s + g + len')) = int ?len * 2 ^ (s + g + len')"
        by simp
      also have "\<dots> < 2 ^ nat_bitlen ?len * 2 ^ (s + g + len')"
        using castlt by (intro mult_strict_right_mono) auto
      finally show ?thesis .
    qed
    also have "(2::int) ^ nat_bitlen ?len * 2 ^ (s + g + len') = 2 ^ (s + g + len' + nat_bitlen ?len)"
      by (simp add: power_add algebra_simps)
    also have "s + g + len' + nat_bitlen ?len = s + (g + (?len - Suc 0) + nat_bitlen ?len)"
      using exp_eq by simp
    finally show ?thesis using main_eq by simp
  qed
  from assms(2) have main: "sgn (trunc_eval2_spec X) = sgn (trunc_eval2_spec Y)"
  proof
    assume Ypos: "0 < trunc_eval2_spec Y"
    have "0 < 2 ^ s * trunc_eval2_spec Y" using Ypos by simp
    then have "0 < trunc_eval2_spec X" using main_lb by linarith
    then show ?thesis using Ypos by simp
  next
    assume Yneg: "trunc_eval2_spec Y \<le> - (2 ^ (g + (?len - Suc 0) + nat_bitlen ?len))"
    have h1: "2 ^ s * trunc_eval2_spec Y
        \<le> 2 ^ s * (- (2 ^ (g + (?len - Suc 0) + nat_bitlen ?len)))"
      by (intro mult_left_mono Yneg) simp
    have h1': "(2::int) ^ s * (- (2 ^ (g + (?len - Suc 0) + nat_bitlen ?len)))
        = - (2 ^ (s + (g + (?len - Suc 0) + nat_bitlen ?len)))"
      by (simp add: power_add)
    have "trunc_eval2_spec X
        < 2 ^ s * trunc_eval2_spec Y + 2 ^ (s + (g + (?len - Suc 0) + nat_bitlen ?len))"
      using main_ub by simp
    also have "\<dots> \<le> - (2 ^ (s + (g + (?len - Suc 0) + nat_bitlen ?len)))
        + 2 ^ (s + (g + (?len - Suc 0) + nat_bitlen ?len))"
      using h1 h1' by simp
    also have "\<dots> = 0" by simp
    finally have Xneg: "trunc_eval2_spec X < 0" .
    have "(0::int) < 2 ^ (g + (?len - Suc 0) + nat_bitlen ?len)" by simp
    then have "trunc_eval2_spec Y < 0" using Yneg by linarith
    then show ?thesis using Xneg by simp
  qed
  have Yne0: "trunc_eval2_spec Y \<noteq> 0"
    using assms(2) by auto
  show "sgn (trunc_eval2_spec X) = sgn (trunc_eval2_spec Y)" using main .
  show "trunc_eval2_spec X \<noteq> 0" using main Yne0 by (auto simp: sgn_eq_0_iff)
qed

section \<open>The stored-node invariant — the \<open>g = 0\<close> sentinel\<close>

text \<open>The impl node stores ONE nat \<open>g\<close> with sentinel semantics: \<open>g = 0\<close> \<longleftrightarrow> the
  carried poly IS the exact node poly (never truncated, or just escalated). This is
  LOAD-BEARING for the dispatch: only at \<open>g = 0\<close> may the node call the plain truncated
  count (whose classify speaks about its own argument) — a freshly-truncated poly has
  zero SLACK (\<open>gframe_trunc_exact\<close>) but is NOT the exact poly, so every truncation
  event stores \<open>g := 1\<close> (sound via \<open>gframe_mono\<close>), never 0. Escalation alone
  restores \<open>g = 0\<close>.\<close>
definition node_frame :: "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> bool" where
  "node_frame X Y g \<longleftrightarrow> (if g = 0 then X = Y else (\<exists>s. gframe s g X Y))"

lemma node_frame_exact: "node_frame X X 0"
  by (simp add: node_frame_def)

lemma node_frameE:
  assumes "node_frame X Y g"
  obtains s where "gframe s g X Y"
proof (cases "g = 0")
  case True
  then have "X = Y" using assms unfolding node_frame_def by simp
  then have "gframe 0 g X Y" using True gframe_exact by simp
  then show ?thesis using that by blast
next
  case False
  then obtain s where "gframe s g X Y" using assms unfolding node_frame_def by auto
  then show ?thesis using that by blast
qed

text \<open>The pure per-child \<open>g\<close> bookkeeping the push sites compute (exactness is
  preserved through the maps, so \<open>g = 0\<close> stays 0 — the zero-overhead floor).\<close>
definition child_g_left :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "child_g_left len g = (if g = 0 then 0 else g + (len - 1))"

definition child_g_right :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "child_g_right len g = (if g = 0 then 0 else g + (2 * len - 1))"

lemma node_frame_child_left:
  assumes "node_frame X Y g"
  shows "node_frame (dilate_list X) (dilate_list Y) (child_g_left (length Y) g)"
proof (cases "g = 0")
  case True
  then have "X = Y" using assms unfolding node_frame_def by simp
  then show ?thesis using True unfolding child_g_left_def node_frame_def by simp
next
  case False
  then obtain s where s: "gframe s g X Y" using assms unfolding node_frame_def by auto
  have "gframe s (g + (length Y - Suc 0)) (dilate_list X) (dilate_list Y)"
    using gframe_dilate[OF s] .
  then show ?thesis using False unfolding child_g_left_def node_frame_def by auto
qed

lemma node_frame_child_right:
  assumes "node_frame X Y g"
  shows "node_frame (taylor_shift_list 1 (dilate_list X))
                    (taylor_shift_list 1 (dilate_list Y))
                    (child_g_right (length Y) g)"
proof (cases "g = 0")
  case True
  then have "X = Y" using assms unfolding node_frame_def by simp
  then show ?thesis using True unfolding child_g_right_def node_frame_def by simp
next
  case False
  then obtain s where s: "gframe s g X Y" using assms unfolding node_frame_def by auto
  have "gframe s (g + (2 * length Y - Suc 0))
      (taylor_shift_list 1 (dilate_list X)) (taylor_shift_list 1 (dilate_list Y))"
    using gframe_bisect_right[OF s] .
  then show ?thesis using False unfolding child_g_right_def node_frame_def by auto
qed

section \<open>Escalation (exact rebuild) — pointers, no new spec content\<close>

text \<open>Escalation rebuilds the exact node poly from the BORROWED ROOT over the node's
  own dyadic box via \<open>carried_init_inplace_monadic\<close> (\<open>Carried_Kernel.thy\<close>),
  which is sign-equivalent to the exact carried node up to a POSITIVE scalar — the
  \<open>carried_repr_scalar\<close> window-algebra spine proven for the Newton keystone
  (\<open>Newton_Spec.thy\<close>). Re-establishes \<open>gframe 0 0\<close> (up to that scalar,
  which no sign/count consumer observes). No new abstract lemma is needed here;
  the equality obligation lives in the loop coupling.\<close>

end
