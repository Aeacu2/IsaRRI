theory Power_Sub_Entry_Sound
  imports Power_Sub_Sound
    "IsaRRI_Refine.Kiou_Bound_Defl_Reflect"
    "IsaRRI_LLVM.Power_Sub_Entry_Impl"
begin

text \<open>\<^bold>\<open>The power-substitution entry theorems.\<close> Nothing here is synthesised.

  \<^bold>\<open>The claim.\<close> A substitution returns different intervals from \<open>dsc_int\<close>, so the output is
  specified by its properties rather than by a reference algorithm: isolation, @{const dsc_pair_ok} on every
  emitted window on both sides of the origin, plus completeness.

  \<^bold>\<open>The chain\<close> is detect, clamp, extract, solve the reduced polynomial, back-map, and each link has its own
  theorem:

    \<^item> detection: @{thm [source] pow_sub_h_monadic_correct} \<open>\<rightarrow> RETURN (pow_sub_h xs)\<close>
    \<^item> the exponent: @{const pow_sub_entry_exp_mop} \<open>= gcd\<close>, via @{thm [source] snat_gcd_monadic_correct}
    \<^item> extraction: @{thm [source] pow_sub_extract_monadic_correct} \<open>\<rightarrow> RETURN (pow_sub_extract d xs)\<close>
    \<^item> the algebra: @{thm [source] pow_sub_compose} and @{thm [source] of_int_poly_pcompose_monom}
    \<^item> the reduced solve: its capstone
    \<^item> the back-map: @{thm [source] pow_sub_backmap_all_pair_ok_mirror}

  \<^bold>\<open>The hypothesis on the reduced polynomial.\<close> The reduced solve's correctness theorem requires its
  precondition of the reduced list. Most of it transports from the input and is discharged below
  (\<open>pow_sub_reduced_len2\<close>, \<open>pow_sub_reduced_last_nz\<close>, and squarefreeness by
  @{thm [source] pow_sub_extract_squarefree}). Its depth-quantified \<open>\<delta>\<close> bounds do not transport in general (see
  the last section), so the precondition on the reduced list remains an explicit hypothesis, not checked at run
  time.

  \<^bold>\<open>What the reduced solve's output could violate is checked at run time.\<close> \<open>0 \<le> A\<close>, \<open>0 \<le> B\<close> and the four word
  bounds on the precision column are decided by the room guard and reach this theorem through
  @{const pow_sub_iv_pre}; on failure the entry returns \<open>ok = False\<close> and the wrapper falls back to the ordinary
  solve. So the conclusion is guarded by \<open>ok\<close> and needs no hypothesis about \<open>k\<close>.\<close>

section \<open>The mechanical half of the precondition transport\<close>

text \<open>\<open>2 \<le> length q\<close> and \<open>last q \<noteq> 0\<close>, the two conjuncts of @{const dsc_isolate_all_split_pre} that are pure list
  arithmetic. Both are stated over the exponent \<open>d\<close> actually used, not the detected \<open>h\<close>.\<close>

lemma pow_sub_reduced_last_nz:
  fixes xs :: "int list"
  assumes d: "0 < d" and ne: "xs \<noteq> []" and nz: "last xs \<noteq> 0"
    and supp: "\<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> d dvd i"
  shows "last (pow_sub_extract d xs) \<noteq> 0"
proof -
  let ?n = "length xs"
  have n0: "0 < ?n" using ne by simp
  have lastnth: "xs ! (?n - 1) \<noteq> 0" using nz ne by (simp add: last_conv_nth)
  \<comment> \<open>the TOP index is a multiple of \<open>d\<close> — that is what makes the last extracted slot land on it\<close>
  have dvd: "d dvd (?n - 1)" using supp n0 lastnth by simp
  then have hit: "(?n - 1) div d * d = ?n - 1" by (rule dvd_div_mult_self)
  \<comment> \<open>\<open>last_conv_nth\<close> is applied to the LENGTH TERM and the arithmetic done afterwards; giving
     it to \<open>simp\<close> as a rule leaves \<open>last q = q ! ((n - 1) div d)\<close> unproved, because \<open>simp\<close> has to
     both know \<open>q \<noteq> []\<close> and collapse \<open>Suc ((n-1) div d) - 1\<close> in one step.\<close>
  have qne: "pow_sub_extract d xs \<noteq> []" by (simp add: pow_sub_extract_def)
  have "last (pow_sub_extract d xs)
          = pow_sub_extract d xs ! (length (pow_sub_extract d xs) - 1)"
    using qne by (rule last_conv_nth)
  also have "\<dots> = pow_sub_extract d xs ! ((?n - 1) div d)" by simp
  also have "\<dots> = xs ! ((?n - 1) div d * d)" by (rule nth_pow_sub_extract) simp
  also have "\<dots> = xs ! (?n - 1)" using hit by simp
  finally show ?thesis using lastnth by simp
qed

text \<open>\<open>2 \<le> length q\<close> needs the ORIGINAL degree to be at least \<open>d\<close>, which \<open>2 \<le> d\<close> plus a nonzero
  top coefficient supplies: the top index is a nonzero multiple of \<open>d\<close>, so it is \<open>\<ge> d\<close> unless it
  is \<open>0\<close> — and a polynomial whose only nonzero coefficient is the constant is not squarefree-plus-
  two-roots material the entry ever substitutes on.\<close>

lemma pow_sub_reduced_len2:
  fixes xs :: "int list"
  assumes d: "0 < d" and dn: "d \<le> length xs - 1"
  shows "2 \<le> length (pow_sub_extract d xs)"
proof -
  \<comment> \<open>through \<open>div_le_mono\<close> off \<open>d div d\<close>. There is no \<open>le_div_iff_mult_le\<close> in this graph, and
     naming a nonexistent fact aborts the whole theory rather than failing one step.\<close>
  have "d div d \<le> (length xs - 1) div d" using dn by (rule div_le_mono)
  then have "1 \<le> (length xs - 1) div d" using d by simp
  thus ?thesis by simp
qed

section \<open>The reduced polynomial's algebra, in the form the back-map wants\<close>

text \<open>The back-map lemmas are stated over \<open>real poly\<close> with \<open>P = Q \<circ>\<^sub>p monom 1 d\<close>, \<open>Q = map_poly real_of_int Q0\<close> and
  \<open>q = coeffs Q0\<close>. Assembling that from @{thm [source] pow_sub_compose} needs \<open>coeffs (Poly q) = q\<close>, which holds only
  for a normalised \<open>q\<close>; @{thm [source] pow_sub_reduced_last_nz} provides that. It is closed with
  @{thm [source] coeffs_Poly_self} (in \<open>Kiou_Bound_Spec\<close>), not \<open>coeffs_Poly\<close>: the latter is a default simp rule
  rewriting \<open>coeffs (Poly q)\<close> to \<open>strip_while ((=) 0) q\<close>, which pre-empts the fact.\<close>

lemma pow_sub_reduced_algebra:
  fixes xs :: "int list"
  assumes d: "0 < d" and ne: "xs \<noteq> []" and nz: "last xs \<noteq> 0"
    and supp: "\<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> d dvd i"
  defines "q \<equiv> pow_sub_extract d xs"
  shows "(real_of_int_poly (Poly xs) :: real poly)
           = real_of_int_poly (Poly q) \<circ>\<^sub>p monom 1 d"
    and "coeffs (Poly q) = q"
proof -
  show "(real_of_int_poly (Poly xs) :: real poly)
          = real_of_int_poly (Poly q) \<circ>\<^sub>p monom 1 d"
    unfolding q_def
    by (simp add: pow_sub_compose[OF d ne supp] of_int_poly_pcompose_monom)
  have lnz: "last q \<noteq> 0" unfolding q_def by (rule pow_sub_reduced_last_nz[OF d ne nz supp])
  \<comment> \<open>via the LENGTH, not \<open>pow_sub_extract_def\<close>: unfolding the definition leaves
     \<open>map \<dots> [0..<Suc \<dots>] \<noteq> []\<close>, which \<open>simp\<close> does not take, whereas
     @{thm [source] length_pow_sub_extract} is a simp rule and makes it \<open>Suc \<dots> \<noteq> 0\<close>.\<close>
  have "0 < length q" unfolding q_def by simp
  then have qne: "q \<noteq> []" by auto
  show "coeffs (Poly q) = q" by (rule coeffs_Poly_self[OF qne lnz])
qed

section \<open>What the reduced solve must deliver\<close>

text \<open>\<^bold>\<open>The existential form does not suffice.\<close> The soundness clause of
  @{thm [source] hybrid_isolate_all_split_main_correct} for the positive vector is

    \<open>\<forall>I \<in> set (dyadic_interval_vec_to_list accP). \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok Q J\<close>

  and @{const real_to_rat_pair} is \<open>(\<lambda>(x, y). (THE r. of_rat r = x, THE r. of_rat r = y))\<close>. On an irrational \<open>x\<close> no
  \<open>r\<close> satisfies \<open>of_rat r = x\<close>, so the \<open>THE\<close> is an unspecified fixed value that may coincide with the rational the
  goal names. So \<open>I = real_to_rat_pair J\<close> does not tie \<open>J\<close> to \<open>(of_rat (fst I), of_rat (snd I))\<close>, and
  \<open>dsc_pair_ok Q J\<close> does not transfer to the emitted interval. The back-map needs isolation on the dyadic numerators
  \<open>(A / 2\<^sup>k, B / 2\<^sup>k)\<close>, a stronger statement. (The multiset equality against @{const dsc_int} does not depend on this
  clause.)\<close>

definition pow_sub_reduced_isolates ::
  "real poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "pow_sub_reduced_isolates Q accQ \<longleftrightarrow>
     (\<forall>j < length (dyadic_interval_vec_triples accQ).
        case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
          dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"

subsection \<open>The pinned form is derivable\<close>

text \<open>The proof of the capstone already derives the pinned form: in \<open>dsc_carried_polr_pos_half_sound\<close>, \<open>I_real\<close>
  establishes \<open>(of_rat (fst I), of_rat (snd I)) = ?J'\<close> (via @{thm [source] newdsc_pol_bail_elems_of_rat_image}: every
  element of the real recursion's output over \<open>of_rat\<close> bounds has \<open>of_rat\<close> endpoints) and \<open>okP\<close> establishes
  \<open>dsc_pair_ok P_real ?J'\<close>. The strengthened chain is \<open>dsc_carried_polr_pos_half_sound_strong\<close> \<open>\<rightarrow>\<close>
  \<open>dsc_carried_hybrid_pos_half_sound_strong\<close> \<open>\<rightarrow>\<close> \<open>hybrid_split_pos_solve_half_strong\<close> \<open>\<rightarrow>\<close>
  @{thm [source] hybrid_isolate_all_split_main_correct_pos_pinned}, with the existential statements as corollaries.
  Only the positive half is needed: the entry frees the reduced solve's negative vector unused.\<close>

lemma pow_sub_dyadic_rat_of_rat:
  fixes A :: int
  shows "(of_rat (dyadic_rat A k) :: real) = real_of_int A / 2 ^ k"
  \<comment> \<open>\<open>of_rat_power\<close> is load-bearing: without it \<open>of_rat_divide\<close> splits the quotient but leaves
     the DENOMINATOR as \<open>real_of_rat (2 ^ k)\<close>, and the goal degenerates to the residue
     \<open>A = 0 \<or> real_of_rat (2 ^ k) = 2 ^ k\<close>\<close>
  unfolding dyadic_rat_def by (simp add: of_rat_divide of_rat_power)

text \<open>The bridge from \<open>to_list\<close> to \<open>triples\<close>: \<open>to_list = map dyadic_interval_of_triple \<circ> triples\<close>, and
  \<open>dyadic_interval_of_triple ((A,B),k) = (dyadic_rat A k, dyadic_rat B k)\<close>.\<close>

lemma pow_sub_reduced_isolates_from_pinned:
  assumes iso: "\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
        dsc_pair_ok Q (of_rat (fst I), of_rat (snd I))"
  shows "pow_sub_reduced_isolates Q accP"
  unfolding pow_sub_reduced_isolates_def
proof (intro allI impI)
  fix j assume j: "j < length (dyadic_interval_vec_triples accP)"
  obtain A B k where t: "dyadic_interval_vec_triples accP ! j = ((A, B), k)"
    by (metis surj_pair)
  have mem: "dyadic_interval_vec_to_list accP ! j
               \<in> set (dyadic_interval_vec_to_list accP)"
    using j unfolding dyadic_interval_vec_to_list_def by simp
  have eq: "dyadic_interval_vec_to_list accP ! j = (dyadic_rat A k, dyadic_rat B k)"
    unfolding dyadic_interval_vec_to_list_def
    using j t by (simp add: dyadic_interval_of_triple_def)
  have "dsc_pair_ok Q (of_rat (dyadic_rat A k), of_rat (dyadic_rat B k))"
    using iso mem eq by (metis fst_conv snd_conv)
  then show "case dyadic_interval_vec_triples accP ! j of ((A, B), k) \<Rightarrow>
               dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    unfolding t by (simp add: pow_sub_dyadic_rat_of_rat)
qed

text \<open>\<^bold>\<open>The first conjunct of \<open>qsolve\<close>.\<close> The reduced solve's isolation, in dyadic-numerator form, follows from the
  reduced polynomial's precondition alone.\<close>

theorem pow_sub_reduced_isolates_of_pre:
  fixes q :: "int list"
  assumes qpre: "dsc_isolate_all_split_hybrid_pre q"
  shows "hybrid_isolate_all_split_main q \<le> SPEC (\<lambda>(accP, accN, xs0).
      pow_sub_reduced_isolates (real_of_int_poly (Poly q)) accP)"
  by (rule weaken_SPEC[OF hybrid_isolate_all_split_main_correct_pos_pinned[OF qpre]])
     (auto intro: pow_sub_reduced_isolates_from_pinned)

text \<open>\<^bold>\<open>The second conjunct of \<open>qsolve\<close>\<close>: vector well-formedness. \<open>hybrid_expol_int_refine\<close> supplies
  \<open>dyadic_interval_vec_invar acc\<close> in \<open>hybrid_split_pos_solve_half_strong\<close>'s \<open>solver\<close> fact, and the capstone carries
  it, since the refinement is not visible outside that proof. The fourth conjunct,
  \<open>length (dyadic_interval_vec_triples accP) + 1 < max_snat\<close>, is treated below.\<close>

theorem pow_sub_reduced_invar_of_pre:
  fixes q :: "int list"
  assumes qpre: "dsc_isolate_all_split_hybrid_pre q"
  shows "hybrid_isolate_all_split_main q \<le> SPEC (\<lambda>(accP, accN, xs0).
      dyadic_interval_vec_invar accP)"
  by (rule weaken_SPEC[OF hybrid_isolate_all_split_main_correct_pos_pinned[OF qpre]]) auto

subsection \<open>Completeness of the reduced solve's contribution\<close>

text \<open>\<^bold>\<open>The covering half of what the reduced solve provides\<close>, read off the pinned completeness clause in
  dyadic-numerator form, as @{thm [source] pow_sub_reduced_isolates_from_pinned} does for isolation.

  \<^bold>\<open>Closed bounds, and only for positive roots.\<close> Closed because that is what the pipeline's completeness gives
  (a root may lie on an endpoint); positive only because \<open>accP\<close> is the positive half. For an even exponent that
  loses nothing: a negative \<open>Q\<close>-root has no real \<open>h\<close>-th root, so it lifts to no \<open>P\<close>-root
  (@{thm [source] pow_sub_lift_neg_eq}), which is why the entry may free the negative vector.\<close>

text \<open>\<^bold>\<open>Stated over explicit components with the read-out equation as a conjunct\<close>, not as a
  \<open>case \<dots> of\<close> over \<open>triples accQ ! j\<close>: a bounded existential whose body is a \<open>case\<close> gives \<open>blast\<close> nothing to unify
  against until it has invented the tuple.\<close>

definition pow_sub_reduced_covers ::
    "real poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "pow_sub_reduced_covers Q accQ = (\<forall>y::real. 0 < y \<longrightarrow> poly Q y = 0 \<longrightarrow>
      (\<exists>j A B k. j < length (dyadic_interval_vec_triples accQ)
         \<and> dyadic_interval_vec_triples accQ ! j = ((A, B), k)
         \<and> ((real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
            \<or> (real_of_int A / 2 ^ k = y \<and> real_of_int B / 2 ^ k = y))))"

lemma pow_sub_reduced_covers_from_pinned:
  assumes cov: "\<forall>x::real. 0 < x \<longrightarrow> poly Q x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
           (of_rat (fst I) < x \<and> x < of_rat (snd I))
           \<or> (of_rat (fst I) = x \<and> of_rat (snd I) = x))"
  shows "pow_sub_reduced_covers Q accP"
  unfolding pow_sub_reduced_covers_def
proof (intro allI impI)
  fix y :: real assume y0: "0 < y" and ry: "poly Q y = 0"
  from cov y0 ry obtain I where Iin: "I \<in> set (dyadic_interval_vec_to_list accP)"
    and c: "(of_rat (fst I) < y \<and> y < of_rat (snd I))
            \<or> (of_rat (fst I) = y \<and> of_rat (snd I) = y)" by blast
  \<comment> \<open>membership \<open>\<rightarrow>\<close> INDEX, the opposite direction to the isolation bridge\<close>
  from Iin obtain j where jn: "j < length (dyadic_interval_vec_to_list accP)"
    and Ij: "dyadic_interval_vec_to_list accP ! j = I" by (metis in_set_conv_nth)
  have jlen: "j < length (dyadic_interval_vec_triples accP)"
    using jn unfolding dyadic_interval_vec_to_list_def by simp
  obtain A B k where t: "dyadic_interval_vec_triples accP ! j = ((A, B), k)"
    by (metis surj_pair)
  have "dyadic_interval_vec_to_list accP ! j = (dyadic_rat A k, dyadic_rat B k)"
    unfolding dyadic_interval_vec_to_list_def
    using jlen t by (simp add: dyadic_interval_of_triple_def)
  then have eqA: "of_rat (fst I) = real_of_int A / 2 ^ k"
    and eqB: "of_rat (snd I) = real_of_int B / 2 ^ k"
    using Ij by (simp_all add: pow_sub_dyadic_rat_of_rat)
  show "\<exists>j A B k. j < length (dyadic_interval_vec_triples accP)
       \<and> dyadic_interval_vec_triples accP ! j = ((A, B), k)
       \<and> ((real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
          \<or> (real_of_int A / 2 ^ k = y \<and> real_of_int B / 2 ^ k = y))"
  proof (intro exI conjI)
    show "j < length (dyadic_interval_vec_triples accP)" by (rule jlen)
    show "dyadic_interval_vec_triples accP ! j = ((A, B), k)" by (rule t)
    show "(real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
          \<or> (real_of_int A / 2 ^ k = y \<and> real_of_int B / 2 ^ k = y)"
      using c eqA eqB by simp
  qed
qed

text \<open>\<^bold>\<open>No runtime guard is needed for a root on a reduced interval's endpoint.\<close> \<open>newdsc_pol_bail\<close> emits
  \<open>mid_root = (if poly P m = 0 then [(m,m)] else [])\<close>, a degenerate interval at every exactly representable root,
  so a \<open>Q\<close>-root never lies on the endpoint of a proper emitted interval. The closed covering
  \<open>fst I \<le> x \<and> x \<le> snd I\<close> does not express this (a root between two adjacent intervals satisfies it for both);
  the strict-or-degenerate form \<open>newdsc_pol_bail_complete_strong\<close> does, and carried through
  @{const pow_sub_reduced_covers} it makes the branch condition in \<open>pow_sub_backmap_cover_of_post\<close> derivable: at
  \<open>A = B\<close> the strict disjunct is vacuous, so the degenerate one pins the root, and at \<open>A \<noteq> B\<close> the degenerate
  disjunct would force \<open>A = B\<close>.\<close>

theorem pow_sub_reduced_covers_of_pre:
  fixes q :: "int list"
  assumes qpre: "dsc_isolate_all_split_hybrid_pre q"
  shows "hybrid_isolate_all_split_main q \<le> SPEC (\<lambda>(accP, accN, xs0).
      pow_sub_reduced_covers (real_of_int_poly (Poly q)) accP)"
  by (rule weaken_SPEC[OF hybrid_isolate_all_split_main_correct_pos_pinned[OF qpre]])
     (auto intro: pow_sub_reduced_covers_from_pinned)

subsection \<open>The bound on the number of emitted intervals\<close>

text \<open>\<^bold>\<open>The fourth conjunct of \<open>qsolve\<close>.\<close> \<open>pow_sub_backmap_all_pair_ok_mirror\<close> needs
  \<open>length (triples accP) + 1 < max_snat\<close> for its push capacity.

  \<^bold>\<open>Where it comes from.\<close> The hybrid keystone's @{const hybrid_budget_invar} (the accumulator budget) carries
  \<open>int (length al) + acc_budget + 1 < max_snat\<close>, and it is an unguarded conjunct of @{const hybrid_state_invar}, so
  it still holds at the loop's exit, where the worklist is empty. Dropping the budget by
  \<open>hybrid_acc_budget_nonneg\<close> gives the bound; \<open>mucap\<close>, a clause of \<open>dsc_isolate_all_split_pre\<close>, pays for it. No
  leaf-count argument about @{const newdsc_pol_bail} is needed, and no runtime check. Bounding the count by the
  root count instead would need disjointness of the intervals, which is not claimed.\<close>

theorem pow_sub_reduced_count_of_pre:
  fixes q :: "int list"
  assumes qpre: "dsc_isolate_all_split_hybrid_pre q"
  shows "hybrid_isolate_all_split_main q \<le> SPEC (\<lambda>(accP, accN, xs0).
      length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len))"
  by (rule weaken_SPEC[OF hybrid_isolate_all_split_main_correct_pos_pinned[OF qpre]]) auto

text \<open>\<^bold>\<open>All four conjuncts at once\<close>, the shape \<open>qsolve\<close> is stated in. It is one \<open>\<le> SPEC\<close> rather than four: only one
  such fact fires per producer call, so separately proved conjuncts would not all reach the continuation.\<close>

theorem pow_sub_reduced_qsolve_of_pre:
  fixes q :: "int list"
  assumes qpre: "dsc_isolate_all_split_hybrid_pre q"
  shows "hybrid_isolate_all_split_main q \<le> SPEC (\<lambda>(accP, accN, xs0).
      dyadic_interval_vec_invar accP
      \<and> length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> pow_sub_reduced_isolates (real_of_int_poly (Poly q)) accP
      \<and> pow_sub_reduced_covers (real_of_int_poly (Poly q)) accP)"
  by (rule weaken_SPEC[OF hybrid_isolate_all_split_main_correct_pos_pinned[OF qpre]])
     (auto intro: pow_sub_reduced_isolates_from_pinned pow_sub_reduced_covers_from_pinned)

section \<open>Word-bound and parity arithmetic for the entry's own ASSERTs\<close>

text \<open>The entry \<open>ASSERT\<close>s \<open>h < max_snat\<close>, \<open>d < max_snat\<close> and \<open>par < max_snat\<close> BEFORE the
  applicability branch, so none of them may use \<open>2 \<le> d\<close>. @{const pow_sub_h} is a @{const Gcd} over
  positions and so is bounded by the list length — the degenerate \<open>h = 0\<close> case (support
  \<open>\<subseteq> {0}\<close>: a nonzero constant, or the zero polynomial) is the easy branch.\<close>

lemma pow_sub_h_le_length:
  fixes xs :: "int list"
  shows "pow_sub_h xs \<le> length xs"
proof (cases "\<forall>i \<in> pow_sub_support xs. i = 0")
  case True
  then have "pow_sub_support xs = {} \<or> pow_sub_support xs = {0}" by auto
  then have "pow_sub_h xs = 0" unfolding pow_sub_h_def by auto
  thus ?thesis by simp
next
  case False
  then obtain i where i: "i \<in> pow_sub_support xs" and i0: "i \<noteq> 0" by blast
  have "pow_sub_h xs dvd i" using i by (rule pow_sub_h_dvd)
  then have le: "pow_sub_h xs \<le> i" using i0 by (simp add: dvd_imp_le)
  have "i < length xs" using i unfolding pow_sub_support_def by simp
  with le show ?thesis by simp
qed

text \<open>\<open>gcd a b \<le> max a b\<close> — the \<open>a = 0\<close> branch is why it is not simply \<open>gcd_le1_nat\<close>:
  \<open>gcd 0 b = b\<close>, so the bound has to be the MAX and not the first argument.\<close>

lemma pow_sub_gcd_le_max: "gcd (a :: nat) b \<le> max a b"
proof (cases "a = 0")
  case True thus ?thesis by simp
next
  case False
  then have "gcd a b \<le> a" by (simp add: gcd_le1_nat)
  thus ?thesis by simp
qed

lemma pow_sub_gcd_two_le: "gcd (d :: nat) 2 \<le> 2"
  using gcd_dvd2[of d 2] by (simp add: dvd_imp_le)

text \<open>\<^bold>\<open>The parity bridge, once.\<close> The code tests \<open>2 \<le> gcd d 2\<close>; the mirror needs \<open>even d\<close>.
  \<open>gcd d 2\<close> divides \<open>2\<close>, so \<open>2 \<le> gcd d 2\<close> forces it to BE \<open>2\<close>, and \<open>gcd d 2 dvd d\<close> finishes.\<close>

lemma pow_sub_par_even:
  fixes d :: nat
  assumes par2: "2 \<le> gcd d 2"
  shows "even d"
proof -
  have "gcd d 2 = 2" using par2 pow_sub_gcd_two_le[of d] by linarith
  moreover have "gcd d 2 dvd d" by simp
  ultimately show ?thesis by simp
qed

section \<open>The entry theorem\<close>

text \<open>\<^bold>\<open>The substituting arm\<close>, separate from the entry so that the branch proof is two one-line rule
  applications. \<open>d\<close> is the exponent actually used and \<open>even d\<close> its parity test, never the detected \<open>h\<close>.\<close>

lemma pow_sub_entry_sub_mop_correct:
  \<comment> \<open>\<open>d\<close> MUST be in \<open>fixes\<close>: a \<open>defines\<close> right-hand side may only mention fixed variables,
     else the \<open>lemma\<close> command itself aborts with \<open>Extra variables on rhs\<close>\<close>
  fixes xs :: "int list" and d dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
    and "q \<equiv> pow_sub_extract d xs"
  \<comment> \<open>\<^bold>\<open>The parity hypothesis is the code's own test \<open>2 \<le> gcd d 2\<close>, not \<open>even d\<close>\<close>, although the two are equivalent.
     Stated as \<open>even d\<close>, the entry proof's closing \<open>auto\<close> meets \<open>even (gcd (pow_sub_h xs) hcap)\<close>, rewrites it by
     \<open>even (gcd a b) \<longleftrightarrow> even a \<and> even b\<close>, and leaves two unprovable goals, \<open>even (pow_sub_h xs)\<close> and \<open>even hcap\<close>. Phrased
     as the test, the hypothesis matches the premise \<open>2 \<le> gcd (gcd \<dots>) 2\<close> syntactically.\<close>
  assumes d2: "2 \<le> d" and par2: "2 \<le> gcd d 2" and db: "d < max_snat LENGTH(gmp_poly_len)"
    and ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and supp: "\<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> d dvd i"
    and qsolve: "defl_isolate_all_split_main q \<le> SPEC (\<lambda>(accP, accN, xs0).
          dyadic_interval_vec_invar accP
          \<and> length (dyadic_interval_vec_triples accP) + 1
              < max_snat LENGTH(gmp_poly_len)
          \<and> pow_sub_reduced_isolates (real_of_int_poly (Poly q)) accP)"
  shows "pow_sub_entry_sub_mop d dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>j < length (dyadic_interval_vec_triples out).
                 case dyadic_interval_vec_triples out ! j of ((L, R), m) \<Rightarrow>
                   dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
                   \<and> dsc_pair_ok P (- (real_of_int R / 2 ^ m),
                                    - (real_of_int L / 2 ^ m))))"
proof -
  have d0: "0 < d" using d2 by simp
  have ev: "even d" by (rule pow_sub_par_even[OF par2])
  have lenxs: "length xs < max_snat LENGTH(gmp_poly_len)" using len1 by simp
  have ne': "0 < length xs" using ne by simp
  \<comment> \<open>the algebra, once\<close>
  have Pdef: "P = real_of_int_poly (Poly q) \<circ>\<^sub>p monom 1 d"
    unfolding P_def q_def by (rule pow_sub_reduced_algebra(1)[OF d0 ne nz supp])
  have canon: "coeffs (Poly q) = q"
    unfolding q_def by (rule pow_sub_reduced_algebra(2)[OF d0 ne nz supp])
  have qlen0: "0 < length q" unfolding q_def by simp
  \<comment> \<open>\<open>length q \<le> length xs\<close>: the extraction takes one slot per \<open>d\<close>-multiple\<close>
  have qlen: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "length q = Suc ((length xs - 1) div d)" unfolding q_def by simp
    also have "\<dots> \<le> Suc (length xs - 1)"
      by (simp add: Euclidean_Rings.div_le_dividend)
    finally show ?thesis using len1 ne' by linarith
  qed
  \<comment> \<open>the back-map, instantiated at the reduced polynomial the solve was run on\<close>
  have bm: "pow_sub_backmap_all_monadic d q dlt accP
        \<le> SPEC (\<lambda>(out, ok).
              dyadic_interval_vec_invar out
              \<and> (ok \<longrightarrow> length (dyadic_interval_vec_triples out)
                          = length (dyadic_interval_vec_triples accP)
                    \<and> (\<forall>j < length (dyadic_interval_vec_triples accP).
                         case dyadic_interval_vec_triples out ! j of ((L, R), m) \<Rightarrow>
                           dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
                           \<and> dsc_pair_ok P (- (real_of_int R / 2 ^ m),
                                            - (real_of_int L / 2 ^ m)))))"
    if ivQ: "dyadic_interval_vec_invar accP"
      and n1: "length (dyadic_interval_vec_triples accP) + 1
                 < max_snat LENGTH(gmp_poly_len)"
      and iso: "pow_sub_reduced_isolates (real_of_int_poly (Poly q)) accP"
    for accP
    by (rule pow_sub_backmap_all_pair_ok_mirror[OF d0 ev db Pdef sfP refl canon[symmetric]
               qlen0 qlen ivQ n1])
       (use iso in \<open>simp add: pow_sub_reduced_isolates_def\<close>)
  \<comment> \<open>\<open>dyadic_interval_vec_free_monadic\<close> has NO \<open>[refine_vcg]\<close> rule (unlike
     @{thm [source] poly_free_monadic_rule}), so it must be UNFOLDED here or \<open>refine_vcg\<close> leaves
     the bare goal \<open>dyadic_interval_vec_free_monadic \<dots> = SUCCEED\<close>. Unfolded, its two inner
     \<open>poly_free_monadic\<close> calls are discharged by that registered rule — but its THIRD component,
     \<open>mop_free ks\<close>, has no rule either and is just \<open>RETURN ()\<close>, so
     that definition goes in the same clause.\<close>
  show ?thesis
    unfolding pow_sub_entry_sub_mop_def PR_CONST_def
      dyadic_interval_vec_free_monadic_def mop_free_def
    apply (refine_vcg
           pow_sub_extract_monadic_correct[OF d0 ne' lenxs, folded q_def, THEN order_trans]
           qsolve[THEN order_trans]
           bm[THEN order_trans])
    apply (all \<open>use d0 db qlen0 qlen ne' lenxs in \<open>auto simp: Let_def\<close>\<close>)
    done
qed

subsection \<open>Completeness of the substituting arm\<close>

text \<open>The counterpart of @{thm [source] pow_sub_entry_sub_mop_correct}, one root at a time in the other
  direction: \<open>x\<close> a root of \<open>P\<close> gives \<open>x\<^sup>d\<close> a root of \<open>Q\<close> (@{thm [source] poly_pcompose_monom}); \<open>x\<^sup>d\<close> is strictly
  positive, because the origin is not a root under the squarefree obligation
  (@{thm [source] pow_sub_squarefree_no_origin}) and \<open>d\<close> is even; so the reduced solve's covering applies, the
  back-map's covering carries it to an emitted window, and @{thm [source] pow_sub_window_covers_lift} puts \<open>x\<close> in that
  window or its reflection.\<close>

lemma pow_sub_entry_sub_mop_complete:
  fixes xs :: "int list" and d dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
    and "q \<equiv> pow_sub_extract d xs"
  assumes d2: "2 \<le> d" and par2: "2 \<le> gcd d 2" and db: "d < max_snat LENGTH(gmp_poly_len)"
    and ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and supp: "\<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> d dvd i"
    and qsolve: "defl_isolate_all_split_main q \<le> SPEC (\<lambda>(accP, accN, xs0).
          dyadic_interval_vec_invar accP
          \<and> length (dyadic_interval_vec_triples accP) + 1
              < max_snat LENGTH(gmp_poly_len)
          \<and> pow_sub_reduced_isolates (real_of_int_poly (Poly q)) accP
          \<and> pow_sub_reduced_covers (real_of_int_poly (Poly q)) accP)"
  shows "pow_sub_entry_sub_mop d dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>x::real. poly P x = 0 \<longrightarrow>
        (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
           \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
           \<and> ((real_of_int L / 2 ^ m \<le> x \<and> x \<le> real_of_int R / 2 ^ m)
              \<or> (- (real_of_int R / 2 ^ m) \<le> x \<and> x \<le> - (real_of_int L / 2 ^ m))))))"
proof -
  have d0: "0 < d" using d2 by simp
  have ev: "even d" by (rule pow_sub_par_even[OF par2])
  have lenxs: "length xs < max_snat LENGTH(gmp_poly_len)" using len1 by simp
  have ne': "0 < length xs" using ne by simp
  have Pdef: "P = real_of_int_poly (Poly q) \<circ>\<^sub>p monom 1 d"
    unfolding P_def q_def by (rule pow_sub_reduced_algebra(1)[OF d0 ne nz supp])
  have canon: "coeffs (Poly q) = q"
    unfolding q_def by (rule pow_sub_reduced_algebra(2)[OF d0 ne nz supp])
  have qlen0: "0 < length q" unfolding q_def by simp
  have qlen: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "length q = Suc ((length xs - 1) div d)" unfolding q_def by simp
    also have "\<dots> \<le> Suc (length xs - 1)" by (simp add: Euclidean_Rings.div_le_dividend)
    finally show ?thesis using len1 ne' by linarith
  qed
  \<comment> \<open>the origin is not a root of the REDUCED polynomial, hence not of \<open>P\<close> either\<close>
  have Qorig: "poly (real_of_int_poly (Poly q)) 0 \<noteq> 0"
    by (rule pow_sub_squarefree_no_origin[OF d2 sfP[unfolded Pdef]])
  have xy: "0 < x ^ d \<and> poly (real_of_int_poly (Poly q)) (x ^ d) = 0"
    if rx: "poly P x = 0" for x :: real
  proof -
    have qroot: "poly (real_of_int_poly (Poly q)) (x ^ d) = 0"
      using rx unfolding Pdef by (simp add: poly_pcompose_monom)
    have xnz: "x \<noteq> 0"
    proof
      assume "x = 0"
      then have "x ^ d = 0" using d0 by (simp add: zero_power)
      with qroot Qorig show False by simp
    qed
    then have "0 < x ^ d" using ev by (simp add: zero_less_power_eq)
    with qroot show ?thesis by simp
  qed
  \<comment> \<open>the back-map, in the covering direction, already carried to \<open>P\<close>-roots\<close>
  have bmc: "pow_sub_backmap_all_monadic d q dlt accP
        \<le> SPEC (\<lambda>(out, ok). ok \<longrightarrow>
             (\<forall>x::real. poly P x = 0 \<longrightarrow>
               (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
                  \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
                  \<and> ((real_of_int L / 2 ^ m \<le> x \<and> x \<le> real_of_int R / 2 ^ m)
                     \<or> (- (real_of_int R / 2 ^ m) \<le> x
                        \<and> x \<le> - (real_of_int L / 2 ^ m))))))"
    if ivQ: "dyadic_interval_vec_invar accP"
      and n1: "length (dyadic_interval_vec_triples accP) + 1
                 < max_snat LENGTH(gmp_poly_len)"
      and iso: "pow_sub_reduced_isolates (real_of_int_poly (Poly q)) accP"
      and cov: "pow_sub_reduced_covers (real_of_int_poly (Poly q)) accP"
    for accP
  proof -
    have base: "pow_sub_backmap_all_monadic d q dlt accP
          \<le> SPEC (\<lambda>(out, ok). ok \<longrightarrow>
               (\<forall>y::real. 0 < y \<longrightarrow> poly (real_of_int_poly (Poly q)) y = 0 \<longrightarrow>
                 (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
                    \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
                    \<and> 0 \<le> L \<and> L \<le> R
                    \<and> (real_of_int L / 2 ^ m) ^ d \<le> y
                    \<and> y \<le> (real_of_int R / 2 ^ m) ^ d)))"
      by (rule pow_sub_backmap_all_cover[OF d0 db Pdef sfP refl canon[symmetric]
                 qlen0 qlen ivQ n1])
         (use iso cov in \<open>auto simp: pow_sub_reduced_isolates_def
                pow_sub_reduced_covers_def\<close>)
    show ?thesis
      apply (rule weaken_SPEC[OF base])
      apply clarsimp
      subgoal premises p for a aa b ba x
      proof -
        have y1: "0 < x ^ d" and y2: "poly (real_of_int_poly (Poly q)) (x ^ d) = 0"
          using xy[OF p(2)] by auto
        obtain j L R m where jn: "j < length (dyadic_interval_vec_triples (a, aa, b))"
          and tj: "dyadic_interval_vec_triples (a, aa, b) ! j = ((L, R), m)"
          and L0: "0 \<le> L" and LR: "L \<le> R"
          and lo: "(real_of_int L / 2 ^ m) ^ d \<le> x ^ d"
          and hi: "x ^ d \<le> (real_of_int R / 2 ^ m) ^ d"
          using p(3) y1 y2 by blast
        have u0: "0 \<le> real_of_int L / 2 ^ m" using L0 by simp
        have v0: "0 \<le> real_of_int R / 2 ^ m" using L0 LR by simp
        have "(real_of_int L / 2 ^ m \<le> x \<and> x \<le> real_of_int R / 2 ^ m)
              \<or> (- (real_of_int R / 2 ^ m) \<le> x \<and> x \<le> - (real_of_int L / 2 ^ m))"
          by (rule pow_sub_window_covers_lift[OF d0 ev u0 v0 lo hi])
        thus ?thesis using jn tj by blast
      qed
      done
  qed
  show ?thesis
    unfolding pow_sub_entry_sub_mop_def PR_CONST_def
      dyadic_interval_vec_free_monadic_def mop_free_def
    apply (refine_vcg
           pow_sub_extract_monadic_correct[OF d0 ne' lenxs, folded q_def, THEN order_trans]
           qsolve[THEN order_trans]
           bmc[THEN order_trans])
    apply (all \<open>use d0 db qlen0 qlen ne' lenxs in \<open>auto simp: Let_def\<close>\<close>)
    done
qed

text \<open>The support fact for the exponent actually used: \<open>pow_sub_h\<close> divides every nonzero position and \<open>gcd\<close>
  divides \<open>pow_sub_h\<close>, so the clamped exponent divides them too. This lets @{thm [source] pow_sub_compose} be applied
  at \<open>d\<close>.\<close>

lemma pow_sub_exp_dvd_support:
  fixes xs :: "int list"
  shows "\<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> gcd (pow_sub_h xs) hcap dvd i"
  using pow_sub_h_dvd_nonzero by (meson gcd_dvd1 dvd_trans)


text \<open>\<^bold>\<open>The entry theorem: soundness.\<close> On \<open>ok = True\<close> every emitted window of \<open>pow_sub_entry_monadic\<close> isolates a
  root of the original \<open>P\<close>, on both sides of the origin.

  \<^bold>\<open>The non-substituting arm needs no clause\<close>: it returns \<open>ok = False\<close>, and the exported wrapper (\<open>isarri_wrapper\<close>)
  then solves \<open>P\<close> itself with the deflating solve, whose capstone covers it. So an \<open>ok\<close>-guarded conclusion is the
  right shape: \<open>ok\<close> is informational, and the wrapper's output is valid either way.

  \<^bold>\<open>The hypothesis\<close> \<open>qsolve\<close> is the reduced solve's specification in numerator form; the corollaries in the last
  section reduce it to the reduced polynomial's precondition.\<close>

theorem pow_sub_entry_monadic_correct:
  fixes xs :: "int list" and nfloor hcap dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and hcb: "hcap < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and qsolve: "\<And>d. 2 \<le> d \<Longrightarrow> even d \<Longrightarrow> d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
          defl_isolate_all_split_main (pow_sub_extract d xs)
            \<le> SPEC (\<lambda>(accP, accN, xs0).
                dyadic_interval_vec_invar accP
                \<and> length (dyadic_interval_vec_triples accP) + 1
                    < max_snat LENGTH(gmp_poly_len)
                \<and> pow_sub_reduced_isolates
                     (real_of_int_poly (Poly (pow_sub_extract d xs))) accP)"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>j < length (dyadic_interval_vec_triples out).
                 case dyadic_interval_vec_triples out ! j of ((L, R), m) \<Rightarrow>
                   dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
                   \<and> dsc_pair_ok P (- (real_of_int R / 2 ^ m),
                                    - (real_of_int L / 2 ^ m))))"
proof -
  have lenxs: "length xs < max_snat LENGTH(gmp_poly_len)" using len1 by simp
  have supp: "\<And>d. d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
        \<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> d dvd i"
    using pow_sub_exp_dvd_support by blast
  \<comment> \<open>the entry's three pre-branch \<open>ASSERT\<close>s, all word bounds\<close>
  have hb: "pow_sub_h xs < max_snat LENGTH(gmp_poly_len)"
    using pow_sub_h_le_length[of xs] lenxs by simp
  have dbnd: "gcd (pow_sub_h xs) hcap < max_snat LENGTH(gmp_poly_len)"
    using pow_sub_gcd_le_max[of "pow_sub_h xs" hcap] hb hcb by simp
  \<comment> \<open>\<open>pow_sub_room_max_snat\<close> (Power_Sub_Sound) turns \<open>max_snat 64\<close> into its numeral so
     \<open>linarith\<close> can compare it against the atom \<open>gcd d 2\<close>; \<open>simp add: max_snat_def\<close> leaves the
     comparison undone because \<open>simp\<close> will not do the arithmetic over an opaque \<open>gcd\<close> term\<close>
  have parbnd: "gcd d 2 < max_snat LENGTH(gmp_poly_len)" for d :: nat
  proof -
    \<comment> \<open>\<open>for d\<close>, not \<open>\<And>d\<close> with a chained fact: under the meta-quantifier the supplied
       \<open>gcd ?d 2 \<le> 2\<close> stays SCHEMATIC and \<open>linarith\<close> cannot instantiate it against the bound
       variable, so it reports the goal untouched\<close>
    have "gcd d 2 \<le> 2" by (rule pow_sub_gcd_two_le)
    thus ?thesis unfolding pow_sub_room_max_snat by linarith
  qed
  \<comment> \<open>the substituting arm, at the exponent the applicability test admitted\<close>
  have sub: "pow_sub_entry_sub_mop d dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
        ok \<longrightarrow> (\<forall>j < length (dyadic_interval_vec_triples out).
                   case dyadic_interval_vec_triples out ! j of ((L, R), m) \<Rightarrow>
                     dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
                     \<and> dsc_pair_ok P (- (real_of_int R / 2 ^ m),
                                      - (real_of_int L / 2 ^ m))))"
    if d2: "2 \<le> d" and par2: "2 \<le> gcd d 2" and db: "d < max_snat LENGTH(gmp_poly_len)"
      and deq: "d = gcd (pow_sub_h xs) hcap"
    for d
  proof -
    \<comment> \<open>\<open>qsolve\<close> is stated over \<open>even d\<close> (the mathematical content), the branch fact over
       \<open>2 \<le> gcd d 2\<close> (what the code tests)\<close>
    have ev: "even d" by (rule pow_sub_par_even[OF par2])
    show ?thesis
      unfolding P_def
      by (rule pow_sub_entry_sub_mop_correct[OF d2 par2 db ne len1 nz sfP[unfolded P_def]
                 supp[OF deq] qsolve[OF d2 ev deq]])
  qed
  show ?thesis
    unfolding pow_sub_entry_monadic_def PR_CONST_def
      pow_sub_entry_applicable_mop_def pow_sub_entry_exp_mop_def
      pow_sub_entry_bail_mop_def poly_length_monadic_def
    \<comment> \<open>\<open>snat_gcd_monadic_correct\<close> is declared \<open>[refine_vcg]\<close>, but that registration does not compose through this
       chain: without it in the hint list, the detection hint fires and the remaining
       \<open>gcd \<rightarrow> ASSERT \<rightarrow> gcd \<rightarrow> if\<close> chain is left inside one \<open>SPEC\<close> (one hint establishes one bind). Both \<open>gcd\<close> calls
       need it: the exponent \<open>gcd h hcap\<close> and the parity \<open>gcd d 2\<close>.\<close>
    apply (refine_vcg
           pow_sub_h_monadic_correct[OF lenxs, THEN order_trans]
           snat_gcd_monadic_correct[THEN order_trans]
           sub[THEN order_trans]
           dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans])
    apply (all \<open>use ne lenxs len1 hb dbnd parbnd in \<open>auto simp: Let_def\<close>\<close>)
    done
qed

subsection \<open>The entry is complete\<close>

text \<open>\<^bold>\<open>The counterpart of @{thm [source] pow_sub_entry_monadic_correct}.\<close> On \<open>ok = True\<close> every real root of the
  input lies in some emitted window or in its reflection through the origin, so the substituting path loses no root.
  The proof has the same skeleton as soundness: the three word-bound \<open>ASSERT\<close>s before the branch, then the
  substituting arm.

  \<^bold>\<open>Its hypothesis is exactly the soundness hypothesis\<close>, \<open>qsolve\<close>, whose isolation half is discharged by
  @{thm [source] pow_sub_reduced_isolates_of_pre} and whose covering half by
  @{thm [source] pow_sub_reduced_covers_of_pre}, both from the reduced polynomial's precondition. Completeness adds no
  obligation of its own. On \<open>ok = False\<close> nothing is claimed here; the wrapper's fallback solve is covered by its own
  capstone.\<close>

theorem pow_sub_entry_monadic_complete:
  fixes xs :: "int list" and nfloor hcap dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and hcb: "hcap < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and qsolve: "\<And>d. 2 \<le> d \<Longrightarrow> even d \<Longrightarrow> d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
          defl_isolate_all_split_main (pow_sub_extract d xs)
            \<le> SPEC (\<lambda>(accP, accN, xs0).
                dyadic_interval_vec_invar accP
                \<and> length (dyadic_interval_vec_triples accP) + 1
                    < max_snat LENGTH(gmp_poly_len)
                \<and> pow_sub_reduced_isolates
                     (real_of_int_poly (Poly (pow_sub_extract d xs))) accP
                \<and> pow_sub_reduced_covers
                     (real_of_int_poly (Poly (pow_sub_extract d xs))) accP)"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>x::real. poly P x = 0 \<longrightarrow>
        (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
           \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
           \<and> ((real_of_int L / 2 ^ m \<le> x \<and> x \<le> real_of_int R / 2 ^ m)
              \<or> (- (real_of_int R / 2 ^ m) \<le> x
                 \<and> x \<le> - (real_of_int L / 2 ^ m))))))"
proof -
  have lenxs: "length xs < max_snat LENGTH(gmp_poly_len)" using len1 by simp
  have supp: "\<And>d. d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
        \<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> d dvd i"
    using pow_sub_exp_dvd_support by blast
  have hb: "pow_sub_h xs < max_snat LENGTH(gmp_poly_len)"
    using pow_sub_h_le_length[of xs] lenxs by simp
  have dbnd: "gcd (pow_sub_h xs) hcap < max_snat LENGTH(gmp_poly_len)"
    using pow_sub_gcd_le_max[of "pow_sub_h xs" hcap] hb hcb by simp
  have parbnd: "gcd d 2 < max_snat LENGTH(gmp_poly_len)" for d :: nat
  proof -
    have "gcd d 2 \<le> 2" by (rule pow_sub_gcd_two_le)
    thus ?thesis unfolding pow_sub_room_max_snat by linarith
  qed
  have sub: "pow_sub_entry_sub_mop d dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
        ok \<longrightarrow> (\<forall>x::real. poly P x = 0 \<longrightarrow>
          (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
             \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
             \<and> ((real_of_int L / 2 ^ m \<le> x \<and> x \<le> real_of_int R / 2 ^ m)
                \<or> (- (real_of_int R / 2 ^ m) \<le> x
                   \<and> x \<le> - (real_of_int L / 2 ^ m))))))"
    if d2: "2 \<le> d" and par2: "2 \<le> gcd d 2" and db: "d < max_snat LENGTH(gmp_poly_len)"
      and deq: "d = gcd (pow_sub_h xs) hcap"
    for d
  proof -
    have ev: "even d" by (rule pow_sub_par_even[OF par2])
    show ?thesis
      unfolding P_def
      by (rule pow_sub_entry_sub_mop_complete[OF d2 par2 db ne len1 nz sfP[unfolded P_def]
                 supp[OF deq] qsolve[OF d2 ev deq]])
  qed
  show ?thesis
    unfolding pow_sub_entry_monadic_def PR_CONST_def
      pow_sub_entry_applicable_mop_def pow_sub_entry_exp_mop_def
      pow_sub_entry_bail_mop_def poly_length_monadic_def
    apply (refine_vcg
           pow_sub_h_monadic_correct[OF lenxs, THEN order_trans]
           snat_gcd_monadic_correct[THEN order_trans]
           sub[THEN order_trans]
           dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans])
    apply (all \<open>use ne lenxs len1 hb dbnd parbnd in \<open>auto simp: Let_def\<close>\<close>)
    done
qed
section \<open>The entry theorems with \<open>qsolve\<close> reduced to one hypothesis\<close>

text \<open>\<^bold>\<open>What the entry theorems are conditional on.\<close> Both take \<open>qsolve\<close>, the reduced solve's
  \<open>\<le> SPEC\<close>, as an assumption, and the corollaries below reduce it to a precondition on the reduced
  polynomial, supplied by @{thm [source] defl_isolate_all_split_main_correct_qsolve}, the deflating
  solve's capstone.

  \<^bold>\<open>The precondition is the deflating bundle.\<close> The capstone holds under
  @{const dsc_isolate_all_split_defl_pre}, so \<open>qpre\<close> below is stated with that bundle. Neither it nor
  @{const dsc_isolate_all_split_hybrid_pre} implies the other: the deflating bundle lacks
  @{const split_cap}'s exponential clause, and its two depth caps are quantified over
  \<open>kD \<le> 258 \<cdot> \<mu>(delta_defl)\<close> rather than \<open>258 \<cdot> \<mu>(delta_P)\<close>, where \<open>delta_defl\<close> is the smaller \<open>\<delta>\<close>,
  hence the larger range. The excess is bounded (\<open>\<mu>(delta_defl) \<le> max (\<mu>(delta_P)) 4\<close>,
  \<open>Kiou_Bound_Defl_Reflect\<close>), but on the clamped branch the caps must still hold up to \<open>kD = 1032\<close>,
  which \<open>length q < 2\<^sup>4\<^sup>0\<close> does not give.

  \<^bold>\<open>The hypothesis does not transport from \<open>P\<close> to \<open>Q\<close> in general.\<close>
  \<open>P(x) = (2\<^sup>8\<^sup>0x\<^sup>2 - 1)(2\<^sup>8\<^sup>0x\<^sup>2 - 4) = Q(x\<^sup>2)\<close> gives \<open>\<mu>\<^sub>P \<approx> 44 < 82 \<approx> \<mu>\<^sub>Q\<close>, a counterexample to the
  depth-quantified \<open>\<delta>\<close> clauses transporting, because \<open>x \<mapsto> x\<^sup>d\<close> compresses roots near zero. Everything
  else in the bundle does transport (@{thm [source] pow_sub_reduced_last_nz},
  @{thm [source] pow_sub_reduced_len2}, @{thm [source] pow_sub_reduced_algebra},
  @{thm [source] pow_sub_exp_dvd_support}, @{thm [source] pow_sub_h_le_length}). So it remains a caller
  obligation, not checked at run time; it is satisfiable (\<open>Split_Pre_Witness\<close>).\<close>

text \<open>\<^bold>\<open>The bridge from the deflating capstone's vocabulary is a DEFINITIONAL UNFOLDING.\<close>
  @{const defl_acc_isolates} and @{const defl_acc_covers}\<open> \<dots> 0\<close> are written onto this
  interface and their bodies are these two, symbol for symbol; they
  are separate constants only because \<open>Deflation_Loop_Refine\<close> is an ANCESTOR theory and cannot
  name a fact of this one. Both sides are in scope here.\<close>

lemma pow_sub_reduced_isolates_of_defl_acc:
  "defl_acc_isolates Q accQ \<Longrightarrow> pow_sub_reduced_isolates Q accQ"
  unfolding pow_sub_reduced_isolates_def defl_acc_isolates_def by simp

lemma pow_sub_reduced_covers_of_defl_acc:
  "defl_acc_covers Q 0 accQ \<Longrightarrow> pow_sub_reduced_covers Q accQ"
  unfolding pow_sub_reduced_covers_def defl_acc_covers_def by simp

corollary pow_sub_entry_monadic_correct_of_pre:
  fixes xs :: "int list" and nfloor hcap dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and hcb: "hcap < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and qpre: "\<And>d. 2 \<le> d \<Longrightarrow> even d \<Longrightarrow> d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
          dsc_isolate_all_split_defl_pre (pow_sub_extract d xs)"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>j < length (dyadic_interval_vec_triples out).
                 case dyadic_interval_vec_triples out ! j of ((L, R), m) \<Rightarrow>
                   dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
                   \<and> dsc_pair_ok P (- (real_of_int R / 2 ^ m),
                                    - (real_of_int L / 2 ^ m))))"
proof -
  \<comment> \<open>the soundness entry wants THREE of the four conjuncts; the covering one is dropped here
     and consumed by the completeness corollary below.\<close>
  have q3: "defl_isolate_all_split_main (pow_sub_extract d xs)
        \<le> SPEC (\<lambda>(accP, accN, xs0).
            dyadic_interval_vec_invar accP
            \<and> length (dyadic_interval_vec_triples accP) + 1
                < max_snat LENGTH(gmp_poly_len)
            \<and> pow_sub_reduced_isolates
                 (real_of_int_poly (Poly (pow_sub_extract d xs))) accP)"
    if d2: "2 \<le> d" and ev: "even d" and deq: "d = gcd (pow_sub_h xs) hcap" for d
    by (rule weaken_SPEC[OF defl_isolate_all_split_main_correct_qsolve[OF qpre[OF d2 ev deq]]])
       (auto intro: pow_sub_reduced_isolates_of_defl_acc)
  show ?thesis
    unfolding P_def
    by (rule pow_sub_entry_monadic_correct[OF ne len1 hcb nz sfP[unfolded P_def] q3])
qed

corollary pow_sub_entry_monadic_complete_of_pre:
  fixes xs :: "int list" and nfloor hcap dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and hcb: "hcap < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and qpre: "\<And>d. 2 \<le> d \<Longrightarrow> even d \<Longrightarrow> d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
          dsc_isolate_all_split_defl_pre (pow_sub_extract d xs)"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>x::real. poly P x = 0 \<longrightarrow>
        (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
           \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
           \<and> ((real_of_int L / 2 ^ m \<le> x \<and> x \<le> real_of_int R / 2 ^ m)
              \<or> (- (real_of_int R / 2 ^ m) \<le> x
                 \<and> x \<le> - (real_of_int L / 2 ^ m))))))"
proof -
  \<comment> \<open>completeness consumes all four conjuncts, so both bridges fire here; the soundness
     corollary drops the covering one.\<close>
  have q4: "defl_isolate_all_split_main (pow_sub_extract d xs)
        \<le> SPEC (\<lambda>(accP, accN, xs0).
            dyadic_interval_vec_invar accP
            \<and> length (dyadic_interval_vec_triples accP) + 1
                < max_snat LENGTH(gmp_poly_len)
            \<and> pow_sub_reduced_isolates
                 (real_of_int_poly (Poly (pow_sub_extract d xs))) accP
            \<and> pow_sub_reduced_covers
                 (real_of_int_poly (Poly (pow_sub_extract d xs))) accP)"
    if d2: "2 \<le> d" and ev: "even d" and deq: "d = gcd (pow_sub_h xs) hcap" for d
    by (rule weaken_SPEC[OF defl_isolate_all_split_main_correct_qsolve[OF qpre[OF d2 ev deq]]])
       (auto intro: pow_sub_reduced_isolates_of_defl_acc pow_sub_reduced_covers_of_defl_acc)
  show ?thesis
    unfolding P_def
    by (rule pow_sub_entry_monadic_complete[OF ne len1 hcb nz sfP[unfolded P_def] q4])
qed

end
