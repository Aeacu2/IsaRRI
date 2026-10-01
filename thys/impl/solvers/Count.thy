theory Count
  imports "IsaRRI_LLVM.Carried_Kernel" Count_Spec "IsaRRI_LLVM.Interval_Eval"
begin

text \<open>Hybrid coefficient truncation for the carried Descartes
  count — the executable/monadic layer. Layer: SEPREF.

  Main export: \<open>carried_descartes_count_trunc_monadic\<close>, a drop-in sibling of
  \<open>carried_descartes_count_monadic\<close> (\<open>Carried_Kernel.thy\<close>) with the IDENTICAL classify
  contract (\<open>carried_descartes_count_trunc_monadic_classify\<close>), used at the single call
  site (\<open>Bisection.thy\<close>, \<open>carried_after_pop\<close>).
  Strategy (msolve's \<open>descartes_truncate\<close>, floor-division variant): reverse-copy the
  node poly, ONE truncation pre-pass (\<open>mpz_fdiv_q_2exp\<close>), then a clone of the fused
  ET-Horner shift+count whose sign accounting only counts THRESHOLD-TRUSTED signs and
  tracks an ambiguity flag; decisive (no ambiguity, or count already \<open>\<ge> 2\<close>) \<Rightarrow> return,
  else exact fallback on a fresh reverse copy. All entry conditions are RUNTIME tests,
  so the public contract carries no new hypotheses.\<close>

text \<open>The borrowed per-coefficient bit-length read @{const poly_coeff_bitlen2_monadic} (with its
  \<open>[llvm_code]\<close> implementation and HNR) is in \<open>Array\<close>, so that callers other than this theory can use it.\<close>

section \<open>Max coefficient bit-length (budget input — perf-only, no correctness content)\<close>

text \<open>\<open>nbits\<close> only picks the truncation budget; a wrong value costs performance, never
  correctness. So the spec is nofail-only. Implementation: borrowed poly + pure word
  state, as in \<open>Kiou_Bound.thy\<close>'s max-fold.\<close>
text \<open>The per-coefficient bit-length is CLAMPED to \<open>max_snat - 1\<close> before the
  \<open>gmp_size\<close> (unat) \<Rightarrow> snat conversion, so the op is UNCONDITIONALLY nofail (a
  coefficient would need \<open>2^63\<close> bits to be clamped in practice). \<open>nb\<close> is perf-only
  (the truncation budget); a clamp only affects an astronomically-large-coefficient
  budget, never correctness.\<close>
text \<open>The runtime signed-word ceiling \<open>max_snat LENGTH('l) - 1\<close> as a registered snat
  op (implemented by the LLVM primitive \<open>ll_max_snat\<close>). A LOCAL copy of
  \<open>Dyadic_Kernel.max_snat_incl\<close> — replicated here (not imported) so the truncation
  track pulls in no extra solver theory (keeps the fast-iteration base small).\<close>
definition [simp]: "trunc_max_snat_incl TYPE('l::len2) \<equiv> max_snat LENGTH('l) - 1"

sepref_register "trunc_max_snat_incl TYPE('l::len2)" :: nat

lemma trunc_max_snat_incl_hnr[sepref_fr_rules]:
  "(uncurry0 ll_max_snat,
    uncurry0 (RETURN (PR_CONST (trunc_max_snat_incl TYPE('l::len2)))))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l)"
  apply sepref_to_hoare
  unfolding in_snat_rel_conv_assn
  by vcg

text \<open>A max-fold over a borrowed polynomial: the loop reads coefficient \<open>i\<close> by index (borrowed), and the
  polynomial is not part of the loop state (only the pure \<open>(i, nb)\<close> is). This shape does not compose with an
  inline \<open>for\<close> and \<open>by sepref\<close>; it uses the condition/body op and \<open>WHILET\<close> assembly of \<open>kiou_maxfold_monadic\<close>
  (\<open>Kiou_Bound\<close>).\<close>
abbreviation max_bitlen_state_assn where
  "max_bitlen_state_assn \<equiv>
    snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"

definition max_bitlen_cond_monadic :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
"max_bitlen_cond_monadic len st \<equiv> (let (i, nb) = st in i < len)"

sepref_register "PR_CONST max_bitlen_cond_monadic" :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"

text \<open>The body, in the shape of \<open>kiou_maxfold\<close>'s: explicit if-then-else rather than \<open>min\<close>/\<open>max\<close> on machine
  words, one op per bind, and a repeated subterm computed once. The per-coefficient bit length (\<open>unat\<close>) is clamped
  at the runtime word ceiling \<open>trunc_max_snat_incl\<close> before the \<open>unat\<close>-to-\<open>snat\<close> conversion, so the op cannot fail
  and needs no magnitude hypotheses; the budget affects only performance, so clamping it is harmless.\<close>
definition max_bitlen_body_mop_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) nres" where
"max_bitlen_body_mop_monadic len xs st \<equiv> doN {
  let (i, nb) = st;
  ASSERT (i < len);
  ASSERT (i < length xs);
  bl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs i;
  top \<leftarrow> RETURN (PR_CONST (trunc_max_snat_incl TYPE(gmp_poly_len)));
  topu \<leftarrow> RETURN (op_snat_unat_conv top);
  ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
  i2 \<leftarrow> RETURN (i + 1);
  if topu \<le> bl then RETURN (i2, top)
  else doN {
    ASSERT (bl < max_snat LENGTH(gmp_poly_len));
    bls \<leftarrow> RETURN (op_unat_snat_conv bl);
    if nb < bls then RETURN (i2, bls) else RETURN (i2, nb)
  }
}"

sepref_register "PR_CONST max_bitlen_body_mop_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) nres"

definition poly_max_bitlen_loop_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"poly_max_bitlen_loop_monadic len xs \<equiv> doN {
  (_, nb) \<leftarrow> WHILET
    (\<lambda>st. (PR_CONST max_bitlen_cond_monadic) len st)
    (\<lambda>st. (PR_CONST max_bitlen_body_mop_monadic) len xs st)
    (0, 0);
  RETURN nb
}"

sepref_register "PR_CONST poly_max_bitlen_loop_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

definition poly_max_bitlen_monadic :: "gmp_poly \<Rightarrow> nat nres" where
"poly_max_bitlen_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  (PR_CONST poly_max_bitlen_loop_monadic) len xs
}"

sepref_register "PR_CONST poly_max_bitlen_monadic"
  :: "gmp_poly \<Rightarrow> nat nres"

lemma poly_max_bitlen_monadic_nofail:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_max_bitlen_monadic xs \<le> SPEC (\<lambda>_. True)"
  unfolding poly_max_bitlen_monadic_def poly_max_bitlen_loop_monadic_def
    max_bitlen_cond_monadic_def max_bitlen_body_mop_monadic_def
    poly_coeff_bitlen2_monadic_def
    poly_length_monadic_def mpz_bitlen2_monadic_def PR_CONST_def
    op_snat_unat_conv_def op_unat_snat_conv_def
  apply (refine_vcg WHILET_rule[where R="measure (\<lambda>(i, nb). length xs - i)"
    and I="\<lambda>(i, nb). i \<le> length xs"])
  using assms by (auto simp: max_snat_def)

section \<open>Machine-word bit-length (threshold scale factor)\<close>

text \<open>\<open>nat_bitlen len\<close> as a pure word loop (\<le> 64 iterations, no GMP). Computed ONCE
  per count call; the per-position threshold is then \<open>min (i+1) (len-1-i) * this\<close>.\<close>
definition snat_bitlen_monadic :: "nat \<Rightarrow> nat nres" where
"snat_bitlen_monadic m \<equiv> doN {
  (_, b) \<leftarrow> WHILET
    (\<lambda>(v, b). 0 < v)
    (\<lambda>(v, b). doN {
      ASSERT (b + 1 < max_snat LENGTH(gmp_poly_len));
      RETURN (v div 2, b + 1)
    })
    (m, 0);
  RETURN b
}"

sepref_register "PR_CONST snat_bitlen_monadic" :: "nat \<Rightarrow> nat nres"

text \<open>Introduction form of @{const nat_bitlen}'s \<open>LEAST\<close> definition, for the loop's
  exit reasoning.\<close>
text \<open>A count capped at 2 plus at most one boundary bit trivially fits (\<open>max_snat\<close> is
  \<open>2^63\<close> at this word length).\<close>
lemma small_lt_max_snat: "(n::nat) \<le> 3 \<Longrightarrow> n < max_snat LENGTH(gmp_poly_len)"
  unfolding max_snat_def by simp

lemma nat_bitlen_eqI:
  assumes "m < 2 ^ b"
    and "\<And>y. m < 2 ^ y \<Longrightarrow> b \<le> y"
  shows "nat_bitlen m = b"
  unfolding nat_bitlen_def using assms by (rule Least_equality)

lemma snat_bitlen_monadic_correct:
  assumes "m < max_snat LENGTH(gmp_poly_len)"
  shows "snat_bitlen_monadic m \<le> RETURN (nat_bitlen m)"
  unfolding snat_bitlen_monadic_def
  apply (refine_vcg WHILET_rule[where R="measure (\<lambda>(v, b). v)"
    and I="\<lambda>(v, b). v = m div 2 ^ b \<and> (0 < b \<longrightarrow> 0 < m div 2 ^ (b - 1))"])
  subgoal by simp  \<comment> \<open>wf\<close>
  subgoal by simp  \<comment> \<open>initial, first conjunct: \<open>m = m div 2^0\<close>\<close>
  subgoal by simp  \<comment> \<open>initial, second conjunct: vacuous (\<open>b = 0\<close>)\<close>
  \<comment> \<open>body ASSERT \<open>b + 1 < max_snat\<close>: from \<open>0 < a = m div 2^b\<close> get \<open>2^b \<le> m\<close>, and
     \<open>b + 1 \<le> 2^b\<close> always, so \<open>b + 1 \<le> m < max_snat\<close>.\<close>
  subgoal premises prems for s a b
  proof -
    from prems have aeq: "a = m div 2 ^ b" and apos: "0 < a" by auto
    have pow_le: "2 ^ b \<le> m"
      using aeq apos by (simp add: div_greater_zero_iff)
    have "b + 1 \<le> 2 ^ b" using less_exp[of b] by (simp add: Suc_le_eq)
    then have "b + 1 \<le> m" using pow_le by linarith
    then show "b + 1 < max_snat LENGTH(gmp_poly_len)" using assms by simp
  qed
  \<comment> \<open>invariant first conjunct after the step: \<open>a div 2 = m div 2^(b+1)\<close>\<close>
  subgoal by (auto simp: div_mult2_eq[symmetric] mult.commute)
  \<comment> \<open>invariant second conjunct: \<open>0 < m div 2^b = a\<close> from the loop condition\<close>
  subgoal by auto
  \<comment> \<open>measure: \<open>a div 2 < a\<close> from \<open>0 < a\<close>\<close>
  subgoal by auto
  \<comment> \<open>exit: \<open>m div 2^b = 0\<close> so \<open>m < 2^b\<close>; minimality from the second conjunct\<close>
  subgoal premises prems for s a b
  proof -
    from prems have veq: "m div 2 ^ b = 0"
      and lower: "0 < b \<longrightarrow> 0 < m div 2 ^ (b - 1)" by auto
    have ub: "m < 2 ^ b" using veq by (simp add: div_eq_0_iff)
    have min: "\<And>y. m < 2 ^ y \<Longrightarrow> b \<le> y"
    proof -
      fix y assume my: "m < 2 ^ y"
      show "b \<le> y"
      proof (rule ccontr)
        assume "\<not> b \<le> y"
        then have yb: "y \<le> b - 1" and bpos: "0 < b" by auto
        have "2 ^ (b - 1) \<le> m"
          using lower bpos by (simp add: div_greater_zero_iff)
        moreover have "(2::nat) ^ y \<le> 2 ^ (b - 1)"
          using yb by (simp add: power_increasing)
        ultimately show False using my by linarith
      qed
    qed
    show "nat_bitlen m = b" using nat_bitlen_eqI[OF ub min] .
  qed
  done

section \<open>In-place floor-truncation pass (clone of the scale-loop triple)\<close>

text \<open>Per-coefficient in-place \<open>div 2^t\<close>. Implementation: \<open>raw_mpz_fdiv_q_2exp\<close> in place
  on the slot (bitcnt is unat; its \<open>snd_notzero\<close> precondition is the \<open>ASSERT (0 < t)\<close> —
  the attempt path guarantees \<open>t \<ge> 1\<close>). Loop and wrapper follow the in-place coefficient
  recipe of \<open>poly_scale_loop_monadic\<close>/\<open>poly_scale_in_place_monadic\<close> (\<open>Dyadic_Interval.thy\<close>).\<close>
definition poly_trunc_coeff_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly nres" where
"poly_trunc_coeff_monadic xs i t \<equiv> doN {
  ASSERT (i < length xs);
  ASSERT (0 < t);
  RETURN (xs[i := xs ! i div 2 ^ t])
}"

sepref_register "PR_CONST poly_trunc_coeff_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly nres"

definition poly_trunc_loop_monadic :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_trunc_loop_monadic len t xs \<equiv>
  for 0 len (\<lambda>i ys. doN {
    ASSERT (i < length ys);
    (PR_CONST poly_trunc_coeff_monadic) ys i t
  }) xs"

sepref_register "PR_CONST poly_trunc_loop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

definition poly_trunc_in_place_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_trunc_in_place_monadic t xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_trunc_loop_monadic) len t xs
}"

sepref_register "PR_CONST poly_trunc_in_place_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

text \<open>Abstract correctness of the in-place truncation loop -- the same per-index
  \<open>for_rule\<close> invariant shape as @{thm [source] poly_scale_loop_correct}.\<close>
lemma poly_trunc_loop_correct:
  assumes "length xs = len" and "0 < t"
  shows "poly_trunc_loop_monadic len t xs \<le> RETURN (trunc_list t xs)"
  unfolding poly_trunc_loop_monadic_def poly_trunc_coeff_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>i ys. length ys = len \<and>
    (\<forall>j<len. ys ! j = (if j < i then xs ! j div 2 ^ t else xs ! j))"])
  using assms
  by (auto simp: trunc_list_def nth_list_update' less_Suc_eq intro!: nth_equalityI)

lemma poly_trunc_in_place_correct:
  assumes "0 < t"
    and "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_trunc_in_place_monadic t xs \<le> RETURN (trunc_list t xs)"
  unfolding poly_trunc_in_place_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg poly_trunc_loop_correct[THEN order_trans])
  using assms by (auto simp: pw_le_iff refine_pw_simps)

section \<open>The guarded (truncated) ET-Horner count kernel\<close>

text \<open>Clone of the exact kernel's cond/body/result mop decomposition
  (\<open>Poly_Ops.thy\<close>) with sign accounting replaced by the THRESHOLD-GUARDED
  step: state \<open>((i, last_s, cnt, amb), xs)\<close>. The Ruffini row op
  @{const poly_ethorner_inner_loop_monadic} is reused UNCHANGED. \<open>bthr\<close> =
  \<open>nat_bitlen len\<close>, computed once outside. Trust test per finalized coefficient \<open>i\<close>:
  positive \<Rightarrow> trusted (free, floor's one-sided residue); negative \<Rightarrow> trusted iff
  \<open>trunc_thresh len i < bitlen\<close>; zero/small-negative \<Rightarrow> ambiguous. Early abort at
  \<open>cnt = 2\<close> stays sound WITH ambiguity (trusted-subsequence undercount,
  @{thm [source] trunc_changes_ge2_sound}).\<close>

definition ethorner_count_trunc_cond ::
  "nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly \<Rightarrow> bool" where
  "ethorner_count_trunc_cond limit st \<equiv>
    (let (st1, xs) = st in let (i, last_s, cnt, amb) = st1 in i < limit \<and> cnt < 2)"

sepref_register "PR_CONST ethorner_count_trunc_cond"
  :: "nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly \<Rightarrow> bool"

definition ethorner_count_trunc_body_mop_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly
   \<Rightarrow> ((nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly) nres" where
"ethorner_count_trunc_body_mop_monadic len bthr st \<equiv> doN {
  let (st1, xs) = st;
  let (i, last_s, cnt, amb) = st1;
  ASSERT (length xs = len);
  ASSERT (1 < len);
  ASSERT (i + 1 < len);
  ASSERT (cnt < 2);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (len * bthr < max_snat LENGTH(gmp_poly_len));
  xs' \<leftarrow> (PR_CONST poly_ethorner_inner_loop_monadic) len i xs;
  ASSERT (i < length xs');
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs' i;
  bl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs' i;
  bt \<leftarrow> RETURN (min (min (i + 1) (len - (i + 1)) * bthr) len);
  let trusted = (0 < s \<or> (s < 0 \<and> bt < bl));
  let new_amb = (amb \<or> \<not> trusted);
  let new_cnt = (if trusted \<and> last_s \<noteq> 0 \<and> s \<noteq> last_s then cnt + 1 else cnt);
  let new_last_s = (if trusted then s else last_s);
  RETURN ((i + 1, new_last_s, new_cnt, new_amb), xs')
}"

sepref_register "PR_CONST ethorner_count_trunc_body_mop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly
     \<Rightarrow> ((nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly) nres"

definition ethorner_count_trunc_result_mop_monadic ::
  "(nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly \<Rightarrow> (nat \<times> int \<times> bool \<times> gmp_poly) nres" where
  "ethorner_count_trunc_result_mop_monadic st \<equiv>
    (let (st1, xs) = st in let (i, last_s, cnt, amb) = st1
     in RETURN (cnt, last_s, amb, xs))"

sepref_register "PR_CONST ethorner_count_trunc_result_mop_monadic"
  :: "(nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly \<Rightarrow> (nat \<times> int \<times> bool \<times> gmp_poly) nres"

text \<open>The outer guarded count: consumes (and frees) the truncated reversed poly,
  returns \<open>(cnt+extra_f, amb)\<close>. The boundary bit mirrors the exact kernel's
  \<open>extra_f\<close>; at the leading position the uniform threshold is 0, so "trusted iff
  nonzero" — a zero truncated lead sets \<open>amb\<close> from the start (the composed op's
  entry guard keeps the lead nonzero on the attempt path anyway).\<close>
definition poly_ethorner_count_trunc_monadic :: "gmp_poly \<Rightarrow> (nat \<times> bool) nres" where
"poly_ethorner_count_trunc_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  if len \<le> 1 then doN { (PR_CONST poly_free_monadic) xs; RETURN (0, False) }
  else doN {
    ASSERT (1 < len);
    bthr \<leftarrow> (PR_CONST snat_bitlen_monadic) len;
    ASSERT (len * bthr < max_snat LENGTH(gmp_poly_len));
    limit \<leftarrow> RETURN (len - 1);
    ASSERT (limit < length xs);
    s_last \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs limit;
    let init = ((0::nat, 0::int, 0::nat, s_last = 0), xs);
    st \<leftarrow> WHILET
      (\<lambda>st. (PR_CONST ethorner_count_trunc_cond) limit st)
      (\<lambda>st. (PR_CONST ethorner_count_trunc_body_mop_monadic) len bthr st)
      init;
    (cnt, last_s, amb, xs_final) \<leftarrow>
      (PR_CONST ethorner_count_trunc_result_mop_monadic) st;
    extra_f \<leftarrow> (if last_s \<noteq> 0 \<and> s_last \<noteq> 0 \<and> last_s \<noteq> s_last
                then RETURN (1::nat) else RETURN 0);
    ASSERT (cnt + extra_f < max_snat LENGTH(gmp_poly_len));
    final_cnt \<leftarrow> RETURN (cnt + extra_f);
    (PR_CONST poly_free_monadic) xs_final;
    RETURN (final_cnt, amb)
  }
}"

(*FASTLOOP_FREEZE_ABOVE*)
sepref_register "PR_CONST poly_ethorner_count_trunc_monadic"
  :: "gmp_poly \<Rightarrow> (nat \<times> bool) nres"

text \<open>The kernel's runtime trust test (sign and bit-length comparison), packaged as one \<open>tsign_step\<close> on the
  masked coefficient: given any \<open>bl\<close> satisfying the unconditional conjuncts of \<open>mpz_bitlen2_monadic\<close>'s
  specification (only the lower bound is used), the body's if-cascade computes the abstract step on \<open>x\<close> if the kernel
  trusts it, and on \<open>0\<close> (@{const trusted_sgn}'s \<open>None\<close>) if it does not. An unmasked form would need the upper bound
  \<open>\<bar>x\<bar> < 2 ^ bl\<close>, available only under a \<open>size_t\<close>-representability guard that an internal coefficient cannot
  discharge; the masked form needs no guard, and the invariant carries the mask (@{const tmask_state}). The
  implementation-side twin of \<open>trusted_sgn_bitlen_test_masked\<close>.\<close>
lemma tsign_step_bitlen_form_masked:
  fixes x :: int
  assumes lb: "x \<noteq> 0 \<longrightarrow> 2 ^ (bl - 1) \<le> \<bar>x\<bar>"
  shows "tsign_step (trusted_sgn len i
           (if 0 < sgn x \<or> (sgn x < 0 \<and> trunc_thresh len i < bl) then x else 0))
           (ls, cnt, amb)
    = ((if 0 < sgn x \<or> (sgn x < 0 \<and> trunc_thresh len i < bl) then sgn x else ls),
       (if (0 < sgn x \<or> (sgn x < 0 \<and> trunc_thresh len i < bl)) \<and> ls \<noteq> 0 \<and> sgn x \<noteq> ls
        then cnt + 1 else cnt),
       (amb \<or> \<not> (0 < sgn x \<or> (sgn x < 0 \<and> trunc_thresh len i < bl))))"
    \<comment> \<open>\<open>lb\<close> is object-level (\<open>\<longrightarrow>\<close>): a meta-level conditional assumption would leave a residual premise on
       \<open>[OF lb]\<close> instances, which stops them firing as rewrite rules. The object form is also the shape of
       \<open>mpz_bitlen2_monadic\<close>'s specification conjunct.\<close>
proof -
  note tst = trusted_sgn_bitlen_test_masked[OF lb[rule_format], of len i]
  show ?thesis
  proof (cases "0 < sgn x \<or> (sgn x < 0 \<and> trunc_thresh len i < bl)")
    case True
    then show ?thesis using tst by simp
  next
    case False
    then show ?thesis using tst by auto
  qed
qed

text \<open>One outer-loop body step preserves the invariant and advances \<open>i\<close> -- the
  truncated twin of @{thm [source] ethorner_count_body_pres}: same Ruffini row op,
  same finalized-coefficient fact (@{thm [source] ethorner_outer_step_nth_final}),
  with the sign accounting replaced by one guarded \<open>tsign_step\<close>.\<close>
lemma ethorner_trunc_body_pres:
  assumes len2: "2 \<le> length ys'"
    and iU: "i < length ys' - 1"
    and cU: "cnt < 2"
    and lenxs: "length xs = length ys'"
    and xseq: "xs = ethorner_outer_step_fun i ys'"
    and steq: "tmask_state ys' amb0 (ls, cnt, amb) i"
    and bound: "length ys' + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length ys' * nat_bitlen (length ys') < max_snat LENGTH(gmp_poly_len)"
  shows "ethorner_count_trunc_body_mop_monadic (length ys') (nat_bitlen (length ys'))
           ((i, ls, cnt, amb), xs)
    \<le> SPEC (\<lambda>((i', ls', cnt', amb'), xs').
          i' = Suc i \<and> i' \<le> length ys' - 1 \<and> cnt' \<le> 2 \<and> length xs' = length ys'
        \<and> xs' = ethorner_outer_step_fun i' ys'
        \<and> tmask_state ys' amb0 (ls', cnt', amb') i')"
proof -
  let ?len = "length ys'"
  let ?T = "taylor_shift_list 1 ys'"
  let ?os = "ethorner_outer_step_fun i ys'"
  have iL: "i < ?len" using iU by simp
  have iLT: "i < length ?T" using iL by simp
  have row: "ethorner_row_fun i ?os = ethorner_outer_step_fun (Suc i) ys'" by simp
  have val_i: "ethorner_row_fun i ?os ! i = ?T ! i"
    using row ethorner_outer_step_nth_final[OF iL] by simp
  \<comment> \<open>the invariant's mask witness at \<open>i\<close>; the step extends it by ONE entry, which is
     the true coefficient when the kernel trusts it and \<open>0\<close> when it does not\<close>
  obtain zs where zs: "length zs = i"
    "\<forall>j<i. zs ! j = 0 \<or> zs ! j = ?T ! j"
    "(ls, cnt, amb) = tsign_fold_idx ?len 0 zs (0, 0, amb0)"
    using steq unfolding tmask_state_def by blast
  have take_step: "\<And>v. tsign_fold_idx ?len 0 (zs @ [v]) (0, 0, amb0)
      = tsign_step (trusted_sgn ?len i v) (ls, cnt, amb)"
    using tsign_fold_idx_append[of ?len 0 zs _ "(0, 0, amb0)"] zs(1,3) by simp
  show ?thesis
    unfolding ethorner_count_trunc_body_mop_monadic_def poly_coeff_sgn_monadic_def
      poly_coeff_bitlen2_monadic_def mpz_bitlen2_monadic_def PR_CONST_def Let_def
    apply (refine_vcg poly_ethorner_inner_loop_monadic_row[THEN order_trans])
    \<comment> \<open>15 goals (shapes read off the goal state, banner rule 3): 1-9 side conditions,
       10-15 the six post conjuncts; goal 15 (the mask invariant) closes by EXTENDING
       the invariant's mask witness by one entry (the append fold split, as
       \<open>take_step\<close>) and rewriting that step via @{thm [source]
       tsign_step_bitlen_form_masked} (its lower-bound premise discharged from the SPEC
       conjuncts) with @{thm [source] ethorner_outer_step_nth_final} (as \<open>val_i\<close>)
       bridging the row coefficient to the shifted coefficient.\<close>
    subgoal using lenxs by auto                                   \<comment> \<open>1: length\<close>
    subgoal using len2 by simp                                    \<comment> \<open>2: 1 < len\<close>
    subgoal using iU by (auto simp: less_diff_conv)               \<comment> \<open>3: i+1 < len\<close>
    subgoal using cU by auto                                      \<comment> \<open>4: cnt < 2\<close>
    subgoal using lenxs bound by auto                             \<comment> \<open>5: snat headroom\<close>
    subgoal using pbound by simp                                  \<comment> \<open>6: product headroom\<close>
    subgoal using len2 by simp                                    \<comment> \<open>7: 2 \<le> len\<close>
    subgoal using iL by auto                                      \<comment> \<open>8: i < len\<close>
    subgoal using iL lenxs by auto                                \<comment> \<open>9: i < length row\<close>
    \<comment> \<open>post conjuncts 1-6: the premises carry the returned tuple with its huge
       if-conditions -- every touch goes through OPAQUE decomposition
       (\<open>metis prod.inject\<close>, or \<open>define\<close>+\<open>folded\<close> to name the if-terms) so the
       simplifier never churns on the sgn/bitlen arithmetic inside them\<close>
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have "aa = i" using prems(1,2) by simp
      moreover have "x1a = aa + 1" using prems(17) p18 by simp
      ultimately show ?thesis by linarith
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have "x1a = aa + 1" using prems(17) p18 by simp
      then show ?thesis using prems(7) by linarith
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have "x1c = (if C \<and> ab \<noteq> 0 \<and> sgn v \<noteq> ab then ac + 1 else ac)"
        using prems(15,16,17) p18 by simp
      then have "x1c = ac \<or> x1c = ac + 1" by simp
      then show ?thesis using prems(8) by auto
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have "x2c = ethorner_row_fun aa b" using p18 by simp
      then show ?thesis using prems(5) by simp
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have eq0: "aa = i" "b = xs" using prems(1,2) by auto
      have x2ceq: "x2c = ethorner_row_fun aa b" using p18 by simp
      have "x1a = aa + 1" using prems(17) p18 by simp
      then have sucform: "x1a = Suc aa" by linarith
      show ?thesis
        unfolding sucform using x2ceq xseq eq0 by simp
    qed
    \<comment> \<open>the money goal: name the coefficient and the trust condition, decompose the
       tuple opaquely, then extend the mask witness by \<open>w\<close> (the coefficient when the
       kernel trusts it, \<open>0\<close> when it does not) via \<open>take_step\<close> and the guarded step via
       @{thm [source] tsign_step_bitlen_form_masked}, bridging the row coefficient to
       the shifted coefficient via \<open>val_i\<close>\<close>
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      have eq0: "aa = i" "ab = ls" "ac = cnt" "bc = amb" "b = xs"
        using prems(1,2,3,4) by auto
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have x1aeq: "x1a = aa + 1" using prems(17) p18 by simp
      have comps: "x1b = (if C then sgn v else ab)"
        "x1c = (if C \<and> ab \<noteq> 0 \<and> sgn v \<noteq> ab then ac + 1 else ac)"
        "x2b = (bc \<or> \<not> C)"
        using prems(15,16,17) p18 by simp_all
      have veq: "v = taylor_shift_list 1 ys' ! i"
        unfolding v_def using eq0 xseq val_i by simp
      have lb: "taylor_shift_list 1 ys' ! i \<noteq> 0 \<longrightarrow>
                 2 ^ (x - 1) \<le> \<bar>taylor_shift_list 1 ys' ! i\<bar>"
        using prems(14)[folded v_def] veq by auto
      have suci: "Suc i = i + 1" by linarith
      have thr: "min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys')
          = trunc_thresh (length ys') i"
        unfolding trunc_thresh_def by (simp only: suci eq0(1))
      have Ceq: "C = (0 < sgn (taylor_shift_list 1 ys' ! i)
          \<or> sgn (taylor_shift_list 1 ys' ! i) < 0 \<and> trunc_thresh (length ys') i < x)"
        unfolding C_def veq thr ..
      \<comment> \<open>the extended mask witness: the true coefficient when trusted, \<open>0\<close> when not\<close>
      define w where "w = (if C then taylor_shift_list 1 ys' ! i else 0)"
      have wform: "w = (if 0 < sgn (taylor_shift_list 1 ys' ! i)
             \<or> sgn (taylor_shift_list 1 ys' ! i) < 0
               \<and> trunc_thresh (length ys') i < x then taylor_shift_list 1 ys' ! i else 0)"
        unfolding w_def Ceq ..
      have fold_eq: "tsign_fold_idx (length ys') 0 (zs @ [w]) (0, 0, amb0)
          = ((if C then sgn v else ls),
             (if C \<and> ls \<noteq> 0 \<and> sgn v \<noteq> ls then cnt + 1 else cnt),
             (amb \<or> \<not> C))"
      proof -
        have "tsign_fold_idx (length ys') 0 (zs @ [w]) (0, 0, amb0)
            = tsign_step (trusted_sgn (length ys') i w) (ls, cnt, amb)"
          using take_step[of w] .
        also have "\<dots> = ((if C then sgn (taylor_shift_list 1 ys' ! i) else ls),
             (if C \<and> ls \<noteq> 0 \<and> sgn (taylor_shift_list 1 ys' ! i) \<noteq> ls then cnt + 1 else cnt),
             (amb \<or> \<not> C))"
          unfolding w_def Ceq
          by (rule tsign_step_bitlen_form_masked[OF lb])
        finally show ?thesis unfolding veq .
      qed
      have lenzsw: "length (zs @ [w]) = Suc i" using zs(1) by simp
      have maskzsw: "\<forall>j<Suc i. (zs @ [w]) ! j = 0 \<or> (zs @ [w]) ! j = taylor_shift_list 1 ys' ! j"
      proof (intro allI impI)
        fix j assume j: "j < Suc i"
        show "(zs @ [w]) ! j = 0 \<or> (zs @ [w]) ! j = taylor_shift_list 1 ys' ! j"
        proof (cases "j < i")
          case True
          then have "(zs @ [w]) ! j = zs ! j" using zs(1) by (simp add: nth_append)
          then show ?thesis using zs(2) True by simp
        next
          case False
          then have ji: "j = i" using j by simp
          have "(zs @ [w]) ! j = w" using zs(1) ji by (simp add: nth_append)
          then show ?thesis unfolding w_def ji by simp
        qed
      qed
      have mstate: "tmask_state ys' amb0
          ((if C then sgn v else ls),
           (if C \<and> ls \<noteq> 0 \<and> sgn v \<noteq> ls then cnt + 1 else cnt),
           (amb \<or> \<not> C)) (Suc i)"
        unfolding tmask_state_def
        by (rule exI[where x="zs @ [w]"]) (simp add: zs(1) lenzsw maskzsw fold_eq)
      show ?thesis
        unfolding comps eq0(2) eq0(3) eq0(4) x1aeq eq0(1)
        using mstate[unfolded suci] by simp
    qed
    done
qed

text \<open>Exit lemma: loop exit (full scan OR early abort) plus the boundary \<open>extra_f\<close>
  step yields the classify facts, via the spec theory's boundary-split, prefix-bound
  and count-transfer machinery. Packaged with the boundary bit as the literal
  if-expression so the keystone-style goals match after their own \<open>extra_f\<close>
  hypothesis collapses the \<open>if\<close>.\<close>
lemma ethorner_trunc_post:
  assumes ys'eq: "ys' = trunc_list t ys"
    and l2: "Suc 0 < length ys'"
    and iinv: "i \<le> length ys' - 1"
    and cle: "cnt \<le> 2"
    and steq: "tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ls, cnt, amb) i"
    and exit: "\<not> (i < length ys' - 1 \<and> cnt < 2)"
    and efeq: "ef = (if ls \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
                      \<and> ls \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else (0::nat))"
  shows "(2 \<le> cnt + ef \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
         (\<not> amb \<longrightarrow>
            (cnt + ef = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0) \<and>
            (cnt + ef = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1) \<and>
            (2 \<le> cnt + ef) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys)))"
proof -
  define len' where "len' = length ys'"
  define T where "T = taylor_shift_list 1 ys'"
  define amb0 where "amb0 = (sgn (ys' ! (len' - 1)) = 0)"
  have lenT: "length T = len'" by (simp add: T_def len'_def)
  have len'ys: "len' = length ys" using ys'eq by (simp add: len'_def)
  have Tys: "T = taylor_shift_list 1 (trunc_list t ys)" using ys'eq by (simp add: T_def)
  have tc_target: "trunc_changes (length ys) (taylor_shift_list 1 (trunc_list t ys))
      = trunc_changes len' T" using len'ys Tys by simp
  have mstate: "tmask_state ys' amb0 (ls, cnt, amb) i"
    using steq by (simp add: len'_def amb0_def)
  from exit iinv consider (full) "i = len' - 1" | (abort) "2 \<le> cnt"
    by (auto simp: len'_def)
  then show ?thesis
  proof cases
    case full
    have ysne: "ys' \<noteq> []" using l2 by (cases ys') auto
    have Tne: "T \<noteq> []" using lenT l2 by (auto simp: len'_def)
    have tbutl: "take i T = butlast T"
      using full lenT by (simp add: butlast_conv_take)
    have lastT: "last T = ys' ! (len' - 1)"
      using last_taylor_shift_list[of ys' 1] ysne last_conv_nth[OF ysne]
      by (simp add: T_def len'_def)
    have lastTnth: "last T = T ! (len' - 1)"
      using lenT Tne by (simp add: last_conv_nth)
    have tsl: "trusted_sgn len' (len' - 1) (last T)
        = (if ys' ! (len' - 1) = 0 then None else Some (sgn (ys' ! (len' - 1))))"
      using trusted_sgn_last[of len' "last T"] lastT by simp
    \<comment> \<open>count soundness (usable WITH ambiguity): the invariant's mask, extended by the
       boundary coefficient, is a mask of the whole shifted-truncated list, so the
       boundary-inclusive count \<open>cnt + ef\<close> never exceeds the true count\<close>
    obtain zs where zs: "length zs = i"
      "\<forall>j<i. zs ! j = 0 \<or> zs ! j = T ! j"
      "(ls, cnt, amb) = tsign_fold_idx len' 0 zs (0, 0, amb0)"
      using mstate unfolding tmask_state_def T_def len'_def by blast
    have ws_fold: "tsign_fold_idx len' 0 (zs @ [last T]) (0, 0, amb0)
        = tsign_step (trusted_sgn len' (len' - 1) (last T)) (ls, cnt, amb)"
      using tsign_fold_idx_append[of len' 0 zs "[last T]" "(0, 0, amb0)"] zs(1,3) full by simp
    have ws_cnt: "(\<lambda>(a, b, c). b) (tsign_fold_idx len' 0 (zs @ [last T]) (0, 0, amb0))
        = cnt + ef"
    proof (cases "ys' ! (len' - 1) = 0")
      case True
      then have "ef = 0" using efeq by (simp add: len'_def)
      then show ?thesis unfolding ws_fold using tsl True by simp
    next
      case False
      have sgnne: "sgn (ys' ! (len' - 1)) \<noteq> 0" using False by (simp add: sgn_eq_0_iff)
      have "ef = (if ls \<noteq> 0 \<and> sgn (ys' ! (len' - 1)) \<noteq> ls then 1 else 0)"
        using efeq sgnne by (auto simp: len'_def)
      then show ?thesis unfolding ws_fold using tsl False by simp
    qed
    have ws_len: "length (zs @ [last T]) = length ys"
      using zs(1) full lenT l2 len'ys by (simp add: len'_def)
    have ws_mask: "\<forall>j<length (zs @ [last T]).
        (zs @ [last T]) ! j = 0 \<or> (zs @ [last T]) ! j = taylor_shift_list 1 (trunc_list t ys) ! j"
    proof (intro allI impI)
      fix j assume j: "j < length (zs @ [last T])"
      then have ji: "j \<le> i" using zs(1) by simp
      show "(zs @ [last T]) ! j = 0 \<or> (zs @ [last T]) ! j = taylor_shift_list 1 (trunc_list t ys) ! j"
      proof (cases "j < i")
        case True
        then have "(zs @ [last T]) ! j = zs ! j" using zs(1) by (simp add: nth_append)
        then show ?thesis using zs(2) True Tys by simp
      next
        case False
        then have jeq: "j = i" using ji by simp
        have "(zs @ [last T]) ! j = last T" using zs(1) jeq by (simp add: nth_append)
        then show ?thesis using lastTnth full jeq Tys by simp
      qed
    qed
    have ge2: "2 \<le> cnt + ef \<Longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)"
    proof -
      assume a2: "2 \<le> cnt + ef"
      have "(\<lambda>(a, b, c). b) (tsign_fold_idx (length ys) 0 (zs @ [last T]) (0, 0, amb0))
          \<le> sign_changes_fold (taylor_shift_list 1 ys)"
        using tsign_mask_cnt_le_full[OF ws_len ws_mask, of amb0] .
      then have "cnt + ef \<le> sign_changes_fold (taylor_shift_list 1 ys)"
        using ws_cnt len'ys by (simp add: len'_def)
      then show ?thesis using a2 by simp
    qed
    \<comment> \<open>the decisive case: \<open>\<not>amb\<close> forces the mask to be TRIVIAL, so the exact transfer
       runs on the UNMASKED prefix fold, which is the very fold the trivial mask denotes\<close>
    have exact_eq: "\<not> amb \<Longrightarrow> cnt + ef = sign_changes_fold (taylor_shift_list 1 ys)"
    proof -
      assume noamb: "\<not> amb"
      have ile: "i \<le> length ys'" using iinv by simp
      have kstate: "(ls, cnt, amb) = tsign_fold_idx len' 0 (butlast T) (0, 0, amb0)"
        using tmask_state_not_amb[OF mstate noamb ile] tbutl by (simp add: len'_def T_def)
      obtain lsF cntF ambF where F:
        "tsign_fold_idx len' 0 (butlast T) (0, 0, False) = (lsF, cntF, ambF)"
        by (cases "tsign_fold_idx len' 0 (butlast T) (0, 0, False)") auto
      have fs: "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx len' 0 (butlast T) (0, 0, amb0))
          = (\<lambda>(a, b, c). (a, b)) (tsign_fold_idx len' 0 (butlast T) (0, 0, False))"
        by (rule tsign_fold_idx_fst_snd_cong) simp
      have "(ls, cnt) = (lsF, cntF)"
        using arg_cong[OF kstate, of "\<lambda>(a, b, c). (a, b)"] fs F by simp
      then have lseq: "ls = lsF" and cnteq: "cnt = cntF" by auto
      have "amb = (\<lambda>(a, b, c). c) (tsign_fold_idx len' 0 (butlast T) (0, 0, amb0))"
        using arg_cong[OF kstate, of "\<lambda>(a, b, c). c"] by simp
      also have "\<dots> = (amb0 \<or> (\<lambda>(a, b, c). c) (tsign_fold_idx len' 0 (butlast T) (0, 0, False)))"
        by (rule tsign_fold_idx_amb_or)
      also have "\<dots> = (amb0 \<or> ambF)" using F by simp
      finally have ambeq: "amb = (amb0 \<or> ambF)" .
      have tc: "trunc_changes len' T
          = (case tsign_step (trusted_sgn len' (len' - 1) (last T)) (lsF, cntF, ambF)
             of (_, c, a) \<Rightarrow> (c, a))"
        using trunc_changes_split_last[OF Tne, of len'] F lenT by simp
      have main: "trunc_changes len' T = (cnt + ef, amb)"
      proof (cases "ys' ! (len' - 1) = 0")
        case True
        then have "trunc_changes len' T = (cntF, True)"
          using tc tsl by simp
        moreover have "ef = 0" using efeq True by (simp add: len'_def)
        moreover have "amb0 = True" using amb0_def True by simp
        ultimately show ?thesis using cnteq ambeq by simp
      next
        case False
        then have step: "tsign_step (trusted_sgn len' (len' - 1) (last T)) (lsF, cntF, ambF)
            = (sgn (ys' ! (len' - 1)),
               (if lsF \<noteq> 0 \<and> sgn (ys' ! (len' - 1)) \<noteq> lsF then cntF + 1 else cntF), ambF)"
          using tsl by simp
        have sgnne: "sgn (ys' ! (len' - 1)) \<noteq> 0" using False by (simp add: sgn_eq_0_iff)
        have "ef = (if lsF \<noteq> 0 \<and> sgn (ys' ! (len' - 1)) \<noteq> lsF then 1 else 0)"
          using efeq lseq sgnne by (auto simp: len'_def)
        moreover have "amb0 = False" using amb0_def False by (simp add: sgn_eq_0_iff)
        ultimately show ?thesis using tc step cnteq ambeq by simp
      qed
      have main': "trunc_changes (length ys) (taylor_shift_list 1 (trunc_list t ys))
          = (cnt + ef, amb)"
        using main tc_target by simp
      show "cnt + ef = sign_changes_fold (taylor_shift_list 1 ys)"
        using trunc_changes_decisive_exact[of ys t] main' noamb by simp
    qed
    show ?thesis using ge2 exact_eq by auto
  next
    case abort
    have ile: "i \<le> length ys" using iinv len'ys by (simp add: len'_def)
    have t2: "2 \<le> sign_changes_fold (taylor_shift_list 1 ys)"
      using tmask_state_cnt_le[OF mstate ys'eq ile] abort by simp
    have cef2: "2 \<le> cnt + ef" using abort by simp
    show ?thesis
    proof (intro conjI impI)
      show "2 \<le> cnt + ef \<Longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)"
        using t2 by simp
      show "\<not> amb \<Longrightarrow> (cnt + ef = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0)"
        using cef2 t2 by auto
      show "\<not> amb \<Longrightarrow> (cnt + ef = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1)"
        using cef2 t2 by auto
      show "\<not> amb \<Longrightarrow> (2 \<le> cnt + ef) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys))"
        using cef2 t2 by auto
    qed
  qed
qed

text \<open>The main proof: mirror the exact keystone
  @{thm [source] poly_ethorner_count_monadic_classify}'s WHILET-invariant architecture
  (rows via \<open>ethorner_row_fun\<close>), with the sign-accounting invariant "cnt =
  trusted-subsequence changes of the finalized prefix, amb = ambiguity seen, last_s =
  last trusted sign", discharged against \<open>Count_Spec\<close>. Note the trichotomy
  holds in BOTH decisive cases: \<open>\<not>amb\<close> (full scan, exact transfer) and \<open>2 \<le> cnt\<close>
  (early abort; \<open>2 \<le> t*\<close> makes the 0/1 clauses vacuous).\<close>
lemma poly_ethorner_count_trunc_monadic_classify:
  assumes ys'eq: "ys' = trunc_list t ys"
    and lbound: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length ys * nat_bitlen (length ys) < max_snat LENGTH(gmp_poly_len)"
  shows "poly_ethorner_count_trunc_monadic ys' \<le> SPEC (\<lambda>(cnt, amb).
    (2 \<le> cnt \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
    (\<not> amb \<longrightarrow>
       (cnt = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0) \<and>
       (cnt = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1) \<and>
       (2 \<le> cnt) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys))))"
proof -
  have lenys': "length ys' = length ys" using ys'eq by simp
  have lb': "length ys' + 1 < max_snat LENGTH(gmp_poly_len)"
    using lbound lenys' by simp
  have pb': "length ys' * nat_bitlen (length ys') < max_snat LENGTH(gmp_poly_len)"
    using pbound lenys' by simp
  have snatlen: "length ys' < max_snat LENGTH(gmp_poly_len)" using lb' by simp
  show ?thesis
    unfolding poly_ethorner_count_trunc_monadic_def ethorner_count_trunc_cond_def
      ethorner_count_trunc_result_mop_monadic_def poly_length_monadic_def
      poly_coeff_sgn_monadic_def PR_CONST_def Let_def
    apply (refine_vcg snat_bitlen_monadic_correct[THEN order_trans]
        WHILET_rule[where
          R="measure (\<lambda>((i, ls, cnt, amb), xsl :: int list). length ys' - 1 - i)"
          and I="\<lambda>((i, ls, cnt, amb), xsl).
               i \<le> length ys' - 1 \<and> cnt \<le> 2 \<and> length xsl = length ys'
             \<and> xsl = ethorner_outer_step_fun i ys'
             \<and> tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ls, cnt, amb) i"])
    apply (simp_all add: snatlen pb' tmask_state_init)
    \<comment> \<open>goals 1-3: the \<open>length ys' \<le> 1\<close> short-circuit -- bridge to \<open>ys\<close> via
       @{thm [source] lenys'} then @{thm [source] scf_taylor_short}\<close>
    subgoal using lenys' scf_taylor_short[of ys] by simp
    subgoal using lenys' scf_taylor_short[of ys] by simp
    subgoal using lenys' scf_taylor_short[of ys] by simp
    \<comment> \<open>goals 4-5: pure \<open>ys'\<close> headroom facts\<close>
    subgoal using snatlen by simp
    subgoal using pb' by simp
    \<comment> \<open>goal: the loop BODY -- destructure the atomic state so
       @{thm [source] ethorner_trunc_body_pres} unifies\<close>
    subgoal premises prems for s
    proof -
      obtain i ls cnt amb xsl where seq: "s = ((i, ls, cnt, amb), xsl)"
        by (metis prod.collapse)
      show ?thesis
        using prems
        unfolding seq
        apply (refine_vcg ethorner_trunc_body_pres)
        using pb' lb' by (auto simp: seq One_nat_def split: prod.splits)
    qed
    \<comment> \<open>the remaining ~10 goals: two \<open>result-fits-snat\<close> side conditions and six
       classify conjuncts (three per boundary branch). Discharged uniformly: feed
       @{thm [source] ethorner_trunc_post}'s full conjunction (its \<open>ef\<close> instantiated
       to the goal's own boundary if-expression via \<open>refl\<close>, so it specializes to
       whichever branch this goal is already split into) plus the small-nat/max_snat
       fact, to \<open>auto\<close> against ALL local premises.\<close>
    subgoal premises prems
      using prems small_lt_max_snat by auto
    subgoal premises prems for s a b aa ba ab bb ac bc bd be af
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> ac \<le> 2 \<and> length b = length ys' \<and>
          tmask_state ys' False (ab, ac, bc) aa"
        using prems(3) by (simp add: One_nat_def)
      have bnd: "ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1))"
        using prems(12) by (simp add: One_nat_def)
      have amb0eq: "(sgn (ys' ! (length ys' - 1)) = 0) = False"
        using bnd by simp
      have steq: "tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, bc) aa"
        using conj amb0eq by simp
      have exit: "\<not> (aa < length ys' - 1 \<and> ac < 2)"
        using prems(4) conj by (auto simp: One_nat_def)
      have efeq: "1 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else 0)"
        using bnd by simp
      have main: "(2 \<le> ac + 1 \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> bc \<longrightarrow>
           (ac + 1 = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0) \<and>
           (ac + 1 = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1) \<and>
           (2 \<le> ac + 1) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys)))"
        using ethorner_trunc_post[OF ys'eq prems(1) conj[THEN conjunct1] conj[THEN conjunct2, THEN conjunct1]
            steq exit efeq] by simp
      show ?thesis using main prems(15) by (simp add: One_nat_def)
    qed
    \<comment> \<open>goals 1-3: ef=1 boundary, amb0 already collapsed to \<open>False\<close> by simp using the
       boundary's own \<open>sgn\<noteq>0\<close> conjunct (same bridging as the goal above)\<close>
    subgoal premises prems for s a aa ba ab bb ac bc bd be af x2
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> ac \<le> 2 \<and>
          tmask_state ys' False (ab, ac, False) aa"
        using prems(3) by (simp add: One_nat_def)
      have bnd: "ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1))"
        using prems(12) by (simp add: One_nat_def)
      have amb0eq: "(sgn (ys' ! (length ys' - 1)) = 0) = False" using bnd by simp
      have steq: "tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, False) aa"
        using conj amb0eq by simp
      have exit: "\<not> (aa < length ys' - 1 \<and> ac < 2)"
        using prems(4) conj by (auto simp: One_nat_def)
      have efeq: "1 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else 0)"
        using bnd by simp
      have main: "(2 \<le> ac + 1 \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> False \<longrightarrow>
           (ac + 1 = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0) \<and>
           (ac + 1 = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1) \<and>
           (2 \<le> ac + 1) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys)))"
        using ethorner_trunc_post[OF ys'eq prems(1) conj[THEN conjunct1] conj[THEN conjunct2, THEN conjunct1]
            steq exit efeq] by simp
      show ?thesis using main by simp
    qed
    subgoal premises prems for s a aa ba ab bb ac bc bd be af x2
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> ac \<le> 2 \<and>
          tmask_state ys' False (ab, ac, False) aa"
        using prems(3) by (simp add: One_nat_def)
      have bnd: "ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1))"
        using prems(12) by (simp add: One_nat_def)
      have amb0eq: "(sgn (ys' ! (length ys' - 1)) = 0) = False" using bnd by simp
      have steq: "tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, False) aa"
        using conj amb0eq by simp
      have exit: "\<not> (aa < length ys' - 1 \<and> ac < 2)"
        using prems(4) conj by (auto simp: One_nat_def)
      have efeq: "1 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else 0)"
        using bnd by simp
      have main: "(2 \<le> ac + 1 \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> False \<longrightarrow>
           (ac + 1 = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0) \<and>
           (ac + 1 = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1) \<and>
           (2 \<le> ac + 1) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys)))"
        using ethorner_trunc_post[OF ys'eq prems(1) conj[THEN conjunct1] conj[THEN conjunct2, THEN conjunct1]
            steq exit efeq] by simp
      show ?thesis using main by presburger
    qed
    subgoal premises prems for s a aa ba ab bb ac bc bd be af x2
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> ac \<le> 2 \<and>
          tmask_state ys' False (ab, ac, False) aa"
        using prems(3) by (simp add: One_nat_def)
      have bnd: "ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1))"
        using prems(12) by (simp add: One_nat_def)
      have amb0eq: "(sgn (ys' ! (length ys' - 1)) = 0) = False" using bnd by simp
      have steq: "tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, False) aa"
        using conj amb0eq by simp
      have exit: "\<not> (aa < length ys' - 1 \<and> ac < 2)"
        using prems(4) conj by (auto simp: One_nat_def)
      have efeq: "1 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else 0)"
        using bnd by simp
      have main: "(2 \<le> ac + 1 \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> False \<longrightarrow>
           (ac + 1 = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0) \<and>
           (ac + 1 = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1) \<and>
           (2 \<le> ac + 1) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys)))"
        using ethorner_trunc_post[OF ys'eq prems(1) conj[THEN conjunct1] conj[THEN conjunct2, THEN conjunct1]
            steq exit efeq] by simp
      show ?thesis using main by presburger
    qed
    \<comment> \<open>goals 4-5: max_snat side conditions for the ef=0 boundary (goal 5's \<open>ac\<close> is
       already the literal \<open>2\<close> -- the early-abort sub-case)\<close>
    subgoal premises prems for s a b aa ba ab bb ac bc bd be
      using prems(3) small_lt_max_snat by auto
    subgoal premises prems for s a b aa ba ab bb bc ad bd be
    proof -
      have conj: "aa \<le> length ys' - 1 \<and>
          tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, 2, bc) aa"
        using prems(3) by (simp add: One_nat_def)
      have exit: "\<not> (aa < length ys' - 1 \<and> (2::nat) < 2)"
        by simp
      have efeq: "0 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else (0::nat))"
        using prems by (simp add: One_nat_def)
      have main: "2 \<le> (2::nat) + 0 \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)"
        using ethorner_trunc_post[OF ys'eq prems(1) conj[THEN conjunct1] le_refl
            conj[THEN conjunct2] exit efeq] by simp
      show ?thesis using main by simp
    qed
    \<comment> \<open>goals 6-8: ef=0 boundary, amb0 stays SYMBOLIC (the boundary condition here is
       \<open>ab=0\<or>sgn=0\<or>ab=sgn\<close>, which does not establish \<open>sgn\<noteq>0\<close>, so no collapse) but
       \<open>amb\<close> (the fold's own output) is known \<open>False\<close> from the \<open>\<not>bc\<close> split\<close>
    subgoal premises prems for s a aa ba ab bb ac bc bd be af x2
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> ac \<le> 2 \<and>
          tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, False) aa"
        using prems(3) by (simp add: One_nat_def)
      have exit: "\<not> (aa < length ys' - 1 \<and> ac < 2)"
        using prems(4) conj by (auto simp: One_nat_def)
      have efeq: "0 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else (0::nat))"
        using prems(12) by (auto simp: One_nat_def)
      have main: "(2 \<le> ac + 0 \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> False \<longrightarrow>
           (ac + 0 = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0) \<and>
           (ac + 0 = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1) \<and>
           (2 \<le> ac + 0) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys)))"
        using ethorner_trunc_post[OF ys'eq prems(1) conj[THEN conjunct1] conj[THEN conjunct2, THEN conjunct1]
            conj[THEN conjunct2, THEN conjunct2] exit efeq] by simp
      show ?thesis using main by simp
    qed
    subgoal premises prems for s a aa ba ab bb ac bc bd be af x2
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> ac \<le> 2 \<and>
          tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, False) aa"
        using prems(3) by (simp add: One_nat_def)
      have exit: "\<not> (aa < length ys' - 1 \<and> ac < 2)"
        using prems(4) conj by (auto simp: One_nat_def)
      have efeq: "0 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else (0::nat))"
        using prems(12) by (auto simp: One_nat_def)
      have main: "(2 \<le> ac + 0 \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> False \<longrightarrow>
           (ac + 0 = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0) \<and>
           (ac + 0 = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1) \<and>
           (2 \<le> ac + 0) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys)))"
        using ethorner_trunc_post[OF ys'eq prems(1) conj[THEN conjunct1] conj[THEN conjunct2, THEN conjunct1]
            conj[THEN conjunct2, THEN conjunct2] exit efeq] by simp
      show ?thesis using main by simp
    qed
    subgoal premises prems for s a aa ba ab bb ac bc bd be af x2
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> ac \<le> 2 \<and>
          tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, False) aa"
        using prems(3) by (simp add: One_nat_def)
      have exit: "\<not> (aa < length ys' - 1 \<and> ac < 2)"
        using prems(4) conj by (auto simp: One_nat_def)
      have efeq: "0 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else (0::nat))"
        using prems(12) by (auto simp: One_nat_def)
      have main: "(2 \<le> ac + 0 \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> False \<longrightarrow>
           (ac + 0 = 0) = (sign_changes_fold (taylor_shift_list 1 ys) = 0) \<and>
           (ac + 0 = 1) = (sign_changes_fold (taylor_shift_list 1 ys) = 1) \<and>
           (2 \<le> ac + 0) = (2 \<le> sign_changes_fold (taylor_shift_list 1 ys)))"
        using ethorner_trunc_post[OF ys'eq prems(1) conj[THEN conjunct1] conj[THEN conjunct2, THEN conjunct1]
            conj[THEN conjunct2, THEN conjunct2] exit efeq] by simp
      show ?thesis using main by presburger
    qed
    done
qed

section \<open>The composed dual-path count (the drop-in sibling)\<close>

text \<open>Tuning knob: extra kept bits beyond msolve's \<open>2*len\<close>. It affects only performance.\<close>
definition trunc_count_margin :: nat where
  "trunc_count_margin = 0"

text \<open>The \<open>O(1)\<close> budget read: the reversed-lead coefficient (the original constant term) carries the maximal
  homothety scaling \<open>2^(depth * deg)\<close> on dyadic carried bisection children, so its bit length tracks the maximum bit
  length in the deep regime where truncation pays, and it is read anyway for the lead-survival test. It returns the raw
  \<open>unat\<close> bit length (for the survival test) with its clamped \<open>snat\<close> twin (for the guard and budget arithmetic), in
  place of an \<open>O(deg)\<close> @{const poly_max_bitlen_monadic} scan.\<close>
definition lead_budget_mop :: "gmp_poly \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) nres" where
"lead_budget_mop xs i \<equiv> doN {
  ASSERT (i < length xs);
  bl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs i;
  top \<leftarrow> RETURN (PR_CONST (trunc_max_snat_incl TYPE(gmp_poly_len)));
  topu \<leftarrow> RETURN (op_snat_unat_conv top);
  if topu \<le> bl then RETURN (bl, top)
  else doN {
    ASSERT (bl < max_snat LENGTH(gmp_poly_len));
    bls \<leftarrow> RETURN (op_unat_snat_conv bl);
    RETURN (bl, bls)
  }
}"

sepref_register "PR_CONST lead_budget_mop" :: "gmp_poly \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) nres"

text \<open>Nofail-only, mirroring @{thm [source] poly_max_bitlen_monadic_nofail}: the budget \<open>nb\<close> is
  perf-only per design point D-e (a wrong/clamped value costs performance, never
  correctness), so the classify needs only totality here, not a value spec.\<close>
lemma lead_budget_mop_nofail:
  assumes "i < length xs"
  shows "lead_budget_mop xs i \<le> SPEC (\<lambda>_. True)"
  unfolding lead_budget_mop_def poly_coeff_bitlen2_monadic_def mpz_bitlen2_monadic_def
    PR_CONST_def
  using assms by (auto simp: pw_le_iff refine_pw_simps max_snat_def)

subsection \<open>The \<open>(0,\<infinity>)\<close> prune\<close>

text \<open>\<^bold>\<open>What it provides.\<close> \<open>sign_changes xs = 0\<close> on the untransformed node polynomial certifies
  \<open>carried_descartes_count xs = 0\<close>, so the truncated-count path (reverse copy, lead budget, truncation, ET-Horner) can
  be skipped.

  \<^bold>\<open>The argument\<close> is elementary and involves no \<open>poly\<close>, no real root and not Descartes' rule:
  \<open>ruffini_step c a (q # qs) = (a + c * q) # ruffini_step c q qs\<close> only adds and multiplies by \<open>c\<close>, so a positive shift
  preserves a uniform coefficient sign. The names carry the \<open>prune_\<close> prefix.\<close>

lemma prune_remdups_adj_const_le1:
  assumes "\<And>y. y \<in> set ys \<Longrightarrow> y = c"
  shows "length (remdups_adj ys) \<le> 1"
  using assms by (induction ys rule: remdups_adj.induct) auto

lemma prune_sign_changes_uniform_zero:
  fixes xs :: "'a :: linordered_idom list"
  assumes "\<And>y. y \<in> set (filter (\<lambda>x. x \<noteq> 0) (map sgn xs)) \<Longrightarrow> y = s"
  shows "sign_changes xs = 0"
  using prune_remdups_adj_const_le1[where ys = "filter (\<lambda>x. x \<noteq> 0) (map sgn xs)" and c = s, OF assms]
  unfolding sign_changes_def by simp

lemma prune_sign_changes_nonneg_zero:
  fixes xs :: "'a :: linordered_idom list"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> 0 \<le> x"
  shows "sign_changes xs = 0"
proof (rule prune_sign_changes_uniform_zero[where s = 1])
  fix y assume "y \<in> set (filter (\<lambda>x. x \<noteq> 0) (map sgn xs))"
  then obtain x where x: "x \<in> set xs" "y = sgn x" "sgn x \<noteq> 0" by auto
  with assms have "0 \<le> x" "x \<noteq> 0" by (auto simp: sgn_0_0)
  hence "0 < x" by (simp add: order_less_le)
  thus "y = 1" using x by simp
qed

lemma prune_sign_changes_nonpos_zero:
  fixes xs :: "'a :: linordered_idom list"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x \<le> 0"
  shows "sign_changes xs = 0"
proof (rule prune_sign_changes_uniform_zero[where s = "-1"])
  fix y assume "y \<in> set (filter (\<lambda>x. x \<noteq> 0) (map sgn xs))"
  then obtain x where x: "x \<in> set xs" "y = sgn x" "sgn x \<noteq> 0" by auto
  with assms have "x \<le> 0" "x \<noteq> 0" by (auto simp: sgn_0_0)
  hence "x < 0" by (simp add: order_less_le)
  thus "y = -1" using x by simp
qed

text \<open>\<open>0 \<le> c\<close> must be a PREMISE of the inducted statement, not an outer \<open>assumes\<close>:
  \<open>ruffini_step.induct\<close> rebinds \<open>c\<close> in every case, so an outer assumption silently refers to a
  different variable and every case goal collapses to \<open>0 \<le> c\<close>.\<close>

lemma prune_ruffini_step_nonneg:
  fixes c :: "'a :: linordered_idom"
  shows "\<lbrakk>0 \<le> c; 0 \<le> a; \<forall>x \<in> set qs. 0 \<le> x\<rbrakk>
         \<Longrightarrow> (\<forall>y \<in> set (ruffini_step c a qs). 0 \<le> y)"
proof (induction c a qs rule: ruffini_step.induct)
  case (1 c a) then show ?case by simp
next
  case (2 c a q qs)
  then show ?case by (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg)
qed

lemma prune_ruffini_step_nonpos:
  fixes c :: "'a :: linordered_idom"
  shows "\<lbrakk>0 \<le> c; a \<le> 0; \<forall>x \<in> set qs. x \<le> 0\<rbrakk>
         \<Longrightarrow> (\<forall>y \<in> set (ruffini_step c a qs). y \<le> 0)"
proof (induction c a qs rule: ruffini_step.induct)
  case (1 c a) then show ?case by simp
next
  case (2 c a q qs)
  then show ?case by (auto intro!: add_nonpos_nonpos mult_nonneg_nonpos)
qed

lemma prune_taylor_shift_list_nonneg:
  fixes c :: "'a :: linordered_idom"
  assumes c: "0 \<le> c"
  shows "(\<forall>x \<in> set xs. 0 \<le> x) \<longrightarrow> (\<forall>y \<in> set (taylor_shift_list c xs). 0 \<le> y)"
proof (induction xs)
  case Nil show ?case by simp
next
  case (Cons a as)
  show ?case
  proof
    assume A: "\<forall>x \<in> set (a # as). 0 \<le> x"
    hence hd: "0 \<le> a" by simp
    from A have "\<forall>x \<in> set as. 0 \<le> x" by simp
    with Cons.IH have inner: "\<forall>x \<in> set (taylor_shift_list c as). 0 \<le> x" by simp
    from prune_ruffini_step_nonneg[OF c hd inner]
    show "\<forall>y \<in> set (taylor_shift_list c (a # as)). 0 \<le> y" by simp
  qed
qed

lemma prune_taylor_shift_list_nonpos:
  fixes c :: "'a :: linordered_idom"
  assumes c: "0 \<le> c"
  shows "(\<forall>x \<in> set xs. x \<le> 0) \<longrightarrow> (\<forall>y \<in> set (taylor_shift_list c xs). y \<le> 0)"
proof (induction xs)
  case Nil show ?case by simp
next
  case (Cons a as)
  show ?case
  proof
    assume A: "\<forall>x \<in> set (a # as). x \<le> 0"
    hence hd: "a \<le> 0" by simp
    from A have "\<forall>x \<in> set as. x \<le> 0" by simp
    with Cons.IH have inner: "\<forall>x \<in> set (taylor_shift_list c as). x \<le> 0" by simp
    from prune_ruffini_step_nonpos[OF c hd inner]
    show "\<forall>y \<in> set (taylor_shift_list c (a # as)). y \<le> 0" by simp
  qed
qed

lemma prune_set_coeffs_Poly_subset: "set (coeffs (Poly xs)) \<subseteq> set xs"
  by (auto simp: coeffs_Poly strip_while_def dest!: set_dropWhileD)

lemma prune_sign_changes_fold_nonneg_zero:
  fixes xs :: "'a :: linordered_idom list"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> 0 \<le> x"
  shows "sign_changes_fold xs = 0"
  using assms prune_set_coeffs_Poly_subset[of xs]
  by (simp add: sign_changes_fold_Poly prune_sign_changes_nonneg_zero subset_iff)

lemma prune_sign_changes_fold_nonpos_zero:
  fixes xs :: "'a :: linordered_idom list"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x \<le> 0"
  shows "sign_changes_fold xs = 0"
  using assms prune_set_coeffs_Poly_subset[of xs]
  by (simp add: sign_changes_fold_Poly prune_sign_changes_nonpos_zero subset_iff)

lemma prune_sign_changes_zero_uniform:
  fixes xs :: "'a :: linordered_idom list"
  assumes "sign_changes xs = 0"
  shows "(\<forall>x \<in> set xs. 0 \<le> x) \<or> (\<forall>x \<in> set xs. x \<le> 0)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain p n where p: "p \<in> set xs" "p < 0" and n: "n \<in> set xs" "0 < n"
    by (auto simp: not_le)
  let ?F = "filter (\<lambda>x. x \<noteq> 0) (map sgn xs)"
  have m1: "(-1 :: 'a) \<in> set ?F" using p by force
  have p1: "(1 :: 'a) \<in> set ?F" using n by force
  have "{-1, 1} \<subseteq> set (remdups_adj ?F)"
    using m1 p1 by (simp add: remdups_adj_set)
  from card_mono[OF finite_set this] have "card {(-1 :: 'a), 1} \<le> card (set (remdups_adj ?F))" .
  hence "2 \<le> card (set (remdups_adj ?F))" by simp
  also have "card (set (remdups_adj ?F)) \<le> length (remdups_adj ?F)" by (rule card_length)
  finally have "2 \<le> length (remdups_adj ?F)" .
  with assms show False unfolding sign_changes_def by simp
qed

text \<open>\<^bold>\<open>The prune's obligation.\<close> Stated on \<open>sign_changes_fold\<close>, which is what @{const poly_sign_changes_monadic}
  returns (@{thm [source] Dsc_Taylor.sign_changes_eq_fold} bridges it to the \<open>sign_changes\<close> spelling).\<close>

lemma count_zero_of_prune_certificate:
  assumes "sign_changes_fold xs = 0"
  shows "carried_descartes_count xs = 0"
proof -
  from assms have "sign_changes xs = 0" by (simp add: sign_changes_eq_fold)
  from prune_sign_changes_zero_uniform[OF this]
  have "(\<forall>x \<in> set (rev xs). 0 \<le> x) \<or> (\<forall>x \<in> set (rev xs). x \<le> 0)" by simp
  then show ?thesis
  proof
    assume "\<forall>x \<in> set (rev xs). 0 \<le> x"
    with prune_taylor_shift_list_nonneg[of 1 "rev xs"]
    have "\<forall>y \<in> set (taylor_shift_list 1 (rev xs)). 0 \<le> y" by simp
    thus ?thesis
      unfolding carried_descartes_count_def
      by (simp add: prune_sign_changes_fold_nonneg_zero)
  next
    assume "\<forall>x \<in> set (rev xs). x \<le> 0"
    with prune_taylor_shift_list_nonpos[of 1 "rev xs"]
    have "\<forall>y \<in> set (taylor_shift_list 1 (rev xs)). y \<le> 0" by simp
    thus ?thesis
      unfolding carried_descartes_count_def
      by (simp add: prune_sign_changes_fold_nonpos_zero)
  qed
qed

text \<open>The same signature, ownership (\<open>xs\<close> borrowed) and single hypothesis as
  @{const carried_descartes_count_monadic}: every attempt condition is a runtime test (budget headroom, word headroom
  for the threshold products, lead survival), so a refused attempt or a fallback costs one truncated try, never
  correctness. The fallback re-reverses from the borrowed \<open>xs\<close>; the no-attempt branch reuses the reverse copy already
  made.

  \<^bold>\<open>The \<open>(0,\<infinity>)\<close> prune comes first.\<close> @{const poly_sign_changes_monadic} borrows \<open>xs\<close> and allocates nothing, so on a hit
  the whole path below is skipped. The operand is the caller's \<open>xs\<close>, and every call site passes an exact node
  polynomial (\<open>carried_descartes_count_g_monadic\<close>'s \<open>g = 0\<close> / \<open>2\<^sup>4\<^sup>2\<close> branches, both certified by \<open>node_frame\<close>;
  \<open>hybrid_main_list_monadic\<close>'s root, pushed with guard \<open>0\<close>; and \<open>newton_try_window_monadic\<close>'s window, built from
  \<open>hybrid_cond_escalate_monadic\<close>'s output). So the prune reads no truncated operand, and the classification below is
  not weakened.\<close>
definition carried_descartes_count_trunc_body_monadic :: "gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_trunc_body_monadic xs \<equiv> doN {
  rxs \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
  len \<leftarrow> (PR_CONST poly_length_monadic) rxs;
  ASSERT (len = length rxs);
  if len \<le> 1 then (PR_CONST poly_ethorner_count_monadic) rxs
  else doN {
    ASSERT (0 < len \<and> len - 1 < length rxs);
    (lbl, nb) \<leftarrow> (PR_CONST lead_budget_mop) rxs (len - 1);
    bthr \<leftarrow> (PR_CONST snat_bitlen_monadic) len;
    let attempt =
      (2 * len + trunc_count_margin < nb \<and>
       2 * len + trunc_count_margin < max_snat LENGTH(gmp_poly_len) \<and>
       len * bthr < max_snat LENGTH(gmp_poly_len) \<and>
       nb < max_snat LENGTH(gmp_poly_len));
    if \<not> attempt then (PR_CONST poly_ethorner_count_monadic) rxs
    else doN {
      t \<leftarrow> RETURN (nb - (2 * len + trunc_count_margin));
      if lbl \<le> t then (PR_CONST poly_ethorner_count_monadic) rxs
      else doN {
        rxs \<leftarrow> (PR_CONST poly_trunc_in_place_monadic) t rxs;
        (cnt, amb) \<leftarrow> (PR_CONST poly_ethorner_count_trunc_monadic) rxs;
        if \<not> amb \<or> 2 \<le> cnt then RETURN cnt
        else doN {
          rxs2 \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
          ASSERT (length rxs2 + 1 < max_snat LENGTH(gmp_poly_len));
          (PR_CONST poly_ethorner_count_monadic) rxs2
        }
      }
    }
  }
}"

text \<open>The prune precedes the body above, so a hit skips the reverse copy, the lead budget, the truncation and
  the ET-Horner count. The body is a separate definition so that its classification ladder below is independent of the
  prune; it is not registered and is unfolded wherever the outer op is.\<close>
definition carried_descartes_count_trunc_monadic :: "gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_trunc_monadic xs \<equiv> doN {
  sc \<leftarrow> (PR_CONST poly_sign_changes_monadic) xs;
  if sc = 0 then RETURN 0
  else (PR_CONST carried_descartes_count_trunc_body_monadic) xs
}"

sepref_register "PR_CONST carried_descartes_count_trunc_monadic"
  :: "gmp_poly \<Rightarrow> nat nres"

text \<open>The public contract — statement-identical to @{thm [source]
  carried_descartes_count_monadic_classify}, so the call site needs no new
  preconditions.\<close>


lemma carried_descartes_count_trunc_body_classify:
  assumes len_bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_trunc_body_monadic xs \<le> SPEC (\<lambda>cnt.
           (cnt = 0) = (carried_descartes_count xs = 0) \<and>
           (cnt = 1) = (carried_descartes_count xs = 1) \<and>
           (2 \<le> cnt) = (2 \<le> carried_descartes_count xs))"
  using len_bound
  unfolding carried_descartes_count_trunc_body_monadic_def carried_descartes_count_def
    poly_length_monadic_def lead_budget_mop_def poly_coeff_bitlen2_monadic_def
    mpz_bitlen2_monadic_def PR_CONST_def Let_def
  apply (refine_vcg
      poly_reverse_monadic_correct[THEN order_trans]
      snat_bitlen_monadic_correct[THEN order_trans]
      poly_trunc_in_place_correct[THEN order_trans]
      poly_ethorner_count_trunc_monadic_classify[THEN order_trans]
      poly_ethorner_count_monadic_classify[THEN order_trans])
  \<comment> \<open>43 goals (\<open>lead_budget_mop\<close>'s two clamp branches double the ladder: G9-25 and G26-43).
     G1-2: reverse/length. G3-5: \<open>len\<le>1\<close> trichotomy. G6-8: \<open>0<len\<close>/\<open>len-1<len\<close>.
     G9: length bound from the clamp's \<open>topu\<le>bl\<close> branch. G10-15: exact-path trichotomy (attempt refused / \<open>lbl\<le>t\<close>)
     for that branch. G16: budget positivity. G17: the kernel-classification hypothesis's \<open>trunc_list\<close> pin (apply-style
     \<open>refl\<close>; \<open>subgoal\<close> would fix the shared schematics). G18-19: headroom. G20-22: decisive branch. G23-25: fallback
     branch. G26-27: the second clamp branch's bound and length facts. G28-43: the G10-25 shape again for that branch
     (G35 is the second \<open>refl\<close>).\<close>
  subgoal by simp
  subgoal by simp
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by simp
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  \<comment> \<open>G17 must be apply-style: \<open>subgoal\<close> freezes the shared schematics.\<close>
  apply (rule refl)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by simp
  subgoal by simp
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  \<comment> \<open>G35, the second clamp branch's twin of G17.\<close>
  apply (rule refl)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

text \<open>The public contract, with the prune in front. The statement is that of the op without the prune, so
  every caller's precondition and every refinement above see the same classification trichotomy against the exact
  \<open>carried_descartes_count xs\<close>. The prune branch discharges all three conjuncts at once from
  @{thm [source] count_zero_of_prune_certificate}: a zero-variation operand has exact count \<open>0\<close>, so returning \<open>0\<close> is a
  correct classification.\<close>

lemma carried_descartes_count_trunc_monadic_classify:
  assumes len_bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_trunc_monadic xs \<le> SPEC (\<lambda>cnt.
           (cnt = 0) = (carried_descartes_count xs = 0) \<and>
           (cnt = 1) = (carried_descartes_count xs = 1) \<and>
           (2 \<le> cnt) = (2 \<le> carried_descartes_count xs))"
  unfolding carried_descartes_count_trunc_monadic_def PR_CONST_def
  apply (refine_vcg poly_sign_changes_monadic_correct[THEN order_trans]
      carried_descartes_count_trunc_body_classify[THEN order_trans])
  \<comment> \<open>Three goals: the sign-scan's length precondition, the body's, and the prune branch's
     trichotomy. Given uniformly rather than positionally — the branch order is refine_vcg's
     to choose.\<close>
  apply (all \<open>(use len_bound count_zero_of_prune_certificate[of xs] in simp); fail\<close>)
  done

text \<open>\<^bold>\<open>W1 safety (obligation 1): the classify result is bounded by 3.\<close> The ET/trunc
  count kernels cap the WHILET at \<open>changes < 2\<close> and add ONE \<open>extra_f\<close> boundary bit, so the
  returned classify is always in \<open>{0,1,2,3}\<close> — DISJOINT from the window-child cache encoding
  \<open>v + 2 \<ge> 4\<close>. This bound is a structural artifact of the capping loop (not implied by the
  trichotomy, which permits any value \<open>\<ge> 2\<close>), so it is re-derived here above the frozen base by
  re-running the two kernels' WHILET with the count component pinned \<open>\<le> 2\<close>.\<close>

lemma sign_step_snd_le_Suc: "snd (sign_step x (ls, c)) \<le> Suc c"
  by (auto split: if_splits)

lemma poly_ethorner_count_monadic_le3:
  assumes "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_ethorner_count_monadic ys \<le> SPEC (\<lambda>c. c \<le> 3)"
  using assms
  unfolding poly_ethorner_count_monadic_def poly_ethorner_count_cond_def
    poly_ethorner_count_result_mop_monadic_def poly_length_monadic_def
    poly_coeff_sgn_monadic_def PR_CONST_def Let_def
  apply (refine_vcg ethorner_count_body_pres
      WHILET_rule[where R="measure (\<lambda>((i, ls, c), xs::int list). length ys - 1 - i)"
        and I="\<lambda>((i, ls, c), xs).
             i \<le> length ys - 1 \<and> length xs = length ys
           \<and> xs = ethorner_outer_step_fun i ys
           \<and> (ls, c) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)
           \<and> c \<le> 2"])
  apply (simp_all add: scf_taylor_short)
  subgoal premises prems for s
  proof -
    obtain i ls c xs where seq: "s = ((i, ls, c), xs)" by (metis prod.collapse)
    show ?thesis
      unfolding seq
      apply (refine_vcg ethorner_count_body_pres)
      using prems assms apply (auto simp: seq One_nat_def split: prod.splits)
      subgoal premises p for aa b ac bb ad bc x1b x2a
      proof -
        have iL: "i < length (taylor_shift_list 1 ys)"
          using p by simp
        have "x2a = snd (sign_step (taylor_shift_list 1 ys ! i) (ls, c))"
          using p fold_sign_step_take_Suc[OF iL] by (metis snd_conv)
        thus "x2a \<le> 2" using sign_step_snd_le_Suc[of "taylor_shift_list 1 ys ! i" ls c] p by simp
      qed
      done
  qed
  done

lemma poly_ethorner_count_trunc_monadic_le3:
  assumes lbound: "length zs + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length zs * nat_bitlen (length zs) < max_snat LENGTH(gmp_poly_len)"
  shows "poly_ethorner_count_trunc_monadic zs \<le> SPEC (\<lambda>(c, amb). c \<le> 3)"
proof -
  have snatlen: "length zs < max_snat LENGTH(gmp_poly_len)" using lbound by simp
  show ?thesis
    unfolding poly_ethorner_count_trunc_monadic_def ethorner_count_trunc_cond_def
      ethorner_count_trunc_result_mop_monadic_def poly_length_monadic_def
      poly_coeff_sgn_monadic_def PR_CONST_def Let_def
    apply (refine_vcg snat_bitlen_monadic_correct[THEN order_trans]
        WHILET_rule[where
          R="measure (\<lambda>((i, ls, cnt, amb), xsl :: int list). length zs - 1 - i)"
          and I="\<lambda>((i, ls, cnt, amb), xsl).
               i \<le> length zs - 1 \<and> cnt \<le> 2 \<and> length xsl = length zs
             \<and> xsl = ethorner_outer_step_fun i zs
             \<and> tmask_state zs (sgn (zs ! (length zs - 1)) = 0) (ls, cnt, amb) i"])
    apply (simp_all add: snatlen pbound tmask_state_init)
    subgoal using snatlen by simp
    subgoal using pbound by simp
    subgoal premises prems for s
    proof -
      obtain i ls cnt amb xsl where seq: "s = ((i, ls, cnt, amb), xsl)"
        by (metis prod.collapse)
      show ?thesis
        using prems
        unfolding seq
        apply (refine_vcg ethorner_trunc_body_pres)
        using pbound lbound by (auto simp: seq One_nat_def split: prod.splits)
    qed
    subgoal premises prems for s a b aa ba ab bb ac bc bd be
      using prems lbound by auto
    subgoal premises prems for s a b aa ba ab bb ac bc bd be
      using prems lbound by auto
    done
qed

lemma carried_descartes_count_trunc_body_le3:
  assumes len_bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_trunc_body_monadic xs \<le> SPEC (\<lambda>cnt. cnt \<le> 3)"
  using len_bound
  unfolding carried_descartes_count_trunc_body_monadic_def carried_descartes_count_def
    poly_length_monadic_def lead_budget_mop_def poly_coeff_bitlen2_monadic_def
    mpz_bitlen2_monadic_def PR_CONST_def Let_def
  apply (refine_vcg
      poly_reverse_monadic_correct[THEN order_trans]
      snat_bitlen_monadic_correct[THEN order_trans]
      poly_trunc_in_place_correct[THEN order_trans]
      poly_ethorner_count_trunc_monadic_le3[THEN order_trans]
      poly_ethorner_count_monadic_le3[THEN order_trans])
  apply (simp_all add: length_trunc_list)
  apply auto
  done

text \<open>The prune keeps the \<open>\<le> 3\<close> range bound: it returns the literal \<open>0\<close>.\<close>
lemma carried_descartes_count_trunc_monadic_le3:
  assumes len_bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_trunc_monadic xs \<le> SPEC (\<lambda>cnt. cnt \<le> 3)"
  unfolding carried_descartes_count_trunc_monadic_def PR_CONST_def
  apply (refine_vcg poly_sign_changes_monadic_correct[THEN order_trans]
      carried_descartes_count_trunc_body_le3[THEN order_trans])
  apply (all \<open>(use len_bound in simp); fail\<close>)
  done

text \<open>The full contract: the classification trichotomy and the \<open>\<le> 3\<close> range bound in one SPEC (the \<open>cs\<close>
  invariant uses both). Combines \<open>carried_descartes_count_trunc_monadic_classify\<close> with
  \<open>carried_descartes_count_trunc_monadic_le3\<close> pointwise.\<close>
lemma carried_descartes_count_trunc_monadic_classify_le3:
  assumes len_bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_trunc_monadic xs \<le> SPEC (\<lambda>cnt.
           cnt \<le> 3 \<and>
           (cnt = 0) = (carried_descartes_count xs = 0) \<and>
           (cnt = 1) = (carried_descartes_count xs = 1) \<and>
           (2 \<le> cnt) = (2 \<le> carried_descartes_count xs))"
  using carried_descartes_count_trunc_monadic_le3[OF len_bound]
        carried_descartes_count_trunc_monadic_classify[OF len_bound]
  by (auto simp: pw_le_iff refine_pw_simps)

section \<open>Sepref synthesis (the executable impls)\<close>

subsection \<open>Machine-word bit length (pure, no GMP)\<close>

text \<open>@{const snat_bitlen_monadic} is a raw \<open>WHILET\<close> over a pure \<open>(nat, nat)\<close> state
  (\<open>v div 2\<close>, \<open>b + 1\<close>). Direct \<open>sepref\<close> with \<open>annot_snat_const\<close>.\<close>
sepref_definition snat_bitlen_impl [llvm_code] is
  "snat_bitlen_monadic" ::
  "[\<lambda>m. m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding snat_bitlen_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma snat_bitlen_impl_hnr[sepref_fr_rules]:
  "(snat_bitlen_impl, PR_CONST snat_bitlen_monadic) \<in>
    [\<lambda>m. m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using snat_bitlen_impl.refine
  by (simp add: PR_CONST_def)

subsection \<open>In-place floor truncation (the right-shift twin of \<open>poly_shift_coeff\<close>)\<close>

text \<open>Scalar in-place shift-RIGHT by a bit count \<open>r := r div 2^k\<close> KEEPING ownership
  (\<open>ri'=ri\<close>), the fdiv twin of @{const mpzb_mul_2exp_impl}. Uses the framework's proven
  in-place op @{const mpz_fdiv_q_2exp.aop_r1_impl}; its \<open>snd_notzero\<close> precondition is
  the \<open>0 < k\<close> hypothesis (\<open>__gmpz_fdiv_q_2exp\<close> is a bit-shift, so \<open>2^k\<close> divisor \<open>\<noteq> 0\<close>).\<close>
definition [llvm_code, llvm_inline]:
  "mpzb_fdiv_q_2exp_impl \<equiv> mpz_fdiv_q_2exp.aop_r1_impl"

lemma mpzb_fdiv_q_2exp_impl_rule_heap:
  assumes "0 < k"
  shows "llvm_htriple
    (mpzb_assn x ri \<and>* unat_assn k ki)
    (mpzb_fdiv_q_2exp_impl ri ki)
    (\<lambda>ri'. mpzb_assn (x div 2 ^ k) ri' \<and>* unat_assn k ki \<and>* \<up>(ri' = ri))"
  unfolding mpzb_fdiv_q_2exp_impl_def mpz_fdiv_q_2exp.aop_r1_impl_def
  supply [vcg_rules] = mpz_fdiv_q_2exp.vcg_rule[THEN conjunct2]
  using assms by vcg'

lemma mpzb_fdiv_q_2exp_impl_rule[vcg_rules]:
  assumes "0 < unat ki"
  shows "llvm_htriple
    (mpzb_assn x ri)
    (mpzb_fdiv_q_2exp_impl ri ki)
    (\<lambda>ri'. mpzb_assn (x div 2 ^ unat ki) ri' \<and>* \<up>(ri' = ri))"
  using mpzb_fdiv_q_2exp_impl_rule_heap[OF assms, of x ri ki]
  by (simp add: pure_app_eq pure_true_conv sep_algebra_simps unat_rel_def unat.rel_def in_br_conv)

text \<open>Keep-ownership in-place shift-right by a \<^bold>\<open>snat\<close> amount \<open>r := r div 2^sh\<close>: cast the
  signed-nat shift to the bit-count via @{const ll_ucast}, then the keep-fdiv. \<open>0 < sh\<close>.\<close>
definition [llvm_code, llvm_inline]:
  "mpzb_shift_right_snat_keep_impl r sh \<equiv> doM {
    k_bit \<leftarrow> ll_ucast sh;
    mpzb_fdiv_q_2exp_impl r k_bit
  }"

lemma mpzb_shift_right_snat_keep_impl_rule[vcg_rules]:
  fixes shi :: "gmp_poly_len word"
  assumes "0 < sh"
  shows "llvm_htriple
    (mpzb_assn x ri \<and>* \<upharpoonleft>snat.assn sh shi)
    (mpzb_shift_right_snat_keep_impl ri shi)
    (\<lambda>ri'. mpzb_assn (x div 2 ^ sh) ri' \<and>* \<upharpoonleft>snat.assn sh shi \<and>* \<up>(ri' = ri))"
  unfolding mpzb_shift_right_snat_keep_impl_def
  supply [vcg_rules] = mpzb_fdiv_q_2exp_impl_rule
  using assms
  apply vcg'
   apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
     dr_assn_pure_asm_prefix_def in_unat_rel_conv_assn[symmetric]
     in_snat_rel_conv_assn[symmetric] pure_part_pure pred_lift_extract_simps
     unat_rel_def unat.rel_def snat_rel_def in_br_conv)
  apply (all \<open>(clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
     STATE_def POSTCOND_def EXTRACT_def dr_assn_pure_asm_prefix_def
     in_unat_rel_conv_assn[symmetric] in_snat_rel_conv_assn[symmetric]
     pure_part_pure pred_lift_extract_simps unat_rel_def unat.rel_def
     snat_rel_def in_br_conv)?\<close>)
  apply (simp_all add: DEFER_SLOT_def SOLVE_AUTO_DEFER_def snats_def max_snat_def
    max_unat_def snat_in_bounds_aux)
  done

definition [llvm_code, llvm_inline]:
  "poly_trunc_coeff_impl p i t \<equiv> doM {
    target \<leftarrow> arl_nth p i;
    mpzb_shift_right_snat_keep_impl target t;
    Mreturn p
  }"

lemma poly_trunc_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii ti :: "gmp_poly_len word"
  assumes "i < length ptrs" and "0 < t"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<upharpoonleft>snat.assn t ti \<and>*
      mpzb_assn xi (ptrs ! i) \<and>* F)
    (poly_trunc_coeff_impl p ii ti)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      (mpzb_assn (xi div 2 ^ t) (ptrs ! i) \<and>* F) \<and>* \<upharpoonleft>snat.assn t ti)"
  using assms
  unfolding poly_trunc_coeff_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms(1)]
    mpzb_shift_right_snat_keep_impl_rule[OF assms(2)]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

lemma poly_trunc_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii ti :: "gmp_poly_len word"
  assumes "i < length xs" and "length ptrs = length xs" and "0 < t"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* \<upharpoonleft>snat.assn t ti)
    (poly_trunc_coeff_impl p ii ti)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (xs[i := xs ! i div 2 ^ t])) ptrs \<and>* \<upharpoonleft>snat.assn t ti)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_trunc_coeff_impl_focused_rule[
      where ptrs=ptrs and i=i and t=t
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          ((map Some xs)[i := None]) ptrs"
        and xi="xs ! i"])
    using assms apply simp
    using assms apply simp
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps
    gmp_poly_slots_unfocus_coeff_update)
  done

lemma poly_trunc_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii ti :: "gmp_poly_len word"
  assumes "i < length xs" and "0 < t"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* \<upharpoonleft>snat.assn t ti)
    (poly_trunc_coeff_impl p ii ti)
    (\<lambda>p'. gmp_poly_assn (xs[i := xs ! i div 2 ^ t]) p' \<and>* \<upharpoonleft>snat.assn t ti)"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_two_snat_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_trunc_coeff_impl_ptrs_rule[OF assms(1) _ assms(2)])
      apply assumption
    apply (clarsimp simp: entails_def sep_algebra_simps)
    subgoal for p' s
      apply (rule exI[where x=ptrs])
      apply (simp add: sep_algebra_simps)
      done
    done
  done

lemma poly_trunc_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_trunc_coeff_impl,
    uncurry2 (PR_CONST poly_trunc_coeff_monadic)) \<in>
    [\<lambda>((xs, i), t). i < length xs \<and> 0 < t \<and> t < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_trunc_coeff_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for t ti i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_trunc_coeff_impl_rule[where t=t])
       apply assumption
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps
      snat.assn_is_rel snat_rel_def pure_def)
    done
  done

sepref_definition poly_trunc_loop_impl [llvm_code] is
  "uncurry2 poly_trunc_loop_monadic" ::
  "[\<lambda>((len, t), xs). length xs = len \<and> 0 < t \<and>
      t < max_snat LENGTH(gmp_poly_len) \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_trunc_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_trunc_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_trunc_loop_impl,
    uncurry2 (PR_CONST poly_trunc_loop_monadic)) \<in>
    [\<lambda>((len, t), xs). length xs = len \<and> 0 < t \<and>
      t < max_snat LENGTH(gmp_poly_len) \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_trunc_loop_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition poly_trunc_in_place_impl [llvm_code] is
  "uncurry poly_trunc_in_place_monadic" ::
  "[\<lambda>(t, xs). 0 < t \<and> t < max_snat LENGTH(gmp_poly_len) \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_trunc_in_place_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_trunc_in_place_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_trunc_in_place_impl,
    uncurry (PR_CONST poly_trunc_in_place_monadic)) \<in>
    [\<lambda>(t, xs). 0 < t \<and> t < max_snat LENGTH(gmp_poly_len) \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_trunc_in_place_impl.refine
  by (simp add: PR_CONST_def)

subsection \<open>Maximum coefficient bit length (borrowed polynomial, pure word accumulator)\<close>

text \<open>The \<open>for\<close>-loop over the BORROWED poly reading each coeff's bitlen (\<open>gmp_size\<close>),
  clamping + converting to snat, folding the max. Poly stays \<open>\<^sup>k\<close>; the accumulator is
  a pure snat. \<open>for_by_while'\<close> + \<open>annot_snat_const\<close>, mirroring the kiou maxfold shape
  but with the borrowed bitlen read (no per-coeff copy).\<close>
sepref_definition max_bitlen_cond_impl [llvm_inline] is
  "uncurry (RETURN oo max_bitlen_cond_monadic)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a max_bitlen_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding max_bitlen_cond_monadic_def Let_def
  by sepref

lemma max_bitlen_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry max_bitlen_cond_impl,
    uncurry (RETURN oo (PR_CONST max_bitlen_cond_monadic))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a max_bitlen_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using max_bitlen_cond_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition max_bitlen_body_impl [llvm_inline] is
  "uncurry2 max_bitlen_body_mop_monadic" ::
  "[\<lambda>((len, xs), i, nb). len \<le> length xs]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a max_bitlen_state_assn\<^sup>d
    \<rightarrow> max_bitlen_state_assn"
  unfolding max_bitlen_body_mop_monadic_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma max_bitlen_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 max_bitlen_body_impl,
    uncurry2 (PR_CONST max_bitlen_body_mop_monadic)) \<in>
    [\<lambda>((len, xs), i, nb). len \<le> length xs]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a max_bitlen_state_assn\<^sup>d
    \<rightarrow> max_bitlen_state_assn"
  using max_bitlen_body_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition poly_max_bitlen_loop_impl [llvm_code] is
  "uncurry poly_max_bitlen_loop_monadic" ::
  "[\<lambda>(len, xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding poly_max_bitlen_loop_monadic_def
  supply [sepref_fr_rules] = max_bitlen_cond_impl_hnr max_bitlen_body_impl_hnr
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_max_bitlen_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_max_bitlen_loop_impl, uncurry (PR_CONST poly_max_bitlen_loop_monadic)) \<in>
    [\<lambda>(len, xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using poly_max_bitlen_loop_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition poly_max_bitlen_impl [llvm_code] is
  "poly_max_bitlen_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding poly_max_bitlen_monadic_def
  by sepref

lemma poly_max_bitlen_impl_hnr[sepref_fr_rules]:
  "(poly_max_bitlen_impl, PR_CONST poly_max_bitlen_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using poly_max_bitlen_impl.refine
  by (simp add: PR_CONST_def)

subsection \<open>The truncated-count kernel (condition/body/result ops and the outer WHILET)\<close>

text \<open>The ambiguity-tracking twin of @{const poly_ethorner_count_impl}: state adds the
  \<open>amb\<close> bool and the body reads each coefficient's \<open>gmp_size\<close> bit-length. The lone
  snat-vs-\<open>gmp_size\<close> comparison \<open>bt < bl\<close> (snat threshold vs unat bit-length) is
  reconciled by an \<open>op_snat_unat_conv\<close> that lives ONLY in an equal impl-form of the
  body (\<open>_impl_form\<close>, proved identity-equal), so the fragile
  @{thm [source] ethorner_trunc_body_pres} proof's returned-tuple term stays untouched.\<close>

abbreviation ethorner_trunc_state_assn where
  "ethorner_trunc_state_assn \<equiv>
    (snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_sint_assn \<times>\<^sub>a
     snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn) \<times>\<^sub>a gmp_poly_assn"

sepref_definition ethorner_count_trunc_cond_impl [llvm_inline] is
  "uncurry (RETURN oo ethorner_count_trunc_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a ethorner_trunc_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding ethorner_count_trunc_cond_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma ethorner_count_trunc_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry ethorner_count_trunc_cond_impl,
    uncurry (RETURN oo (PR_CONST ethorner_count_trunc_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a ethorner_trunc_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using ethorner_count_trunc_cond_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The threshold arithmetic \<open>min (min (i+1) (len-(i+1)) * bthr) len\<close> as its own op (machine-word arithmetic
  in a heap-op body does not translate inline). One op per bind; \<open>min\<close> via explicit if-then-else. The outer
  \<open>min _ len\<close> cap keeps the trust threshold from being too conservative in the middle of the polynomial (see
  \<open>Count_Spec.trunc_thresh\<close>).\<close>
definition trunc_thresh_mop :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where
"trunc_thresh_mop i len bthr \<equiv> doN {
  ASSERT (i + 1 < len);
  ASSERT (len * bthr < max_snat LENGTH(gmp_poly_len));
  ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
  a \<leftarrow> RETURN (i + 1);
  b \<leftarrow> RETURN (len - a);
  m \<leftarrow> (if a \<le> b then RETURN a else RETURN b);
  ASSERT (m * bthr < max_snat LENGTH(gmp_poly_len));
  mb \<leftarrow> RETURN (m * bthr);
  (if mb \<le> len then RETURN mb else RETURN len)
}"

sepref_register "PR_CONST trunc_thresh_mop" :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres"

sepref_definition trunc_thresh_impl [llvm_inline] is
  "uncurry2 trunc_thresh_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding trunc_thresh_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma trunc_thresh_impl_hnr[sepref_fr_rules]:
  "(uncurry2 trunc_thresh_impl, uncurry2 (PR_CONST trunc_thresh_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using trunc_thresh_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The pure per-coefficient TRUST + tuple update, extracted as its own op (the
  kiou-\<open>kiou_update_mop\<close> pattern): all the compound-boolean / if-update / word-conversion
  logic that would not translate inside the heap-carrying \<open>WHILET\<close> body lives HERE, over
  PURE word/int/bool inputs only (no poly, no nested destructive state), where it
  synthesises cleanly. \<open>op_snat_unat_conv bt\<close> reconciles the snat threshold with the
  \<open>gmp_size\<close> (unat) bit-length; the internal \<open>ASSERT (cnt < 2)\<close> bounds \<open>cnt + 1\<close>.\<close>
definition trunc_update_mop ::
  "int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (int \<times> nat \<times> bool) nres" where
"trunc_update_mop s bl bt last_s cnt amb \<equiv> doN {
  ASSERT (cnt < 2);
  btu \<leftarrow> RETURN (op_snat_unat_conv bt);
  trusted \<leftarrow> (if 0 < s then RETURN True
              else if s < 0
                then (if btu < bl then RETURN True else RETURN False)
                else RETURN False);
  new_last_s \<leftarrow> (if trusted then RETURN s else RETURN last_s);
  new_amb \<leftarrow> (if trusted then RETURN amb else RETURN True);
  new_cnt \<leftarrow> (if trusted
              then (if last_s \<noteq> 0
                    then (if s \<noteq> last_s then RETURN (cnt + 1) else RETURN cnt)
                    else RETURN cnt)
              else RETURN cnt);
  RETURN (new_last_s, new_cnt, new_amb)
}"

sepref_register "PR_CONST trunc_update_mop"
  :: "int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (int \<times> nat \<times> bool) nres"

sepref_definition trunc_update_impl [llvm_inline] is
  "uncurry5 trunc_update_mop" ::
  "gmp_sint_assn\<^sup>k *\<^sub>a gmp_size_assn\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a
    gmp_sint_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  unfolding trunc_update_mop_def Let_def
  apply (annot_sint_const gmp_int_t)?
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma trunc_update_impl_hnr[sepref_fr_rules]:
  "(uncurry5 trunc_update_impl, uncurry5 (PR_CONST trunc_update_mop)) \<in>
    gmp_sint_assn\<^sup>k *\<^sub>a gmp_size_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a
      gmp_sint_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  using trunc_update_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Impl-form of the body: identical to @{const ethorner_count_trunc_body_mop_monadic}
  except the threshold arithmetic and trust+update are delegated to the two registered
  pure ops above, leaving a heap body of ONLY registered-op calls + ASSERTs +
  destructuring + one tuple RETURN (the Poly_Ops/kiou shape). Equal as NRES programs
  (the ops' internal ASSERTs are implied by the body's early ones — pointwise \<open>pw_eq_iff\<close>).\<close>
definition ethorner_count_trunc_body_impl_form ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly
   \<Rightarrow> ((nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly) nres" where
"ethorner_count_trunc_body_impl_form len bthr st \<equiv> doN {
  let (st1, xs) = st;
  let (i, last_s, cnt, amb) = st1;
  ASSERT (length xs = len);
  ASSERT (1 < len);
  ASSERT (i + 1 < len);
  ASSERT (cnt < 2);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (len * bthr < max_snat LENGTH(gmp_poly_len));
  xs' \<leftarrow> (PR_CONST poly_ethorner_inner_loop_monadic) len i xs;
  ASSERT (i < length xs');
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs' i;
  bl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs' i;
  bt \<leftarrow> (PR_CONST trunc_thresh_mop) i len bthr;
  (new_last_s, new_cnt, new_amb) \<leftarrow>
    (PR_CONST trunc_update_mop) s bl bt last_s cnt amb;
  RETURN ((i + 1, new_last_s, new_cnt, new_amb), xs')
}"

text \<open>Under the caller's ASSERT facts, the two pure ops COMPUTE closed forms — the
  bridges that let the impl-form body fold back onto the proven mop body. Deterministic
  case-split proofs, with no search over the whole peeled program.\<close>
lemma trunc_thresh_mop_eq:
  assumes "i + 1 < len" and "len < max_snat LENGTH(gmp_poly_len)"
    and "len * bthr < max_snat LENGTH(gmp_poly_len)"
  shows "trunc_thresh_mop i len bthr
    = RETURN (min (min (i + 1) (len - (i + 1)) * bthr) len)"
proof -
  have m: "min (i + 1) (len - (i + 1)) \<le> len" using assms(1) by (simp add: min_def)
  have mb: "min (i + 1) (len - (i + 1)) * bthr < max_snat LENGTH(gmp_poly_len)"
    using m assms(3) by (meson le_less_trans mult_le_mono1)
  show ?thesis
    unfolding trunc_thresh_mop_def
    using assms mb by (auto simp: pw_eq_iff refine_pw_simps min_def)
qed

lemma trunc_update_mop_eq:
  assumes "cnt < 2"
  shows "trunc_update_mop s bl bt last_s cnt amb
    = RETURN ((if 0 < s \<or> (s < 0 \<and> bt < bl) then s else last_s),
              (if (0 < s \<or> (s < 0 \<and> bt < bl)) \<and> last_s \<noteq> 0 \<and> s \<noteq> last_s
               then cnt + 1 else cnt),
              (amb \<or> \<not> (0 < s \<or> (s < 0 \<and> bt < bl))))"
  unfolding trunc_update_mop_def op_snat_unat_conv_def
  using assms
  by (cases "0 < s"; cases "s < 0"; cases "bt < bl";
      cases "last_s = 0"; cases "s = last_s"; simp)

text \<open>\<open>bind_cong\<close>'s \<open>RETURN x \<le> M\<close> premise is VACUOUS for \<open>M = ASSERT P\<close> (it does not
  yield \<open>P\<close>) — to peel an ASSERT chain WITH its facts, rewrite asserts to \<open>if\<close>-form
  first and peel with \<open>if_cong\<close>, which puts the condition in the branch's context.\<close>
lemma ASSERT_bind_eq_if:
  "(ASSERT P \<bind> f) = (if P then f () else FAIL)"
  by (cases P) simp_all

text \<open>A REDUNDANT ASSERT (needed only for a Sepref fr_rule precondition, already
  IMPLIED by context and absent from the abstract mop) discharges via direct
  substitution, not \<open>if_cong\<close> congruence (which would require the mop to carry a
  syntactically-matching \<open>if\<close> it doesn't have).\<close>
lemma ASSERT_true_bind: "P \<Longrightarrow> (ASSERT P \<bind> f) = f ()"
  by simp

lemma ethorner_count_trunc_body_impl_form_eq:
  "ethorner_count_trunc_body_impl_form len bthr st
    = ethorner_count_trunc_body_mop_monadic len bthr st"
proof -
  obtain st1 xs where st: "st = (st1, xs)" by (cases st)
  obtain i last_s cnt amb where st1: "st1 = (i, last_s, cnt, amb)"
    by (cases st1) auto
  show ?thesis
    unfolding ethorner_count_trunc_body_impl_form_def
      ethorner_count_trunc_body_mop_monadic_def PR_CONST_def st st1
    apply (simp only: Let_def prod.case ASSERT_bind_eq_if)
    apply (intro bind_cong if_cong refl)
    subgoal \<comment> \<open>the threshold segment vs its closed form\<close>
      by (simp add: trunc_thresh_mop_eq)
    subgoal \<comment> \<open>the update segment vs the mop's let-tail\<close>
      by (simp add: trunc_update_mop_eq)
    done
qed

sepref_definition ethorner_count_trunc_body_impl [llvm_inline] is
  "uncurry2 ethorner_count_trunc_body_impl_form" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    ethorner_trunc_state_assn\<^sup>d \<rightarrow>\<^sub>a ethorner_trunc_state_assn"
  unfolding ethorner_count_trunc_body_impl_form_def Let_def
  apply (annot_sint_const gmp_int_t)?
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma ethorner_count_trunc_body_impl_form_eq_ext:
  "ethorner_count_trunc_body_impl_form = ethorner_count_trunc_body_mop_monadic"
  by (intro ext) (rule ethorner_count_trunc_body_impl_form_eq)

lemma ethorner_count_trunc_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 ethorner_count_trunc_body_impl,
    uncurry2 (PR_CONST ethorner_count_trunc_body_mop_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      ethorner_trunc_state_assn\<^sup>d \<rightarrow>\<^sub>a ethorner_trunc_state_assn"
  using ethorner_count_trunc_body_impl.refine
  by (simp add: PR_CONST_def ethorner_count_trunc_body_impl_form_eq_ext)

sepref_definition ethorner_count_trunc_result_impl [llvm_inline] is
  "ethorner_count_trunc_result_mop_monadic" ::
  "ethorner_trunc_state_assn\<^sup>d \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_sint_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a gmp_poly_assn"
  unfolding ethorner_count_trunc_result_mop_monadic_def Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma ethorner_count_trunc_result_impl_hnr[sepref_fr_rules]:
  "(ethorner_count_trunc_result_impl,
    PR_CONST ethorner_count_trunc_result_mop_monadic) \<in>
    ethorner_trunc_state_assn\<^sup>d \<rightarrow>\<^sub>a
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_sint_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a gmp_poly_assn"
  using ethorner_count_trunc_result_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition poly_ethorner_count_trunc_impl [llvm_code] is
  "poly_ethorner_count_trunc_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  unfolding poly_ethorner_count_trunc_monadic_def Let_def
  supply [sepref_fr_rules] =
    ethorner_count_trunc_cond_impl_hnr
    ethorner_count_trunc_body_impl_hnr
    ethorner_count_trunc_result_impl_hnr
  apply (annot_sint_const gmp_int_t)
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_ethorner_count_trunc_impl_hnr[sepref_fr_rules]:
  "(poly_ethorner_count_trunc_impl,
    PR_CONST poly_ethorner_count_trunc_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  using poly_ethorner_count_trunc_impl.refine
  by (simp add: PR_CONST_def)

subsection \<open>The composed count (guard op, implementation form, equality, Sepref)\<close>

text \<open>The runtime ATTEMPT guard as its own op: the mop's \<open>let attempt = (\<dots> < max_snat \<dots>)\<close>
  conjunction, computed OVERFLOW-FREE (\<open>len \<le> top div 2\<close> instead of \<open>2*len < max_snat\<close> —
  the \<open>dyadic_shift_guard\<close> trick, since computing \<open>2*len\<close> needs the very bound being
  tested). \<open>trunc_count_margin = 0\<close> is folded in. Atomic conditions only.\<close>
definition trunc_attempt_guard_mop :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
"trunc_attempt_guard_mop len nb bthr \<equiv> doN {
  top \<leftarrow> RETURN (PR_CONST (trunc_max_snat_incl TYPE(gmp_poly_len)));
  cap2 \<leftarrow> RETURN (top div 2);
  if len \<le> cap2 then doN {
    ASSERT (2 * len < max_snat LENGTH(gmp_poly_len));
    l2 \<leftarrow> RETURN (2 * len);
    if l2 < nb then
      (if nb \<le> top then
        (if bthr = 0 then RETURN True
         else doN {
           cap3 \<leftarrow> RETURN (top div bthr);
           if len \<le> cap3 then RETURN True else RETURN False
         })
       else RETURN False)
    else RETURN False
  } else RETURN False
}"

sepref_register "PR_CONST trunc_attempt_guard_mop" :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres"

lemma trunc_attempt_guard_mop_eq:
  "trunc_attempt_guard_mop len nb bthr
    = RETURN (2 * len < nb \<and> 2 * len < max_snat LENGTH(gmp_poly_len) \<and>
              len * bthr < max_snat LENGTH(gmp_poly_len) \<and>
              nb < max_snat LENGTH(gmp_poly_len))"
proof -
  let ?M = "max_snat (64::nat)"  \<comment> \<open>the NUMERAL-reduced form the goals print
    (\<open>LENGTH(64)\<close> simp-reduces to \<open>64\<close>; a \<open>LENGTH\<close>-form pattern never unifies)\<close>
  have M0: "0 < ?M" by (simp add: max_snat_def)
  have c2: "(len \<le> (?M - Suc 0) div 2) = (2 * len < ?M)"
    using M0 by (simp add: less_eq_div_iff_mult_less_eq mult.commute) linarith
  have c3: "0 < bthr \<Longrightarrow> (len \<le> (?M - Suc 0) div bthr) = (len * bthr < ?M)"
    using M0 by (simp add: less_eq_div_iff_mult_less_eq) linarith
  have c4: "(nb \<le> ?M - Suc 0) = (nb < ?M)"
    using M0 by linarith
  show ?thesis
    unfolding trunc_attempt_guard_mop_def
    apply (cases "len \<le> (?M - 1) div 2"; cases "2 * len < nb";
           cases "nb \<le> ?M - 1"; cases "bthr = 0")
    by (auto simp add: pw_eq_iff refine_pw_simps c2 c3 c4 M0)
qed

sepref_definition trunc_attempt_guard_impl [llvm_inline] is
  "uncurry2 trunc_attempt_guard_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding trunc_attempt_guard_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma trunc_attempt_guard_impl_hnr[sepref_fr_rules]:
  "(uncurry2 trunc_attempt_guard_impl, uncurry2 (PR_CONST trunc_attempt_guard_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using trunc_attempt_guard_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Extracting a deterministic result from a bind-congruence hypothesis: the peel's
  \<open>RETURN x \<le> M\<close> premise plus an op's \<open>\<le> RETURN v\<close> \<open>_correct\<close> pins \<open>x = v\<close>
  (\<open>M \<le> RETURN v\<close> forces \<open>nofail M\<close>, so the premise's implication fires).\<close>
lemma RETURN_le_det_eq:
  assumes "RETURN x \<le> M" and "M \<le> RETURN v"
  shows "x = v"
  using assms by (auto simp: pw_le_iff refine_pw_simps)

text \<open>Impl-form of the composed count: identical to
  @{const carried_descartes_count_trunc_monadic} except (a) the attempt conjunction is
  the registered overflow-free guard op, (b) the \<open>gmp_size\<close>-vs-snat comparison
  \<open>lbl \<le> t\<close> goes through \<open>op_snat_unat_conv\<close>, and (c) the HNR-precondition ASSERTs
  (post-attempt word bounds, \<open>0 < t\<close>, the post-trunc length) are at their call sites.
  Equal to the mop as NRES programs.\<close>
text \<open>The truncation-attempt tail as its own named op: a deeply nested inline \<open>doN\<close> with five or more binds and
  \<open>if\<close>s does not translate as one term, and splitting at this boundary suffices. It takes the length-derived scalars and
  both polynomials (\<open>rxs\<close> owned and consumed on every path, \<open>xs\<close> borrowed for the re-reverse in the ambiguous
  fallback).\<close>
text \<open>The index and gap arithmetic, each as its own registered op: a heap-op body may contain only registered-op
  calls, ASSERTs, destructuring and one \<open>RETURN\<close>, with no inline arithmetic.\<close>
definition trunc_lead_idx_mop :: "nat \<Rightarrow> nat nres" where
  "trunc_lead_idx_mop len \<equiv> doN { ASSERT (1 \<le> len); RETURN (len - 1) }"

sepref_register "PR_CONST trunc_lead_idx_mop" :: "nat \<Rightarrow> nat nres"

sepref_definition trunc_lead_idx_impl [llvm_inline] is
  "trunc_lead_idx_mop" ::
  "[\<lambda>len. 1 \<le> len]\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding trunc_lead_idx_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma trunc_lead_idx_impl_hnr[sepref_fr_rules]:
  "(trunc_lead_idx_impl, PR_CONST trunc_lead_idx_mop) \<in>
    [\<lambda>len. 1 \<le> len]\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using trunc_lead_idx_impl.refine by (simp add: PR_CONST_def)

text \<open>Returns BOTH forms of the snat gap, because both are needed and by different callers:
  the raw snat gap \<open>t\<close> is what @{const poly_trunc_in_place_monadic} consumes, and its
  \<open>gmp_size\<close> (unat) twin \<open>tu\<close> is what the comparison against the
  \<open>gmp_size\<close>-typed \<open>lbl\<close> consumes. Returning the pair is what lets each
  consumer take the form it wants without a conversion of its own.\<close>
definition trunc_gap_mop :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) nres" where
  "trunc_gap_mop nb len \<equiv> doN {
    l2 \<leftarrow> RETURN (2 * len);
    ASSERT (l2 \<le> nb);
    t \<leftarrow> RETURN (nb - l2);
    tu \<leftarrow> RETURN (op_snat_unat_conv t);
    RETURN (t, tu)
  }"

sepref_register "PR_CONST trunc_gap_mop" :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) nres"

sepref_definition trunc_gap_impl [llvm_inline] is
  "uncurry trunc_gap_mop" ::
  "[\<lambda>(nb, len). 2 * len \<le> nb]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
    snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_size_assn"
  unfolding trunc_gap_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma trunc_gap_impl_hnr[sepref_fr_rules]:
  "(uncurry trunc_gap_impl, uncurry (PR_CONST trunc_gap_mop)) \<in>
    [\<lambda>(nb, len). 2 * len \<le> nb]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
    snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_size_assn"
  using trunc_gap_impl.refine by (simp add: PR_CONST_def)

lemma trunc_gap_mop_eq:
  assumes "2 * len \<le> nb"
  shows "trunc_gap_mop nb len = RETURN (nb - 2 * len, nb - 2 * len)"
  unfolding trunc_gap_mop_def op_snat_unat_conv_def
  using assms by (simp add: pw_eq_iff refine_pw_simps)

lemma trunc_lead_idx_mop_eq:
  assumes "1 \<le> len" shows "trunc_lead_idx_mop len = RETURN (len - 1)"
  unfolding trunc_lead_idx_mop_def using assms by simp

sepref_definition lead_budget_impl [llvm_inline] is
  "uncurry lead_budget_mop" ::
  "[\<lambda>(xs, i). i < length xs]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
    gmp_size_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding lead_budget_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma lead_budget_impl_hnr[sepref_fr_rules]:
  "(uncurry lead_budget_impl, uncurry (PR_CONST lead_budget_mop)) \<in>
    [\<lambda>(xs, i). i < length xs]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
    gmp_size_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using lead_budget_impl.refine by (simp add: PR_CONST_def)

text \<open>The ambiguous-fallback: re-reverse the BORROWED original and run the exact count.
  Its own op with \<open>xs\<close> as the SOLE argument, so \<open>xs\<close>'s borrowed status crosses one
  call boundary instead of surviving the tail's whole nested structure (the
  \<open>hn_val UNIV\<close> fix — the kiou "borrowed curried param" shape).\<close>
definition trunc_fallback_mop :: "gmp_poly \<Rightarrow> nat nres" where
"trunc_fallback_mop xs \<equiv> doN {
  rxs2 \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs2 + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_ethorner_count_monadic) rxs2
}"

sepref_register "PR_CONST trunc_fallback_mop" :: "gmp_poly \<Rightarrow> nat nres"

sepref_definition trunc_fallback_impl [llvm_inline] is
  "trunc_fallback_mop" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding trunc_fallback_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma trunc_fallback_impl_hnr[sepref_fr_rules]:
  "(trunc_fallback_impl, PR_CONST trunc_fallback_mop) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using trunc_fallback_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The whole POST-KERNEL decision as one registered op (empirical finding, 3-probe
  bisection: an \<open>if\<close> whose branches are plain \<open>RETURN\<close>s of case-prod-destructured
  components would not trans inside the heap tail regardless of position/condition
  shape, while a registered-op TAIL CALL with clean args always does). Decision rule:
  the truncated count is decisive (\<open>\<not>amb\<close>) or already \<open>\<ge>2\<close> \<Rightarrow> trust it; else the
  exact fallback on the borrowed original.\<close>
definition trunc_decide_mop :: "nat \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"trunc_decide_mop cnt amb xs \<equiv>
  (if \<not> amb \<or> 2 \<le> cnt then RETURN cnt else (PR_CONST trunc_fallback_mop) xs)"

sepref_register "PR_CONST trunc_decide_mop" :: "nat \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

sepref_definition trunc_decide_impl [llvm_inline] is
  "uncurry2 trunc_decide_mop" ::
  "[\<lambda>((cnt, amb), xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k
    \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding trunc_decide_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma trunc_decide_impl_hnr[sepref_fr_rules]:
  "(uncurry2 trunc_decide_impl, uncurry2 (PR_CONST trunc_decide_mop)) \<in>
    [\<lambda>((cnt, amb), xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k
    \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using trunc_decide_impl.refine
  by (simp add: PR_CONST_def)

definition carried_descartes_count_trunc_tail_mop ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_trunc_tail_mop len rxs xs \<equiv> doN {
  lidx \<leftarrow> (PR_CONST trunc_lead_idx_mop) len;
  ASSERT (0 < len \<and> lidx < length rxs);
  (lbl, nb) \<leftarrow> (PR_CONST lead_budget_mop) rxs lidx;
  bthr \<leftarrow> (PR_CONST snat_bitlen_monadic) len;
  attempt \<leftarrow> (PR_CONST trunc_attempt_guard_mop) len nb bthr;
  if \<not> attempt then (PR_CONST poly_ethorner_count_monadic) rxs
  else doN {
    ASSERT (2 * len \<le> nb);
    (t, tu) \<leftarrow> (PR_CONST trunc_gap_mop) nb len;
    ASSERT (0 < t \<and> t < max_snat LENGTH(gmp_poly_len));
    if lbl \<le> tu then (PR_CONST poly_ethorner_count_monadic) rxs
    else doN {
      rxs \<leftarrow> (PR_CONST poly_trunc_in_place_monadic) t rxs;
      ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
      (cnt, amb) \<leftarrow> (PR_CONST poly_ethorner_count_trunc_monadic) rxs;
      (PR_CONST trunc_decide_mop) cnt amb xs
    }
  }
}"

sepref_register "PR_CONST carried_descartes_count_trunc_tail_mop"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

definition carried_descartes_count_trunc_body_impl_form :: "gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_trunc_body_impl_form xs \<equiv> doN {
  rxs \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
  len \<leftarrow> (PR_CONST poly_length_monadic) rxs;
  ASSERT (len = length rxs);
  if len \<le> 1 then (PR_CONST poly_ethorner_count_monadic) rxs
  else (PR_CONST carried_descartes_count_trunc_tail_mop) len rxs xs
}"

text \<open>The prune in Sepref shape: the same one-branch wrapper as @{const carried_descartes_count_trunc_monadic}, so
  the two \<open>_eq\<close> lemmas below compose.\<close>
definition carried_descartes_count_trunc_impl_form :: "gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_trunc_impl_form xs \<equiv> doN {
  sc \<leftarrow> (PR_CONST poly_sign_changes_monadic) xs;
  if sc = 0 then RETURN 0
  else (PR_CONST carried_descartes_count_trunc_body_impl_form) xs
}"

text \<open>A call-site length ASSERT after the in-place truncation ABSORBS unconditionally
  (given \<open>0 < t\<close>): if the truncation ran (nofail), its OWN leading assert bounds the
  input length and its \<open>_correct\<close> pins the result to \<open>trunc_list\<close> (length-preserving);
  if it failed, both sides are FAIL. This is how a Sepref-only call-site precondition
  crosses a \<open>bind_cong\<close> peel whose \<open>RETURN x \<le> M\<close> premise is vacuous: prove the
  absorb SEGMENT-locally from the producer's own asserts + \<open>_correct\<close>, no context
  facts needed.\<close>
lemma trunc_in_place_length_absorb:
  assumes t0: "0 < t"
  shows "poly_trunc_in_place_monadic t xs \<bind>
      (\<lambda>r. ASSERT (length r + 1 < max_snat LENGTH(gmp_poly_len)) \<bind> (\<lambda>_. K r))
    = poly_trunc_in_place_monadic t xs \<bind> K"
proof (cases "length xs + 1 < max_snat LENGTH(gmp_poly_len)")
  case True
  have le: "poly_trunc_in_place_monadic t xs \<le> RETURN (trunc_list t xs)"
    by (rule poly_trunc_in_place_correct[OF t0 True])
  show ?thesis
    using le True
    by (auto simp: pw_eq_iff pw_le_iff refine_pw_simps trunc_list_def)
next
  case False
  then have nf: "\<not> nofail (poly_trunc_in_place_monadic t xs)"
    unfolding poly_trunc_in_place_monadic_def poly_length_monadic_def PR_CONST_def
    by (auto simp: refine_pw_simps)
  show ?thesis using nf by (auto simp: pw_eq_iff refine_pw_simps)
qed

lemma carried_descartes_count_trunc_body_impl_form_eq:
  "carried_descartes_count_trunc_body_impl_form xs
    = carried_descartes_count_trunc_body_monadic xs"
  unfolding carried_descartes_count_trunc_body_impl_form_def
    carried_descartes_count_trunc_tail_mop_def trunc_decide_mop_def
    trunc_fallback_mop_def
    carried_descartes_count_trunc_body_monadic_def PR_CONST_def
  apply (simp only: trunc_attempt_guard_mop_eq trunc_count_margin_def Let_def
    add_0_right nres_monad1)
  apply (rule bind_cong[OF refl])
  apply (rule bind_cong[OF refl])
  apply (rule bind_cong[OF refl])
  apply (rule bind_cong[OF refl])
  subgoal for x xa xb xc
    apply (cases "xb \<le> (1::nat)")
    subgoal by simp
    apply simp
    subgoal premises prems
      apply (subgoal_tac "1 \<le> xb")
      prefer 2
      subgoal using prems by linarith
      apply (simp only: trunc_lead_idx_mop_eq nres_monad1 One_nat_def)
      apply (rule bind_cong[OF refl])
      apply (rule bind_cong[OF refl])
      apply (simp only: split_paired_all prod.case)
      apply (rule bind_cong[OF refl])
      subgoal for xa lbl nb bthr
        apply (cases "2 * xb < nb \<and> 2 * xb < max_snat LENGTH(gmp_poly_len) \<and>
          xb * bthr < max_snat LENGTH(gmp_poly_len) \<and> nb < max_snat LENGTH(gmp_poly_len)")
        prefer 2
        subgoal by simp
        subgoal premises prems2
          apply (subgoal_tac "2 * xb \<le> nb")
          prefer 2
          subgoal using prems2 by linarith
          apply (subgoal_tac
            "0 < nb - 2 * xb \<and> nb - 2 * xb < max_snat LENGTH(gmp_poly_len)")
          prefer 2
          subgoal using prems2 by (intro conjI; linarith)
          apply (simp only: ASSERT_true_bind trunc_gap_mop_eq nres_monad1 prod.case)
          \<comment> \<open>the post-trunc length ASSERT (call-site precondition for the kernel's
             fr_rule, absent from the mop) absorbs segment-locally\<close>
          apply (rule if_cong[OF refl])
          subgoal by (rule refl)
          apply (rule if_cong[OF refl])
          subgoal by (rule refl)
          apply (subst trunc_in_place_length_absorb[unfolded One_nat_def])
          subgoal using prems2 by linarith
          by (rule refl)
        done
      done
    done
  done

text \<open>The prune branch is the same term on both sides, so the wrapper equality is the body equality lifted
  through the \<open>if\<close> by congruence.\<close>
lemma carried_descartes_count_trunc_impl_form_eq:
  "carried_descartes_count_trunc_impl_form xs
    = carried_descartes_count_trunc_monadic xs"
  unfolding carried_descartes_count_trunc_impl_form_def
    carried_descartes_count_trunc_monadic_def PR_CONST_def
  \<comment> \<open>The NRES bind congruence blocks simp from entering the continuation, so peel it
     explicitly — the same \<open>bind_cong[OF refl]\<close> idiom the body's own \<open>_eq\<close> ladder uses.\<close>
  apply (rule bind_cong[OF refl])
  by (simp add: carried_descartes_count_trunc_body_impl_form_eq)

lemma carried_descartes_count_trunc_impl_form_eq_ext:
  "carried_descartes_count_trunc_impl_form = carried_descartes_count_trunc_monadic"
  by (intro ext) (rule carried_descartes_count_trunc_impl_form_eq)

text \<open>The composed drop-in count, exported \<open>[llvm_code]\<close>: reverse -> length -> the
  bail-out \<open>len \<le> 1\<close> path -> max-bitlen -> lead bitlen -> word-bitlen budget -> the
  overflow-free attempt guard -> threshold -> the conv+compare -> in-place truncate ->
  the trunc kernel -> the decisive-or-fallback branch. All ops registered above.\<close>
text \<open>The tail's synthesis: the extra bracket conjunct \<open>length xs + 1 < max_snat\<close>
  feeds @{const trunc_fallback_mop}'s HNR precondition (its borrowed \<open>xs\<close> is the
  original un-reversed poly); the outer wrapper's own precondition supplies it at
  the call site.\<close>
sepref_definition carried_descartes_count_trunc_tail_impl [llvm_inline] is
  "uncurry2 carried_descartes_count_trunc_tail_mop" ::
  "[\<lambda>((len, rxs), xs). 1 \<le> len \<and> length rxs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>k
    \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding carried_descartes_count_trunc_tail_mop_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma carried_descartes_count_trunc_tail_impl_hnr[sepref_fr_rules]:
  "(uncurry2 carried_descartes_count_trunc_tail_impl,
    uncurry2 (PR_CONST carried_descartes_count_trunc_tail_mop)) \<in>
    [\<lambda>((len, rxs), xs). 1 \<le> len \<and> length rxs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>k
    \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using carried_descartes_count_trunc_tail_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The body without the prune, synthesised as its own inline leaf, so the outer wrapper below is one
  \<open>poly_sign_changes\<close> call and one branch. It is both registered and given \<open>[sepref_fr_rules]\<close>.\<close>
sepref_register "PR_CONST carried_descartes_count_trunc_body_impl_form"
  :: "gmp_poly \<Rightarrow> nat nres"

sepref_definition carried_descartes_count_trunc_body_impl [llvm_inline] is
  "carried_descartes_count_trunc_body_impl_form" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding carried_descartes_count_trunc_body_impl_form_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma carried_descartes_count_trunc_body_impl_hnr[sepref_fr_rules]:
  "(carried_descartes_count_trunc_body_impl,
    PR_CONST carried_descartes_count_trunc_body_impl_form) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using carried_descartes_count_trunc_body_impl.refine
  by (simp add: PR_CONST_def)

text \<open>BORROWED input (\<open>\<^sup>k\<close>), mirroring the exact @{const carried_descartes_count_impl}
  it drops in for — the carried driver keeps the node poly.\<close>
sepref_definition carried_descartes_count_trunc_impl [llvm_code] is
  "carried_descartes_count_trunc_impl_form" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding carried_descartes_count_trunc_impl_form_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma carried_descartes_count_trunc_impl_hnr[sepref_fr_rules]:
  "(carried_descartes_count_trunc_impl,
    PR_CONST carried_descartes_count_trunc_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using carried_descartes_count_trunc_impl.refine
  by (simp add: PR_CONST_def carried_descartes_count_trunc_impl_form_eq_ext)

section \<open>Sepref synthesis: order and routes\<close>

text \<open>Synthesis order and per-op routes:

  1. \<open>poly_coeff_bitlen2_impl\<close>: a hand-written \<open>[llvm_code]\<close> slot read (\<open>arl_nth\<close> and \<open>mpz_bitlen2_impl\<close>, as
     \<open>poly_shift_coeff_impl\<close> in \<open>Dyadic_Interval\<close>), HNR by \<open>sepref_to_hoare\<close> and \<open>vcg\<close>; signature
     \<open>gmp_poly_assn\<^sup>k *\<^sub>a snat\<^sup>k \<rightarrow>\<^sub>a gmp_size_assn\<close>.
  2. \<open>poly_trunc_coeff_impl\<close>/\<open>poly_trunc_loop_impl\<close>/\<open>poly_trunc_in_place_impl\<close>: the scale-loop triple's Sepref blocks
     (\<open>Dyadic_Interval\<close>, \<open>for_by_while'\<close> and \<open>annot_snat_const\<close>); the per-coefficient op calls \<open>raw_mpz_fdiv_q_2exp\<close> in
     place (bit count \<open>unat\<close>; the \<open>0 < t\<close> ASSERT serves its \<open>snd_notzero\<close> precondition).
  3. \<open>snat_bitlen_impl\<close>: a plain word WHILET with \<open>annot_snat_const\<close>, no GMP.
  4. \<open>poly_max_bitlen_impl\<close>: borrowed polynomial, pure word state; between \<open>gmp_size\<close>/\<open>unat\<close> and \<open>snat\<close>, a runtime
     cap test and then \<open>op_unat_snat_conv\<close>, never \<open>mop_unat_snat_upcast\<close> in a \<open>RETURN\<close> position.
  5. The kernel, with state assertion
     \<open>(snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_sint_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn) \<times>\<^sub>a gmp_poly_assn\<close>
     (the exact kernel's \<open>poly_ethorner_count_state_assn\<close> with a \<open>bool1_assn\<close>); condition/body/result
     \<open>[llvm_inline]\<close> Sepref definitions with \<open>_hnr\<close> bridges, then the outer \<open>[llvm_code]\<close> definition supplying the
     three HNRs, following the exact kernel's blocks in \<open>Poly_Ops\<close>.
  6. \<open>carried_descartes_count_trunc_impl [llvm_code]\<close>: signature as \<open>carried_descartes_count_impl\<close>
     (\<open>gmp_poly_assn\<^sup>k \<rightarrow> snat\<close>); \<open>annot_snat_const\<close> for the literals; \<open>mk_free_is_pure\<close> in the frame-free supply where
     the exact op's block has it.\<close>


definition carried_descartes_count_exact_monadic :: "gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_exact_monadic xs \<equiv> doN {
  rxs \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST descartes_finish_monadic) rxs
}"

text \<open>Route: \<open>refine_vcg\<close> collapse of @{thm [source] poly_reverse_monadic_correct}
  + @{thm [source] descartes_finish_monadic_correct} (mirroring the classify proof
  in \<open>Carried_Kernel.thy\<close> — but the conclusion here is exact, no trichotomy).\<close>
lemma carried_descartes_count_exact_monadic_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_exact_monadic xs
           \<le> RETURN (carried_descartes_count xs)"
  using assms
  unfolding carried_descartes_count_exact_monadic_def carried_descartes_count_def PR_CONST_def
  apply (refine_vcg
      poly_reverse_monadic_correct[THEN order_trans]
      descartes_finish_monadic_correct[THEN order_trans])
  apply (simp_all add: length_rev)
  done

text \<open>Sepref: same reverse+finish structure as @{const carried_descartes_count_monadic}
  (borrows @{term xs}, creates+consumes the reversed copy internally), so the borrowed
  \<open>gmp_poly_assn\<^sup>k\<close> synthesis clones \<open>carried_descartes_count_impl\<close>'s route (Carried_Kernel.thy).\<close>
sepref_register "PR_CONST carried_descartes_count_exact_monadic"
  :: "gmp_poly \<Rightarrow> nat nres"

sepref_definition carried_descartes_count_exact_impl [llvm_code] is
  "carried_descartes_count_exact_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding carried_descartes_count_exact_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma carried_descartes_count_exact_impl_hnr[sepref_fr_rules]:
  "(carried_descartes_count_exact_impl,
    PR_CONST carried_descartes_count_exact_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using carried_descartes_count_exact_impl.refine
  by (simp add: PR_CONST_def)
definition poly_eval1_pair :: "gmp_poly \<Rightarrow> int \<times> int" where
  "poly_eval1_pair xs = (sum_list xs, \<Sum>i < length xs. int i * xs ! i)"
abbreviation eval1_state_assn where
"eval1_state_assn \<equiv> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"

abbreviation eval1_state2_assn where
"eval1_state2_assn \<equiv> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn"

definition poly_eval1_pair_cond :: "nat \<Rightarrow> nat \<times> int \<times> int \<times> int \<Rightarrow> bool" where
"poly_eval1_pair_cond len st \<equiv> (let (i, s, ds, ic) = st in i < len)"

sepref_register "PR_CONST poly_eval1_pair_cond"
  :: "nat \<Rightarrow> nat \<times> int \<times> int \<times> int \<Rightarrow> bool"

sepref_definition poly_eval1_pair_cond_impl [llvm_inline] is
  "uncurry (RETURN oo poly_eval1_pair_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    eval1_state2_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding poly_eval1_pair_cond_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma poly_eval1_pair_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_eval1_pair_cond_impl,
    uncurry (RETURN oo (PR_CONST poly_eval1_pair_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      eval1_state2_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using poly_eval1_pair_cond_impl.refine
  by (simp add: PR_CONST_def)

definition poly_eval1_pair_body_mop_monadic ::
  "gmp_poly \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<times> int \<times> int \<times> int \<Rightarrow> (nat \<times> int \<times> int \<times> int) nres" where
"poly_eval1_pair_body_mop_monadic xs one len st \<equiv> doN {
  let (i, s, ds, ic) = st;
  ASSERT (i < len);
  ASSERT (i < length xs);
  s \<leftarrow> (PR_CONST poly_hom_eval_addmul_monadic) s xs i one;
  ds \<leftarrow> (PR_CONST poly_hom_eval_addmul_monadic) ds xs i ic;
  ic \<leftarrow> (PR_CONST mpz_add_monadic) ic one;
  ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
  RETURN (i + 1, s, ds, ic)
}"

sepref_register "PR_CONST poly_eval1_pair_body_mop_monadic"
  :: "gmp_poly \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<times> int \<times> int \<times> int \<Rightarrow> (nat \<times> int \<times> int \<times> int) nres"

sepref_definition poly_eval1_pair_body2_impl [llvm_inline] is
  "uncurry3 poly_eval1_pair_body_mop_monadic" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    eval1_state2_assn\<^sup>d \<rightarrow>\<^sub>a eval1_state2_assn"
  unfolding poly_eval1_pair_body_mop_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_fr_rules] = poly_hom_eval_addmul_impl_hnr mpzb_add_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma poly_eval1_pair_body2_impl_hnr[sepref_fr_rules]:
  "(uncurry3 poly_eval1_pair_body2_impl,
    uncurry3 (PR_CONST poly_eval1_pair_body_mop_monadic)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      eval1_state2_assn\<^sup>d \<rightarrow>\<^sub>a eval1_state2_assn"
  using poly_eval1_pair_body2_impl.refine
  by (simp add: PR_CONST_def)

definition poly_eval1_pair_finish_monadic ::
  "nat \<times> int \<times> int \<times> int \<Rightarrow> (int \<times> int) nres" where
"poly_eval1_pair_finish_monadic st \<equiv> doN {
  let (i, s, ds, ic) = st;
  (PR_CONST mpzb_discard_monadic) ic;
  RETURN (s, ds)
}"

sepref_register "PR_CONST poly_eval1_pair_finish_monadic"
  :: "nat \<times> int \<times> int \<times> int \<Rightarrow> (int \<times> int) nres"

sepref_definition poly_eval1_pair_finish2_impl [llvm_inline] is
  "poly_eval1_pair_finish_monadic" ::
  "eval1_state2_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn"
  unfolding poly_eval1_pair_finish_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma poly_eval1_pair_finish2_impl_hnr[sepref_fr_rules]:
  "(poly_eval1_pair_finish2_impl,
    PR_CONST poly_eval1_pair_finish_monadic) \<in>
    eval1_state2_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn"
  using poly_eval1_pair_finish2_impl.refine
  by (simp add: PR_CONST_def)

definition poly_eval1_pair_monadic :: "gmp_poly \<Rightarrow> (int \<times> int) nres" where
"poly_eval1_pair_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (0 < len);
  ASSERT (slong_bounds (int 0));
  s0 \<leftarrow> (PR_CONST mpz_of_snat_monadic) 0;
  ASSERT (slong_bounds (int 0));
  ds0 \<leftarrow> (PR_CONST mpz_of_snat_monadic) 0;
  ASSERT (slong_bounds (int 1));
  one \<leftarrow> (PR_CONST mpz_of_snat_monadic) 1;
  ASSERT (slong_bounds (int 0));
  ic0 \<leftarrow> (PR_CONST mpz_of_snat_monadic) 0;
  st \<leftarrow> WHILET
    (\<lambda>st. (PR_CONST poly_eval1_pair_cond) len st)
    (\<lambda>st. (PR_CONST poly_eval1_pair_body_mop_monadic) xs one len st)
    (0, s0, ds0, ic0);
  res \<leftarrow> (PR_CONST poly_eval1_pair_finish_monadic) st;
  (PR_CONST mpzb_discard_monadic) one;
  RETURN res
}"

text \<open>Correctness: the standalone-accumulator evaluation computes the SAME
  pair as @{const poly_eval1_pair}. The loop state is
  \<open>(i, s, ds, ic)\<close> (three owned scalars) rather than a cloned poly with appended slots. The
  invariant carries \<open>s = sum_list (take i xs)\<close>, \<open>ds = (\<Sum>j<i. int j * xs!j)\<close>, and the counter
  shadow \<open>ic = int i\<close>. The body's \<open>one\<close> parameter is the literal \<open>1\<close> (fed from the wrapper),
  so \<open>s += xs!i * one = s + xs!i\<close> and \<open>ic += one\<close> steps the shadow.\<close>
lemma poly_eval1_pair_monadic_correct:
  assumes ne: "0 < length xs" and lb: "length xs + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_eval1_pair_monadic xs \<le> RETURN (poly_eval1_pair xs)"
proof -
  have wl: "WHILET
      (\<lambda>st. (PR_CONST poly_eval1_pair_cond) (length xs) st)
      (\<lambda>st. (PR_CONST poly_eval1_pair_body_mop_monadic) xs 1 (length xs) st)
      (0, 0, 0, 0)
    \<le> SPEC (\<lambda>(i, s, ds, ic). i = length xs
        \<and> s = sum_list xs \<and> ds = (\<Sum>j < length xs. int j * xs ! j) \<and> ic = int (length xs))"
    apply (rule WHILET_rule[where
        R = "measure (\<lambda>(i, s, ds, ic). length xs - i)"
        and I = "\<lambda>(i, s, ds, ic). i \<le> length xs
          \<and> s = sum_list (take i xs) \<and> ds = (\<Sum>j < i. int j * xs ! j) \<and> ic = int i"])
    subgoal by simp
    subgoal by simp
    subgoal for st
      unfolding poly_eval1_pair_body_mop_monadic_def poly_eval1_pair_cond_def
        poly_hom_eval_addmul_monadic_def mpz_add_monadic_def PR_CONST_def
      apply refine_vcg
      using lb
      by (auto simp: take_Suc_conv_app_nth sum.lessThan_Suc max_snat_def)
    subgoal by (auto simp: take_all poly_eval1_pair_cond_def)
    done
  \<comment> \<open>Tail: the finish discards \<open>ic\<close> and returns \<open>(s,ds)\<close>, then the wrapper discards \<open>one\<close>
    (\<open>= 1\<close>) and returns; both discards are \<open>RETURN ()\<close> abstractly, so the tail is
    \<open>RETURN (s,ds)\<close>, which equals @{const poly_eval1_pair} under the loop postcondition.\<close>
  have wl_step: "WHILET
      (\<lambda>st. (PR_CONST poly_eval1_pair_cond) (length xs) st)
      (\<lambda>st. (PR_CONST poly_eval1_pair_body_mop_monadic) xs 1 (length xs) st)
      (0, 0, 0, 0)
    \<le> SPEC (\<lambda>st. (poly_eval1_pair_finish_monadic st \<bind>
            (\<lambda>res. mpzb_discard_monadic 1 \<bind> (\<lambda>_. RETURN res)))
          \<le> RES {poly_eval1_pair xs})"
    by (rule SPEC_cons_rule[OF wl])
       (clarsimp simp: poly_eval1_pair_finish_monadic_def mpzb_discard_monadic_def
          PR_CONST_def poly_eval1_pair_def)
  show ?thesis
    unfolding poly_eval1_pair_monadic_def
      poly_length_monadic_def
      mpz_of_snat_monadic_def snat_sint_cast.mop_def PR_CONST_def
    apply (refine_vcg mpz_of_snat_monadic_correct[THEN order_trans])
    using ne lb
    apply (simp_all add: slong_bounds_def max_sint_def min_sint_def)
    apply (rule wl_step[unfolded PR_CONST_def])
    done
qed

sepref_register "PR_CONST poly_eval1_pair_monadic"
  :: "gmp_poly \<Rightarrow> (int \<times> int) nres"

sepref_definition poly_eval1_pair_impl [llvm_inline] is
  "poly_eval1_pair_monadic" ::
  "[\<lambda>xs. 0 < length xs \<and> length xs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  unfolding poly_eval1_pair_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_fr_rules] =
    mpz_of_snat_impl_hnr
    poly_eval1_pair_cond_impl_hnr
    poly_eval1_pair_body2_impl_hnr
    poly_eval1_pair_finish2_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma poly_eval1_pair_impl_hnr[sepref_fr_rules]:
  "(poly_eval1_pair_impl, PR_CONST poly_eval1_pair_monadic) \<in>
    [\<lambda>xs. 0 < length xs \<and> length xs + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  using poly_eval1_pair_impl.refine
  by (simp add: PR_CONST_def)
definition poly_ethorner_count_cap_cond ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat) \<times> gmp_poly \<Rightarrow> bool" where
  "poly_ethorner_count_cap_cond cap limit st \<equiv>
    (let (st1, xs) = st in let (i, last_s, changes) = st1 in i < limit \<and> changes < cap)"

sepref_register "PR_CONST poly_ethorner_count_cap_cond"
  :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat) \<times> gmp_poly \<Rightarrow> bool"

sepref_definition poly_ethorner_count_cap_cond_impl [llvm_inline] is
  "uncurry2 (RETURN ooo poly_ethorner_count_cap_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    poly_ethorner_count_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding poly_ethorner_count_cap_cond_def Let_def
  \<comment> \<open>no numeric literal left (the original's \<open>2\<close> became \<open>cap\<close>) \<Rightarrow> annot is optional\<close>
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma poly_ethorner_count_cap_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_ethorner_count_cap_cond_impl,
    uncurry2 (RETURN ooo (PR_CONST poly_ethorner_count_cap_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      poly_ethorner_count_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using poly_ethorner_count_cap_cond_impl.refine
  by (simp add: PR_CONST_def)
definition poly_ethorner_count_cap_body_mop_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat) \<times> gmp_poly \<Rightarrow> ((nat \<times> int \<times> nat) \<times> gmp_poly) nres" where
"poly_ethorner_count_cap_body_mop_monadic cap len st \<equiv> doN {
  let (st1, xs) = st;
  let (i, last_s, changes) = st1;
  ASSERT (length xs = len);
  ASSERT (1 < len);
  ASSERT (i + 1 < len);
  ASSERT (changes < cap);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  xs' \<leftarrow> (PR_CONST poly_ethorner_inner_loop_monadic) len i xs;
  ASSERT (i < length xs');
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs' i;
  let new_changes = (if last_s \<noteq> 0 \<and> s \<noteq> 0 \<and> last_s \<noteq> s then changes + 1 else changes);
  let new_last_s = (if s \<noteq> 0 then s else last_s);
  RETURN ((i + 1, new_last_s, new_changes), xs')
}"

sepref_register "PR_CONST poly_ethorner_count_cap_body_mop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat) \<times> gmp_poly \<Rightarrow> ((nat \<times> int \<times> nat) \<times> gmp_poly) nres"

sepref_definition poly_ethorner_count_cap_body_impl [llvm_inline] is
  "uncurry2 poly_ethorner_count_cap_body_mop_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    poly_ethorner_count_state_assn\<^sup>d \<rightarrow>\<^sub>a poly_ethorner_count_state_assn"
  unfolding poly_ethorner_count_cap_body_mop_monadic_def Let_def
  apply (annot_sint_const gmp_int_t)
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_ethorner_count_cap_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_ethorner_count_cap_body_impl,
    uncurry2 (PR_CONST poly_ethorner_count_cap_body_mop_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      poly_ethorner_count_state_assn\<^sup>d \<rightarrow>\<^sub>a poly_ethorner_count_state_assn"
  using poly_ethorner_count_cap_body_impl.refine
  by (simp add: PR_CONST_def)
definition poly_ethorner_count_cap_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"poly_ethorner_count_cap_monadic cap xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  if len \<le> 1 then doN { (PR_CONST poly_free_monadic) xs; RETURN 0 }
  else doN {
    ASSERT (1 < len);
    limit \<leftarrow> RETURN (len - 1);
    ASSERT (limit < length xs);
    s_last \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs limit;
    let init = ((0::nat, 0::int, 0::nat), xs);
    st \<leftarrow> WHILET
      (\<lambda>st. (PR_CONST poly_ethorner_count_cap_cond) cap limit st)
      (\<lambda>st. (PR_CONST poly_ethorner_count_cap_body_mop_monadic) cap len st)
      init;
    (changes, last_s, xs_final) \<leftarrow> (PR_CONST poly_ethorner_count_result_mop_monadic) st;
    extra_f \<leftarrow> (if last_s \<noteq> 0 \<and> s_last \<noteq> 0 \<and> last_s \<noteq> s_last
                then RETURN (1::nat) else RETURN 0);
    ASSERT (changes + extra_f < max_snat LENGTH(gmp_poly_len));
    final_changes \<leftarrow> RETURN (changes + extra_f);
    (PR_CONST poly_free_monadic) xs_final;
    RETURN final_changes
  }
}"

text \<open>The cap generalisation of @{thm [source] ethorner_count_final_classify}
  (\<open>Poly_Ops.thy\<close>, frozen — cloned here with the literal \<open>2\<close> lifted to \<open>cap\<close> and the
  trichotomy conclusion replaced by the cap contract). The FULL-run case is byte-identical
  (cap-independent exact count); the early-abort case replaces \<open>2 \<le> cnt\<close> by \<open>cap \<le> cnt\<close>.\<close>
lemma ethorner_count_final_cap:
  fixes ys :: "int list"
  assumes len: "2 \<le> length ys"
    and i: "i \<le> length ys - 1"
    and st: "(last_s, cnt) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)"
    and exit: "\<not> (i < length ys - 1 \<and> cnt < cap)"
    and cap2: "2 \<le> cap"
  defines "ef \<equiv> (if last_s \<noteq> 0 \<and> sgn (ys ! (length ys - 1)) \<noteq> 0
                    \<and> last_s \<noteq> sgn (ys ! (length ys - 1)) then 1 else (0::nat))"
  shows "(cnt + ef < cap \<longrightarrow> cnt + ef = sign_changes_fold (taylor_shift_list 1 ys))
       \<and> (cap \<le> cnt + ef \<longrightarrow> cap \<le> sign_changes_fold (taylor_shift_list 1 ys))"
proof -
  let ?tl = "taylor_shift_list 1 ys"
  have lentl: "length ?tl = length ys" by simp
  have ysne: "ys \<noteq> []" using len by auto
  have tlne: "?tl \<noteq> []" using len lentl by fastforce
  have rz: "last_s = 0 \<longrightarrow> cnt = 0"
    using st fold_sign_step_z[of "take i ?tl"] by (metis fst_conv snd_conv)
  have bnd: "sgn (?tl ! (length ys - 1)) = sgn (ys ! (length ys - 1))"
  proof -
    have "?tl ! (length ys - 1) = last ?tl" using tlne lentl by (simp add: last_conv_nth)
    also have "\<dots> = last ys" using ysne by (simp add: last_taylor_shift_list)
    also have "\<dots> = ys ! (length ys - 1)" using ysne by (simp add: last_conv_nth)
    finally show ?thesis by simp
  qed
  have snd_eq: "snd (sign_step (?tl ! (length ys - 1)) (last_s, cnt))
              = (if last_s \<noteq> 0 \<and> sgn (?tl ! (length ys - 1)) \<noteq> 0
                   \<and> last_s \<noteq> sgn (?tl ! (length ys - 1)) then cnt + 1 else cnt)"
    by (simp only: sign_step_eq_body[OF rz] snd_conv)
  have valeq: "cnt + ef = snd (sign_step (?tl ! (length ys - 1)) (last_s, cnt))"
    unfolding snd_eq ef_def bnd by (simp split: if_split)
  show ?thesis
  proof (cases "i = length ys - 1")
    case True
    have tk: "take i ?tl = butlast ?tl" using True lentl by (simp add: butlast_conv_take)
    have ln: "?tl ! (length ys - 1) = last ?tl" using tlne lentl by (simp add: last_conv_nth)
    have "cnt + ef = snd (sign_step (last ?tl) (fold sign_step (butlast ?tl) (0, 0)))"
      using valeq st tk ln by simp
    also have "\<dots> = snd (fold sign_step (butlast ?tl @ [last ?tl]) (0, 0))"
      by (simp add: fold_append)
    also have "butlast ?tl @ [last ?tl] = ?tl" using tlne by simp
    finally have exact: "cnt + ef = sign_changes_fold ?tl" by (simp add: sign_changes_fold_def)
    show ?thesis using exact by simp
  next
    case False
    with i exit have ccap: "cap \<le> cnt" by auto
    have mono: "cnt \<le> snd (fold sign_step (drop i ?tl) (last_s, cnt))"
      using fold_sign_step_snd_mono[of "(last_s, cnt)" "drop i ?tl"] rz by simp
    have foldeq: "sign_changes_fold ?tl = snd (fold sign_step (drop i ?tl) (last_s, cnt))"
    proof -
      have "sign_changes_fold ?tl = snd (fold sign_step (take i ?tl @ drop i ?tl) (0, 0))"
        by (simp add: sign_changes_fold_def)
      also have "\<dots> = snd (fold sign_step (drop i ?tl) (fold sign_step (take i ?tl) (0, 0)))"
        by (simp only: fold_append comp_apply)
      also have "\<dots> = snd (fold sign_step (drop i ?tl) (last_s, cnt))" by (simp flip: st)
      finally show ?thesis .
    qed
    from mono ccap foldeq have "cap \<le> sign_changes_fold ?tl" by simp
    thus ?thesis using ccap by simp
  qed
qed

text \<open>The cap clone of @{thm [source] ethorner_count_body_pres} (\<open>c < 2\<close> \<rightarrow> \<open>c < cap\<close>,
  over the cap body mop). One outer-loop step preserves the invariant and advances \<open>i\<close>.\<close>
lemma ethorner_count_cap_body_pres:
  assumes len2: "2 \<le> length ys"
    and iU: "i < length ys - 1"
    and cU: "c < cap"
    and lenxs: "length xs = length ys"
    and xseq: "xs = ethorner_outer_step_fun i ys"
    and steq: "(ls, c) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)"
    and bound: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_ethorner_count_cap_body_mop_monadic cap (length ys) ((i, ls, c), xs)
    \<le> SPEC (\<lambda>((i', ls', c'), xs').
          i' = Suc i \<and> i' \<le> length ys - 1 \<and> length xs' = length ys
        \<and> xs' = ethorner_outer_step_fun i' ys
        \<and> (ls', c') = fold sign_step (take i' (taylor_shift_list 1 ys)) (0, 0))"
proof -
  let ?tl = "taylor_shift_list 1 ys"
  let ?os = "ethorner_outer_step_fun i ys"
  have iL: "i < length ys" using iU by simp
  have rz: "ls = 0 \<longrightarrow> c = 0"
    using steq fold_sign_step_z[of "take i ?tl"] by (metis fst_conv snd_conv)
  have row: "ethorner_row_fun i ?os = ethorner_outer_step_fun (Suc i) ys" by simp
  have sgn_i: "sgn (ethorner_row_fun i ?os ! i) = sgn (?tl ! i)"
    using row ethorner_outer_step_nth_final[OF iL] by simp
  have iLtl: "i < length ?tl" using iL by simp
  have newstate:
    "((if sgn (?tl ! i) \<noteq> 0 then sgn (?tl ! i) else ls),
      (if ls \<noteq> 0 \<and> sgn (?tl ! i) \<noteq> 0 \<and> ls \<noteq> sgn (?tl ! i) then c + 1 else c))
     = fold sign_step (take (Suc i) ?tl) (0, 0)"
    using sign_step_eq_body[OF rz, of "?tl ! i"]
          fold_sign_step_take_Suc[OF iLtl] steq by simp
  have bodyval: "poly_ethorner_count_cap_body_mop_monadic cap (length ys) ((i, ls, c), ?os)
     \<le> RETURN ((Suc i,
          (if sgn (?tl ! i) \<noteq> 0 then sgn (?tl ! i) else ls),
          (if ls \<noteq> 0 \<and> sgn (?tl ! i) \<noteq> 0 \<and> ls \<noteq> sgn (?tl ! i) then c + 1 else c)),
        ethorner_row_fun i ?os)"
    unfolding poly_ethorner_count_cap_body_mop_monadic_def poly_coeff_sgn_monadic_def
      PR_CONST_def Let_def
    apply (refine_vcg poly_ethorner_inner_loop_monadic_row[THEN order_trans])
    apply (all \<open>(hypsubst_thin)?\<close>)
    apply (simp_all add: sgn_i len2 cU)
    using iU bound by simp_all
  show ?thesis
    unfolding xseq
    apply (rule order_trans[OF bodyval])
    apply (rule RETURN_rule)
    apply (simp only: prod.case)
    apply (intro conjI)
    subgoal by simp
    subgoal using iU by simp
    subgoal by simp
    subgoal by (rule row)
    subgoal by (rule newstate)
    done
qed

text \<open>Post-loop wrapper mirroring @{thm [source] ethorner_post_full} (bundled invariant +
  ncond interface) so the keystone's post goals discharge with the same shape.\<close>
lemma ethorner_post_full_cap:
  fixes ys :: "int list"
  assumes l2: "Suc 0 < length ys"
    and inv: "i \<le> length ys - Suc 0 \<and> length b = length ys
              \<and> (last_s, cnt) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)"
    and ncond: "i < length ys - Suc 0 \<longrightarrow>
              \<not> (case fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)
                  of (l, c) \<Rightarrow> c < cap)"
    and cap2: "2 \<le> cap"
  shows "(cnt + (if last_s \<noteq> 0 \<and> sgn (ys ! (length ys - Suc 0)) \<noteq> 0
                  \<and> last_s \<noteq> sgn (ys ! (length ys - Suc 0)) then 1 else 0) < cap
           \<longrightarrow> cnt + (if last_s \<noteq> 0 \<and> sgn (ys ! (length ys - Suc 0)) \<noteq> 0
                  \<and> last_s \<noteq> sgn (ys ! (length ys - Suc 0)) then 1 else 0)
               = sign_changes_fold (taylor_shift_list 1 ys))
       \<and> (cap \<le> cnt + (if last_s \<noteq> 0 \<and> sgn (ys ! (length ys - Suc 0)) \<noteq> 0
                  \<and> last_s \<noteq> sgn (ys ! (length ys - Suc 0)) then 1 else 0)
           \<longrightarrow> cap \<le> sign_changes_fold (taylor_shift_list 1 ys))"
proof -
  have l2': "2 \<le> length ys" using l2 by simp
  have iaa: "i \<le> length ys - 1" using inv by (simp add: One_nat_def)
  have st: "(last_s, cnt) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)"
    using inv by simp
  have ex: "\<not> (i < length ys - 1 \<and> cnt < cap)"
    using ncond by (simp add: st[symmetric] One_nat_def split: prod.splits)
  show ?thesis
    using ethorner_count_final_cap[OF l2' iaa st ex cap2] by (simp add: One_nat_def)
qed

text \<open>The capped-count contract: with
  \<open>t\<close> the exact count of \<open>ys\<close>, abort (\<open>cap \<le> r\<close>) certifies \<open>cap \<le> t\<close>; a full run
  (\<open>r < cap\<close>) is exact. The window try calls it at \<open>cap = v\<close>:
  \<open>v \<le> r\<close> accepts via \<open>carried_window_count_mono\<close> + the \<open>count xs \<le> v\<close> precondition,
  \<open>r < v\<close> rejects EXACTLY.\<close>
lemma poly_ethorner_count_cap_monadic_classify:
  assumes "length ys + 1 < max_snat LENGTH(gmp_poly_len)" and "2 \<le> cap"
  shows "poly_ethorner_count_cap_monadic cap ys
    \<le> SPEC (\<lambda>r.
        (r < cap \<longrightarrow> r = sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (cap \<le> r \<longrightarrow> cap \<le> sign_changes_fold (taylor_shift_list 1 ys)))"
  using assms
  unfolding poly_ethorner_count_cap_monadic_def poly_ethorner_count_cap_cond_def
    poly_ethorner_count_result_mop_monadic_def
    poly_length_monadic_def poly_coeff_sgn_monadic_def PR_CONST_def Let_def
  apply (refine_vcg ethorner_count_cap_body_pres
      WHILET_rule[where R="measure (\<lambda>((i, ls, c), xs::int list). length ys - 1 - i)"
        and I="\<lambda>((i, ls, c), xs).
             i \<le> length ys - 1 \<and> length xs = length ys
           \<and> xs = ethorner_outer_step_fun i ys
           \<and> (ls, c) = fold sign_step (take i (taylor_shift_list 1 ys)) (0, 0)"])
  apply (simp_all add: scf_taylor_short)
  \<comment> \<open>Goal 1: outer-loop body preservation (destructure the atomic state).\<close>
  subgoal premises prems for s
  proof -
    obtain i ls c xs where seq: "s = ((i, ls, c), xs)" by (metis prod.collapse)
    show ?thesis
      unfolding seq
      apply (refine_vcg ethorner_count_cap_body_pres)
      using prems assms by (auto simp: seq One_nat_def split: prod.splits)
  qed
  \<comment> \<open>Goal 2: \<open>Suc bb < max_snat\<close> (boundary ef=1).\<close>
  subgoal premises prems for s a b aa ba ab bb bc
  proof -
    from prems have inv: "aa \<le> length ys - Suc 0
        \<and> (ab, bb) = fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)" by blast
    have e1: "(ab, bb) = fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)"
      using inv by simp
    have "bb = snd (fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0))"
      using e1 by (metis snd_conv)
    also have "\<dots> \<le> length (take aa (taylor_shift_list 1 ys))"
      using fold_sign_step_snd_le[of "take aa (taylor_shift_list 1 ys)" "(0, 0)"] by simp
    also have "\<dots> \<le> aa" by simp
    also have "aa \<le> length ys - Suc 0" using inv by simp
    finally have "bb \<le> length ys - Suc 0" .
    thus ?thesis using prems by linarith
  qed
  \<comment> \<open>Goal 3: \<open>Suc bb = t\<close> (ef=1, exact half).\<close>
  subgoal premises prems for s a b aa ba ab bb bc
  proof -
    from prems have l2: "Suc 0 < length ys" by blast
    from prems have inv: "aa \<le> length ys - Suc 0 \<and> length b = length ys
        \<and> (ab, bb) = fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)" by blast
    from prems have nc: "aa < length ys - Suc 0 \<longrightarrow>
        \<not> (case fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)
            of (l, c) \<Rightarrow> c < cap)" by blast
    show ?thesis
      using ethorner_post_full_cap[OF l2 inv nc assms(2)] prems by (auto split: if_splits)
  qed
  \<comment> \<open>Goal 4: \<open>cap \<le> t\<close> (ef=1).\<close>
  subgoal premises prems for s a b aa ba ab bb bc
  proof -
    from prems have l2: "Suc 0 < length ys" by blast
    from prems have inv: "aa \<le> length ys - Suc 0 \<and> length b = length ys
        \<and> (ab, bb) = fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)" by blast
    from prems have nc: "aa < length ys - Suc 0 \<longrightarrow>
        \<not> (case fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)
            of (l, c) \<Rightarrow> c < cap)" by blast
    show ?thesis
      using ethorner_post_full_cap[OF l2 inv nc assms(2)] prems by (auto split: if_splits)
  qed
  \<comment> \<open>Goal 5: \<open>bb < max_snat\<close> (boundary ef=0).\<close>
  subgoal premises prems for s a b aa ba ab bb bc
  proof -
    from prems have inv: "aa \<le> length ys - Suc 0
        \<and> (ab, bb) = fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)" by blast
    have e1: "(ab, bb) = fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)"
      using inv by simp
    have "bb = snd (fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0))"
      using e1 by (metis snd_conv)
    also have "\<dots> \<le> length (take aa (taylor_shift_list 1 ys))"
      using fold_sign_step_snd_le[of "take aa (taylor_shift_list 1 ys)" "(0, 0)"] by simp
    also have "\<dots> \<le> aa" by simp
    also have "aa \<le> length ys - Suc 0" using inv by simp
    finally have "bb \<le> length ys - Suc 0" .
    thus ?thesis using prems by linarith
  qed
  \<comment> \<open>Goal 6: \<open>bb = t\<close> (ef=0, exact half).\<close>
  subgoal premises prems for s a b aa ba ab bb bc
  proof -
    from prems have l2: "Suc 0 < length ys" by blast
    from prems have inv: "aa \<le> length ys - Suc 0 \<and> length b = length ys
        \<and> (ab, bb) = fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)" by blast
    from prems have nc: "aa < length ys - Suc 0 \<longrightarrow>
        \<not> (case fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)
            of (l, c) \<Rightarrow> c < cap)" by blast
    show ?thesis
      using ethorner_post_full_cap[OF l2 inv nc assms(2)] prems by (auto split: if_splits)
  qed
  \<comment> \<open>Goal 7: \<open>cap \<le> t\<close> (ef=0).\<close>
  subgoal premises prems for s a b aa ba ab bb bc
  proof -
    from prems have l2: "Suc 0 < length ys" by blast
    from prems have inv: "aa \<le> length ys - Suc 0 \<and> length b = length ys
        \<and> (ab, bb) = fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)" by blast
    from prems have nc: "aa < length ys - Suc 0 \<longrightarrow>
        \<not> (case fold sign_step (take aa (taylor_shift_list 1 ys)) (0, 0)
            of (l, c) \<Rightarrow> c < cap)" by blast
    show ?thesis
      using ethorner_post_full_cap[OF l2 inv nc assms(2)] prems by (auto split: if_splits)
  qed
  done

sepref_register "PR_CONST poly_ethorner_count_cap_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

sepref_definition poly_ethorner_count_cap_impl [llvm_code] is
  "uncurry poly_ethorner_count_cap_monadic" ::
  "[\<lambda>(cap, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding poly_ethorner_count_cap_monadic_def Let_def
  supply [sepref_fr_rules] =
    poly_ethorner_count_cap_cond_impl_hnr
    poly_ethorner_count_cap_body_impl_hnr
    poly_ethorner_count_result_impl_hnr
  apply (annot_sint_const gmp_int_t)
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_ethorner_count_cap_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_ethorner_count_cap_impl,
    uncurry (PR_CONST poly_ethorner_count_cap_monadic)) \<in>
    [\<lambda>(cap, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using poly_ethorner_count_cap_impl.refine
  by (simp add: PR_CONST_def)

section \<open>The capped carried count (reverse + cap kernel)\<close>

text \<open>Clone of @{const carried_descartes_count_exact_monadic} (defined above in this
  theory) with the cap kernel in place of @{const descartes_finish_monadic}. Borrows \<open>xs\<close>;
  the reversed copy is consumed by the kernel (which frees it on every path).\<close>

definition carried_descartes_count_cap_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_cap_monadic cap xs \<equiv> doN {
  rxs \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_ethorner_count_cap_monadic) cap rxs
}"

text \<open>Route: \<open>refine_vcg\<close> collapse of \<open>poly_reverse_monadic_correct\<close> +
  @{thm [source] poly_ethorner_count_cap_monadic_classify}, then
  \<open>carried_descartes_count_def\<close> aligns \<open>taylor_shift_list 1 (rev xs)\<close> (mirroring the
  exact wrapper's proof in \<open>Newton.thy\<close>).\<close>
lemma carried_descartes_count_cap_monadic_classify:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)" and "2 \<le> cap"
  shows "carried_descartes_count_cap_monadic cap xs
    \<le> SPEC (\<lambda>r.
        (r < cap \<longrightarrow> r = carried_descartes_count xs) \<and>
        (cap \<le> r \<longrightarrow> cap \<le> carried_descartes_count xs))"
  using assms
  unfolding carried_descartes_count_cap_monadic_def carried_descartes_count_def PR_CONST_def
  apply (refine_vcg
      poly_reverse_monadic_correct[THEN order_trans]
      poly_ethorner_count_cap_monadic_classify[THEN order_trans])
  apply (simp_all add: length_rev)
  done

sepref_register "PR_CONST carried_descartes_count_cap_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

sepref_definition carried_descartes_count_cap_impl [llvm_code] is
  "uncurry carried_descartes_count_cap_monadic" ::
  "[\<lambda>(cap, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding carried_descartes_count_cap_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma carried_descartes_count_cap_impl_hnr[sepref_fr_rules]:
  "(uncurry carried_descartes_count_cap_impl,
    uncurry (PR_CONST carried_descartes_count_cap_monadic)) \<in>
    [\<lambda>(cap, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using carried_descartes_count_cap_impl.refine
  by (simp add: PR_CONST_def)

subsection \<open>The truncated capped Descartes count\<close>

text \<open>\<^bold>\<open>What this is.\<close> @{const carried_descartes_count_cap_monadic}, the Newton window probe's accept test, with
  the truncated low-precision decision that @{const carried_descartes_count_trunc_monadic} applies to the exact count.

  \<^bold>\<open>It is @{const carried_descartes_count_trunc_body_monadic} with the literal \<open>2\<close> replaced by \<open>cap\<close>\<close> in two places, the
  kernel's early-abort bound and the decisive test, the same transformation that gives
  @{thm [source] ethorner_count_final_cap} from \<open>ethorner_count_final_classify\<close>. It is a separate op, so the exact
  chain is unchanged.

  \<^bold>\<open>The generalisation to \<open>cap\<close> needs no new mathematics.\<close> Every specification-level ingredient is independent of the
  threshold: @{thm [source] tmask_state_cnt_le} bounds the masked prefix count by the exact count,
  @{thm [source] trunc_changes_decisive_exact} gives equality under \<open>\<not>amb\<close>, and @{thm [source] trunc_changes_le_sound}
  bounds the truncated count by the exact one. So the abort can stay at the caller's \<open>cap\<close>. Aborting at \<open>2\<close> instead
  would make the decisive test \<open>cap \<le> cnt\<close> unsatisfiable for \<open>cap > 2\<close>, so every probe with a true count in \<open>[2, cap)\<close>
  would fall back to the exact path.\<close>

text \<open>The pure trust+update op. IDENTICAL to @{const trunc_update_mop} except its internal
  \<open>ASSERT (cnt < 2)\<close> — which is there only to bound \<open>cnt + 1\<close> — is weakened to the bound
  itself, so the op is usable at ANY cap without taking \<open>cap\<close> as an argument (the arity,
  and hence the \<open>uncurry5\<close> Sepref shape, is unchanged). Generated code is identical.\<close>
definition trunc_update_cap_mop ::
  "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool
   \<Rightarrow> (int \<times> nat \<times> bool) nres" where
"trunc_update_cap_mop cap s bl bt last_s cnt amb \<equiv> doN {
  ASSERT (cnt < cap);
  btu \<leftarrow> RETURN (op_snat_unat_conv bt);
  trusted \<leftarrow> (if 0 < s then RETURN True
              else if s < 0
                then (if btu < bl then RETURN True else RETURN False)
                else RETURN False);
  new_last_s \<leftarrow> (if trusted then RETURN s else RETURN last_s);
  new_amb \<leftarrow> (if trusted then RETURN amb else RETURN True);
  new_cnt \<leftarrow> (if trusted
              then (if last_s \<noteq> 0
                    then (if s \<noteq> last_s then RETURN (cnt + 1) else RETURN cnt)
                    else RETURN cnt)
              else RETURN cnt);
  RETURN (new_last_s, new_cnt, new_amb)
}"

sepref_register "PR_CONST trunc_update_cap_mop"
  :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool
     \<Rightarrow> (int \<times> nat \<times> bool) nres"

sepref_definition trunc_update_cap_impl [llvm_inline] is
  "uncurry6 trunc_update_cap_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k *\<^sub>a gmp_size_assn\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a
    gmp_sint_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  unfolding trunc_update_cap_mop_def Let_def
  apply (annot_sint_const gmp_int_t)?
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma trunc_update_cap_impl_hnr[sepref_fr_rules]:
  "(uncurry6 trunc_update_cap_impl, uncurry6 (PR_CONST trunc_update_cap_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k *\<^sub>a gmp_size_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a
      gmp_sint_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  using trunc_update_cap_impl.refine
  by (simp add: PR_CONST_def)

lemma trunc_update_cap_mop_eq:
  assumes "cnt < cap"
  shows "trunc_update_cap_mop cap s bl bt last_s cnt amb
    = RETURN ((if 0 < s \<or> (s < 0 \<and> bt < bl) then s else last_s),
              (if (0 < s \<or> (s < 0 \<and> bt < bl)) \<and> last_s \<noteq> 0 \<and> s \<noteq> last_s
               then cnt + 1 else cnt),
              (amb \<or> \<not> (0 < s \<or> (s < 0 \<and> bt < bl))))"
  unfolding trunc_update_cap_mop_def op_snat_unat_conv_def
  using assms
  by (cases "0 < s"; cases "s < 0"; cases "bt < bl";
      cases "last_s = 0"; cases "s = last_s"; simp)

text \<open>The loop condition with \<open>cap\<close>: @{const ethorner_count_trunc_cond} with \<open>cnt < 2\<close> replaced by \<open>cnt < cap\<close>, so
  the truncated kernel aborts where the exact capped kernel does.\<close>
definition ethorner_count_trunc_cap_cond ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly \<Rightarrow> bool" where
  "ethorner_count_trunc_cap_cond cap limit st \<equiv>
    (let (st1, xs) = st in let (i, last_s, cnt, amb) = st1 in i < limit \<and> cnt < cap)"

sepref_register "PR_CONST ethorner_count_trunc_cap_cond"
  :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly \<Rightarrow> bool"

sepref_definition ethorner_count_trunc_cap_cond_impl [llvm_inline] is
  "uncurry2 (RETURN ooo ethorner_count_trunc_cap_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    ethorner_trunc_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding ethorner_count_trunc_cap_cond_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma ethorner_count_trunc_cap_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry2 ethorner_count_trunc_cap_cond_impl,
    uncurry2 (RETURN ooo (PR_CONST ethorner_count_trunc_cap_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      ethorner_trunc_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using ethorner_count_trunc_cap_cond_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The loop body. IDENTICAL to @{const ethorner_count_trunc_body_mop_monadic} except the
  \<open>ASSERT (cnt < 2)\<close> becomes the cap-generic \<open>cnt + 1\<close> bound, so the body itself needs no
  \<open>cap\<close> argument and its Sepref arity is unchanged.\<close>
definition ethorner_count_trunc_cap_body_mop_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly
   \<Rightarrow> ((nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly) nres" where
"ethorner_count_trunc_cap_body_mop_monadic cap len bthr st \<equiv> doN {
  let (st1, xs) = st;
  let (i, last_s, cnt, amb) = st1;
  ASSERT (length xs = len);
  ASSERT (1 < len);
  ASSERT (i + 1 < len);
  ASSERT (cnt < cap);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (len * bthr < max_snat LENGTH(gmp_poly_len));
  xs' \<leftarrow> (PR_CONST poly_ethorner_inner_loop_monadic) len i xs;
  ASSERT (i < length xs');
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs' i;
  bl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs' i;
  bt \<leftarrow> RETURN (min (min (i + 1) (len - (i + 1)) * bthr) len);
  let trusted = (0 < s \<or> (s < 0 \<and> bt < bl));
  let new_amb = (amb \<or> \<not> trusted);
  let new_cnt = (if trusted \<and> last_s \<noteq> 0 \<and> s \<noteq> last_s then cnt + 1 else cnt);
  let new_last_s = (if trusted then s else last_s);
  RETURN ((i + 1, new_last_s, new_cnt, new_amb), xs')
}"

sepref_register "PR_CONST ethorner_count_trunc_cap_body_mop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly
     \<Rightarrow> ((nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly) nres"

definition ethorner_count_trunc_cap_body_impl_form ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly
   \<Rightarrow> ((nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly) nres" where
"ethorner_count_trunc_cap_body_impl_form cap len bthr st \<equiv> doN {
  let (st1, xs) = st;
  let (i, last_s, cnt, amb) = st1;
  ASSERT (length xs = len);
  ASSERT (1 < len);
  ASSERT (i + 1 < len);
  ASSERT (cnt < cap);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (len * bthr < max_snat LENGTH(gmp_poly_len));
  xs' \<leftarrow> (PR_CONST poly_ethorner_inner_loop_monadic) len i xs;
  ASSERT (i < length xs');
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs' i;
  bl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs' i;
  bt \<leftarrow> (PR_CONST trunc_thresh_mop) i len bthr;
  (new_last_s, new_cnt, new_amb) \<leftarrow>
    (PR_CONST trunc_update_cap_mop) cap s bl bt last_s cnt amb;
  RETURN ((i + 1, new_last_s, new_cnt, new_amb), xs')
}"

lemma ethorner_count_trunc_cap_body_impl_form_eq:
  "ethorner_count_trunc_cap_body_impl_form cap len bthr st
    = ethorner_count_trunc_cap_body_mop_monadic cap len bthr st"
proof -
  obtain st1 xs where st: "st = (st1, xs)" by (cases st)
  obtain i last_s cnt amb where st1: "st1 = (i, last_s, cnt, amb)"
    by (cases st1) auto
  show ?thesis
    unfolding ethorner_count_trunc_cap_body_impl_form_def
      ethorner_count_trunc_cap_body_mop_monadic_def PR_CONST_def st st1
    apply (simp only: Let_def prod.case ASSERT_bind_eq_if)
    apply (intro bind_cong if_cong refl)
    subgoal \<comment> \<open>the threshold segment vs its closed form\<close>
      by (simp add: trunc_thresh_mop_eq)
    subgoal \<comment> \<open>the update segment vs the mop's let-tail\<close>
      by (simp add: trunc_update_cap_mop_eq)
    done
qed

sepref_definition ethorner_count_trunc_cap_body_impl [llvm_inline] is
  "uncurry3 ethorner_count_trunc_cap_body_impl_form" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    ethorner_trunc_state_assn\<^sup>d \<rightarrow>\<^sub>a ethorner_trunc_state_assn"
  unfolding ethorner_count_trunc_cap_body_impl_form_def Let_def
  apply (annot_sint_const gmp_int_t)?
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  done

lemma ethorner_count_trunc_cap_body_impl_form_eq_ext:
  "ethorner_count_trunc_cap_body_impl_form = ethorner_count_trunc_cap_body_mop_monadic"
  by (intro ext) (rule ethorner_count_trunc_cap_body_impl_form_eq)

lemma ethorner_count_trunc_cap_body_impl_hnr[sepref_fr_rules]:
  "(uncurry3 ethorner_count_trunc_cap_body_impl,
    uncurry3 (PR_CONST ethorner_count_trunc_cap_body_mop_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      ethorner_trunc_state_assn\<^sup>d \<rightarrow>\<^sub>a ethorner_trunc_state_assn"
  using ethorner_count_trunc_cap_body_impl.refine
  by (simp add: PR_CONST_def ethorner_count_trunc_cap_body_impl_form_eq_ext)

lemma ethorner_trunc_body_pres_cap:
  assumes len2: "2 \<le> length ys'"
    and iU: "i < length ys' - 1"
    and cU: "cnt < cap"
    and lenxs: "length xs = length ys'"
    and xseq: "xs = ethorner_outer_step_fun i ys'"
    and steq: "tmask_state ys' amb0 (ls, cnt, amb) i"
    and bound: "length ys' + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length ys' * nat_bitlen (length ys') < max_snat LENGTH(gmp_poly_len)"
  shows "ethorner_count_trunc_cap_body_mop_monadic cap (length ys') (nat_bitlen (length ys'))
           ((i, ls, cnt, amb), xs)
    \<le> SPEC (\<lambda>((i', ls', cnt', amb'), xs').
          i' = Suc i \<and> i' \<le> length ys' - 1 \<and> cnt' \<le> cap \<and> length xs' = length ys'
        \<and> xs' = ethorner_outer_step_fun i' ys'
        \<and> tmask_state ys' amb0 (ls', cnt', amb') i')"
proof -
  let ?len = "length ys'"
  let ?T = "taylor_shift_list 1 ys'"
  let ?os = "ethorner_outer_step_fun i ys'"
  have iL: "i < ?len" using iU by simp
  have iLT: "i < length ?T" using iL by simp
  have row: "ethorner_row_fun i ?os = ethorner_outer_step_fun (Suc i) ys'" by simp
  have val_i: "ethorner_row_fun i ?os ! i = ?T ! i"
    using row ethorner_outer_step_nth_final[OF iL] by simp
  \<comment> \<open>the invariant's mask witness at \<open>i\<close>; the step extends it by ONE entry, which is
     the true coefficient when the kernel trusts it and \<open>0\<close> when it does not\<close>
  obtain zs where zs: "length zs = i"
    "\<forall>j<i. zs ! j = 0 \<or> zs ! j = ?T ! j"
    "(ls, cnt, amb) = tsign_fold_idx ?len 0 zs (0, 0, amb0)"
    using steq unfolding tmask_state_def by blast
  have take_step: "\<And>v. tsign_fold_idx ?len 0 (zs @ [v]) (0, 0, amb0)
      = tsign_step (trusted_sgn ?len i v) (ls, cnt, amb)"
    using tsign_fold_idx_append[of ?len 0 zs _ "(0, 0, amb0)"] zs(1,3) by simp
  show ?thesis
    unfolding ethorner_count_trunc_cap_body_mop_monadic_def poly_coeff_sgn_monadic_def
      poly_coeff_bitlen2_monadic_def mpz_bitlen2_monadic_def PR_CONST_def Let_def
    apply (refine_vcg poly_ethorner_inner_loop_monadic_row[THEN order_trans])
    \<comment> \<open>15 goals (shapes read off the goal state, banner rule 3): 1-9 side conditions,
       10-15 the six post conjuncts; goal 15 (the mask invariant) closes by EXTENDING
       the invariant's mask witness by one entry (the append fold split, as
       \<open>take_step\<close>) and rewriting that step via @{thm [source]
       tsign_step_bitlen_form_masked} (its lower-bound premise discharged from the SPEC
       conjuncts) with @{thm [source] ethorner_outer_step_nth_final} (as \<open>val_i\<close>)
       bridging the row coefficient to the shifted coefficient.\<close>
    subgoal using lenxs by auto                                   \<comment> \<open>1: length\<close>
    subgoal using len2 by simp                                    \<comment> \<open>2: 1 < len\<close>
    subgoal using iU by (auto simp: less_diff_conv)               \<comment> \<open>3: i+1 < len\<close>
    subgoal using cU by auto                                      \<comment> \<open>4: cnt < cap\<close>
    subgoal using lenxs bound by auto                             \<comment> \<open>5: snat headroom\<close>
    subgoal using pbound by simp                                  \<comment> \<open>6: product headroom\<close>
    subgoal using len2 by simp                                    \<comment> \<open>7: 2 \<le> len\<close>
    subgoal using iL by auto                                      \<comment> \<open>8: i < len\<close>
    subgoal using iL lenxs by auto                                \<comment> \<open>9: i < length row\<close>
    \<comment> \<open>post conjuncts 1-6: the premises carry the returned tuple with its huge
       if-conditions -- every touch goes through OPAQUE decomposition
       (\<open>metis prod.inject\<close>, or \<open>define\<close>+\<open>folded\<close> to name the if-terms) so the
       simplifier never churns on the sgn/bitlen arithmetic inside them\<close>
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have "aa = i" using prems(1,2) by simp
      moreover have "x1a = aa + 1" using prems(17) p18 by simp
      ultimately show ?thesis by linarith
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have "x1a = aa + 1" using prems(17) p18 by simp
      then show ?thesis using prems(7) by linarith
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have "x1c = (if C \<and> ab \<noteq> 0 \<and> sgn v \<noteq> ab then ac + 1 else ac)"
        using prems(15,16,17) p18 by simp
      then have "x1c = ac \<or> x1c = ac + 1" by simp
      then show ?thesis using prems(8) by auto
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have "x2c = ethorner_row_fun aa b" using p18 by simp
      then show ?thesis using prems(5) by simp
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have eq0: "aa = i" "b = xs" using prems(1,2) by auto
      have x2ceq: "x2c = ethorner_row_fun aa b" using p18 by simp
      have "x1a = aa + 1" using prems(17) p18 by simp
      then have sucform: "x1a = Suc aa" by linarith
      show ?thesis
        unfolding sucform using x2ceq xseq eq0 by simp
    qed
    \<comment> \<open>the money goal: name the coefficient and the trust condition, decompose the
       tuple opaquely, then extend the mask witness by \<open>w\<close> (the coefficient when the
       kernel trusts it, \<open>0\<close> when it does not) via \<open>take_step\<close> and the guarded step via
       @{thm [source] tsign_step_bitlen_form_masked}, bridging the row coefficient to
       the shifted coefficient via \<open>val_i\<close>\<close>
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      have eq0: "aa = i" "ab = ls" "ac = cnt" "bc = amb" "b = xs"
        using prems(1,2,3,4) by auto
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note p18 = prems(18)[folded v_def, folded C_def]
      have x1aeq: "x1a = aa + 1" using prems(17) p18 by simp
      have comps: "x1b = (if C then sgn v else ab)"
        "x1c = (if C \<and> ab \<noteq> 0 \<and> sgn v \<noteq> ab then ac + 1 else ac)"
        "x2b = (bc \<or> \<not> C)"
        using prems(15,16,17) p18 by simp_all
      have veq: "v = taylor_shift_list 1 ys' ! i"
        unfolding v_def using eq0 xseq val_i by simp
      have lb: "taylor_shift_list 1 ys' ! i \<noteq> 0 \<longrightarrow>
                 2 ^ (x - 1) \<le> \<bar>taylor_shift_list 1 ys' ! i\<bar>"
        using prems(14)[folded v_def] veq by auto
      have suci: "Suc i = i + 1" by linarith
      have thr: "min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys')
          = trunc_thresh (length ys') i"
        unfolding trunc_thresh_def by (simp only: suci eq0(1))
      have Ceq: "C = (0 < sgn (taylor_shift_list 1 ys' ! i)
          \<or> sgn (taylor_shift_list 1 ys' ! i) < 0 \<and> trunc_thresh (length ys') i < x)"
        unfolding C_def veq thr ..
      \<comment> \<open>the extended mask witness: the true coefficient when trusted, \<open>0\<close> when not\<close>
      define w where "w = (if C then taylor_shift_list 1 ys' ! i else 0)"
      have wform: "w = (if 0 < sgn (taylor_shift_list 1 ys' ! i)
             \<or> sgn (taylor_shift_list 1 ys' ! i) < 0
               \<and> trunc_thresh (length ys') i < x then taylor_shift_list 1 ys' ! i else 0)"
        unfolding w_def Ceq ..
      have fold_eq: "tsign_fold_idx (length ys') 0 (zs @ [w]) (0, 0, amb0)
          = ((if C then sgn v else ls),
             (if C \<and> ls \<noteq> 0 \<and> sgn v \<noteq> ls then cnt + 1 else cnt),
             (amb \<or> \<not> C))"
      proof -
        have "tsign_fold_idx (length ys') 0 (zs @ [w]) (0, 0, amb0)
            = tsign_step (trusted_sgn (length ys') i w) (ls, cnt, amb)"
          using take_step[of w] .
        also have "\<dots> = ((if C then sgn (taylor_shift_list 1 ys' ! i) else ls),
             (if C \<and> ls \<noteq> 0 \<and> sgn (taylor_shift_list 1 ys' ! i) \<noteq> ls then cnt + 1 else cnt),
             (amb \<or> \<not> C))"
          unfolding w_def Ceq
          by (rule tsign_step_bitlen_form_masked[OF lb])
        finally show ?thesis unfolding veq .
      qed
      have lenzsw: "length (zs @ [w]) = Suc i" using zs(1) by simp
      have maskzsw: "\<forall>j<Suc i. (zs @ [w]) ! j = 0 \<or> (zs @ [w]) ! j = taylor_shift_list 1 ys' ! j"
      proof (intro allI impI)
        fix j assume j: "j < Suc i"
        show "(zs @ [w]) ! j = 0 \<or> (zs @ [w]) ! j = taylor_shift_list 1 ys' ! j"
        proof (cases "j < i")
          case True
          then have "(zs @ [w]) ! j = zs ! j" using zs(1) by (simp add: nth_append)
          then show ?thesis using zs(2) True by simp
        next
          case False
          then have ji: "j = i" using j by simp
          have "(zs @ [w]) ! j = w" using zs(1) ji by (simp add: nth_append)
          then show ?thesis unfolding w_def ji by simp
        qed
      qed
      have mstate: "tmask_state ys' amb0
          ((if C then sgn v else ls),
           (if C \<and> ls \<noteq> 0 \<and> sgn v \<noteq> ls then cnt + 1 else cnt),
           (amb \<or> \<not> C)) (Suc i)"
        unfolding tmask_state_def
        by (rule exI[where x="zs @ [w]"]) (simp add: zs(1) lenzsw maskzsw fold_eq)
      show ?thesis
        unfolding comps eq0(2) eq0(3) eq0(4) x1aeq eq0(1)
        using mstate[unfolded suci] by simp
    qed
    done
qed

lemma ethorner_trunc_post_cap:
  assumes ys'eq: "ys' = trunc_list t ys"
    and l2: "Suc 0 < length ys'"
    and iinv: "i \<le> length ys' - 1"
    and cle: "cnt \<le> cap"
    and cap2: "2 \<le> cap"
    and steq: "tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ls, cnt, amb) i"
    and exit: "\<not> (i < length ys' - 1 \<and> cnt < cap)"
    and efeq: "ef = (if ls \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
                      \<and> ls \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else (0::nat))"
  shows "(cap \<le> cnt + ef \<longrightarrow> cap \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
         (\<not> amb \<and> cnt + ef < cap
            \<longrightarrow> cnt + ef = sign_changes_fold (taylor_shift_list 1 ys))"
proof -
  define len' where "len' = length ys'"
  define T where "T = taylor_shift_list 1 ys'"
  define amb0 where "amb0 = (sgn (ys' ! (len' - 1)) = 0)"
  have lenT: "length T = len'" by (simp add: T_def len'_def)
  have len'ys: "len' = length ys" using ys'eq by (simp add: len'_def)
  have Tys: "T = taylor_shift_list 1 (trunc_list t ys)" using ys'eq by (simp add: T_def)
  have tc_target: "trunc_changes (length ys) (taylor_shift_list 1 (trunc_list t ys))
      = trunc_changes len' T" using len'ys Tys by simp
  have mstate: "tmask_state ys' amb0 (ls, cnt, amb) i"
    using steq by (simp add: len'_def amb0_def)
  from exit iinv consider (full) "i = len' - 1" | (abort) "cap \<le> cnt"
    by (auto simp: len'_def)
  then show ?thesis
  proof cases
    case full
    have ysne: "ys' \<noteq> []" using l2 by (cases ys') auto
    have Tne: "T \<noteq> []" using lenT l2 by (auto simp: len'_def)
    have tbutl: "take i T = butlast T"
      using full lenT by (simp add: butlast_conv_take)
    have lastT: "last T = ys' ! (len' - 1)"
      using last_taylor_shift_list[of ys' 1] ysne last_conv_nth[OF ysne]
      by (simp add: T_def len'_def)
    have lastTnth: "last T = T ! (len' - 1)"
      using lenT Tne by (simp add: last_conv_nth)
    have tsl: "trusted_sgn len' (len' - 1) (last T)
        = (if ys' ! (len' - 1) = 0 then None else Some (sgn (ys' ! (len' - 1))))"
      using trusted_sgn_last[of len' "last T"] lastT by simp
    \<comment> \<open>count soundness (usable WITH ambiguity): the invariant's mask, extended by the
       boundary coefficient, is a mask of the whole shifted-truncated list, so the
       boundary-inclusive count \<open>cnt + ef\<close> never exceeds the true count\<close>
    obtain zs where zs: "length zs = i"
      "\<forall>j<i. zs ! j = 0 \<or> zs ! j = T ! j"
      "(ls, cnt, amb) = tsign_fold_idx len' 0 zs (0, 0, amb0)"
      using mstate unfolding tmask_state_def T_def len'_def by blast
    have ws_fold: "tsign_fold_idx len' 0 (zs @ [last T]) (0, 0, amb0)
        = tsign_step (trusted_sgn len' (len' - 1) (last T)) (ls, cnt, amb)"
      using tsign_fold_idx_append[of len' 0 zs "[last T]" "(0, 0, amb0)"] zs(1,3) full by simp
    have ws_cnt: "(\<lambda>(a, b, c). b) (tsign_fold_idx len' 0 (zs @ [last T]) (0, 0, amb0))
        = cnt + ef"
    proof (cases "ys' ! (len' - 1) = 0")
      case True
      then have "ef = 0" using efeq by (simp add: len'_def)
      then show ?thesis unfolding ws_fold using tsl True by simp
    next
      case False
      have sgnne: "sgn (ys' ! (len' - 1)) \<noteq> 0" using False by (simp add: sgn_eq_0_iff)
      have "ef = (if ls \<noteq> 0 \<and> sgn (ys' ! (len' - 1)) \<noteq> ls then 1 else 0)"
        using efeq sgnne by (auto simp: len'_def)
      then show ?thesis unfolding ws_fold using tsl False by simp
    qed
    have ws_len: "length (zs @ [last T]) = length ys"
      using zs(1) full lenT l2 len'ys by (simp add: len'_def)
    have ws_mask: "\<forall>j<length (zs @ [last T]).
        (zs @ [last T]) ! j = 0 \<or> (zs @ [last T]) ! j = taylor_shift_list 1 (trunc_list t ys) ! j"
    proof (intro allI impI)
      fix j assume j: "j < length (zs @ [last T])"
      then have ji: "j \<le> i" using zs(1) by simp
      show "(zs @ [last T]) ! j = 0 \<or> (zs @ [last T]) ! j = taylor_shift_list 1 (trunc_list t ys) ! j"
      proof (cases "j < i")
        case True
        then have "(zs @ [last T]) ! j = zs ! j" using zs(1) by (simp add: nth_append)
        then show ?thesis using zs(2) True Tys by simp
      next
        case False
        then have jeq: "j = i" using ji by simp
        have "(zs @ [last T]) ! j = last T" using zs(1) jeq by (simp add: nth_append)
        then show ?thesis using lastTnth full jeq Tys by simp
      qed
    qed
    \<comment> \<open>the bound is proved in general, before any specialisation to \<open>2\<close>, which is why the generalisation to
       \<open>cap\<close> needs no new mathematics.\<close>
    have le_full: "cnt + ef \<le> sign_changes_fold (taylor_shift_list 1 ys)"
    proof -
      have "(\<lambda>(a, b, c). b) (tsign_fold_idx (length ys) 0 (zs @ [last T]) (0, 0, amb0))
          \<le> sign_changes_fold (taylor_shift_list 1 ys)"
        using tsign_mask_cnt_le_full[OF ws_len ws_mask, of amb0] .
      then show ?thesis
        using ws_cnt len'ys by (simp add: len'_def)
    qed
    \<comment> \<open>the decisive case: \<open>\<not>amb\<close> forces the mask to be TRIVIAL, so the exact transfer
       runs on the UNMASKED prefix fold, which is the very fold the trivial mask denotes\<close>
    have exact_eq: "\<not> amb \<Longrightarrow> cnt + ef = sign_changes_fold (taylor_shift_list 1 ys)"
    proof -
      assume noamb: "\<not> amb"
      have ile: "i \<le> length ys'" using iinv by simp
      have kstate: "(ls, cnt, amb) = tsign_fold_idx len' 0 (butlast T) (0, 0, amb0)"
        using tmask_state_not_amb[OF mstate noamb ile] tbutl by (simp add: len'_def T_def)
      obtain lsF cntF ambF where F:
        "tsign_fold_idx len' 0 (butlast T) (0, 0, False) = (lsF, cntF, ambF)"
        by (cases "tsign_fold_idx len' 0 (butlast T) (0, 0, False)") auto
      have fs: "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx len' 0 (butlast T) (0, 0, amb0))
          = (\<lambda>(a, b, c). (a, b)) (tsign_fold_idx len' 0 (butlast T) (0, 0, False))"
        by (rule tsign_fold_idx_fst_snd_cong) simp
      have "(ls, cnt) = (lsF, cntF)"
        using arg_cong[OF kstate, of "\<lambda>(a, b, c). (a, b)"] fs F by simp
      then have lseq: "ls = lsF" and cnteq: "cnt = cntF" by auto
      have "amb = (\<lambda>(a, b, c). c) (tsign_fold_idx len' 0 (butlast T) (0, 0, amb0))"
        using arg_cong[OF kstate, of "\<lambda>(a, b, c). c"] by simp
      also have "\<dots> = (amb0 \<or> (\<lambda>(a, b, c). c) (tsign_fold_idx len' 0 (butlast T) (0, 0, False)))"
        by (rule tsign_fold_idx_amb_or)
      also have "\<dots> = (amb0 \<or> ambF)" using F by simp
      finally have ambeq: "amb = (amb0 \<or> ambF)" .
      have tc: "trunc_changes len' T
          = (case tsign_step (trusted_sgn len' (len' - 1) (last T)) (lsF, cntF, ambF)
             of (_, c, a) \<Rightarrow> (c, a))"
        using trunc_changes_split_last[OF Tne, of len'] F lenT by simp
      have main: "trunc_changes len' T = (cnt + ef, amb)"
      proof (cases "ys' ! (len' - 1) = 0")
        case True
        then have "trunc_changes len' T = (cntF, True)"
          using tc tsl by simp
        moreover have "ef = 0" using efeq True by (simp add: len'_def)
        moreover have "amb0 = True" using amb0_def True by simp
        ultimately show ?thesis using cnteq ambeq by simp
      next
        case False
        then have step: "tsign_step (trusted_sgn len' (len' - 1) (last T)) (lsF, cntF, ambF)
            = (sgn (ys' ! (len' - 1)),
               (if lsF \<noteq> 0 \<and> sgn (ys' ! (len' - 1)) \<noteq> lsF then cntF + 1 else cntF), ambF)"
          using tsl by simp
        have sgnne: "sgn (ys' ! (len' - 1)) \<noteq> 0" using False by (simp add: sgn_eq_0_iff)
        have "ef = (if lsF \<noteq> 0 \<and> sgn (ys' ! (len' - 1)) \<noteq> lsF then 1 else 0)"
          using efeq lseq sgnne by (auto simp: len'_def)
        moreover have "amb0 = False" using amb0_def False by (simp add: sgn_eq_0_iff)
        ultimately show ?thesis using tc step cnteq ambeq by simp
      qed
      have main': "trunc_changes (length ys) (taylor_shift_list 1 (trunc_list t ys))
          = (cnt + ef, amb)"
        using main tc_target by simp
      show "cnt + ef = sign_changes_fold (taylor_shift_list 1 ys)"
        using trunc_changes_decisive_exact[of ys t] main' noamb by simp
    qed
    show ?thesis using le_full exact_eq by auto
  next
    case abort
    \<comment> \<open>@{thm [source] tmask_state_cnt_le} is independent of the threshold (it bounds the masked prefix count by
       the exact count), so the early-abort case is one step at any cap. The decisive conjunct is vacuous here:
       \<open>cap \<le> cnt \<le> cnt + ef\<close>.\<close>
    have ile: "i \<le> length ys" using iinv len'ys by (simp add: len'_def)
    have tcap: "cap \<le> sign_changes_fold (taylor_shift_list 1 ys)"
      using tmask_state_cnt_le[OF mstate ys'eq ile] abort by simp
    have cefcap: "cap \<le> cnt + ef" using abort by simp
    show ?thesis using tcap cefcap by auto
  qed
qed

text \<open>The truncated CAP kernel: @{const poly_ethorner_count_trunc_monadic} with the loop's
  abort bound lifted from the literal \<open>2\<close> to \<open>cap\<close>. Everything else — the truncated
  triangle, the per-index trust threshold, the boundary bit, the \<open>amb\<close> flag, the free — is
  that op unchanged.\<close>
definition poly_ethorner_count_trunc_cap_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> (nat \<times> bool) nres" where
"poly_ethorner_count_trunc_cap_monadic cap xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  if len \<le> 1 then doN { (PR_CONST poly_free_monadic) xs; RETURN (0, False) }
  else doN {
    ASSERT (1 < len);
    bthr \<leftarrow> (PR_CONST snat_bitlen_monadic) len;
    ASSERT (len * bthr < max_snat LENGTH(gmp_poly_len));
    limit \<leftarrow> RETURN (len - 1);
    ASSERT (limit < length xs);
    s_last \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs limit;
    let init = ((0::nat, 0::int, 0::nat, s_last = 0), xs);
    st \<leftarrow> WHILET
      (\<lambda>st. (PR_CONST ethorner_count_trunc_cap_cond) cap limit st)
      (\<lambda>st. (PR_CONST ethorner_count_trunc_cap_body_mop_monadic) cap len bthr st)
      init;
    (cnt, last_s, amb, xs_final) \<leftarrow>
      (PR_CONST ethorner_count_trunc_result_mop_monadic) st;
    extra_f \<leftarrow> (if last_s \<noteq> 0 \<and> s_last \<noteq> 0 \<and> last_s \<noteq> s_last
                then RETURN (1::nat) else RETURN 0);
    ASSERT (cnt + extra_f < max_snat LENGTH(gmp_poly_len));
    final_cnt \<leftarrow> RETURN (cnt + extra_f);
    (PR_CONST poly_free_monadic) xs_final;
    RETURN (final_cnt, amb)
  }
}"

sepref_register "PR_CONST poly_ethorner_count_trunc_cap_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> (nat \<times> bool) nres"

text \<open>The kernel's contract, in the CAP shape rather than the trichotomy: decisive either when
  the scan completed with no ambiguity (\<open>cnt\<close> is then the exact count) or when it aborted at
  \<open>cap\<close> (the exact count is then at least \<open>cap\<close>, which is all the caller's test asks).\<close>
lemma poly_ethorner_count_trunc_cap_monadic_classify:
  assumes ys'eq: "ys' = trunc_list t ys"
    and lbound: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length ys * nat_bitlen (length ys) < max_snat LENGTH(gmp_poly_len)"
    and cap2: "2 \<le> cap"
  shows "poly_ethorner_count_trunc_cap_monadic cap ys' \<le> SPEC (\<lambda>(cnt, amb).
    (cap \<le> cnt \<longrightarrow> cap \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
    (\<not> amb \<and> cnt < cap
       \<longrightarrow> cnt = sign_changes_fold (taylor_shift_list 1 ys)))"
proof -
  have lenys': "length ys' = length ys" using ys'eq by simp
  have lb': "length ys' + 1 < max_snat LENGTH(gmp_poly_len)"
    using lbound lenys' by simp
  have pb': "length ys' * nat_bitlen (length ys') < max_snat LENGTH(gmp_poly_len)"
    using pbound lenys' by simp
  have snatlen: "length ys' < max_snat LENGTH(gmp_poly_len)" using lb' by simp
  \<comment> \<open>\<^bold>\<open>Why the contract needs no bound on \<open>cap\<close>.\<close> The two result-fits-snat side conditions need
     \<open>Suc cnt < max_snat\<close>. Assuming \<open>cap + 1 < max_snat\<close> would add a conjunct for the caller, and it is not needed: the
     count is bounded by the polynomial, not by the cap. @{thm [source] tmask_state_cnt_le} bounds \<open>cnt\<close> by the exact
     count, and the exact count is bounded by the length via @{thm [source] fold_sign_step_snd_le}, so \<open>lbound\<close> alone
     discharges both.\<close>
  have scf_len: "sign_changes_fold zs \<le> length zs" for zs :: "int list"
    using fold_sign_step_snd_le[of zs "(0, 0)"] by (simp add: sign_changes_fold_def)
  show ?thesis
    unfolding poly_ethorner_count_trunc_cap_monadic_def ethorner_count_trunc_cap_cond_def
      ethorner_count_trunc_result_mop_monadic_def poly_length_monadic_def
      poly_coeff_sgn_monadic_def PR_CONST_def Let_def
    apply (refine_vcg snat_bitlen_monadic_correct[THEN order_trans]
        WHILET_rule[where
          R="measure (\<lambda>((i, ls, cnt, amb), xsl :: int list). length ys' - 1 - i)"
          and I="\<lambda>((i, ls, cnt, amb), xsl).
               i \<le> length ys' - 1 \<and> cnt \<le> cap \<and> length xsl = length ys'
             \<and> xsl = ethorner_outer_step_fun i ys'
             \<and> tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ls, cnt, amb) i"])
    apply (simp_all add: snatlen pb' tmask_state_init cap2)
    \<comment> \<open>1: the \<open>length ys' \<le> 1\<close> short-circuit. Only ONE goal survives here where the
       exact trichotomy leaves three -- the cap contract's first conjunct is vacuous at
       \<open>cnt = 0\<close> given \<open>2 \<le> cap\<close>, and \<open>simp_all\<close> closes it with @{thm [source] cap2}.\<close>
    subgoal using lenys' scf_taylor_short[of ys] by simp
    \<comment> \<open>2-3: pure \<open>ys'\<close> headroom facts\<close>
    subgoal using snatlen by simp
    subgoal using pb' by simp
    \<comment> \<open>4: the loop BODY -- destructure the atomic state so
       @{thm [source] ethorner_trunc_body_pres_cap} unifies\<close>
    subgoal premises prems for s
    proof -
      obtain i ls cnt amb xsl where seq: "s = ((i, ls, cnt, amb), xsl)"
        by (metis prod.collapse)
      show ?thesis
        using prems
        unfolding seq
        apply (refine_vcg ethorner_trunc_body_pres_cap)
        using pb' lb' by (auto simp: seq One_nat_def split: prod.splits)
    qed
    \<comment> \<open>5: the first \<open>result-fits-snat\<close> side condition, via the count bound above\<close>
    subgoal premises prems for s a b aa ba ab bb ac bc bd be
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> ac \<le> cap \<and> length b = length ys' \<and>
          tmask_state ys' False (ab, ac, bc) aa"
        using prems(3) by (simp add: One_nat_def)
      have ile: "aa \<le> length ys"
        using conj[THEN conjunct1] lenys' diff_le_self le_trans by metis
      have "ac \<le> sign_changes_fold (taylor_shift_list 1 ys)"
        using tmask_state_cnt_le[OF conj[THEN conjunct2, THEN conjunct2, THEN conjunct2]
            ys'eq ile] .
      then have "ac \<le> length ys" using scf_len[of "taylor_shift_list 1 ys"] by simp
      then show ?thesis using lbound by simp
    qed
    \<comment> \<open>6, 7: the \<open>ef = 1\<close> boundary branch; 9, 10: the \<open>ef = 0\<close> branch. All four are
       @{thm [source] ethorner_trunc_post_cap} instances, its \<open>ef\<close> fixed by the goal's own
       boundary if-expression via \<open>efeq\<close>.\<close>
    subgoal premises prems for s a b aa ba ab bb ac bc bd be af
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> ac \<le> cap \<and> length b = length ys' \<and>
          tmask_state ys' False (ab, ac, bc) aa"
        using prems(3) by (simp add: One_nat_def)
      have bnd: "ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1))"
        using prems(12) by (simp add: One_nat_def)
      have amb0eq: "(sgn (ys' ! (length ys' - 1)) = 0) = False" using bnd by simp
      have steq: "tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, bc) aa"
        using conj amb0eq by simp
      have exit: "\<not> (aa < length ys' - 1 \<and> ac < cap)"
        using prems(4) conj by (auto simp: One_nat_def)
      have efeq: "1 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else (0::nat))"
        using bnd by simp
      have main: "(cap \<le> ac + 1 \<longrightarrow> cap \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> bc \<and> ac + 1 < cap
           \<longrightarrow> ac + 1 = sign_changes_fold (taylor_shift_list 1 ys))"
        using ethorner_trunc_post_cap[OF ys'eq prems(1) conj[THEN conjunct1]
            conj[THEN conjunct2, THEN conjunct1] cap2 steq exit efeq] by simp
      show ?thesis using main prems(15) by (simp add: One_nat_def)
    qed
    \<comment> \<open>7: \<open>ef = 1\<close>, the DECISIVE branch. \<open>i = length ys' - 1\<close> makes \<open>exit\<close> immediate
       (the loop ran to completion rather than aborting), and \<open>Suc ac < cap\<close> supplies both
       \<open>cle\<close> and the conjunct's own guard.\<close>
    subgoal premises prems for s a ba ab bb ac bc bd be af x2
    proof -
      have steq: "tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, False)
          (length ys' - 1)"
        using prems(3,11) by (simp add: One_nat_def)
      have bnd: "ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1))"
        using prems(11) by (simp add: One_nat_def)
      have cle: "ac \<le> cap" using prems(14) by simp
      have exit: "\<not> (length ys' - 1 < length ys' - 1 \<and> ac < cap)" by simp
      have efeq: "1 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else (0::nat))"
        using bnd by simp
      have main: "(cap \<le> ac + 1 \<longrightarrow> cap \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> False \<and> ac + 1 < cap
           \<longrightarrow> ac + 1 = sign_changes_fold (taylor_shift_list 1 ys))"
        using ethorner_trunc_post_cap[OF ys'eq prems(1) order_refl cle cap2 steq exit efeq]
        by simp
      show ?thesis using main prems(14) by (simp add: One_nat_def)
    qed
    \<comment> \<open>8: the second \<open>result-fits-snat\<close> side condition (the \<open>ef = 0\<close> branch)\<close>
    subgoal premises prems for s a b aa ba ab bb ac bc bd be
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> ac \<le> cap \<and> length b = length ys' \<and>
          tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, bc) aa"
        using prems(3) by (simp add: One_nat_def)
      have ile: "aa \<le> length ys"
        using conj[THEN conjunct1] lenys' diff_le_self le_trans by metis
      have "ac \<le> sign_changes_fold (taylor_shift_list 1 ys)"
        using tmask_state_cnt_le[OF conj[THEN conjunct2, THEN conjunct2, THEN conjunct2]
            ys'eq ile] .
      then have "ac \<le> length ys" using scf_len[of "taylor_shift_list 1 ys"] by simp
      then show ?thesis using lbound by simp
    qed
    \<comment> \<open>9: \<open>ef = 0\<close> and the count sits AT the cap -- the early-abort case, where
       \<open>exit\<close> holds because \<open>cap < cap\<close> is false.\<close>
    subgoal premises prems for s a b aa ba ab bb bc ad bd be
    proof -
      have conj: "aa \<le> length ys' - 1 \<and> length b = length ys' \<and>
          tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, cap, bc) aa"
        using prems(3) by (simp add: One_nat_def)
      have efeq: "0 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else (0::nat))"
        using prems(11) by (simp add: One_nat_def)
      have exit: "\<not> (aa < length ys' - 1 \<and> cap < cap)" by simp
      have main: "(cap \<le> cap + 0 \<longrightarrow> cap \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> bc \<and> cap + 0 < cap
           \<longrightarrow> cap + 0 = sign_changes_fold (taylor_shift_list 1 ys))"
        using ethorner_trunc_post_cap[OF ys'eq prems(1) conj[THEN conjunct1] order_refl
            cap2 conj[THEN conjunct2, THEN conjunct2] exit efeq] by simp
      show ?thesis using main by simp
    qed
    \<comment> \<open>10: \<open>ef = 0\<close>, DECISIVE branch -- the full scan with no ambiguity anywhere\<close>
    subgoal premises prems for s a ba ab bb ac bc bd be af x2
    proof -
      have steq: "tmask_state ys' (sgn (ys' ! (length ys' - 1)) = 0) (ab, ac, False)
          (length ys' - 1)"
        using prems(3) by (simp add: One_nat_def)
      have cle: "ac \<le> cap" using prems(14) by simp
      have exit: "\<not> (length ys' - 1 < length ys' - 1 \<and> ac < cap)" by simp
      have efeq: "0 = (if ab \<noteq> 0 \<and> sgn (ys' ! (length ys' - 1)) \<noteq> 0
          \<and> ab \<noteq> sgn (ys' ! (length ys' - 1)) then 1 else (0::nat))"
        using prems(11) by (simp add: One_nat_def)
      have main: "(cap \<le> ac + 0 \<longrightarrow> cap \<le> sign_changes_fold (taylor_shift_list 1 ys)) \<and>
        (\<not> False \<and> ac + 0 < cap
           \<longrightarrow> ac + 0 = sign_changes_fold (taylor_shift_list 1 ys))"
        using ethorner_trunc_post_cap[OF ys'eq prems(1) order_refl cle cap2 steq exit efeq]
        by simp
      show ?thesis using main prems(14) by (simp add: One_nat_def)
    qed
    done
qed

sepref_definition poly_ethorner_count_trunc_cap_impl [llvm_code] is
  "uncurry poly_ethorner_count_trunc_cap_monadic" ::
  "[\<lambda>(cap, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  unfolding poly_ethorner_count_trunc_cap_monadic_def Let_def
  supply [sepref_fr_rules] =
    ethorner_count_trunc_cap_cond_impl_hnr
    ethorner_count_trunc_cap_body_impl_hnr
    ethorner_count_trunc_result_impl_hnr
  apply (annot_sint_const gmp_int_t)
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_ethorner_count_trunc_cap_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_ethorner_count_trunc_cap_impl,
    uncurry (PR_CONST poly_ethorner_count_trunc_cap_monadic)) \<in>
    [\<lambda>(cap, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
        \<rightarrow> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  using poly_ethorner_count_trunc_cap_impl.refine
  by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The truncated capped count, composed.\<close> @{const carried_descartes_count_trunc_body_monadic} with \<open>2\<close> replaced
  by \<open>cap\<close> in the abort bound and the decisive test, and every exact call replaced by the capped exact call: an \<open>O(1)\<close>
  budget read, a single budget \<open>w = 2n\<close> (\<open>t = nb - (2*len + trunc_count_margin)\<close> with \<open>trunc_count_margin = 0\<close>), a
  closed-form machine-word threshold, and the exact path as a fallback.

  \<^bold>\<open>Costs.\<close> (i) The three non-truncating exits (\<open>len \<le> 1\<close>, \<open>\<not>attempt\<close> and the lead-survival test) reuse \<open>rxs\<close>, the
  reverse already made, so a rejection costs the exact op plus \<open>O(1)\<close> of guard. Only the ambiguity fallback reverses
  again, and must, because @{const poly_trunc_in_place_monadic} has consumed \<open>rxs\<close>. (ii) No allocation is added: the
  truncation is in place and the reverse is the one the exact op makes.\<close>
definition carried_descartes_count_trunc_cap_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_trunc_cap_monadic cap xs \<equiv> doN {
  rxs \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
  len \<leftarrow> (PR_CONST poly_length_monadic) rxs;
  ASSERT (len = length rxs);
  if len \<le> 1 then (PR_CONST poly_ethorner_count_cap_monadic) cap rxs
  else doN {
    ASSERT (0 < len \<and> len - 1 < length rxs);
    (lbl, nb) \<leftarrow> (PR_CONST lead_budget_mop) rxs (len - 1);
    bthr \<leftarrow> (PR_CONST snat_bitlen_monadic) len;
    let attempt =
      (2 * len + trunc_count_margin < nb \<and>
       2 * len + trunc_count_margin < max_snat LENGTH(gmp_poly_len) \<and>
       len * bthr < max_snat LENGTH(gmp_poly_len) \<and>
       nb < max_snat LENGTH(gmp_poly_len));
    if \<not> attempt then (PR_CONST poly_ethorner_count_cap_monadic) cap rxs
    else doN {
      t \<leftarrow> RETURN (nb - (2 * len + trunc_count_margin));
      if lbl \<le> t then (PR_CONST poly_ethorner_count_cap_monadic) cap rxs
      else doN {
        rxs \<leftarrow> (PR_CONST poly_trunc_in_place_monadic) t rxs;
        (cnt, amb) \<leftarrow> (PR_CONST poly_ethorner_count_trunc_cap_monadic) cap rxs;
        if \<not> amb \<or> cap \<le> cnt then RETURN cnt
        else doN {
          rxs2 \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
          ASSERT (length rxs2 + 1 < max_snat LENGTH(gmp_poly_len));
          (PR_CONST poly_ethorner_count_cap_monadic) cap rxs2
        }
      }
    }
  }
}"

sepref_register "PR_CONST carried_descartes_count_trunc_cap_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

text \<open>The composed contract. \<^bold>\<open>Statement TOKEN-IDENTICAL to
  @{thm [source] carried_descartes_count_cap_monadic_classify}\<close> — same two assumptions, same
  conclusion — so this is a drop-in for the exact op at every call site and no caller
  obligation moves.\<close>
lemma carried_descartes_count_trunc_cap_monadic_classify:
  assumes len_bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)" and cap2: "2 \<le> cap"
  shows "carried_descartes_count_trunc_cap_monadic cap xs
    \<le> SPEC (\<lambda>r.
        (r < cap \<longrightarrow> r = carried_descartes_count xs) \<and>
        (cap \<le> r \<longrightarrow> cap \<le> carried_descartes_count xs))"
  using len_bound cap2
  unfolding carried_descartes_count_trunc_cap_monadic_def carried_descartes_count_def
    poly_length_monadic_def lead_budget_mop_def poly_coeff_bitlen2_monadic_def
    mpz_bitlen2_monadic_def PR_CONST_def Let_def
  apply (refine_vcg
      poly_reverse_monadic_correct[THEN order_trans]
      snat_bitlen_monadic_correct[THEN order_trans]
      poly_trunc_in_place_correct[THEN order_trans]
      poly_ethorner_count_trunc_cap_monadic_classify[THEN order_trans]
      poly_ethorner_count_cap_monadic_classify[THEN order_trans])
  \<comment> \<open>34 goals, where the trichotomy ladder (@{thm [source] carried_descartes_count_trunc_body_classify}) has 43:
     the cap contract has two conjuncts where the trichotomy has three. \<open>lead_budget_mop\<close>'s two clamp branches still
     double the ladder: G1-20 is the first, G21-34 the second. G14/G28 are the kernel-classification \<open>trunc_list\<close> pins
     and stay apply-style, since a \<open>subgoal\<close> would fix the shared schematics.\<close>
  subgoal by simp
  subgoal by simp
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by simp
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  apply (rule refl)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by simp
  subgoal by simp
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  apply (rule refl)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

text \<open>The Sepref-shaped pipeline for the truncated capped count, following the truncating one
  (@{const carried_descartes_count_trunc_tail_mop} and related ops) with \<open>2\<close> replaced by \<open>cap\<close>. The three pure guard ops,
  @{const trunc_lead_idx_mop}, @{const trunc_attempt_guard_mop} and @{const trunc_gap_mop}, do not depend on the cap and
  are reused.\<close>
definition trunc_fallback_cap_mop :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"trunc_fallback_cap_mop cap xs \<equiv> doN {
  rxs2 \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs2 + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_ethorner_count_cap_monadic) cap rxs2
}"

sepref_register "PR_CONST trunc_fallback_cap_mop" :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

sepref_definition trunc_fallback_cap_impl [llvm_inline] is
  "uncurry trunc_fallback_cap_mop" ::
  "[\<lambda>(cap, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k
      \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding trunc_fallback_cap_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma trunc_fallback_cap_impl_hnr[sepref_fr_rules]:
  "(uncurry trunc_fallback_cap_impl, uncurry (PR_CONST trunc_fallback_cap_mop)) \<in>
    [\<lambda>(cap, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k
        \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using trunc_fallback_cap_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The post-kernel decision, cap-lifted: the truncated count is decisive when it is
  unambiguous or has already reached \<open>cap\<close> — the second disjunct is @{const
  trunc_decide_mop}'s \<open>2 \<le> cnt\<close> with the literal lifted, and it is the whole reason the
  kernel's abort had to stay at \<open>cap\<close>.\<close>
definition trunc_decide_cap_mop :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"trunc_decide_cap_mop cap cnt amb xs \<equiv>
  (if \<not> amb \<or> cap \<le> cnt then RETURN cnt else (PR_CONST trunc_fallback_cap_mop) cap xs)"

sepref_register "PR_CONST trunc_decide_cap_mop"
  :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

sepref_definition trunc_decide_cap_impl [llvm_inline] is
  "uncurry3 trunc_decide_cap_mop" ::
  "[\<lambda>(((cap, cnt), amb), xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding trunc_decide_cap_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma trunc_decide_cap_impl_hnr[sepref_fr_rules]:
  "(uncurry3 trunc_decide_cap_impl, uncurry3 (PR_CONST trunc_decide_cap_mop)) \<in>
    [\<lambda>(((cap, cnt), amb), xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using trunc_decide_cap_impl.refine
  by (simp add: PR_CONST_def)

definition carried_descartes_count_trunc_cap_tail_mop ::
  "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_trunc_cap_tail_mop cap len rxs xs \<equiv> doN {
  lidx \<leftarrow> (PR_CONST trunc_lead_idx_mop) len;
  ASSERT (0 < len \<and> lidx < length rxs);
  (lbl, nb) \<leftarrow> (PR_CONST lead_budget_mop) rxs lidx;
  bthr \<leftarrow> (PR_CONST snat_bitlen_monadic) len;
  attempt \<leftarrow> (PR_CONST trunc_attempt_guard_mop) len nb bthr;
  if \<not> attempt then (PR_CONST poly_ethorner_count_cap_monadic) cap rxs
  else doN {
    ASSERT (2 * len \<le> nb);
    (t, tu) \<leftarrow> (PR_CONST trunc_gap_mop) nb len;
    ASSERT (0 < t \<and> t < max_snat LENGTH(gmp_poly_len));
    if lbl \<le> tu then (PR_CONST poly_ethorner_count_cap_monadic) cap rxs
    else doN {
      rxs \<leftarrow> (PR_CONST poly_trunc_in_place_monadic) t rxs;
      ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
      (cnt, amb) \<leftarrow> (PR_CONST poly_ethorner_count_trunc_cap_monadic) cap rxs;
      (PR_CONST trunc_decide_cap_mop) cap cnt amb xs
    }
  }
}"

sepref_register "PR_CONST carried_descartes_count_trunc_cap_tail_mop"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> nat nres"

definition carried_descartes_count_trunc_cap_impl_form :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat nres" where
"carried_descartes_count_trunc_cap_impl_form cap xs \<equiv> doN {
  rxs \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
  ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
  len \<leftarrow> (PR_CONST poly_length_monadic) rxs;
  ASSERT (len = length rxs);
  if len \<le> 1 then (PR_CONST poly_ethorner_count_cap_monadic) cap rxs
  else (PR_CONST carried_descartes_count_trunc_cap_tail_mop) cap len rxs xs
}"

lemma carried_descartes_count_trunc_cap_impl_form_eq:
  "carried_descartes_count_trunc_cap_impl_form cap xs
    = carried_descartes_count_trunc_cap_monadic cap xs"
  unfolding carried_descartes_count_trunc_cap_impl_form_def
    carried_descartes_count_trunc_cap_tail_mop_def trunc_decide_cap_mop_def
    trunc_fallback_cap_mop_def
    carried_descartes_count_trunc_cap_monadic_def PR_CONST_def
  apply (simp only: trunc_attempt_guard_mop_eq trunc_count_margin_def Let_def
    add_0_right nres_monad1)
  apply (rule bind_cong[OF refl])
  apply (rule bind_cong[OF refl])
  apply (rule bind_cong[OF refl])
  apply (rule bind_cong[OF refl])
  subgoal for x xa xb xc
    apply (cases "xb \<le> (1::nat)")
    subgoal by simp
    apply simp
    subgoal premises prems
      apply (subgoal_tac "1 \<le> xb")
      prefer 2
      subgoal using prems by linarith
      apply (simp only: trunc_lead_idx_mop_eq nres_monad1 One_nat_def)
      apply (rule bind_cong[OF refl])
      apply (rule bind_cong[OF refl])
      apply (simp only: split_paired_all prod.case)
      apply (rule bind_cong[OF refl])
      subgoal for xa lbl nb bthr
        apply (cases "2 * xb < nb \<and> 2 * xb < max_snat LENGTH(gmp_poly_len) \<and>
          xb * bthr < max_snat LENGTH(gmp_poly_len) \<and> nb < max_snat LENGTH(gmp_poly_len)")
        prefer 2
        subgoal by simp
        subgoal premises prems2
          apply (subgoal_tac "2 * xb \<le> nb")
          prefer 2
          subgoal using prems2 by linarith
          apply (subgoal_tac
            "0 < nb - 2 * xb \<and> nb - 2 * xb < max_snat LENGTH(gmp_poly_len)")
          prefer 2
          subgoal using prems2 by (intro conjI; linarith)
          apply (simp only: ASSERT_true_bind trunc_gap_mop_eq nres_monad1 prod.case)
          apply (rule if_cong[OF refl])
          subgoal by (rule refl)
          apply (rule if_cong[OF refl])
          subgoal by (rule refl)
          apply (subst trunc_in_place_length_absorb[unfolded One_nat_def])
          subgoal using prems2 by linarith
          by (rule refl)
        done
      done
    done
  done

lemma carried_descartes_count_trunc_cap_impl_form_eq_ext:
  "carried_descartes_count_trunc_cap_impl_form = carried_descartes_count_trunc_cap_monadic"
  by (intro ext) (rule carried_descartes_count_trunc_cap_impl_form_eq)

sepref_definition carried_descartes_count_trunc_cap_tail_impl [llvm_inline] is
  "uncurry3 carried_descartes_count_trunc_cap_tail_mop" ::
  "[\<lambda>(((cap, len), rxs), xs). 1 \<le> len \<and>
      length rxs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding carried_descartes_count_trunc_cap_tail_mop_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma carried_descartes_count_trunc_cap_tail_impl_hnr[sepref_fr_rules]:
  "(uncurry3 carried_descartes_count_trunc_cap_tail_impl,
    uncurry3 (PR_CONST carried_descartes_count_trunc_cap_tail_mop)) \<in>
    [\<lambda>(((cap, len), rxs), xs). 1 \<le> len \<and>
      length rxs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using carried_descartes_count_trunc_cap_tail_impl.refine
  by (simp add: PR_CONST_def)

text \<open>BORROWED input (\<open>\<^sup>k\<close>), signature TOKEN-IDENTICAL to
  @{const carried_descartes_count_cap_impl} — the op this drops in for.\<close>
sepref_definition carried_descartes_count_trunc_cap_impl [llvm_code] is
  "uncurry carried_descartes_count_trunc_cap_impl_form" ::
  "[\<lambda>(cap, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k
      \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding carried_descartes_count_trunc_cap_impl_form_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma carried_descartes_count_trunc_cap_impl_hnr[sepref_fr_rules]:
  "(uncurry carried_descartes_count_trunc_cap_impl,
    uncurry (PR_CONST carried_descartes_count_trunc_cap_monadic)) \<in>
    [\<lambda>(cap, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k
        \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using carried_descartes_count_trunc_cap_impl.refine
  by (simp add: PR_CONST_def carried_descartes_count_trunc_cap_impl_form_eq_ext)

text \<open>Accept-test arithmetic at \<open>cap = v\<close>. The capped kernel aborts at the \<open>v\<close>-th sign change; with the
  window-count monotonicity bound \<open>c \<le> v\<close> (\<open>carried_window_count_mono\<close>) that abort is conclusive: \<open>v \<le> r\<close> proves \<open>c = v\<close>,
  so accepted windows do not scan the rest of the list. A cap above \<open>v\<close> would need no monotonicity bound but would lose
  that early exit.\<close>
lemma cap_match_mono_iff:
  fixes r v c :: nat
  assumes post: "(r < v \<longrightarrow> r = c) \<and> (v \<le> r \<longrightarrow> v \<le> c)"
      and le: "c \<le> v"
  shows "(v \<le> r) = (c = v)"
proof (cases "v \<le> r")
  case True
  with post have "v \<le> c" by simp
  with le show ?thesis using True by simp
next
  case False
  hence "r < v" by simp
  with post have "r = c" by simp
  with \<open>r < v\<close> show ?thesis using False by simp
qed

text \<open>The derived cap-kernel spec the fold consumes: under the mono bound \<open>count ys \<le> v\<close>,
  the test \<open>v \<le> r\<close> decides \<open>count ys = v\<close> exactly.\<close>
lemma cap_count_match_mono:
  assumes len: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
      and v2: "2 \<le> v"
      and le: "carried_descartes_count ys \<le> v"
  shows "carried_descartes_count_cap_monadic v ys
    \<le> SPEC (\<lambda>r. (v \<le> r) = (carried_descartes_count ys = v))"
proof -
  have base: "carried_descartes_count_cap_monadic v ys \<le> SPEC (\<lambda>r.
      (r < v \<longrightarrow> r = carried_descartes_count ys) \<and>
      (v \<le> r \<longrightarrow> v \<le> carried_descartes_count ys))"
    by (rule carried_descartes_count_cap_monadic_classify[OF len v2])
  show ?thesis
    by (rule SPEC_cons_rule[OF base]) (rule cap_match_mono_iff[OF _ le])
qed

text \<open>The accept test over the truncating op, derived as the exact one is: the classification it consumes has
  the same statement.\<close>
lemma cap_count_match_mono_trunc:
  assumes len: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
      and v2: "2 \<le> v"
      and le: "carried_descartes_count ys \<le> v"
  shows "carried_descartes_count_trunc_cap_monadic v ys
    \<le> SPEC (\<lambda>r. (v \<le> r) = (carried_descartes_count ys = v))"
proof -
  have base: "carried_descartes_count_trunc_cap_monadic v ys \<le> SPEC (\<lambda>r.
      (r < v \<longrightarrow> r = carried_descartes_count ys) \<and>
      (v \<le> r \<longrightarrow> v \<le> carried_descartes_count ys))"
    by (rule carried_descartes_count_trunc_cap_monadic_classify[OF len v2])
  show ?thesis
    by (rule SPEC_cons_rule[OF base]) (rule cap_match_mono_iff[OF _ le])
qed


subsection \<open>The speculative probe rejection\<close>

text \<open>\<^bold>\<open>What this is.\<close> The Newton window probe (\<open>newton_try_window_monadic\<close> in \<open>Newton\<close>) builds the candidate child
  exactly (an \<open>O(deg\<^sup>2)\<close> Ruffini triangle at full coefficient width) and only then counts it, to test \<open>count cand = v\<close>.
  When the answer is no, the build is wasted. This decides the rejection without the exact build.

  \<^bold>\<open>The mechanism needs no error analysis.\<close> The probe pipeline, @{const carried_init_same_den} followed by
  @{const carried_descartes_count}, is linear with non-negative coefficients whenever the window offset \<open>l\<close> is
  non-negative, which the call site asserts (\<open>0 \<le> m\<close>): \<open>scale_for_fractional_shift\<close> and \<open>scale_poly_list\<close> multiply
  entry \<open>i\<close> by a positive constant, and \<open>(taylor_shift_list c v)\<^sub>j = \<Sum>\<^sub>i C(i,j) c\<^sup>i\<^sup>-\<^sup>j v\<^sub>i\<close> has non-negative coefficients for
  \<open>0 \<le> c\<close>. So floor truncation gives a one-sided enclosure: with \<open>q\<^sub>i = x\<^sub>i div b\<close> and \<open>b > 0\<close>,

    \<open>b * q \<le> xs \<le> b * (q + 1)\<close>   pointwise, hence   \<open>b * pipe q \<le> pipe xs \<le> b * pipe (q + 1)\<close>

  by monotonicity, with the scalars extracted by homogeneity. A coefficient's sign is certain when \<open>0 < (pipe q)\<^sub>j\<close> or
  \<open>(pipe (q+1))\<^sub>j < 0\<close>, and in both cases it equals \<open>sgn (pipe q)\<^sub>j\<close>, so the certified count is the count of the truncated
  build (\<open>probe_decide_sound\<close>).

  \<^bold>\<open>Consequences.\<close> (a) No amplification bound or error composition is needed: the enclosure is exact, and the
  mathematics is monotonicity, homogeneity and the floor decomposition. (b) The decide uses existing ops
  (@{const poly_trunc_in_place_monadic}, @{const carried_init_inplace_monadic}, @{const poly_reverse_in_place_monadic},
  @{const poly_taylor_shift_one_monadic}, @{const poly_sign_changes_monadic}); the only new low-level op is a
  per-coefficient increment over @{const mpz_add_ui.aop_r1_impl}, so there is no new GMP binding. (c) The truncation
  exponent and the admission gate affect only performance: soundness holds for every \<open>b = 2\<^sup>t\<close>, so they owe only a
  no-failure obligation, as for @{const lead_budget_mop}.

  The lemmas carry the \<open>pipe_\<close>/\<open>probe_\<close> prefixes.\<close>

(* ---- pointwise monotonicity of each pipeline stage (int, non-negative multipliers) ---- *)

lemma pipe_ruffini_step_mono:
  fixes c :: int
  shows "0 \<le> c \<Longrightarrow> a \<le> a' \<Longrightarrow> list_all2 (\<le>) qs qs'
         \<Longrightarrow> list_all2 (\<le>) (ruffini_step c a qs) (ruffini_step c a' qs')"
proof (induction qs arbitrary: a a' qs')
  case Nil then show ?case by (cases qs') auto
next
  case (Cons q qs)
  from Cons.prems(3) obtain q' qs'' where qs': "qs' = q' # qs''"
    and hd: "q \<le> q'" and tl: "list_all2 (\<le>) qs qs''"
    by (cases qs') auto
  have "a + c * q \<le> a' + c * q'"
    using Cons.prems(1,2) hd by (simp add: add_mono mult_left_mono)
  moreover have "list_all2 (\<le>) (ruffini_step c q qs) (ruffini_step c q' qs'')"
    using Cons.IH[OF Cons.prems(1) hd tl] .
  ultimately show ?case by (simp add: qs')
qed

lemma pipe_taylor_shift_list_mono:
  fixes c :: int
  shows "0 \<le> c \<Longrightarrow> list_all2 (\<le>) xs ys
         \<Longrightarrow> list_all2 (\<le>) (taylor_shift_list c xs) (taylor_shift_list c ys)"
proof (induction xs arbitrary: ys)
  case Nil then show ?case by (cases ys) auto
next
  case (Cons x xs)
  from Cons.prems(2) obtain y ys' where ys: "ys = y # ys'"
    and hd: "x \<le> y" and tl: "list_all2 (\<le>) xs ys'"
    by (cases ys) auto
  show ?case
    using pipe_ruffini_step_mono[OF Cons.prems(1) hd Cons.IH[OF Cons.prems(1) tl]]
    by (simp add: ys)
qed

lemma pipe_scale_ffs_mono:
  fixes den :: int
  shows "0 \<le> den \<Longrightarrow> 0 \<le> acc \<Longrightarrow> list_all2 (\<le>) xs ys
         \<Longrightarrow> list_all2 (\<le>) (scale_for_fractional_shift den acc xs)
                            (scale_for_fractional_shift den acc ys)"
proof (induction xs arbitrary: ys acc)
  case Nil then show ?case by (cases ys) auto
next
  case (Cons x xs)
  from Cons.prems(3) obtain y ys' where ys: "ys = y # ys'"
    and hd: "x \<le> y" and tl: "list_all2 (\<le>) xs ys'"
    by (cases ys) auto
  have "x * acc \<le> y * acc" using hd Cons.prems(2) by (simp add: mult_right_mono)
  moreover have "list_all2 (\<le>) (scale_for_fractional_shift den (acc * den) xs)
                               (scale_for_fractional_shift den (acc * den) ys')"
    using Cons.IH[OF Cons.prems(1) _ tl] Cons.prems(1,2) by simp
  ultimately show ?case by (simp add: ys)
qed

lemma pipe_scale_poly_list_aux_mono:
  fixes c :: int
  shows "0 \<le> c \<Longrightarrow> 0 \<le> acc \<Longrightarrow> list_all2 (\<le>) xs ys
         \<Longrightarrow> list_all2 (\<le>) (scale_poly_list_aux c acc xs) (scale_poly_list_aux c acc ys)"
proof (induction xs arbitrary: ys acc)
  case Nil then show ?case by (cases ys) auto
next
  case (Cons x xs)
  from Cons.prems(3) obtain y ys' where ys: "ys = y # ys'"
    and hd: "x \<le> y" and tl: "list_all2 (\<le>) xs ys'"
    by (cases ys) auto
  have "x * acc \<le> y * acc" using hd Cons.prems(2) by (simp add: mult_right_mono)
  moreover have "list_all2 (\<le>) (scale_poly_list_aux c (acc * c) xs)
                               (scale_poly_list_aux c (acc * c) ys')"
    using Cons.IH[OF Cons.prems(1) _ tl] Cons.prems(1,2) by simp
  ultimately show ?case by (simp add: ys)
qed

lemma pipe_scale_poly_list_mono:
  fixes c :: int
  shows "0 \<le> c \<Longrightarrow> list_all2 (\<le>) xs ys
         \<Longrightarrow> list_all2 (\<le>) (scale_poly_list c xs) (scale_poly_list c ys)"
  unfolding scale_poly_list_def by (rule pipe_scale_poly_list_aux_mono) auto

lemma pipe_rev_mono: "list_all2 (\<le>) xs ys \<Longrightarrow> list_all2 (\<le>) (rev xs) (rev ys)"
  by simp

(* ---- homogeneity: every stage commutes with a scalar multiple ---- *)

lemma pipe_ruffini_step_smult:
  fixes c k :: int
  shows "ruffini_step c (k * a) (map ((*) k) qs) = map ((*) k) (ruffini_step c a qs)"
  by (induction qs arbitrary: a) (simp_all add: algebra_simps)

lemma pipe_taylor_shift_list_smult:
  fixes c k :: int
  shows "taylor_shift_list c (map ((*) k) xs) = map ((*) k) (taylor_shift_list c xs)"
  by (induction xs) (simp_all add: pipe_ruffini_step_smult)

lemma pipe_scale_ffs_smult:
  fixes den k :: int
  shows "scale_for_fractional_shift den acc (map ((*) k) xs)
       = map ((*) k) (scale_for_fractional_shift den acc xs)"
  by (induction xs arbitrary: acc) (simp_all add: algebra_simps)

lemma pipe_scale_poly_list_aux_smult:
  fixes c k :: int
  shows "scale_poly_list_aux c acc (map ((*) k) xs)
       = map ((*) k) (scale_poly_list_aux c acc xs)"
  by (induction xs arbitrary: acc) (simp_all add: algebra_simps)

lemma pipe_scale_poly_list_smult:
  fixes c k :: int
  shows "scale_poly_list c (map ((*) k) xs) = map ((*) k) (scale_poly_list c xs)"
  unfolding scale_poly_list_def by (rule pipe_scale_poly_list_aux_smult)

lemma pipe_carried_init_same_den_smult:
  fixes l d r k :: int
  shows "carried_init_same_den l d r (map ((*) k) xs)
       = map ((*) k) (carried_init_same_den l d r xs)"
  unfolding carried_init_same_den_def
  by (simp add: rev_map pipe_scale_ffs_smult pipe_taylor_shift_list_smult
                pipe_scale_poly_list_smult)

lemma pipe_carried_init_same_den_mono:
  fixes l d r :: int
  assumes "0 \<le> l" and "0 \<le> d" and "l \<le> r" and "list_all2 (\<le>) xs ys"
  shows "list_all2 (\<le>) (carried_init_same_den l d r xs) (carried_init_same_den l d r ys)"
  unfolding carried_init_same_den_def
  by (rule pipe_scale_poly_list_mono, use assms in simp,
      rule pipe_taylor_shift_list_mono[OF assms(1)], rule pipe_rev_mono,
      rule pipe_scale_ffs_mono[OF assms(2)], simp, rule pipe_rev_mono[OF assms(4)])

definition probe_count_pipe :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "probe_count_pipe l d r xs = taylor_shift_list 1 (rev (carried_init_same_den l d r xs))"

lemma probe_count_pipe_count:
  "carried_descartes_count (carried_init_same_den l d r xs)
     = sign_changes_fold (probe_count_pipe l d r xs)"
  by (simp add: carried_descartes_count_def probe_count_pipe_def)

lemma probe_count_pipe_mono:
  fixes l d r :: int
  assumes "0 \<le> l" and "0 \<le> d" and "l \<le> r" and "list_all2 (\<le>) xs ys"
  shows "list_all2 (\<le>) (probe_count_pipe l d r xs) (probe_count_pipe l d r ys)"
  unfolding probe_count_pipe_def
  by (rule pipe_taylor_shift_list_mono, simp, rule pipe_rev_mono,
      rule pipe_carried_init_same_den_mono[OF assms])

lemma probe_count_pipe_smult:
  fixes l d r k :: int
  shows "probe_count_pipe l d r (map ((*) k) xs) = map ((*) k) (probe_count_pipe l d r xs)"
  unfolding probe_count_pipe_def
  by (simp add: pipe_carried_init_same_den_smult rev_map pipe_taylor_shift_list_smult)

lemma probe_div_lower: "(0::int) < b \<Longrightarrow> b * (x div b) \<le> x"
  by (simp add: Float.mult_div_le)

lemma probe_div_upper: "(0::int) < b \<Longrightarrow> x \<le> b * (x div b + 1)"
proof -
  assume b: "0 < b"
  have e: "x = b * (x div b) + x mod b" by simp
  have m: "x mod b < b" using b by simp
  have g: "b * (x div b + 1) = b * (x div b) + b" by (simp add: algebra_simps)
  from e m g show ?thesis by linarith
qed

lemma probe_floor_lower:
  fixes b :: int
  shows "0 < b \<Longrightarrow> list_all2 (\<le>) (map ((*) b) (map (\<lambda>x. x div b) xs)) xs"
  by (induction xs) (simp_all add: probe_div_lower)

lemma probe_floor_upper:
  fixes b :: int
  shows "0 < b \<Longrightarrow> list_all2 (\<le>) xs (map ((*) b) (map (\<lambda>x. x div b + 1) xs))"
  by (induction xs) (simp_all add: probe_div_upper)

lemma probe_enclose_lower:
  fixes l d r b :: int
  assumes "0 \<le> l" and "0 \<le> d" and "l \<le> r" and "0 < b"
  shows "list_all2 (\<le>) (map ((*) b) (probe_count_pipe l d r (map (\<lambda>x. x div b) xs)))
                       (probe_count_pipe l d r xs)"
proof -
  have A: "list_all2 (\<le>) (probe_count_pipe l d r (map ((*) b) (map (\<lambda>x. x div b) xs)))
                         (probe_count_pipe l d r xs)"
    by (rule probe_count_pipe_mono[OF assms(1,2,3) probe_floor_lower[OF assms(4)]])
  have E: "probe_count_pipe l d r (map ((*) b) (map (\<lambda>x. x div b) xs))
             = map ((*) b) (probe_count_pipe l d r (map (\<lambda>x. x div b) xs))"
    by (rule probe_count_pipe_smult)
  from A E show ?thesis by simp
qed

lemma probe_enclose_upper:
  fixes l d r b :: int
  assumes "0 \<le> l" and "0 \<le> d" and "l \<le> r" and "0 < b"
  shows "list_all2 (\<le>) (probe_count_pipe l d r xs)
                       (map ((*) b) (probe_count_pipe l d r (map (\<lambda>x. x div b + 1) xs)))"
proof -
  have A: "list_all2 (\<le>) (probe_count_pipe l d r xs)
                         (probe_count_pipe l d r (map ((*) b) (map (\<lambda>x. x div b + 1) xs)))"
    by (rule probe_count_pipe_mono[OF assms(1,2,3) probe_floor_upper[OF assms(4)]])
  have E: "probe_count_pipe l d r (map ((*) b) (map (\<lambda>x. x div b + 1) xs))
             = map ((*) b) (probe_count_pipe l d r (map (\<lambda>x. x div b + 1) xs))"
    by (rule probe_count_pipe_smult)
  from A E show ?thesis by simp
qed

lemma pipe_fold_sign_step_sgn_cong:
  fixes as bs :: "int list"
  shows "list_all2 (\<lambda>a b. sgn a = sgn b) as bs
         \<Longrightarrow> fold sign_step as s = fold sign_step bs s"
proof (induction as arbitrary: bs s)
  case Nil then show ?case by (cases bs) auto
next
  case (Cons a as)
  from Cons.prems obtain b bs' where bs: "bs = b # bs'"
    and hd: "sgn a = sgn b" and tl: "list_all2 (\<lambda>a b. sgn a = sgn b) as bs'"
    by (cases bs) auto
  have "sign_step a s = sign_step b s"
    by (metis hd sign_step_sgn surj_pair)
  thus ?case using Cons.IH[OF tl] by (simp add: bs)
qed

lemma pipe_sign_changes_fold_sgn_cong:
  fixes as bs :: "int list"
  assumes "list_all2 (\<lambda>a b. sgn a = sgn b) as bs"
  shows "sign_changes_fold as = sign_changes_fold bs"
  using pipe_fold_sign_step_sgn_cong[OF assms] by (simp add: sign_changes_fold_def)

lemma pipe_trunc_le_incr:
  fixes b :: int
  shows "list_all2 (\<le>) (map (\<lambda>x. x div b) xs) (map (\<lambda>x. x div b + 1) xs)"
  by (induction xs) simp_all

lemma probe_decide_sound:
  fixes l d r b :: int
  assumes L: "0 \<le> l" and D: "0 \<le> d" and R: "l \<le> r" and B: "0 < b"
  assumes cert: "list_all2 (\<lambda>a c. 0 < a \<or> c < 0)
                   (probe_count_pipe l d r (map (\<lambda>x. x div b) xs))
                   (probe_count_pipe l d r (map (\<lambda>x. x div b + 1) xs))"
  shows "carried_descartes_count (carried_init_same_den l d r xs)
       = carried_descartes_count (carried_init_same_den l d r (map (\<lambda>x. x div b) xs))"
proof -
  define A where "A = probe_count_pipe l d r (map (\<lambda>x. x div b) xs)"
  define C where "C = probe_count_pipe l d r (map (\<lambda>x. x div b + 1) xs)"
  define P where "P = probe_count_pipe l d r xs"
  have lo: "list_all2 (\<le>) (map ((*) b) A) P"
    unfolding A_def P_def by (rule probe_enclose_lower[OF L D R B])
  have hi: "list_all2 (\<le>) P (map ((*) b) C)"
    unfolding C_def P_def by (rule probe_enclose_upper[OF L D R B])
  have ac: "list_all2 (\<le>) A C"
    unfolding A_def C_def by (rule probe_count_pipe_mono[OF L D R pipe_trunc_le_incr])
  have lAP: "length A = length P" using list_all2_lengthD[OF lo] by simp
  have lAC: "length A = length C" using list_all2_lengthD[OF ac] by simp
  have sgneq: "\<And>j. j < length A \<Longrightarrow> sgn (P ! j) = sgn (A ! j)"
  proof -
    fix j assume j: "j < length A"
    have jP: "j < length P" using j lAP by simp
    have jC: "j < length C" using j lAC by simp
    have l1: "b * (A ! j) \<le> P ! j"
      using list_all2_nthD[OF lo, of j] j by simp
    have h1: "P ! j \<le> b * (C ! j)"
      using list_all2_nthD[OF hi, of j] jP jC by simp
    have a1: "A ! j \<le> C ! j" using list_all2_nthD[OF ac, of j] j by simp
    from cert have "0 < A ! j \<or> C ! j < 0"
      using list_all2_nthD[of "\<lambda>a c. 0 < a \<or> c < 0"] j
      unfolding A_def C_def by (metis A_def C_def j)
    then show "sgn (P ! j) = sgn (A ! j)"
    proof
      assume "0 < A ! j"
      hence "0 < b * (A ! j)" using B by simp
      hence "0 < P ! j" using l1 by linarith
      thus ?thesis using \<open>0 < A ! j\<close> by simp
    next
      assume "C ! j < 0"
      hence "b * (C ! j) < 0" using B by (simp add: mult_pos_neg)
      hence "P ! j < 0" using h1 by linarith
      moreover have "A ! j < 0" using a1 \<open>C ! j < 0\<close> by linarith
      ultimately show ?thesis by simp
    qed
  qed
  have "sign_changes_fold P = sign_changes_fold A"
    by (rule pipe_sign_changes_fold_sgn_cong,
        simp add: list_all2_conv_all_nth lAP[symmetric] sgneq)
  thus ?thesis
    unfolding A_def P_def by (simp add: probe_count_pipe_count)
qed


subsubsection \<open>Implementation (a): the per-coefficient increment\<close>

text \<open>The upper end of the enclosure is \<open>q + 1\<close> taken per coefficient, so the decide needs an
  in-place \<open>+1\<close> pass. This is the truncation triple
  (@{const poly_trunc_coeff_monadic} / @{const poly_trunc_loop_monadic} /
  @{const poly_trunc_in_place_monadic}) with @{const mpz_add_ui.aop_r1_impl} in place of the
  shift. It is SIMPLER than its model: \<open>aop_r1\<close>'s only side condition is \<open>top\<close>, i.e. none,
  where the shift carried \<open>0 < t\<close> for \<open>snd_notzero\<close>. \<^bold>\<open>No new GMP binding\<close> --- \<open>__gmpz_add_ui\<close>
  is already bound and its in-place refinement @{thm [source] mpz_add_ui.aop_r1_impl_refine} already proved.\<close>

definition poly_incr_coeff_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly nres" where
"poly_incr_coeff_monadic xs i \<equiv> doN {
  ASSERT (i < length xs);
  RETURN (xs[i := xs ! i + 1])
}"

sepref_register "PR_CONST poly_incr_coeff_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly nres"

definition poly_incr_loop_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_incr_loop_monadic len xs \<equiv>
  for 0 len (\<lambda>i ys. doN {
    ASSERT (i < length ys);
    (PR_CONST poly_incr_coeff_monadic) ys i
  }) xs"

sepref_register "PR_CONST poly_incr_loop_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

definition poly_incr_in_place_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_incr_in_place_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_incr_loop_monadic) len xs
}"

sepref_register "PR_CONST poly_incr_in_place_monadic"
  :: "gmp_poly \<Rightarrow> gmp_poly nres"

text \<open>Abstract correctness --- the same per-index \<open>for_rule\<close> invariant as
  @{thm [source] poly_trunc_loop_correct}.\<close>
lemma poly_incr_loop_correct:
  assumes "length xs = len"
  shows "poly_incr_loop_monadic len xs \<le> RETURN (map (\<lambda>x. x + 1) xs)"
  unfolding poly_incr_loop_monadic_def poly_incr_coeff_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>i ys. length ys = len \<and>
    (\<forall>j<len. ys ! j = (if j < i then xs ! j + 1 else xs ! j))"])
  using assms
  by (auto simp: nth_list_update' less_Suc_eq intro!: nth_equalityI)

lemma poly_incr_in_place_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_incr_in_place_monadic xs \<le> RETURN (map (\<lambda>x. x + 1) xs)"
  unfolding poly_incr_in_place_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg poly_incr_loop_correct[THEN order_trans])
  using assms by (auto simp: pw_le_iff refine_pw_simps)


text \<open>The impl side of the increment: the \<open>mpzb\<close> wrapper for the already-bound
  \<open>__gmpz_add_ui\<close>, then the same four-level focused/ptrs/poly/hnr stack as
  @{thm [source] poly_trunc_coeff_impl_hnr}. The length side condition uses the ONE-snat
  member of the family (@{thm [source] gmp_poly_raw_slots_snat_lenD}) because this op takes
  no second index, where the truncation's takes the shift amount.\<close>

definition [llvm_code, llvm_inline]:
  "mpzb_add_one_impl r \<equiv> mpz_add_ui.aop_r1_impl r 1"

lemma mpzb_add_ui_impl_rule_heap:
  "llvm_htriple
    (mpzb_assn x ri \<and>* uint_assn b bi)
    (mpz_add_ui.aop_r1_impl ri bi)
    (\<lambda>ri'. mpzb_assn (x + b) ri' \<and>* uint_assn b bi \<and>* \<up>(ri' = ri))"
  unfolding mpz_add_ui.aop_r1_impl_def
  supply [vcg_rules] = mpz_add_ui.vcg_rule[THEN conjunct2]
  by vcg'

lemma mpzb_add_one_impl_rule[vcg_rules]:
  "llvm_htriple
    (mpzb_assn x ri)
    (mpzb_add_one_impl ri)
    (\<lambda>ri'. mpzb_assn (x + 1) ri' \<and>* \<up>(ri' = ri))"
  using mpzb_add_ui_impl_rule_heap[of x ri 1 1]
  by (simp add: mpzb_add_one_impl_def pure_app_eq pure_true_conv sep_algebra_simps
                uint_rel_def uint.rel_def in_br_conv)


definition [llvm_code, llvm_inline]:
  "poly_incr_coeff_impl p i \<equiv> doM {
    target \<leftarrow> arl_nth p i;
    mpzb_add_one_impl target;
    Mreturn p
  }"

lemma poly_incr_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn xi (ptrs ! i) \<and>* F)
    (poly_incr_coeff_impl p ii)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>* (mpzb_assn (xi + 1) (ptrs ! i) \<and>* F))"
  using assms
  unfolding poly_incr_coeff_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms(1)]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

lemma poly_incr_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs" and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii)
    (poly_incr_coeff_impl p ii)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (xs[i := xs ! i + 1])) ptrs)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_incr_coeff_impl_focused_rule[
      where ptrs=ptrs and i=i
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          ((map Some xs)[i := None]) ptrs"
        and xi="xs ! i"])
    using assms apply simp
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps
    gmp_poly_slots_unfocus_coeff_update)
  done

lemma poly_incr_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii)
    (poly_incr_coeff_impl p ii)
    (\<lambda>p'. gmp_poly_assn (xs[i := xs ! i + 1]) p')"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule gmp_poly_raw_slots_snat_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_incr_coeff_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def sep_algebra_simps)
    subgoal for p' s
      apply (rule exI[where x=ptrs])
      apply (simp add: sep_algebra_simps)
      done
    done
  done

lemma poly_incr_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_incr_coeff_impl,
    uncurry (PR_CONST poly_incr_coeff_monadic)) \<in>
    [\<lambda>(xs, i). i < length xs]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> gmp_poly_assn"
  apply sepref_to_hoare
  unfolding poly_incr_coeff_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_incr_coeff_impl_rule)
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (clarsimp simp: entails_def sep_algebra_simps
      snat.assn_is_rel snat_rel_def pure_def)
    done
  done


sepref_definition poly_incr_loop_impl [llvm_code] is
  "uncurry poly_incr_loop_monadic" ::
  "[\<lambda>(len, xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_incr_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_incr_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_incr_loop_impl,
    uncurry (PR_CONST poly_incr_loop_monadic)) \<in>
    [\<lambda>(len, xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_incr_loop_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition poly_incr_in_place_impl [llvm_code] is
  "poly_incr_in_place_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_incr_in_place_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_incr_in_place_impl_hnr[sepref_fr_rules]:
  "(poly_incr_in_place_impl, PR_CONST poly_incr_in_place_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_incr_in_place_impl.refine
  by (simp add: PR_CONST_def)


subsubsection \<open>Implementation (b): the probe pipeline, composed from existing ops\<close>

text \<open>Lengths first: every stage of the pipeline is length-preserving, which the composed
  correctness proof needs in order to thread the \<open>max_snat\<close> side conditions.\<close>

lemma pipe_ruffini_step_length: "length (ruffini_step c a qs) = Suc (length qs)"
  by (induction qs arbitrary: a) simp_all

lemma pipe_taylor_shift_list_length: "length (taylor_shift_list c xs) = length xs"
  by (induction xs) (simp_all add: pipe_ruffini_step_length)

lemma pipe_scale_ffs_length:
  "length (scale_for_fractional_shift den acc xs) = length xs"
  by (induction xs arbitrary: acc) simp_all

lemma pipe_scale_poly_list_aux_length:
  "length (scale_poly_list_aux c acc xs) = length xs"
  by (induction xs arbitrary: acc) simp_all

lemma pipe_scale_poly_list_length: "length (scale_poly_list c xs) = length xs"
  unfolding scale_poly_list_def by (rule pipe_scale_poly_list_aux_length)

lemma pipe_carried_init_same_den_length:
  "length (carried_init_same_den l d r xs) = length xs"
  unfolding carried_init_same_den_def
  by (simp add: pipe_scale_poly_list_length pipe_taylor_shift_list_length pipe_scale_ffs_length)

lemma probe_count_pipe_length: "length (probe_count_pipe l d r xs) = length xs"
  unfolding probe_count_pipe_def
  by (simp add: pipe_taylor_shift_list_length pipe_carried_init_same_den_length)

text \<open>The pipeline as an op: the carried build, then the in-place reverse, then
  the shift-by-one. \<^bold>\<open>Every one of the three already exists and is already refined\<close> ---
  this definition adds no arithmetic, which is the whole point of the enclosure being exact.\<close>
definition probe_count_pipe_monadic :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"probe_count_pipe_monadic l k r xs \<equiv> doN {
  p \<leftarrow> (PR_CONST carried_init_inplace_monadic) l k r xs;
  ASSERT (0 < length p);
  ASSERT (length p + 1 < max_snat LENGTH(gmp_poly_len));
  p \<leftarrow> (PR_CONST poly_reverse_in_place_monadic) p;
  ASSERT (length p + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>\<open>poly_taylor_shift_one\<close> borrows (\<open>\<^sup>k\<close>) and allocates its result, unlike the destructive (\<open>\<^sup>d\<close>) reverse above it, so
     the reversed buffer is freed here. The vector is materialised because the certificate compares the two pipelines
     entrywise, whereas the count kernel fuses the shift by one into its scan.\<close>
  res \<leftarrow> (PR_CONST poly_taylor_shift_one_monadic) p;
  (PR_CONST poly_free_monadic) p;
  RETURN res
}"

sepref_register "PR_CONST probe_count_pipe_monadic"
  :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

lemma probe_count_pipe_monadic_correct:
  assumes "0 < length xs"
    and "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and "k * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "probe_count_pipe_monadic l k r xs \<le> RETURN (probe_count_pipe l (2 ^ k) r xs)"
  unfolding probe_count_pipe_monadic_def probe_count_pipe_def PR_CONST_def
  apply (refine_vcg
    carried_init_inplace_monadic_correct[THEN order_trans]
    poly_reverse_in_place_monadic_correct[THEN order_trans]
    poly_taylor_shift_one_monadic_correct[THEN order_trans])
  using assms
  by (auto simp: pipe_carried_init_same_den_length)


subsubsection \<open>Implementation (c): the two-sided certificate\<close>

text \<open>Per index: the sign of the exact entry is CERTAIN when the lower end is positive or the
  upper end is negative, and in both cases it agrees with the lower end's sign
  (\<open>probe_decide_sound\<close>). The loop is a plain \<open>for\<close> over the two borrowed polys reading
  @{const poly_coeff_sgn_monadic} --- an existing op --- and accumulating a bool. It does not
  abort early: the decide's cost is the two \<open>O(deg\<^sup>2)\<close> pipelines, against which this \<open>O(deg)\<close>
  scan is noise, and a \<open>for\<close> is markedly cheaper to prove than an early-exit \<open>WHILE\<close>.\<close>

definition probe_cert_loop_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
"probe_cert_loop_monadic len as cs \<equiv>
  for 0 len (\<lambda>i ok. doN {
    ASSERT (i < length as);
    ASSERT (i < length cs);
    sa \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) as i;
    sc \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) cs i;
    RETURN (ok \<and> (sa = 1 \<or> sc = - 1))
  }) True"

sepref_register "PR_CONST probe_cert_loop_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

lemma probe_cert_loop_correct:
  assumes "length as = len" and "length cs = len"
  shows "probe_cert_loop_monadic len as cs
    \<le> RETURN (\<forall>j<len. 0 < as ! j \<or> cs ! j < 0)"
  unfolding probe_cert_loop_monadic_def poly_coeff_sgn_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>i ok. ok = (\<forall>j<i. 0 < as ! j \<or> cs ! j < 0)"])
  using assms
  by (auto simp: sgn_1_pos sgn_1_neg less_Suc_eq)

subsubsection \<open>Implementation (d): the decide\<close>

text \<open>\<^bold>\<open>The truncation exponent \<open>t\<close> is an input with no proof obligation.\<close> The enclosure is exact for every \<open>t\<close>, so a
  wrong or clamped budget affects performance, never correctness. The admission gate is at the call site (\<open>Newton\<close>),
  where the window data it reads is in scope. The op returns \<open>True\<close> only on a certified rejection; otherwise it returns
  \<open>False\<close> and the caller runs the exact path unchanged.\<close>

definition probe_reject_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
"probe_reject_monadic v k m m4 t xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  \<comment> \<open>The \<open>length\<close> ASSERTs are spec-level (erased at codegen) and are what makes each
     callee's own precondition discharge: every stage here is length-preserving, but the
     synthesis cannot see that without being told at each step.\<close>
  q  \<leftarrow> (PR_CONST poly_copy_monadic) xs;
  ASSERT (length q = len);
  q  \<leftarrow> (PR_CONST poly_trunc_in_place_monadic) t q;
  ASSERT (length q = len);
  qh \<leftarrow> (PR_CONST poly_copy_monadic) q;
  ASSERT (length qh = len);
  qh \<leftarrow> (PR_CONST poly_incr_in_place_monadic) qh;
  ASSERT (length qh = len);
  a  \<leftarrow> (PR_CONST probe_count_pipe_monadic) m k m4 q;
  ASSERT (length a = len);
  c  \<leftarrow> (PR_CONST probe_count_pipe_monadic) m k m4 qh;
  ASSERT (length c = len);
  (PR_CONST poly_free_monadic) q;
  (PR_CONST poly_free_monadic) qh;
  ok \<leftarrow> (PR_CONST probe_cert_loop_monadic) len a c;
  cnt \<leftarrow> (PR_CONST poly_sign_changes_monadic) a;
  (PR_CONST poly_free_monadic) a;
  (PR_CONST poly_free_monadic) c;
  RETURN (ok \<and> cnt \<noteq> v)
}"

sepref_register "PR_CONST probe_reject_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres"


text \<open>The value the op computes, before it is read as a certificate. Each step is the
  op's own correctness lemma; nothing here is new arithmetic.\<close>
lemma probe_reject_monadic_val:
  assumes len0: "0 < length xs"
    and lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and kb: "k * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
    and t0: "0 < t"
  shows "probe_reject_monadic v k m m4 t xs \<le> RETURN (
    (\<forall>j<length xs. 0 < probe_count_pipe m (2 ^ k) m4 (trunc_list t xs) ! j
                 \<or> probe_count_pipe m (2 ^ k) m4 (map (\<lambda>x. x + 1) (trunc_list t xs)) ! j < 0)
    \<and> sign_changes_fold (probe_count_pipe m (2 ^ k) m4 (trunc_list t xs)) \<noteq> v)"
  unfolding probe_reject_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg
    poly_copy_correct[THEN order_trans]
    poly_trunc_in_place_correct[THEN order_trans]
    poly_incr_in_place_correct[THEN order_trans]
    probe_count_pipe_monadic_correct[THEN order_trans]
    probe_cert_loop_correct[THEN order_trans]
    poly_sign_changes_monadic_correct[THEN order_trans])
  using assms
  by (auto simp: pw_le_iff refine_pw_simps length_trunc_list probe_count_pipe_length
                 pipe_carried_init_same_den_length)

text \<open>\<^bold>\<open>Soundness of the probe rejection.\<close> \<open>True\<close> certifies that the probe's exact count differs from \<open>v\<close> (the \<open>None\<close>
  branch) without computing the exact build. Beyond the existing ops it needs only \<open>probe_decide_sound\<close>. Its
  hypotheses on the window (\<open>0 \<le> m\<close>, \<open>m \<le> m4\<close>, and the two \<open>max_snat\<close> bounds) are asserted at the call site, so no caller
  obligation is added.\<close>
theorem probe_reject_monadic_sound:
  assumes m0: "0 \<le> m" and mr: "m \<le> m4"
    and len0: "0 < length xs"
    and lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and kb: "k * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
    and t0: "0 < t"
  shows "probe_reject_monadic v k m m4 t xs
    \<le> SPEC (\<lambda>r. r \<longrightarrow>
        carried_descartes_count (carried_init_same_den m (2 ^ k) m4 xs) \<noteq> v)"
proof -
  define A where "A = probe_count_pipe m (2 ^ k) m4 (trunc_list t xs)"
  define C where "C = probe_count_pipe m (2 ^ k) m4 (map (\<lambda>x. x + 1) (trunc_list t xs))"
  define R where
    "R = ((\<forall>j<length xs. 0 < A ! j \<or> C ! j < 0) \<and> sign_changes_fold A \<noteq> v)"
  have step: "probe_reject_monadic v k m m4 t xs \<le> RETURN R"
    unfolding R_def A_def C_def
    by (rule probe_reject_monadic_val[OF len0 lenb kb t0])
  have PR:
    "R \<longrightarrow> carried_descartes_count (carried_init_same_den m (2 ^ k) m4 xs) \<noteq> v"
  proof
    assume Rr: R
    hence cert0: "\<forall>j<length xs. 0 < A ! j \<or> C ! j < 0"
      and cnt: "sign_changes_fold A \<noteq> v" unfolding R_def by auto
    have qeq: "trunc_list t xs = map (\<lambda>x. x div 2 ^ t) xs"
      by (simp add: trunc_list_def)
    have qheq: "map (\<lambda>x. x + 1) (trunc_list t xs) = map (\<lambda>x. x div 2 ^ t + 1) xs"
      by (simp add: trunc_list_def)
    have cert: "list_all2 (\<lambda>a c. 0 < a \<or> c < 0)
        (probe_count_pipe m (2 ^ k) m4 (map (\<lambda>x. x div 2 ^ t) xs))
        (probe_count_pipe m (2 ^ k) m4 (map (\<lambda>x. x div 2 ^ t + 1) xs))"
      using cert0 unfolding A_def C_def qeq[symmetric] qheq[symmetric]
      by (simp add: list_all2_conv_all_nth probe_count_pipe_length length_trunc_list)
    have "carried_descartes_count (carried_init_same_den m (2 ^ k) m4 xs)
        = carried_descartes_count
            (carried_init_same_den m (2 ^ k) m4 (map (\<lambda>x. x div 2 ^ t) xs))"
      by (rule probe_decide_sound[OF m0 _ mr _ cert]) simp_all
    also have "\<dots> = sign_changes_fold A"
      unfolding A_def by (simp add: probe_count_pipe_count qeq)
    finally have EQ:
      "carried_descartes_count (carried_init_same_den m (2 ^ k) m4 xs)
         = sign_changes_fold A" .
    from EQ cnt
    show "carried_descartes_count (carried_init_same_den m (2 ^ k) m4 xs) \<noteq> v"
      by simp
  qed
  have "RETURN R \<le> SPEC (\<lambda>r. r \<longrightarrow>
      carried_descartes_count (carried_init_same_den m (2 ^ k) m4 xs) \<noteq> v)"
    using PR by simp
  with step show ?thesis by (rule order_trans)
qed



subsubsection \<open>Implementation (f): the admission gate (performance only)\<close>

text \<open>\<^bold>\<open>Nothing here affects soundness.\<close> \<open>probe_reject_monadic_sound\<close> holds for every truncation exponent, so this op
  owes only that the \<open>t\<close> it returns is a valid word (\<open>0\<close> declines), which is what the decide's \<open>0 < t\<close> side condition
  needs.

  \<^bold>\<open>Two constants\<close>:
  \<^item> \<open>probe_reject_budget_mul\<close>: the budget is \<open>w = mul * len\<close>, a constant multiple rather than a per-call \<open>bitlen m\<close>
    read, which would need a scalar op for a quantity that affects only performance;
  \<^item> \<open>probe_reject_gate_c\<close>: the ratio \<open>c\<close> that bounds the wasted work.
  A gate on the dilation, \<open>kn \<le> w\<close>, would not be a reliable per-probe discriminator, and there is none.

  \<^bold>\<open>\<open>nb\<close> is the \<open>O(deg)\<close> true maximum, not the \<open>O(1)\<close> leading coefficient's bit length\<close>: at this site the leading
  coefficient is typically much smaller than the largest (unlike the site where @{const lead_budget_mop} is used). The
  scan is \<open>O(deg)\<close> against an \<open>O(deg\<^sup>2)\<close> decide.

  The guards have the overflow shape of @{const trunc_attempt_guard_mop}: \<open>len\<close> is bounded by \<open>top div mul\<close>, so the
  product cannot overflow, and the comparison is by \<open>nb div c\<close> rather than \<open>c * budget\<close>, for the same reason.\<close>

definition probe_reject_budget_mul :: nat where "probe_reject_budget_mul = 6"
definition probe_reject_gate_c :: nat where "probe_reject_gate_c = 8"

definition probe_reject_gate_mop :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where
"probe_reject_gate_mop len kn nb \<equiv> doN {
  top \<leftarrow> RETURN (PR_CONST (trunc_max_snat_incl TYPE(gmp_poly_len)));
  capm \<leftarrow> RETURN (top div probe_reject_budget_mul);
  if len \<le> capm \<and> nb \<le> top then doN {
    w \<leftarrow> RETURN (probe_reject_budget_mul * len);
    if kn \<le> top - w then doN {
      thr \<leftarrow> RETURN (nb div probe_reject_gate_c);
      if w + kn < thr then RETURN (nb - w) else RETURN 0
    } else RETURN 0
  } else RETURN 0
}"

sepref_register "PR_CONST probe_reject_gate_mop" :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres"

text \<open>The one fact the call site needs: an admitted probe gets a POSITIVE exponent that is a
  valid machine word. Everything else about the gate is perf-only.\<close>
lemma probe_reject_gate_mop_admits_pos:
  "probe_reject_gate_mop len kn nb \<le> SPEC (\<lambda>t. 0 < t \<longrightarrow>
      t < max_snat LENGTH(gmp_poly_len))"
proof -
  have "\<And>w. w + kn < nb div probe_reject_gate_c \<Longrightarrow> nb \<le> trunc_max_snat_incl TYPE(gmp_poly_len)
        \<Longrightarrow> 0 < nb - w \<and> nb - w < max_snat LENGTH(gmp_poly_len)"
  proof -
    fix w assume A: "w + kn < nb div probe_reject_gate_c"
      and B: "nb \<le> trunc_max_snat_incl TYPE(gmp_poly_len)"
    have "nb div probe_reject_gate_c \<le> nb" by simp
    with A have "w < nb" by linarith
    moreover have "nb - w \<le> nb" by simp
    ultimately show "0 < nb - w \<and> nb - w < max_snat LENGTH(gmp_poly_len)"
      using B by (simp add: max_snat_def)
  qed
  thus ?thesis
    unfolding probe_reject_gate_mop_def PR_CONST_def
    by (auto simp: pw_le_iff refine_pw_simps max_snat_def)
qed

subsubsection \<open>Implementation (e): Sepref synthesis\<close>

sepref_definition probe_reject_gate_impl [llvm_inline] is
  "uncurry2 probe_reject_gate_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding probe_reject_gate_mop_def probe_reject_budget_mul_def probe_reject_gate_c_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma probe_reject_gate_impl_hnr[sepref_fr_rules]:
  "(uncurry2 probe_reject_gate_impl, uncurry2 (PR_CONST probe_reject_gate_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using probe_reject_gate_impl.refine by (simp add: PR_CONST_def)

sepref_definition probe_cert_loop_impl [llvm_code] is
  "uncurry2 probe_cert_loop_monadic" ::
  "[\<lambda>((len, as), cs). length as = len \<and> length cs = len \<and>
      len + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding probe_cert_loop_monadic_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_sint_const gmp_int_t)
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma probe_cert_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry2 probe_cert_loop_impl, uncurry2 (PR_CONST probe_cert_loop_monadic)) \<in>
    [\<lambda>((len, as), cs). length as = len \<and> length cs = len \<and>
      len + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using probe_cert_loop_impl.refine
  by (simp add: PR_CONST_def)


sepref_definition probe_count_pipe_impl [llvm_code] is
  "uncurry3 probe_count_pipe_monadic" ::
  "[\<lambda>(((l, k), r), xs). 0 < length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length xs - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding probe_count_pipe_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma probe_count_pipe_impl_hnr[sepref_fr_rules]:
  "(uncurry3 probe_count_pipe_impl, uncurry3 (PR_CONST probe_count_pipe_monadic)) \<in>
    [\<lambda>(((l, k), r), xs). 0 < length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length xs - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using probe_count_pipe_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition probe_reject_impl [llvm_code] is
  "uncurry5 probe_reject_monadic" ::
  "[\<lambda>(((((v, k), m), m4), t), xs). 0 < length xs \<and> 0 < t \<and>
      t < max_snat LENGTH(gmp_poly_len) \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length xs - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding probe_reject_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma probe_reject_impl_hnr[sepref_fr_rules]:
  "(uncurry5 probe_reject_impl, uncurry5 (PR_CONST probe_reject_monadic)) \<in>
    [\<lambda>(((((v, k), m), m4), t), xs). 0 < length xs \<and> 0 < t \<and>
      t < max_snat LENGTH(gmp_poly_len) \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length xs - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using probe_reject_impl.refine
  by (simp add: PR_CONST_def)


section \<open>The low-precision decide that the right child is empty\<close>

text \<open>\<^bold>\<open>The decide's obligation needs no threshold machinery.\<close> Write \<open>F = T \<circ> rev \<circ> T\<close>, so
  \<open>carried_descartes_count (carried_right xs) = sigma (F (carried_left xs))\<close> (@{thm carried_descartes_count_def},
  @{thm carried_right_def}). \<open>F\<close> is a composition of linear maps with non-negative coefficients
  (@{thm taylor_shift_list_nth_binom}), and floor truncation is one-sided: \<open>L = 2^t * trunc t L + e\<close> with \<open>0 \<le> e\<^sub>i < 2^t\<close>
  componentwise, for any sign of \<open>L\<close>. Hence \<open>F L = 2^t * F (trunc t L) + F e\<close> with \<open>F e \<ge> 0\<close>, so a non-negative computed
  \<open>F (trunc t L)\<close> forces a non-negative \<open>F L\<close>, and a non-negative list has no sign changes. Zeros are allowed.

  \<^bold>\<open>The mirror.\<close> \<open>sigma\<close> is invariant under negating every entry, so the same rule applied to \<open>-L\<close> certifies \<open>L\<close> too,
  which covers vectors that are uniformly negative.
  \<^item> So no amplification vector, per-index threshold or ambiguity bit is needed;
  \<^item> and \<open>t\<close> affects only performance: the decide is self-certifying, so no budget makes it unsound, only less often
    successful.\<close>

abbreviation Ffun :: "int list \<Rightarrow> int list" where
  "Ffun v \<equiv> taylor_shift_list 1 (rev (taylor_shift_list 1 v))"

lemma taylor_shift_list_1_mono:
  fixes as bs :: "int list"
  assumes len: "length as = length bs"
    and le: "\<And>i. i < length as \<Longrightarrow> as ! i \<le> bs ! i"
    and i: "i < length as"
  shows "taylor_shift_list 1 as ! i \<le> taylor_shift_list 1 bs ! i"
proof -
  have "(\<Sum>t = i..<length as. int (t choose i) * as ! t)
      \<le> (\<Sum>t = i..<length as. int (t choose i) * bs ! t)"
    by (intro sum_mono mult_left_mono le) auto
  thus ?thesis using i len by (simp add: taylor_shift_list_nth_binom)
qed

lemma taylor_shift_list_1_smult:
  fixes xs :: "int list"
  assumes i: "i < length xs"
  shows "taylor_shift_list 1 (map ((*) k) xs) ! i = k * (taylor_shift_list 1 xs ! i)"
  using assms
  by (simp add: taylor_shift_list_nth_binom sum_distrib_left
                mult.left_commute mult.assoc)

lemma taylor_shift_list_1_smult_list:
  fixes xs :: "int list"
  shows "taylor_shift_list 1 (map ((*) k) xs) = map ((*) k) (taylor_shift_list 1 xs)"
  by (intro nth_equalityI) (auto simp: taylor_shift_list_1_smult)

lemma fold_sign_step_nonneg:
  fixes xs :: "int list"
  shows "\<lbrakk> \<forall>x\<in>set xs. 0 \<le> x; s \<in> {0, 1} \<rbrakk>
     \<Longrightarrow> fst (fold sign_step xs (s, 0)) \<in> {0, 1}
       \<and> snd (fold sign_step xs (s, 0)) = 0"
proof (induction xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  have "sign_step a (s, 0) \<in> {0, 1} \<times> {0}"
    using Cons.prems by (cases "a = 0"; cases "s = 0") (auto simp: sgn_if)
  then obtain s' where "sign_step a (s, 0) = (s', 0)" and "s' \<in> {0, 1}" by auto
  thus ?case using Cons.IH[of s'] Cons.prems by simp
qed

lemma sign_changes_fold_nonneg:
  fixes xs :: "int list"
  assumes "\<forall>x\<in>set xs. 0 \<le> x"
  shows "sign_changes_fold xs = 0"
  using fold_sign_step_nonneg[OF assms, of 0]
  by (simp add: sign_changes_fold_def)

lemma F_mono:
  fixes as bs :: "int list"
  assumes len: "length as = length bs"
    and le: "\<And>i. i < length as \<Longrightarrow> as ! i \<le> bs ! i"
    and i: "i < length as"
  shows "Ffun as ! i \<le> Ffun bs ! i"
proof (rule taylor_shift_list_1_mono)
  show "length (rev (taylor_shift_list 1 as)) = length (rev (taylor_shift_list 1 bs))"
    using len by simp
  show "j < length (rev (taylor_shift_list 1 as)) \<Longrightarrow>
        rev (taylor_shift_list 1 as) ! j \<le> rev (taylor_shift_list 1 bs) ! j" for j
    using len le by (simp add: rev_nth taylor_shift_list_1_mono)
  show "i < length (rev (taylor_shift_list 1 as))" using i by simp
qed

lemma F_smult: "Ffun (map ((*) k) xs) = map ((*) k) (Ffun xs)"
  by (simp add: taylor_shift_list_1_smult_list rev_map)

text \<open>The uminus form, proved DIRECTLY from the binomial formula rather than via
  \<open>(*) (-1)\<close> --- simp normalises those two to each other, so the scalar version is
  useless as a rewrite here.\<close>
lemma taylor_shift_list_1_uminus_list:
  fixes xs :: "int list"
  shows "taylor_shift_list 1 (map uminus xs) = map uminus (taylor_shift_list 1 xs)"
  by (intro nth_equalityI) (auto simp: taylor_shift_list_nth_binom sum_negf)

lemma F_uminus: "Ffun (map uminus xs) = map uminus (Ffun xs)"
  by (simp add: taylor_shift_list_1_uminus_list rev_map)

lemma F_len: "length (Ffun v) = length v" by simp

text \<open>\<^bold>\<open>The core, stated as a lifting property rather than as a count.\<close> The count is a corollary; the list-level
  non-negativity is the fact that survives a change of node, and the \<open>gframe\<close> transfer needs it.

  A caller holding \<open>gframe s g X Y\<close> decides about \<open>Y\<close> but must conclude about \<open>X\<close>.
  \<open>carried_descartes_count (carried_right Y) = 0\<close> says nothing about \<open>X\<close> by itself; \<open>0 \<le> Ffun (carried_left Y)\<close> does,
  because \<open>gframe\<close> is one-sided and @{thm F_mono} is monotone.\<close>
lemma F_nonneg_lift:
  fixes L :: "int list"
  assumes nn: "\<And>i. i < length L \<Longrightarrow> 0 \<le> Ffun (map (\<lambda>x. x div 2 ^ t) L) ! i"
    and i: "i < length L"
  shows "0 \<le> Ffun L ! i"
proof -
  define c where "c = map (\<lambda>x. x div 2 ^ t) L"
  have lenc: "length c = length L" by (simp add: c_def)
  have floor_le: "2 ^ t * (x div 2 ^ t) \<le> x" for x :: int
  proof -
    have "(2::int) ^ t * (x div 2 ^ t) + x mod 2 ^ t = x" by simp
    moreover have "0 \<le> x mod (2::int) ^ t" by simp
    ultimately show ?thesis by linarith
  qed
  have step: "map ((*) (2 ^ t)) c ! i \<le> L ! i" if "i < length L" for i
    using that floor_le by (simp add: c_def)
  have A: "Ffun (map ((*) (2 ^ t)) c) ! i \<le> Ffun L ! i"
    by (rule F_mono) (use i lenc step in simp_all)
  have B: "Ffun (map ((*) (2 ^ t)) c) ! i = 2 ^ t * (Ffun c ! i)"
    using i lenc by (simp add: F_smult)
  have C: "0 \<le> Ffun c ! i" using nn[of i] i unfolding c_def by simp
  from C have "0 \<le> 2 ^ t * (Ffun c ! i)" by simp
  with A B show ?thesis by linarith
qed

lemma F_nonneg_sound:
  fixes L :: "int list"
  assumes nn: "\<And>i. i < length L \<Longrightarrow> 0 \<le> Ffun (map (\<lambda>x. x div 2 ^ t) L) ! i"
  shows "sign_changes_fold (Ffun L) = 0"
proof -
  have key: "0 \<le> Ffun L ! i" if i: "i < length L" for i
    by (rule F_nonneg_lift[OF nn i])
  have "\<forall>x \<in> set (Ffun L). 0 \<le> x" using key by (metis in_set_conv_nth F_len)
  thus ?thesis by (rule sign_changes_fold_nonneg)
qed

text \<open>\<^bold>\<open>The frame transfer: the decide can run on a truncated node.\<close> The decide receives the stored node \<open>Y\<close>, but
  the abstract discard is about the exact node \<open>X\<close>, and at a truncated guard they differ. On the non-negative arm the
  gap closes because the frame is one-sided:

  \<^item> \<open>gframe s g X Y\<close> gives \<open>2\<^sup>s * Y ! i \<le> X ! i\<close>: the exact coefficients lie above the scaled carried ones;
  \<^item> \<open>carried_left\<close> multiplies index \<open>i\<close> by the non-negative weight \<open>2 ^ (n - 1 - i)\<close>, which preserves the inequality;
  \<^item> \<open>Ffun\<close>, two binomial shifts and a \<open>rev\<close>, is a linear map with non-negative coefficients (@{thm F_mono},
    @{thm F_smult}).

  Hence \<open>Ffun (carried_left X) \<ge> 2\<^sup>s * Ffun (carried_left Y) \<ge> 0\<close>, and a non-negative list has no sign changes: a
  successful non-negative arm certifies the exact child at any guard.

  The mirror arm does not transfer this way: it concludes \<open>Ffun (carried_left Y) \<le> 0\<close>, and \<open>2\<^sup>s * (\<le> 0) + (\<ge> 0)\<close> has no
  determined sign; it needs the frame's upper bound and a margin.

  The transfer itself is in \<open>Hybrid_Solver_Dispatch\<close>, because \<open>gframe\<close> is declared in \<open>Truncate_Spec\<close>, which this
  theory does not import. What is here is the arm-level fact @{thm F_nonneg_lift} and the weight monotonicity
  \<open>carried_left_nth_mono\<close>.\<close>

lemma carried_left_nth_mono:
  fixes X Y :: "int list"
  assumes len: "length X = length Y"
    and le: "\<And>j. j < length Y \<Longrightarrow> 2 ^ s * Y ! j \<le> X ! j"
    and i: "i < length Y"
  shows "map ((*) (2 ^ s)) (carried_left Y) ! i \<le> carried_left X ! i"
proof -
  have lenL: "length (carried_left Y) = length Y"
    and lenLX: "length (carried_left X) = length X" by (simp_all add: carried_left_def)
  have nthY: "carried_left Y ! i = Y ! i * 2 ^ (length Y - 1 - i)"
    using i by (simp add: nth_carried_left carried_left_coeff_def)
  have nthX: "carried_left X ! i = X ! i * 2 ^ (length X - 1 - i)"
    using i len by (simp add: nth_carried_left carried_left_coeff_def)
  have "2 ^ s * (Y ! i * 2 ^ (length Y - 1 - i)) = (2 ^ s * Y ! i) * 2 ^ (length Y - 1 - i)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> (X ! i) * 2 ^ (length Y - 1 - i)"
    by (rule mult_right_mono) (use le[OF i] in simp_all)
  finally show ?thesis using i lenL nthY nthX len by simp
qed

text \<open>The MIRROR: \<open>sigma\<close> is invariant under negating every entry, so the same free rule
  run on \<open>-L\<close> certifies \<open>L\<close>. This is what recovers the all-NEGATIVE population.\<close>
lemma sign_step_uminus:
  "sign_step (- (x::int)) (- s, n) = (\<lambda>(s', n'). (- s', n')) (sign_step x (s, n))"
  by (auto simp: sgn_if)

lemma fold_sign_step_uminus:
  fixes xs :: "int list"
  shows "fold sign_step (map uminus xs) (- s, n)
       = (\<lambda>(s', n'). (- s', n')) (fold sign_step xs (s, n))"
proof (induction xs arbitrary: s n)
  case Nil thus ?case by simp
next
  case (Cons a xs) thus ?case by (simp add: sign_step_uminus split: prod.splits)
qed

lemma sign_changes_fold_uminus:
  fixes xs :: "int list"
  shows "sign_changes_fold (map uminus xs) = sign_changes_fold xs"
  using fold_sign_step_uminus[of xs 0 0]
  by (simp add: sign_changes_fold_def split: prod.splits)

lemma F_nonpos_sound:
  fixes L :: "int list"
  assumes nn: "\<And>i. i < length L \<Longrightarrow> 0 \<le> Ffun (map (\<lambda>x. x div 2 ^ t) (map uminus L)) ! i"
  shows "sign_changes_fold (Ffun L) = 0"
proof -
  have "sign_changes_fold (Ffun (map uminus L)) = 0"
    by (rule F_nonneg_sound) (use nn in simp)
  thus ?thesis by (simp add: F_uminus sign_changes_fold_uminus)
qed

text \<open>\<^bold>\<open>THE DECIDE OBLIGATION\<close>, both arms, at the call site.\<close>
theorem right_empty_decide_sound:
  fixes xs :: "int list"
  assumes "(\<forall>i < length (carried_left xs).
              0 \<le> Ffun (map (\<lambda>x. x div 2 ^ t) (carried_left xs)) ! i)
         \<or> (\<forall>i < length (carried_left xs).
              0 \<le> Ffun (map (\<lambda>x. x div 2 ^ t) (map uminus (carried_left xs))) ! i)"
  shows "carried_descartes_count (carried_right xs) = 0"
proof -
  have "sign_changes_fold (Ffun (carried_left xs)) = 0"
    using assms
  proof (elim disjE)
    assume "\<forall>i < length (carried_left xs).
              0 \<le> Ffun (map (\<lambda>x. x div 2 ^ t) (carried_left xs)) ! i"
    thus ?thesis using F_nonneg_sound[where t = t and L = "carried_left xs"] by simp
  next
    assume "\<forall>i < length (carried_left xs).
              0 \<le> Ffun (map (\<lambda>x. x div 2 ^ t) (map uminus (carried_left xs))) ! i"
    thus ?thesis using F_nonpos_sound[where t = t and L = "carried_left xs"] by simp
  qed
  thus ?thesis by (simp add: carried_descartes_count_def carried_right_def)
qed



section \<open>The executable decide: negate, scan, gate\<close>

text \<open>\<^bold>\<open>Add a BORROWED mpz into one coefficient, in place.\<close> The mirror arm's frame correction is
  the ramp \<open>2\<^sup>g\<^sup>+\<^sup>n\<^sup>-\<^sup>1\<^sup>-\<^sup>j\<close> (\<open>carried_left_shift_const_nth\<close>), and nothing in the tree adds an
  EXTERNAL mpz to a coefficient: @{const poly_add_coeff_monadic} adds another coefficient of the
  SAME poly and @{const poly_addmul_coeff_monadic} needs a second index.

  \<^bold>\<open>It is defined here rather than in \<open>impl/shared\<close>\<close>: the op needs only \<open>arl_nth\<close>,
  \<open>mpzb_add_impl\<close> and the slot-focus lemmas, all of which \<open>impl/shared\<close> exports. The four-rule ladder is
  @{thm [source] poly_negate_coeff_impl_focused_rule}'s, which is the right template because
  only ONE slot is focused; the borrowed \<open>c\<close> rides in the frame \<open>F\<close> and is KEPT.\<close>

definition poly_add_mpz_coeff_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly nres" where
"poly_add_mpz_coeff_monadic xs i c \<equiv> doN {
  ASSERT (i < length xs);
  RETURN (xs[i := xs ! i + c])
}"

sepref_register "PR_CONST poly_add_mpz_coeff_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly nres"

definition [llvm_code, llvm_inline]:
  "poly_add_mpz_coeff_impl p i ci \<equiv> doM {
    target \<leftarrow> arl_nth p i;
    mpzb_add_impl target ci;
    Mreturn p
  }"

lemma poly_add_mpz_coeff_impl_focused_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* \<upharpoonleft>snat.assn i ii \<and>*
      mpzb_assn xi (ptrs ! i) \<and>* mpzb_assn c ci \<and>* F)
    (poly_add_mpz_coeff_impl p ii ci)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      (mpzb_assn (xi + c) (ptrs ! i) \<and>* mpzb_assn c ci \<and>* F))"
  using assms
  unfolding poly_add_mpz_coeff_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

lemma poly_add_mpz_coeff_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
    and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn c ci)
    (poly_add_mpz_coeff_impl p ii ci)
    (\<lambda>p'. raw_al_assn ptrs p' \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        (map Some (xs[i := xs ! i + c])) ptrs \<and>* mpzb_assn c ci)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    apply (rule poly_add_mpz_coeff_impl_focused_rule[
      where ptrs=ptrs and i=i and c=c
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
          ((map Some xs)[i := None]) ptrs"
        and xi="xs ! i"])
    using assms apply simp
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  \<comment> \<open>The borrowed \<open>mpzb_assn c ci\<close> sits BETWEEN the refocused slot and the \<open>[i := None]\<close>
     list, so the two-conjunct unfocus pattern never matches forwards. Rewrite the GOAL side into
     focused form instead (the addmul twin's shape, via its \<open>focus_two_coeff_update\<close>) and let
     \<open>sep_conj_c\<close> align the rest.\<close>
  apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
    gmp_poly_slots_unfocus_coeff_update[symmetric])
  done

lemma poly_add_mpz_coeff_impl_rule:
  fixes p :: gmp_poly_raw and ii :: "gmp_poly_len word"
  assumes "i < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* \<upharpoonleft>snat.assn i ii \<and>* mpzb_assn c ci)
    (poly_add_mpz_coeff_impl p ii ci)
    (\<lambda>p'. gmp_poly_assn (xs[i := xs ! i + c]) p' \<and>* mpzb_assn c ci)"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    \<comment> \<open>\<open>_snat_coeff_lenD\<close>, not \<open>_snat_lenD\<close>: the pure part is \<open>arl * slots * snat * mpzb\<close>.\<close>
    apply (frule gmp_poly_raw_slots_snat_coeff_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule poly_add_mpz_coeff_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def sep_algebra_simps)
    subgoal for p' s
      apply (rule exI[where x=ptrs])
      apply (simp add: sep_algebra_simps)
      done
    done
  done

lemma poly_add_mpz_coeff_impl_hnr[sepref_fr_rules]:
  "(uncurry2 poly_add_mpz_coeff_impl,
    uncurry2 (PR_CONST poly_add_mpz_coeff_monadic)) \<in>
    [\<lambda>((xs, i), c). i < length xs]\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  \<comment> \<open>\<^bold>\<open>Ending cloned from \<open>poly_addmul_coeff_impl_hnr\<close>, NOT from \<open>poly_negate_coeff_impl_hnr\<close>.\<close>
     The negate op has no external operand, so its closer never has to PIN one; here the
     borrowed \<open>c\<close> is left schematic (\<open>?c11\<close>) unless the rule is instantiated \<open>where c = c\<close>,
     and the post then needs the index's pure fact to discharge the returned \<open>mpzb_assn c ci\<close>.
     Measured: the negate-shaped closer fails with two schematic subgoals.
     \<^bold>\<open>But NOT addmul's \<open>dsc_pure_part_pure_assn_pureD\<close>\<close>: addmul carries TWO index conjuncts
     (\<open>\<up>P ** mpzb ** \<up>Q\<close>); here there is one (\<open>\<up>P ** mpzb\<close>), which is
     \<open>dsc_pure_part_left_pureD\<close>'s shape.\<close>
  apply sepref_to_hoare
  unfolding poly_add_mpz_coeff_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for c ci i ii xs p
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule poly_add_mpz_coeff_impl_rule[where i=i and c=c])
      apply assumption
     apply (clarsimp simp: entails_def sep_algebra_simps
       snat.assn_is_rel snat_rel_def pure_def)
    apply (frule dsc_pure_part_left_pureD)
    apply (simp add: conj_entails_mono gmp_poly_assn_return_entails
        pure_true_conv sep_conj_aci(1))
    done
  done

text \<open>\<^bold>\<open>The RAMP: the mirror arm's frame correction, in place.\<close> \<open>carried_left_shift_const_nth\<close>
  turns the node-level constant \<open>2\<^sup>g\<close> into the per-index \<open>2\<^sup>g\<^sup>+\<^sup>l\<^sup>e\<^sup>n\<^sup>-\<^sup>1\<^sup>-\<^sup>j\<close> the arm can add to
  the copy it ALREADY allocates --- so this costs one \<open>O(n)\<close> pass and no extra vector, against
  the \<open>O(n\<^sup>2)\<close> build the decide skips. Shape cloned from
  \<open>poly_negate_loop_monadic\<close>: a \<open>for\<close> over a DESTRUCTIVE poly with a per-index body.\<close>

definition err_ramp_body_monadic :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly nres" where
"err_ramp_body_monadic g len c j \<equiv> doN {
  ASSERT (j < length c);
  \<comment> \<open>guards the snat subtraction \<open>len - 1 - j\<close>: \<open>len - 1\<close> needs both \<open>annot_snat_const\<close> for the literal and \<open>0 < len\<close>.\<close>
  ASSERT (0 < len);
  ASSERT (j < len);
  \<comment> \<open>@{thm [source] mpz_pow2_monadic_spec}'s precondition. NOT a new caller obligation: the
     keystone already carries \<open>max g 2\<^sup>4\<^sup>2 + length rp < max_snat\<close> (\<open>gcap_rp\<close>), which bounds
     \<open>g + len\<close> outright.\<close>
  ASSERT (g + (len - 1 - j) < max_snat LENGTH(gmp_poly_len));
  p \<leftarrow> (PR_CONST mpz_pow2_monadic) (g + (len - 1 - j));
  c \<leftarrow> (PR_CONST poly_add_mpz_coeff_monadic) c j p;
  (PR_CONST mpzb_discard_monadic) p;
  RETURN c
}"

sepref_register "PR_CONST err_ramp_body_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_poly nres"

definition err_ramp_loop_monadic :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"err_ramp_loop_monadic g len xs \<equiv>
  for 0 len (\<lambda>j ys. (PR_CONST err_ramp_body_monadic) g len ys j) xs"

sepref_register "PR_CONST err_ramp_loop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

definition err_ramp_in_place_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"err_ramp_in_place_monadic g xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>\<^bold>\<open>Ramp ONLY at a truncated guard, \<open>0 < g < 2\<^sup>4\<^sup>2\<close>.\<close> At \<open>g = 0\<close> the stored node IS the exact
     node (\<open>node_frame\<close>), and under the lock \<open>2\<^sup>4\<^sup>2 \<le> g\<close> it is too (the loops' lock invariant),
     so the mirror arm needs no correction there. And it must not get one: the lock encodes an
     exact \<open>v\<close>-bound as \<open>g = 2\<^sup>4\<^sup>2 + v\<close>, so an unconditional ramp would build \<open>2\<^sup>2\<^sup>\<^sup>4\<^sup>2\<close> --- a 512 GB
     integer --- at every locked mirror-arm call (all of \<open>defl_split\<close>'s).\<close>
  if 0 < g \<and> g < 4398046511104 then (PR_CONST err_ramp_loop_monadic) g len xs
  else RETURN xs
}"

sepref_register "PR_CONST err_ramp_in_place_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

text \<open>The ramped list, named so the arm and decide contracts stay readable. It is exactly
  \<open>carried_left (Y + 2\<^sup>g)\<close> when the operand is \<open>carried_left Y\<close> --- see \<open>err_ramp_carried_left\<close>
  below, which is the bridge the frame transfer consumes.\<close>
definition err_ramp :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
"err_ramp g xs = map (\<lambda>j. xs ! j + 2 ^ (g + (length xs - 1 - j))) [0..<length xs]"

lemma err_ramp_length[simp]: "length (err_ramp g xs) = length xs"
  by (simp add: err_ramp_def)

lemma err_ramp_nth:
  "j < length xs \<Longrightarrow> err_ramp g xs ! j = xs ! j + 2 ^ (g + (length xs - 1 - j))"
  by (simp add: err_ramp_def)

text \<open>\<^bold>\<open>The bridge\<close>: adding the constant \<open>2\<^sup>g\<close> at the NODE and adding the ramp AFTER the
  \<open>carried_left\<close> scale are the same list, because \<open>carried_left\<close> is a per-index scaling. This is
  what lets the arm work on its own copy and never see the node.\<close>
lemma err_ramp_carried_left:
  "err_ramp g (carried_left Y) = carried_left (map (\<lambda>y. y + 2 ^ g) Y)"
proof (intro nth_equalityI)
  show "length (err_ramp g (carried_left Y)) = length (carried_left (map (\<lambda>y. y + 2 ^ g) Y))"
    by (simp add: carried_left_def)
  fix j assume j: "j < length (err_ramp g (carried_left Y))"
  hence jY: "j < length Y" by (simp add: carried_left_def)
  have lenL: "length (carried_left Y) = length Y" by (simp add: carried_left_def)
  have A: "err_ramp g (carried_left Y) ! j
         = carried_left Y ! j + 2 ^ (g + (length Y - 1 - j))"
    using jY lenL by (simp add: err_ramp_nth)
  have B: "carried_left (map (\<lambda>y. y + 2 ^ g) Y) ! j
         = (Y ! j + 2 ^ g) * 2 ^ (length Y - 1 - j)"
    using jY by (simp add: nth_carried_left carried_left_coeff_def)
  have C: "carried_left Y ! j = Y ! j * 2 ^ (length Y - 1 - j)"
    using jY by (simp add: nth_carried_left carried_left_coeff_def)
  show "err_ramp g (carried_left Y) ! j = carried_left (map (\<lambda>y. y + 2 ^ g) Y) ! j"
    unfolding A B C by (simp add: algebra_simps power_add)
qed

text \<open>The ramp as the arm APPLIES it --- only at a truncated guard --- and the node-level shift it
  stands for. \<open>err_shift g Y\<close> is the operand the exact-node transfer is stated about.\<close>
definition err_ramp_opt :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
"err_ramp_opt g xs = (if 0 < g \<and> g < 4398046511104 then err_ramp g xs else xs)"

definition err_shift :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
"err_shift g Y = (if 0 < g \<and> g < 4398046511104 then map (\<lambda>y. y + 2 ^ g) Y else Y)"

lemma err_ramp_opt_length[simp]: "length (err_ramp_opt g xs) = length xs"
  by (simp add: err_ramp_opt_def)

lemma err_shift_length[simp]: "length (err_shift g Y) = length Y"
  by (simp add: err_shift_def)

lemma err_ramp_opt_carried_left:
  "err_ramp_opt g (carried_left Y) = carried_left (err_shift g Y)"
  by (simp add: err_ramp_opt_def err_shift_def err_ramp_carried_left)

lemma err_ramp_body_correct:
  assumes j: "j < length ys"
    and jl: "j < len"
    and kb: "g + (len - 1 - j) < max_snat LENGTH(gmp_poly_len)"
  shows "err_ramp_body_monadic g len ys j
       \<le> RETURN (ys[j := ys ! j + 2 ^ (g + (len - 1 - j))])"
  unfolding err_ramp_body_monadic_def poly_add_mpz_coeff_monadic_def
    mpzb_discard_monadic_def PR_CONST_def
  apply (refine_vcg mpz_pow2_monadic_spec[OF kb, THEN order_trans])
  using assms by (auto simp: pw_le_iff refine_pw_simps)

lemma err_ramp_loop_correct:
  assumes len: "length xs = len"
    and kb: "g + len < max_snat LENGTH(gmp_poly_len)"
  shows "err_ramp_loop_monadic g len xs
       \<le> RETURN (err_ramp g xs)"
  unfolding err_ramp_loop_monadic_def err_ramp_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>i ys. length ys = len \<and>
    (\<forall>j<len. ys ! j = (if j < i then xs ! j + 2 ^ (g + (len - 1 - j)) else xs ! j))"]
    err_ramp_body_correct[THEN order_trans])
  using assms
  by (auto simp: nth_list_update' less_Suc_eq intro!: nth_equalityI)

lemma err_ramp_in_place_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and "g + length xs < max_snat LENGTH(gmp_poly_len)"
  shows "err_ramp_in_place_monadic g xs
       \<le> RETURN (err_ramp_opt g xs)"
  unfolding err_ramp_in_place_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg err_ramp_loop_correct[THEN order_trans])
  using assms by (auto simp: err_ramp_opt_def pw_le_iff refine_pw_simps)

text \<open>In-place negation: the \<open>poly_trunc_*\<close> loop triple with @{const poly_negate_coeff_monadic}
  in the body. Needed because the decide's MIRROR arm runs the same non-negativity rule on
  \<open>-L\<close> (@{thm F_nonpos_sound}), and truncation does NOT commute with negation, so the negated
  operand must be built before it is truncated.\<close>
definition poly_negate_loop_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_negate_loop_monadic len xs \<equiv>
  for 0 len (\<lambda>i ys. doN {
    ASSERT (i < length ys);
    (PR_CONST poly_negate_coeff_monadic) ys i
  }) xs"

sepref_register "PR_CONST poly_negate_loop_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

definition poly_negate_in_place_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"poly_negate_in_place_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  (PR_CONST poly_negate_loop_monadic) len xs
}"

sepref_register "PR_CONST poly_negate_in_place_monadic"
  :: "gmp_poly \<Rightarrow> gmp_poly nres"

lemma poly_negate_loop_correct:
  assumes "length xs = len"
  shows "poly_negate_loop_monadic len xs \<le> RETURN (map uminus xs)"
  unfolding poly_negate_loop_monadic_def poly_negate_coeff_monadic_def PR_CONST_def
  apply (refine_vcg for_rule[where I="\<lambda>i ys. length ys = len \<and>
    (\<forall>j<len. ys ! j = (if j < i then - (xs ! j) else xs ! j))"])
  using assms
  by (auto simp: nth_list_update' less_Suc_eq intro!: nth_equalityI)

lemma poly_negate_in_place_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_negate_in_place_monadic xs \<le> RETURN (map uminus xs)"
  unfolding poly_negate_in_place_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg poly_negate_loop_correct[THEN order_trans])
  using assms by (auto simp: pw_le_iff refine_pw_simps)

text \<open>The O(n) non-negativity scan --- the WHOLE verdict of the decide
  (@{thm F_nonneg_sound}). It BORROWS its argument: no allocation, no mutation.
  \<^bold>\<open>Shape\<close>: the explicit \<open>WHILET\<close> with registered cond/body ops, i.e. the
  @{const poly_max_bitlen_loop_monadic} idiom for a BORROWED poly with a pure accumulator ---
  NOT the \<open>for\<close>/\<open>for_by_while'\<close> shape of @{const poly_trunc_loop_monadic}, which threads a
  DESTRUCTIVE poly and whose initial sepref method does not apply here. The cond carries \<open>b\<close>,
  so the scan EARLY-EXITS on the first negative coefficient.\<close>
abbreviation nonneg_scan_state_assn where
  "nonneg_scan_state_assn \<equiv> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"

definition nonneg_scan_cond :: "nat \<Rightarrow> nat \<times> bool \<Rightarrow> bool" where
"nonneg_scan_cond len st \<equiv> (let (i, b) = st in i < len \<and> b)"

sepref_register "PR_CONST nonneg_scan_cond" :: "nat \<Rightarrow> nat \<times> bool \<Rightarrow> bool"

definition nonneg_scan_body_mop_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<times> bool \<Rightarrow> (nat \<times> bool) nres" where
"nonneg_scan_body_mop_monadic len xs st \<equiv> doN {
  let (i, b) = st;
  ASSERT (i < len);
  ASSERT (i < length xs);
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs i;
  ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
  i2 \<leftarrow> RETURN (i + 1);
  if s < 0 then RETURN (i2, False) else RETURN (i2, True)
}"

sepref_register "PR_CONST nonneg_scan_body_mop_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<times> bool \<Rightarrow> (nat \<times> bool) nres"

definition poly_all_nonneg_loop_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
"poly_all_nonneg_loop_monadic len xs \<equiv> doN {
  (_, b) \<leftarrow> WHILET
    (\<lambda>st. (PR_CONST nonneg_scan_cond) len st)
    (\<lambda>st. (PR_CONST nonneg_scan_body_mop_monadic) len xs st)
    (0, True);
  RETURN b
}"

sepref_register "PR_CONST poly_all_nonneg_loop_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

definition poly_all_nonneg_monadic :: "gmp_poly \<Rightarrow> bool nres" where
"poly_all_nonneg_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  (PR_CONST poly_all_nonneg_loop_monadic) len xs
}"

sepref_register "PR_CONST poly_all_nonneg_monadic"
  :: "gmp_poly \<Rightarrow> bool nres"

lemma poly_all_nonneg_loop_correct:
  assumes len: "length xs = len"
    and cap: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_all_nonneg_loop_monadic len xs \<le> RETURN (\<forall>i<len. 0 \<le> xs ! i)"
  unfolding poly_all_nonneg_loop_monadic_def nonneg_scan_cond_def
    nonneg_scan_body_mop_monadic_def poly_coeff_sgn_monadic_def PR_CONST_def
  apply (refine_vcg WHILET_rule[where R="measure (\<lambda>(i, b). len - i)"
    and I="\<lambda>(i, b). i \<le> len \<and> b = (\<forall>j<i. 0 \<le> xs ! j)"])
  using assms
  by (auto simp: max_snat_def less_Suc_eq sgn_if split: if_splits)

lemma poly_all_nonneg_correct:
  assumes "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "poly_all_nonneg_monadic xs \<le> RETURN (\<forall>i<length xs. 0 \<le> xs ! i)"
  unfolding poly_all_nonneg_monadic_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg poly_all_nonneg_loop_correct[THEN order_trans])
  using assms by (auto simp: pw_le_iff refine_pw_simps)



subsection \<open>Sepref synthesis for the two loops\<close>

sepref_definition poly_negate_loop_impl [llvm_code] is
  "uncurry poly_negate_loop_monadic" ::
  "[\<lambda>(len, xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_negate_loop_monadic_def Let_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_negate_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_negate_loop_impl,
    uncurry (PR_CONST poly_negate_loop_monadic)) \<in>
    [\<lambda>(len, xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_negate_loop_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition poly_negate_in_place_impl [llvm_code] is
  "poly_negate_in_place_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding poly_negate_in_place_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma poly_negate_in_place_impl_hnr[sepref_fr_rules]:
  "(poly_negate_in_place_impl,
    PR_CONST poly_negate_in_place_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using poly_negate_in_place_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The scan BORROWS the poly (\<open>\<^sup>k\<close>) and carries a pure bool --- the shape of the
  \<open>max_bitlen\<close> fold, not of the trunc loop.\<close>
text \<open>\<^bold>\<open>Two registrations each\<close> (PROOF_BRIDGE_AND_PATTERNS \<section>: an op needs BOTH a
  \<open>sepref_register\<close> AND a \<open>[sepref_fr_rules]\<close> HNR). The cond and body are synthesised as
  their OWN ops here; the loop below then consumes their HNRs and does NOT unfold them ---
  unfolding turns them into raw lambdas that \<open>sepref\<close>'s initial method cannot match, which is
  exactly the "Failed to apply initial proof method" this shape first produced.\<close>
sepref_definition nonneg_scan_cond_impl [llvm_inline] is
  "uncurry (RETURN oo nonneg_scan_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a nonneg_scan_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding nonneg_scan_cond_def Let_def
  by sepref

lemma nonneg_scan_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry nonneg_scan_cond_impl,
    uncurry (RETURN oo (PR_CONST nonneg_scan_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a nonneg_scan_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using nonneg_scan_cond_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition nonneg_scan_body_impl [llvm_inline] is
  "uncurry2 nonneg_scan_body_mop_monadic" ::
  "[\<lambda>((len, xs), i, b). len \<le> length xs]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a nonneg_scan_state_assn\<^sup>d
    \<rightarrow> nonneg_scan_state_assn"
  unfolding nonneg_scan_body_mop_monadic_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)?
  by sepref

lemma nonneg_scan_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 nonneg_scan_body_impl,
    uncurry2 (PR_CONST nonneg_scan_body_mop_monadic)) \<in>
    [\<lambda>((len, xs), i, b). len \<le> length xs]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a nonneg_scan_state_assn\<^sup>d
    \<rightarrow> nonneg_scan_state_assn"
  using nonneg_scan_body_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition poly_all_nonneg_loop_impl [llvm_code] is
  "uncurry poly_all_nonneg_loop_monadic" ::
  "[\<lambda>(len, xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding poly_all_nonneg_loop_monadic_def
  supply [sepref_fr_rules] = nonneg_scan_cond_impl_hnr nonneg_scan_body_impl_hnr
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma poly_all_nonneg_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry poly_all_nonneg_loop_impl,
    uncurry (PR_CONST poly_all_nonneg_loop_monadic)) \<in>
    [\<lambda>(len, xs). length xs = len \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using poly_all_nonneg_loop_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition poly_all_nonneg_impl [llvm_code] is
  "poly_all_nonneg_monadic" ::
  "[\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding poly_all_nonneg_monadic_def
  by sepref

lemma poly_all_nonneg_impl_hnr[sepref_fr_rules]:
  "(poly_all_nonneg_impl, PR_CONST poly_all_nonneg_monadic) \<in>
    [\<lambda>xs. length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using poly_all_nonneg_impl.refine
  by (simp add: PR_CONST_def)

subsection \<open>The ratio gate, as @{const probe_reject_gate_mop}\<close>

text \<open>\<open>M > c * (w + k*n)\<close> at \<open>w = 2n\<close>, \<open>k = 2\<close> (two triangles) and \<open>c = 8\<close>. It returns the truncation exponent \<open>t = nb - w\<close>,
  or \<open>0\<close> for ``do not attempt''. It affects only performance: the decide is self-certifying
  (@{thm right_empty_decide_sound} holds for every \<open>t\<close>), so no choice here is unsound.\<close>
definition right_empty_budget_mul :: nat where "right_empty_budget_mul = 2"
definition right_empty_gate_c :: nat where "right_empty_gate_c = 8"

definition right_empty_gate_mop :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where
"right_empty_gate_mop len nb \<equiv> doN {
  top \<leftarrow> RETURN (PR_CONST (trunc_max_snat_incl TYPE(gmp_poly_len)));
  capm \<leftarrow> RETURN (top div (2 * right_empty_budget_mul));
  if len \<le> capm \<and> nb \<le> top then doN {
    w \<leftarrow> RETURN (right_empty_budget_mul * len);
    kn \<leftarrow> RETURN (right_empty_budget_mul * len);
    if kn \<le> top - w then doN {
      thr \<leftarrow> RETURN (nb div right_empty_gate_c);
      if w + kn < thr then RETURN (nb - w) else RETURN 0
    } else RETURN 0
  } else RETURN 0
}"

sepref_register "PR_CONST right_empty_gate_mop" :: "nat \<Rightarrow> nat \<Rightarrow> nat nres"

text \<open>The fact the call site needs: an admitted node gets a positive exponent that is a valid machine word.\<close>
lemma right_empty_gate_mop_admits_pos:
  "right_empty_gate_mop len nb \<le> SPEC (\<lambda>t. 0 < t \<longrightarrow> t < max_snat LENGTH(gmp_poly_len))"
proof -
  have "\<And>w kn. w + kn < nb div right_empty_gate_c \<Longrightarrow> nb \<le> trunc_max_snat_incl TYPE(gmp_poly_len)
        \<Longrightarrow> 0 < nb - w \<and> nb - w < max_snat LENGTH(gmp_poly_len)"
  proof -
    fix w kn assume A: "w + kn < nb div right_empty_gate_c"
      and B: "nb \<le> trunc_max_snat_incl TYPE(gmp_poly_len)"
    have "nb div right_empty_gate_c \<le> nb" by simp
    with A have "w < nb" by linarith
    moreover have "nb - w \<le> nb" by simp
    ultimately show "0 < nb - w \<and> nb - w < max_snat LENGTH(gmp_poly_len)"
      using B by (simp add: max_snat_def)
  qed
  thus ?thesis
    unfolding right_empty_gate_mop_def PR_CONST_def
    by (auto simp: pw_le_iff refine_pw_simps max_snat_def)
qed

sepref_definition right_empty_gate_impl [llvm_inline] is
  "uncurry right_empty_gate_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  unfolding right_empty_gate_mop_def right_empty_budget_mul_def right_empty_gate_c_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma right_empty_gate_impl_hnr[sepref_fr_rules]:
  "(uncurry right_empty_gate_impl, uncurry (PR_CONST right_empty_gate_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  using right_empty_gate_impl.refine
  by (simp add: PR_CONST_def)



subsection \<open>The composed decide\<close>

text \<open>\<^bold>\<open>One arm\<close>: copy (BORROWS \<open>ql\<close>), truncate in place, then \<open>F = T \<circ> rev \<circ> T\<close>, then the
  O(n) non-negativity scan. Every constituent is an existing op with its own HNR, so nothing new
  enters the TCB.\<close>
definition right_empty_arm_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
"right_empty_arm_monadic t ql \<equiv> doN {
  ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_copy_monadic) ql;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_trunc_in_place_monadic) t c;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_taylor_shift_one_in_place_monadic) c;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_reverse_in_place_monadic) c;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_taylor_shift_one_in_place_monadic) c;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  b \<leftarrow> (PR_CONST poly_all_nonneg_monadic) c;
  (PR_CONST poly_free_monadic) c;
  RETURN b
}"

sepref_register "PR_CONST right_empty_arm_monadic" :: "nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

text \<open>\<^bold>\<open>The MIRROR arm\<close>: the same, on \<open>-ql\<close>. Truncation does NOT commute with negation, so the
  negation must happen BEFORE the truncation --- which is why this is a second arm and not a
  sign flip of the first one's result.\<close>
definition right_empty_neg_arm_monadic :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
"right_empty_neg_arm_monadic g t ql \<equiv> doN {
  ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_copy_monadic) ql;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>\<^bold>\<open>The frame ramp makes this arm sound on a truncated node.\<close> The non-negative arm transfers across \<open>gframe\<close>
     directly (the frame is one-sided upwards and \<open>Ffun\<close> is monotone); this arm concludes \<open>Ffun (carried_left Y) \<le> 0\<close>, where
     \<open>2\<^sup>s * (\<le> 0) + (\<ge> 0)\<close> has no determined sign. Adding \<open>2\<^sup>g\<^sup>+\<^sup>l\<^sup>e\<^sup>n\<^sup>-\<^sup>1\<^sup>-\<^sup>j\<close> makes the arm decide about \<open>carried_left (Y + 2\<^sup>g)\<close>, which
     dominates \<open>carried_left X / 2\<^sup>s\<close> because \<open>X ! j < 2\<^sup>s * (Y ! j + 2\<^sup>g)\<close>, so a successful arm certifies the exact child. It
     comes before the negation and the truncation, since these steps do not commute.\<close>
  c \<leftarrow> (PR_CONST err_ramp_in_place_monadic) g c;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_negate_in_place_monadic) c;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_trunc_in_place_monadic) t c;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_taylor_shift_one_in_place_monadic) c;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_reverse_in_place_monadic) c;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  c \<leftarrow> (PR_CONST poly_taylor_shift_one_in_place_monadic) c;
  ASSERT (length c + 1 < max_snat LENGTH(gmp_poly_len));
  b \<leftarrow> (PR_CONST poly_all_nonneg_monadic) c;
  (PR_CONST poly_free_monadic) c;
  RETURN b
}"

sepref_register "PR_CONST right_empty_neg_arm_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

lemma right_empty_arm_correct:
  assumes t: "0 < t"
    and ne: "0 < length ql"
    and cap: "length ql + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "right_empty_arm_monadic t ql
       \<le> RETURN (\<forall>i < length ql. 0 \<le> Ffun (trunc_list t ql) ! i)"
  unfolding right_empty_arm_monadic_def PR_CONST_def
  apply (refine_vcg poly_copy_correct[THEN order_trans]
    poly_trunc_in_place_correct[THEN order_trans]
    poly_taylor_shift_one_in_place_monadic_correct[THEN order_trans]
    poly_reverse_in_place_monadic_correct[THEN order_trans]
    poly_all_nonneg_correct[THEN order_trans]
    poly_free_monadic_bind_rule)
  using assms
  by (auto simp: trunc_list_def pw_le_iff refine_pw_simps)

lemma right_empty_neg_arm_correct:
  assumes t: "0 < t"
    and ne: "0 < length ql"
    and cap: "length ql + 1 < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length ql < max_snat LENGTH(gmp_poly_len)"
  shows "right_empty_neg_arm_monadic g t ql
       \<le> RETURN (\<forall>i < length ql. 0 \<le> Ffun (trunc_list t (map uminus (err_ramp_opt g ql))) ! i)"
  unfolding right_empty_neg_arm_monadic_def PR_CONST_def
  apply (refine_vcg poly_copy_correct[THEN order_trans]
    err_ramp_in_place_correct[THEN order_trans]
    poly_negate_in_place_correct[THEN order_trans]
    poly_trunc_in_place_correct[THEN order_trans]
    poly_taylor_shift_one_in_place_monadic_correct[THEN order_trans]
    poly_reverse_in_place_monadic_correct[THEN order_trans]
    poly_all_nonneg_correct[THEN order_trans]
    poly_free_monadic_bind_rule)
  using assms
  by (auto simp: trunc_list_def pw_le_iff refine_pw_simps)

text \<open>\<^bold>\<open>The decide.\<close> The gate first (no allocation), then at most two arms. The budget read is the exact maximum
  (@{const poly_max_bitlen_monadic}) rather than the \<open>O(1)\<close> leading coefficient, whose bit length can be far below the
  maximum at this site, so that the attempt guard does not fail on those inputs. The scan is \<open>O(n)\<close> bit-length reads
  against an \<open>O(n\<^sup>2)\<close> decide, and since \<open>t\<close> affects only performance, using the exact maximum is sound by the same
  theorem.\<close>
definition right_empty_decide_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
"right_empty_decide_monadic g ql \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) ql;
  ASSERT (len = length ql);
  ASSERT (0 < len);
  nb \<leftarrow> (PR_CONST poly_max_bitlen_monadic) ql;
  t \<leftarrow> (PR_CONST right_empty_gate_mop) len nb;
  if t = 0 then RETURN False
  else doN {
    \<comment> \<open>Discharged by @{thm right_empty_gate_mop_admits_pos} together with \<open>t \<noteq> 0\<close>. It is here because
       \<open>poly_trunc_in_place\<close>'s HNR demands both halves and Sepref cannot read them off the
       gate's RESULT type alone.\<close>
    ASSERT (0 < t \<and> t < max_snat LENGTH(gmp_poly_len));
    b \<leftarrow> (PR_CONST right_empty_arm_monadic) t ql;
    if b then RETURN True else (PR_CONST right_empty_neg_arm_monadic) g t ql
  }
}"

sepref_register "PR_CONST right_empty_decide_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

text \<open>\<^bold>\<open>THE PAYOFF\<close> --- a fired decide PROVES the right child empty, which is what lets the
  caller skip both the \<open>O(n\<^sup>2)\<close> build and the push. One-directional: \<open>False\<close> says nothing, and the
  caller then runs the exact path unchanged.\<close>
text \<open>\<^bold>\<open>The ramp only makes the mirror arm stricter\<close>, so its conclusion is unchanged: the ramp term is non-negative
  and \<open>Ffun\<close> is monotone, so \<open>Ffun ys \<le> Ffun (err_ramp_opt g ys) \<le> 0\<close>. On an exact node \<open>g\<close> is \<open>0\<close> and the ramp is as small as
  it can be, and \<open>carried_left_right_skip_right_correct\<close> needs no change.\<close>
lemma err_ramp_ge: "j < length ys \<Longrightarrow> ys ! j \<le> err_ramp_opt g ys ! j"
  by (simp add: err_ramp_opt_def err_ramp_nth)

lemma F_nonpos_of_err_ramp:
  fixes ys :: "int list"
  assumes np: "\<And>i. i < length ys
        \<Longrightarrow> 0 \<le> Ffun (map (\<lambda>x. x div 2 ^ t) (map uminus (err_ramp_opt g ys))) ! i"
    and i: "i < length ys"
  shows "Ffun ys ! i \<le> 0"
proof -
  have lenm: "length (map uminus (err_ramp_opt g ys)) = length ys" by simp
  have "0 \<le> Ffun (map uminus (err_ramp_opt g ys)) ! i"
    by (rule F_nonneg_lift[where t = t]) (use np i lenm in simp_all)
  hence R: "Ffun (err_ramp_opt g ys) ! i \<le> 0" using i by (simp add: F_uminus)
  have "Ffun ys ! i \<le> Ffun (err_ramp_opt g ys) ! i"
    by (rule F_mono) (use i err_ramp_ge in simp_all)
  with R show ?thesis by linarith
qed

lemma sign_changes_fold_of_err_ramp:
  fixes ys :: "int list"
  assumes np: "\<And>i. i < length ys
        \<Longrightarrow> 0 \<le> Ffun (map (\<lambda>x. x div 2 ^ t) (map uminus (err_ramp_opt g ys))) ! i"
  shows "sign_changes_fold (Ffun ys) = 0"
proof -
  have "\<forall>x \<in> set (map uminus (Ffun ys)). 0 \<le> x"
  proof
    fix x assume "x \<in> set (map uminus (Ffun ys))"
    then obtain i where i: "i < length (Ffun ys)" and x: "x = - (Ffun ys ! i)"
      by (auto simp: in_set_conv_nth)
    have "i < length ys" using i by simp
    thus "0 \<le> x" using F_nonpos_of_err_ramp[OF np] x by simp
  qed
  hence "sign_changes_fold (map uminus (Ffun ys)) = 0" by (rule sign_changes_fold_nonneg)
  thus ?thesis by (simp add: sign_changes_fold_uminus)
qed

theorem right_empty_decide_monadic_sound:
  assumes ne: "0 < length (carried_left xs)"
    and cap: "length (carried_left xs) + 1 < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length (carried_left xs) < max_snat LENGTH(gmp_poly_len)"
  shows "right_empty_decide_monadic g (carried_left xs)
       \<le> SPEC (\<lambda>b. b \<longrightarrow> carried_descartes_count (carried_right xs) = 0)"
proof -
  \<comment> \<open>CALCULATIONAL, not \<open>fastforce\<close>: a one-shot search has to bridge \<open>trunc_list\<close> AND
     discharge \<open>RETURN \<le> SPEC\<close> over \<open>nres\<close> at once. Split, each step is a rewrite.\<close>
  have arm: "right_empty_arm_monadic t (carried_left xs)
      \<le> SPEC (\<lambda>b. b \<longrightarrow> carried_descartes_count (carried_right xs) = 0)"
    if t: "0 < t" for t
  proof -
    have "right_empty_arm_monadic t (carried_left xs)
        \<le> RETURN (\<forall>i < length (carried_left xs).
                     0 \<le> Ffun (trunc_list t (carried_left xs)) ! i)"
      by (rule right_empty_arm_correct[OF t ne cap])
    also have "\<dots> \<le> SPEC (\<lambda>b. b \<longrightarrow> carried_descartes_count (carried_right xs) = 0)"
      using right_empty_decide_sound[of xs t] by (auto simp: trunc_list_def)
    finally show ?thesis .
  qed
  have narm: "right_empty_neg_arm_monadic g t (carried_left xs)
      \<le> SPEC (\<lambda>b. b \<longrightarrow> carried_descartes_count (carried_right xs) = 0)"
    if t: "0 < t" for t
  proof -
    have "right_empty_neg_arm_monadic g t (carried_left xs)
        \<le> RETURN (\<forall>i < length (carried_left xs).
                     0 \<le> Ffun (trunc_list t (map uminus (err_ramp_opt g (carried_left xs)))) ! i)"
      by (rule right_empty_neg_arm_correct[OF t ne cap kb])
    also have "\<dots> \<le> SPEC (\<lambda>b. b \<longrightarrow> carried_descartes_count (carried_right xs) = 0)"
      using sign_changes_fold_of_err_ramp[where ys = "carried_left xs" and g = g and t = t]
      by (auto simp: trunc_list_def carried_descartes_count_def carried_right_def)
    finally show ?thesis .
  qed
  show ?thesis
    \<comment> \<open>\<open>poly_length_monadic\<close> must be UNFOLDED: without a rule for it \<open>refine_vcg\<close> stalls at the
       first bind and leaves the whole chain as one goal. The arms go in as vcg rules, not as facts.\<close>
    unfolding right_empty_decide_monadic_def PR_CONST_def poly_length_monadic_def
    apply (refine_vcg poly_max_bitlen_monadic_nofail[THEN order_trans]
      right_empty_gate_mop_admits_pos[THEN order_trans] arm narm)
    using assms by simp_all
qed

text \<open>\<^bold>\<open>What the EXACT-node transfer consumes.\<close> @{thm right_empty_decide_monadic_sound} speaks
  about the stored node only, and throws away WHICH arm fired --- but the transfer to the exact
  node needs exactly that: the non-negative arm transfers across \<open>gframe\<close> as it stands, the
  mirror arm only as the statement about \<open>err_shift g Y\<close>. The two disjuncts below are stated in
  the precise shapes of the transfer lemmas' hypotheses (\<open>Hybrid_Solver_Dispatch\<close>), so the
  consumer eliminates the disjunction and applies them with no further bridging.\<close>
definition right_empty_certified :: "nat \<Rightarrow> int list \<Rightarrow> bool" where
"right_empty_certified g Y \<longleftrightarrow>
   (\<forall>j < length (carried_left Y). 0 \<le> Ffun (carried_left Y) ! j) \<or>
   (\<forall>j < length (carried_left (err_shift g Y)). Ffun (carried_left (err_shift g Y)) ! j \<le> 0)"

theorem right_empty_decide_monadic_certifies:
  assumes ne: "0 < length (carried_left xs)"
    and cap: "length (carried_left xs) + 1 < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length (carried_left xs) < max_snat LENGTH(gmp_poly_len)"
  shows "right_empty_decide_monadic g (carried_left xs)
       \<le> SPEC (\<lambda>b. b \<longrightarrow> carried_descartes_count (carried_right xs) = 0 \<and> right_empty_certified g xs)"
proof -
  have lenL: "length (carried_left xs) = length xs" by (simp add: carried_left_def)
  have arm: "right_empty_arm_monadic t (carried_left xs)
      \<le> SPEC (\<lambda>b. b \<longrightarrow> carried_descartes_count (carried_right xs) = 0 \<and> right_empty_certified g xs)"
    if t: "0 < t" for t
  proof -
    have "right_empty_arm_monadic t (carried_left xs)
        \<le> RETURN (\<forall>i < length (carried_left xs).
                     0 \<le> Ffun (trunc_list t (carried_left xs)) ! i)"
      by (rule right_empty_arm_correct[OF t ne cap])
    also have "\<dots> \<le> SPEC (\<lambda>b. b \<longrightarrow> carried_descartes_count (carried_right xs) = 0 \<and>
                                right_empty_certified g xs)"
    proof -
      have C: "0 \<le> Ffun (carried_left xs) ! j"
        if nn: "\<forall>i < length (carried_left xs). 0 \<le> Ffun (trunc_list t (carried_left xs)) ! i"
          and j: "j < length (carried_left xs)" for j
        by (rule F_nonneg_lift[where t = t]) (use nn j in \<open>simp_all add: trunc_list_def\<close>)
      show ?thesis
        using right_empty_decide_sound[of xs t] C
        by (auto simp: trunc_list_def right_empty_certified_def)
    qed
    finally show ?thesis .
  qed
  have narm: "right_empty_neg_arm_monadic g t (carried_left xs)
      \<le> SPEC (\<lambda>b. b \<longrightarrow> carried_descartes_count (carried_right xs) = 0 \<and> right_empty_certified g xs)"
    if t: "0 < t" for t
  proof -
    have "right_empty_neg_arm_monadic g t (carried_left xs)
        \<le> RETURN (\<forall>i < length (carried_left xs).
                     0 \<le> Ffun (trunc_list t (map uminus (err_ramp_opt g (carried_left xs)))) ! i)"
      by (rule right_empty_neg_arm_correct[OF t ne cap kb])
    also have "\<dots> \<le> SPEC (\<lambda>b. b \<longrightarrow> carried_descartes_count (carried_right xs) = 0 \<and>
                                right_empty_certified g xs)"
    proof -
      have C: "Ffun (carried_left (err_shift g xs)) ! j \<le> 0"
        if np: "\<forall>i < length (carried_left xs).
                  0 \<le> Ffun (trunc_list t (map uminus (err_ramp_opt g (carried_left xs)))) ! i"
          and j: "j < length (carried_left (err_shift g xs))" for j
      proof -
        have jL: "j < length (carried_left xs)" using j by (simp add: carried_left_def)
        have lenR: "length (map uminus (err_ramp_opt g (carried_left xs))) = length (carried_left xs)"
          by simp
        have "0 \<le> Ffun (map uminus (err_ramp_opt g (carried_left xs))) ! j"
          by (rule F_nonneg_lift[where t = t]) (use np jL lenR in \<open>simp_all add: trunc_list_def\<close>)
        hence "Ffun (err_ramp_opt g (carried_left xs)) ! j \<le> 0" using jL by (simp add: F_uminus)
        thus ?thesis by (simp add: err_ramp_opt_carried_left)
      qed
      have Z: "carried_descartes_count (carried_right xs) = 0"
        if np: "\<forall>i < length (carried_left xs).
                  0 \<le> Ffun (trunc_list t (map uminus (err_ramp_opt g (carried_left xs)))) ! i"
        using sign_changes_fold_of_err_ramp[where ys = "carried_left xs" and g = g and t = t] np
        by (auto simp: trunc_list_def carried_descartes_count_def carried_right_def)
      show ?thesis
        using C Z by (auto simp: right_empty_certified_def)
    qed
    finally show ?thesis .
  qed
  show ?thesis
    unfolding right_empty_decide_monadic_def PR_CONST_def poly_length_monadic_def
    apply (refine_vcg poly_max_bitlen_monadic_nofail[THEN order_trans]
      right_empty_gate_mop_admits_pos[THEN order_trans] arm narm)
    using assms by simp_all
qed


subsection \<open>The decide's Sepref layer\<close>

text \<open>\<^bold>\<open>The two-registration rule.\<close> Each of the three ops above already had a
  \<open>sepref_register\<close>; a register WITHOUT a \<open>sepref_definition\<close>+HNR is exactly the configuration
  whose failure surfaces at the CONSUMER ("Failed to apply initial proof method") rather than
  here, so all three are synthesised before anything downstream is attempted.
  \<^bold>\<open>Ownership\<close>: both arms BORROW \<open>ql\<close> --- the copy is what they mutate, and they free it
  themselves --- so \<open>ql\<close> is \<open>\<^sup>k\<close> and the decide can call the second arm after the
  first has run.\<close>

sepref_definition right_empty_arm_impl [llvm_code] is
  "uncurry right_empty_arm_monadic" ::
  "[\<lambda>(t, ql). 0 < t \<and> t < max_snat LENGTH(gmp_poly_len) \<and>
      length ql + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding right_empty_arm_monadic_def
  by sepref

lemma right_empty_arm_impl_hnr[sepref_fr_rules]:
  "(uncurry right_empty_arm_impl, uncurry (PR_CONST right_empty_arm_monadic)) \<in>
    [\<lambda>(t, ql). 0 < t \<and> t < max_snat LENGTH(gmp_poly_len) \<and>
      length ql + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using right_empty_arm_impl.refine
  by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The ramp ops get their own registrations first\<close> --- the two-registration rule
  (\<open>PROOF_BRIDGE_AND_PATTERNS\<close>): each needs BOTH a \<open>sepref_register\<close> (above) and an HNR here, or
  the arm's synthesis fails with the generic "Failed to apply initial proof method".\<close>

sepref_definition err_ramp_body_impl [llvm_code] is
  "uncurry3 err_ramp_body_monadic" ::
  \<comment> \<open>\<^bold>\<open>No precondition.\<close> Every fact the body's ops need is one of its own ASSERTs
     (\<open>j < length c\<close>, \<open>0 < len\<close>, \<open>j < len\<close>, the \<open>mpz_pow2\<close> bound), which Sepref reads off the
     program. A precondition would have to be RE-PROVED at the loop's call site, where
     \<open>length ys\<close> is unknown after the first iteration.
     \<^bold>\<open>History\<close>: this was blamed on the pre/body \<open>annot_snat_const\<close> mismatch; the real cause,
     found with \<open>sepref_dbg_trans_keep\<close>, was that @{const poly_add_mpz_coeff_monadic} had no HNR
     in scope --- its ladder failed upstream at the \<open>ptrs\<close> rule's unfocus step.\<close>
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a gmp_poly_assn"
  unfolding err_ramp_body_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma err_ramp_body_impl_hnr[sepref_fr_rules]:
  "(uncurry3 err_ramp_body_impl, uncurry3 (PR_CONST err_ramp_body_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a gmp_poly_assn"
  using err_ramp_body_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The \<open>poly_negate_loop_impl\<close> shape: \<open>for_by_while'\<close> needs the \<open>length xs + 1\<close> word bound,
  which @{const err_ramp_in_place_monadic} already ASSERTs for this call.\<close>
sepref_definition err_ramp_loop_impl [llvm_code] is
  "uncurry2 err_ramp_loop_monadic" ::
  "[\<lambda>((g, len), xs). len = length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding err_ramp_loop_monadic_def
  apply (subst for_by_while'[where t="TYPE(gmp_poly_len)"])
   apply simp
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma err_ramp_loop_impl_hnr[sepref_fr_rules]:
  "(uncurry2 err_ramp_loop_impl, uncurry2 (PR_CONST err_ramp_loop_monadic)) \<in>
    [\<lambda>((g, len), xs). len = length xs \<and>
      length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using err_ramp_loop_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition err_ramp_in_place_impl [llvm_code] is
  "uncurry err_ramp_in_place_monadic" ::
  "[\<lambda>(g, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  unfolding err_ramp_in_place_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma err_ramp_in_place_impl_hnr[sepref_fr_rules]:
  "(uncurry err_ramp_in_place_impl, uncurry (PR_CONST err_ramp_in_place_monadic)) \<in>
    [\<lambda>(g, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn"
  using err_ramp_in_place_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition right_empty_neg_arm_impl [llvm_code] is
  "uncurry2 right_empty_neg_arm_monadic" ::
  "[\<lambda>((g, t), ql). 0 < t \<and> t < max_snat LENGTH(gmp_poly_len) \<and>
      length ql + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding right_empty_neg_arm_monadic_def
  by sepref

lemma right_empty_neg_arm_impl_hnr[sepref_fr_rules]:
  "(uncurry2 right_empty_neg_arm_impl, uncurry2 (PR_CONST right_empty_neg_arm_monadic)) \<in>
    [\<lambda>((g, t), ql). 0 < t \<and> t < max_snat LENGTH(gmp_poly_len) \<and>
      length ql + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using right_empty_neg_arm_impl.refine
  by (simp add: PR_CONST_def)

sepref_definition right_empty_decide_impl [llvm_code] is
  "uncurry right_empty_decide_monadic" ::
  "[\<lambda>(g, ql). length ql + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding right_empty_decide_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma right_empty_decide_impl_hnr[sepref_fr_rules]:
  "(uncurry right_empty_decide_impl, uncurry (PR_CONST right_empty_decide_monadic)) \<in>
    [\<lambda>(g, ql). length ql + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using right_empty_decide_impl.refine
  by (simp add: PR_CONST_def)


subsection \<open>The \<open>qr!0\<close> fast path: an \<open>O(n)\<close> read in place of a quadratic build\<close>

text \<open>Both call sites (\<open>truncate_children_mid_monadic\<close> in \<open>Truncate\<close> and \<open>defl_split_children_monadic\<close> in
  \<open>Hybrid_Solver_Dispatch\<close>, both later in the build and so named in plain text) read \<open>qr!0\<close>'s sign and bit length to
  drive \<open>truncate_mid_decide_monadic\<close>. On the fast path the right child is not built, so the read comes from the left
  child, in \<open>O(n)\<close>: \<open>carried_right xs ! 0 = poly (Poly (carried_left xs)) 1 = sum_list (carried_left xs)\<close>, which is the first
  component of @{const poly_eval1_pair}. (\<open>Deflation_Bridge.carried_right_nth0_eq_left_poly_1\<close> and
  \<open>Hybrid_Keystone.carried_right_nth0_poly\<close> state the same fact; neither is imported here.)\<close>

lemma poly_Poly_at_1:
  fixes ys :: "int list"
  shows "poly (Poly ys) 1 = sum_list ys"
  by (induction ys) auto

lemma carried_right_nth0_sum_list:
  assumes ne: "0 < length xs"
  shows "carried_right xs ! 0 = sum_list (carried_left xs)"
proof -
  have len: "length (carried_right xs) = length xs" by (simp add: carried_right_def)
  have ne': "carried_right xs \<noteq> []" using ne len by fastforce
  have "carried_right xs ! 0 = poly.coeff (Poly (carried_right xs)) 0"
    using ne ne' by (simp add: nth_default_def)
  also have "\<dots> = poly (Poly (carried_right xs)) 0"
    by (simp add: poly_0_coeff_0)
  also have "\<dots> = poly (pcompose (Poly (carried_left xs)) [:1, 1:]) 0"
    by (simp add: carried_right_def Poly_taylor_shift_list)
  also have "\<dots> = poly (Poly (carried_left xs)) 1"
    by (simp add: poly_pcompose)
  finally show ?thesis by (simp add: poly_Poly_at_1)
qed

corollary carried_right_nth0_eval1:
  assumes ne: "0 < length xs"
  shows "carried_right xs ! 0 = fst (poly_eval1_pair (carried_left xs))"
  using carried_right_nth0_sum_list[OF ne] by (simp add: poly_eval1_pair_def)

text \<open>\<^bold>\<open>THE DEFLATION INTERLOCK.\<close> A Descartes count of \<open>0\<close> does NOT imply the midpoint is not a
  root: the count is about the OPEN box, and a root AT the shared endpoint contributes no sign
  variation. So the fast path must fall back to the exact build whenever \<open>qr!0 = 0\<close>, or
  \<open>defl_children_monadic\<close> would shed a linear factor from a child that was never built. The
  guard is exactly \<open>sum_list (carried_left xs) \<noteq> 0\<close>, and it is FREE --- the fast path computes
  that sum anyway for \<open>mids\<close>/\<open>midbl\<close>.\<close>
lemma carried_right_nth0_nz_iff:
  assumes ne: "0 < length xs"
  shows "(carried_right xs ! 0 \<noteq> 0) = (sum_list (carried_left xs) \<noteq> 0)"
  using carried_right_nth0_sum_list[OF ne] by simp


end
