theory Power_Sub_Degen_Impl
  imports Power_Sub_Search_Impl
begin

text \<open>Precision search, \<^bold>\<open>degenerate branch\<close>.

  @{thm [source] pow_sub_backmap_pair_exists} branches on \<open>fst I = snd I\<close> and emits two different
  windows:

  \<^item> proper \<open>(a, b)\<close>: \<open>(pow_sub_hi h m a, pow_sub_lo h m b)\<close>, shrinking, which
    \<open>pow_sub_search_monadic\<close> implements;
  \<^item> degenerate \<open>(a, a)\<close>: \<open>(pow_sub_lo h m a, pow_sub_hi h m a)\<close>, widening, which this op implements.

  Feeding a degenerate \<open>Q\<close>-pair to the shrinking search puts \<open>\<lceil>\<cdot>\<rceil>\<close> on the window's low end and
  \<open>\<lfloor>\<cdot>\<rfloor>\<close> on its high end: an empty or inverted window, whose Descartes count is never \<open>1\<close>, so the
  search would exhaust \<open>mcap\<close> and return \<open>ok = False\<close>. That is sound (the entry falls back to a full
  solve), but the reduced solve does emit degenerate \<open>[a,a]\<close> pairs for exact dyadic roots, and each
  such case would lose the substitution.

  \<^bold>\<open>The widening pair needs only one bisection\<close>: the ceiling is the floor plus one except when the
  \<open>h\<close>-th root is exactly representable, and that case is decided by the integer identity
  @{thm [source] pow_sub_root_exact_iff}, which \<open>root_exact_monadic\<close> evaluates. When it holds,
  \<open>\<lfloor>\<cdot>\<rfloor> = \<lceil>\<cdot>\<rceil>\<close> and the emitted \<open>P\<close>-pair is degenerate too; its @{const dsc_pair_ok} arm is
  \<open>poly P u = 0\<close>, discharged by @{thm [source] pow_sub_pair_ok_degenerate} with no count test, so
  the loop accepts immediately.

  The loop condition is shared with the proper search: @{const pow_sub_search_cond} is a pure
  predicate on \<open>(m, ok)\<close> and \<open>mcap\<close>.\<close>

section \<open>The pure test\<close>

text \<open>Stated on what the OP computes, not on \<open>pow_sub_num_hi\<close>: the op derives the high endpoint
  as \<open>L + 1\<close> and short-circuits on the exact case, so phrasing the test that way makes the
  refinement proof nearly definitional. @{thm [source] pow_sub_hi_of_num} is what reconciles
  \<open>L + 1\<close> with \<open>pow_sub_num_hi\<close> where the soundness bridge needs it.\<close>

definition pow_sub_deg_tst :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> bool" where
  "pow_sub_deg_tst h A k xs m \<equiv>
     (let L = pow_sub_num_lo h m (real_of_int A / 2 ^ k) in
        L ^ h * 2 ^ k = A * 2 ^ (h * m)
        \<or> (descartes_preprocess (L ^ h) (2 ^ (h * m)) ((1 + L) ^ h) (2 ^ (h * m)) xs = 1
            \<and> L ^ h < (1 + L) ^ h))"
  \<comment> \<open>\<^bold>\<open>\<open>1 + L\<close>, not \<open>L + 1\<close>\<close>: \<open>mpz_add.amop_r1 one L\<close> yields \<open>1 + L\<close>, and the refinement goal carries
     that orientation. Writing \<open>L + 1\<close> leaves an AC gap that only \<open>algebra_simps\<close> closes, which is
     too expensive inside the body's closing \<open>auto\<close>.\<close>

section \<open>The body: one bisection, an exactness test, then certify\<close>

text \<open>\<^bold>\<open>Ownership.\<close> \<open>A\<close> and \<open>xs\<close> are KEPT — the loop re-emits from them at every precision.
  \<open>root_floor_gmp2\<close> hands back an OWNED \<open>L\<close>; \<open>rhs\<close> is owned and discarded once the exactness
  test has read it; on the non-exact branch \<open>mpz_add.amop_r1\<close> consumes the literal \<open>1\<close> and
  KEEPS \<open>L\<close>, and @{const pow_sub_certify_monadic} keeps both endpoints, so \<open>L\<close> and \<open>R\<close> are
  discarded here on every exit.

  \<^bold>\<open>The HNR precondition is STATE-INDEPENDENT\<close> — it never mentions \<open>m\<close>. The two state-dependent
  needs, \<open>h \<cdot> m < max_snat\<close> and \<open>m + 1 < max_snat\<close>, are ASSERTs INSIDE the body;
  @{thm hn_ASSERT_bind} turns them into assumptions at synthesis and the enclosing program
  discharges them from the invariant \<open>m \<le> mcap\<close> plus the caller's \<open>h \<cdot> mcap < max_snat\<close>. This
  is the rule that cost two sessions to learn; see \<open>Power_Sub_Detect_Impl\<close>.\<close>

definition pow_sub_deg_body_mop ::
  "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<times> bool \<Rightarrow> (nat \<times> bool) nres" where
  "pow_sub_deg_body_mop h A k xs st \<equiv> doN {
     let (m, ok) = st;
     ASSERT (0 < h \<and> 0 \<le> A
             \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> h * m < max_snat LENGTH(gmp_poly_len)
             \<and> m + 1 < max_snat LENGTH(gmp_poly_len)
             \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
     L \<leftarrow> (PR_CONST root_floor_gmp2) h m A k;
     rhs \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) (COPY A) (h * m);
     e \<leftarrow> (PR_CONST root_exact_monadic) h k rhs L;
     (PR_CONST mpzb_discard_monadic) rhs;
     if e then doN {
       (PR_CONST mpzb_discard_monadic) L;
       RETURN (m, True)
     } else doN {
       one \<leftarrow> RETURN (mpz_from_int 1);
       R \<leftarrow> (PR_CONST mpz_add.amop_r1) one L;
       c \<leftarrow> (PR_CONST pow_sub_certify_monadic) h m L R xs;
       (PR_CONST mpzb_discard_monadic) L;
       (PR_CONST mpzb_discard_monadic) R;
       if c then RETURN (m, True) else RETURN (m + 1, False)
     }
   }"

lemma pow_sub_deg_body_correct:
  assumes h: "0 < h" and A0: "0 \<le> A"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and hm: "h * m < max_snat LENGTH(gmp_poly_len)"
    and len: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and m1: "m + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_deg_body_mop h A k xs (m, ok)
           \<le> SPEC (\<lambda>(m', ok'). ok' = pow_sub_deg_tst h A k xs m
                                \<and> (ok' \<longrightarrow> m' = m)
                                \<and> (\<not> ok' \<longrightarrow> m' = m + 1))"
  \<comment> \<open>stated WITHOUT an \<open>if\<close> on the right, for the same reason as
     \<open>pow_sub_search_body_correct\<close>: with one there, \<open>refine_vcg\<close> case-splits before it walks
     the binds and the emit/certify rules have nothing to fire on\<close>
proof -
  have lo: "root_floor_gmp2 h m A k
              \<le> SPEC (\<lambda>n. pow_sub_lo h m (real_of_int A / 2 ^ k) = real_of_int n / 2 ^ m)"
    by (rule root_floor_gmp2_is_pow_sub_lo[OF h A0 hb k hm refl])
  show ?thesis
    unfolding pow_sub_deg_body_mop_def PR_CONST_def mpzb_discard_monadic_def
      mpz_add.amop_r1_def mpz_add.aop_r1_def mpz_from_int_def COPY_def
    apply (simp only: Let_def prod.case)
    using h A0 hb k hm len m1
    apply (refine_vcg)
    apply (all \<open>(auto; fail)
                | (rule order_trans[OF lo],
                   refine_vcg
                     mpz_shift_left_snat_monadic_spec_plain[OF hm, THEN order_trans]
                     root_exact_monadic_correct[OF h hb k, THEN order_trans]
                     pow_sub_certify_monadic_correct[OF h hb hm len, THEN order_trans],
                   auto simp: pow_sub_deg_tst_def Let_def
                        dest!: pow_sub_num_lo_unique)\<close>)
    done
qed

section \<open>What the degenerate test certifies\<close>

text \<open>Two arms, matching @{const pow_sub_deg_tst}'s disjunction.

  \<^item> \<^bold>\<open>Exact\<close>: \<open>L\<^sup>h \<cdot> 2\<^sup>k = A \<cdot> 2\<^sup>h\<^sup>\<cdot>\<^sup>m\<close> says \<open>(L/2\<^sup>m)\<^sup>h = a\<close> exactly, and \<open>a\<close> is a root of \<open>Q\<close> (that
    is what \<open>dsc_pair_ok Q (a,a)\<close> gives), so \<open>poly P (L/2\<^sup>m) = 0\<close> and the emitted degenerate
    \<open>P\<close>-pair satisfies @{const dsc_pair_ok} by @{thm [source] pow_sub_pair_ok_degenerate}.
  \<^item> \<^bold>\<open>Counted\<close>: the count-\<open>1\<close> arm goes through @{thm [source] descartes_preprocess_one_root}
    as the proper branch's does; @{thm [source] pow_sub_certify_isolates} is stated generically in
    \<open>L\<close> and \<open>R\<close> and so applies with \<open>R = 1 + L\<close>.

  Only the first arm is proved here; the second is @{thm [source] pow_sub_certify_isolates}
  unchanged, and the \<open>P\<close>-side transfer for both is @{thm [source] pow_sub_roots_in_eq}, which needs
  \<open>P = Q \<circ>\<^sub>p monom 1 h\<close> in scope and therefore belongs to the entry.\<close>

lemma pow_sub_deg_exact_isolates:
  fixes Q :: "real poly" and A L :: int
  assumes h: "0 < h" and P: "P = Q \<circ>\<^sub>p monom 1 h"
    and adef: "a = real_of_int A / 2 ^ k"
    and root: "poly Q a = 0"
    and exact: "L ^ h * 2 ^ k = A * 2 ^ (h * m)"
  shows "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int L / 2 ^ m)"
proof -
  \<comment> \<open>\<open>(2\<^sup>m)\<^sup>h = 2\<^sup>h\<^sup>\<cdot>\<^sup>m\<close> as a STANDALONE step. Handing it to \<open>simp\<close> inside the main equation
     lets \<open>power_mult\<close> fire on both sides in different directions and leaves the unprovable
     residual \<open>(2\<^sup>m)\<^sup>h = (2\<^sup>h)\<^sup>m\<close>. Same shape as \<open>e2\<close> inside
     @{thm [source] pow_sub_root_exact_iff}.\<close>
  have e2: "((2::real) ^ m) ^ h = 2 ^ (h * m)"
  proof -
    have "((2::real) ^ m) ^ h = 2 ^ (m * h)" by (simp add: power_mult)
    then show ?thesis by (simp add: mult.commute)
  qed
  have "(real_of_int L / 2 ^ m) ^ h = (real_of_int L) ^ h / ((2::real) ^ m) ^ h"
    by (rule power_divide)
  also have "\<dots> = real_of_int (L ^ h) / 2 ^ (h * m)" using e2 by simp
  also have "\<dots> = a"
  proof -
    from exact have "real_of_int (L ^ h * 2 ^ k) = real_of_int (A * 2 ^ (h * m))" by simp
    then have "real_of_int (L ^ h) * 2 ^ k = real_of_int A * 2 ^ (h * m)" by simp
    then show ?thesis unfolding adef by (simp add: field_simps)
  qed
  finally have "poly Q ((real_of_int L / 2 ^ m) ^ h) = 0" using root by simp
  then show ?thesis by (rule pow_sub_pair_ok_degenerate[OF h P])
qed

section \<open>Sepref: the body\<close>

sepref_register "PR_CONST pow_sub_deg_body_mop"
  :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<times> bool \<Rightarrow> (nat \<times> bool) nres"

sepref_definition pow_sub_deg_body_impl [llvm_code] is
  "uncurry4 pow_sub_deg_body_mop" ::
  "[\<lambda>((((h, A), k), xs), st). 0 < h \<and> 0 \<le> A
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      pow_sub_search_state_assn\<^sup>d \<rightarrow> pow_sub_search_state_assn"
  unfolding pow_sub_deg_body_mop_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const gmp_int_t)?
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

lemma pow_sub_deg_body_impl_hnr[sepref_fr_rules]:
  "(uncurry4 pow_sub_deg_body_impl, uncurry4 (PR_CONST pow_sub_deg_body_mop)) \<in>
    [\<lambda>((((h, A), k), xs), st). 0 < h \<and> 0 \<le> A
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      pow_sub_search_state_assn\<^sup>d \<rightarrow> pow_sub_search_state_assn"
  using pow_sub_deg_body_impl.refine by (simp add: PR_CONST_def)

section \<open>The degenerate search\<close>

text \<open>The same capped shape as @{const pow_sub_search_monadic}, for the same two reasons (see
  that theory's header). The search starts at \<open>k\<close>.\<close>

definition pow_sub_deg_search_monadic ::
  "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> (nat \<times> bool) nres" where
  "pow_sub_deg_search_monadic h A k xs mcap \<equiv> doN {
     ASSERT (0 < h \<and> 0 \<le> A
             \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k \<le> mcap
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> h * mcap < max_snat LENGTH(gmp_poly_len)
             \<and> mcap < max_snat LENGTH(gmp_poly_len)
             \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
     st \<leftarrow> WHILEIT
        (\<lambda>(m, ok). k \<le> m \<and> m \<le> mcap \<and> (ok \<longrightarrow> pow_sub_deg_tst h A k xs m))
        (\<lambda>st. (PR_CONST pow_sub_search_cond) mcap st)
        (\<lambda>st. (PR_CONST pow_sub_deg_body_mop) h A k xs st)
        (k, False);
     RETURN st
   }"

lemma pow_sub_deg_search_monadic_correct:
  assumes h: "0 < h" and A0: "0 \<le> A"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and kmc: "k \<le> mcap"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and hmc: "h * mcap < max_snat LENGTH(gmp_poly_len)"
    and mc: "mcap < max_snat LENGTH(gmp_poly_len)"
    and len: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_deg_search_monadic h A k xs mcap
           \<le> SPEC (\<lambda>(m, ok). k \<le> m \<and> m \<le> mcap
                              \<and> (ok \<longrightarrow> pow_sub_deg_tst h A k xs m))"
proof -
  have body: "\<And>a. a < mcap \<Longrightarrow>
      pow_sub_deg_body_mop h A k xs (a, False)
        \<le> SPEC (\<lambda>(m', ok'). ok' = pow_sub_deg_tst h A k xs a
                             \<and> (ok' \<longrightarrow> m' = a)
                             \<and> (\<not> ok' \<longrightarrow> m' = a + 1))"
  proof -
    fix a :: nat assume alt: "a < mcap"
    have hle: "h * a \<le> h * mcap" using alt by (simp add: mult_le_mono2 less_imp_le)
    have hma: "h * a < max_snat LENGTH(gmp_poly_len)"
      using hle hmc by (rule order_le_less_trans)
    have a1: "a + 1 < max_snat LENGTH(gmp_poly_len)" using alt mc by simp
    show "pow_sub_deg_body_mop h A k xs (a, False)
            \<le> SPEC (\<lambda>(m', ok'). ok' = pow_sub_deg_tst h A k xs a
                                 \<and> (ok' \<longrightarrow> m' = a)
                                 \<and> (\<not> ok' \<longrightarrow> m' = a + 1))"
      by (rule pow_sub_deg_body_correct[OF h A0 hb k hma len a1])
  qed
  show ?thesis
    unfolding pow_sub_deg_search_monadic_def pow_sub_search_cond_def PR_CONST_def
    using h A0 hb kmc k hmc mc len
    apply (refine_vcg
           WHILEIT_rule[where R = "measure (\<lambda>(m, ok). (mcap - m) + (if ok then 0 else 1))"])
    apply (all \<open>(auto simp: Let_def intro!: order_trans[OF body])\<close>)
    done
qed

sepref_register "PR_CONST pow_sub_deg_search_monadic"
  :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> (nat \<times> bool) nres"

sepref_definition pow_sub_deg_search_impl [llvm_code] is
  "uncurry4 pow_sub_deg_search_monadic" ::
  "[\<lambda>((((h, A), k), xs), mcap). 0 < h \<and> 0 \<le> A
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k \<le> mcap
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * mcap < max_snat LENGTH(gmp_poly_len)
       \<and> mcap < max_snat LENGTH(gmp_poly_len)
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> pow_sub_search_state_assn"
  unfolding pow_sub_deg_search_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    pow_sub_search_cond_impl_hnr pow_sub_deg_body_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

lemma pow_sub_deg_search_impl_hnr[sepref_fr_rules]:
  "(uncurry4 pow_sub_deg_search_impl, uncurry4 (PR_CONST pow_sub_deg_search_monadic)) \<in>
    [\<lambda>((((h, A), k), xs), mcap). 0 < h \<and> 0 \<le> A
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k \<le> mcap
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * mcap < max_snat LENGTH(gmp_poly_len)
       \<and> mcap < max_snat LENGTH(gmp_poly_len)
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> pow_sub_search_state_assn"
  using pow_sub_deg_search_impl.refine by (simp add: PR_CONST_def)

end
