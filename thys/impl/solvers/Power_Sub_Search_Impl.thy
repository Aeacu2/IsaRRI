theory Power_Sub_Search_Impl
  imports Power_Sub_Certify_Impl
begin

text \<open>The precision search: the hybrid test-and-double loop (op \<open>pow_sub_backmap_loop_monadic\<close>).

  \<^bold>\<open>The loop is capped.\<close> The abstract search is unbounded: it \<open>ASSERT\<close>s \<open>\<exists>m. tst m\<close> and climbs
  towards a witness it cannot compute.

  \<^bold>\<open>The machine word alone forces a cap.\<close> \<open>m\<close> is an \<open>snat\<close> loop state, so \<open>m + 1\<close> needs
  \<open>m + 1 < max_snat\<close> in the invariant, and (as for every loop here, see \<open>Power_Sub_Detect_Impl\<close>)
  that bound cannot be discharged at the loop boundary without a cap. The choice is between a small
  cap with a fallback and a large, vacuous one; a large cap is worse, because a case that never
  certifies would run for \<open>\<approx>2\<^sup>6\<^sup>3/h\<close> iterations.

  \<^bold>\<open>The cap cannot be removed by proof either.\<close> The count-level witness exists:
  @{thm [source] Dsc_Misc.Bernstein_changes_small_interval_le_1} (the engine of
  @{thm [source] NewDsc.newdsc_terminates_squarefree}) gives \<open>count \<le> 1\<close> once the window is no wider
  than \<open>delta_P\<close>, and \<open>Bernstein_changes_test\<close> (via
  @{thm [source] Dsc_Misc.Bernstein_changes_pos_of_root}) gives \<open>roots_in \<le> count\<close>, so with
  \<open>roots_in = 1\<close> from \<open>pow_sub_shrink_exists\<close> the count is exactly 1. But that bound is stated in
  terms of \<open>delta_P\<close>, a root separation: it yields \<open>\<exists>m\<close>, never \<open>m \<le> f(\<dots>)\<close> for a quantity the
  runtime can compute, and a separation-derived quantity is not demanded of callers.

  So the fallback is permanent. This op is sound and terminates unconditionally; when it returns
  \<open>ok = False\<close> the caller does not substitute.

  \<^bold>\<open>The cap is relative to the caller's exponent \<open>k\<close>.\<close> The loop starts at \<open>m\<^sub>0\<close> and runs to
  \<open>mcap\<close>, and the entry passes \<open>m\<^sub>0 = k\<close>, \<open>mcap = k + \<Delta>\<close>. Starting at \<open>0\<close> would pay one bisection
  \<open>h\<close>-th root and one certification test for each of the \<open>k\<close> precisions below the one the caller
  already reached. \<open>\<Delta>\<close> is an argument of the entry, not a constant fixed here.\<close>

section \<open>The pure test the loop is searching for\<close>

definition pow_sub_num_hi :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> int" where
  "pow_sub_num_hi h m a = \<lceil>(a powr (1 / real h)) * 2 ^ m\<rceil>"

definition pow_sub_num_lo :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> int" where
  "pow_sub_num_lo h m a = \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>"

text \<open>The emit op reports its endpoints as \<open>pow_sub_hi h m a = l / 2\<^sup>m\<close>; dividing by \<open>2\<^sup>m\<close> is
  injective, so that equation PINS \<open>l\<close>. These two lemmas are what let the loop's refinement
  proof turn the emit SPEC into a statement about the pure test.\<close>

lemma pow_sub_num_hi_unique:
  assumes "pow_sub_hi h m a = real_of_int l / 2 ^ m"
  shows "l = pow_sub_num_hi h m a"
proof -
  have "real_of_int l = real_of_int (pow_sub_num_hi h m a)"
    using assms unfolding pow_sub_hi_def pow_sub_num_hi_def
    by (simp add: divide_eq_eq)
  then show ?thesis by (simp only: of_int_eq_iff)
qed

lemma pow_sub_num_lo_unique:
  assumes "pow_sub_lo h m a = real_of_int l / 2 ^ m"
  shows "l = pow_sub_num_lo h m a"
proof -
  have "real_of_int l = real_of_int (pow_sub_num_lo h m a)"
    using assms unfolding pow_sub_lo_def pow_sub_num_lo_def
    by (simp add: divide_eq_eq)
  then show ?thesis by (simp only: of_int_eq_iff)
qed

text \<open>\<^bold>\<open>The test is a sign change rather than a Descartes count.\<close> A Descartes count
  \<open>descartes_preprocess \<dots> = 1\<close> on the shrunk window is correct but costs one \<open>O(n\<^sup>2)\<close> transform of the
  whole reduced polynomial per emitted interval. @{const pow_sub_sign_tst} decides the same question
  in \<open>O(n)\<close> coefficient operations, certifies the same intervals at the same precision, and needs no
  one-circle argument (see \<open>Power_Sub_Certify_Impl\<close>'s sign section).

  \<^bold>\<open>The two endpoints are the ones the emit reports\<close>, so the test is phrased on
  @{const pow_sub_num_hi}/@{const pow_sub_num_lo}, and the uniqueness lemmas below turn the emit's
  specification into a statement about it.\<close>

text \<open>\<^bold>\<open>It is a disjunction, and the count arm is reachable.\<close> The sign test needs a strict change, so
  it cannot succeed when \<open>Q\<close> vanishes at a shrunk endpoint, which is what an exactly representable
  neighbouring root looks like. Example: \<open>x\<^sup>4 - 5x\<^sup>2 + 4\<close>, with \<open>Q = (y-1)(y-4)\<close>; the reduced solve emits
  \<open>(1/4, 4)\<close> beside the degenerate \<open>[4,4]\<close>, and \<open>\<lfloor>\<surd>4 \<cdot> 2\<^sup>m\<rfloor> = 2\<^sup>m\<^sup>+\<^sup>1\<close> exactly at every \<open>m\<close>, so the shrunk
  right endpoint lies on the neighbour's root and \<open>Q\<close> evaluates to \<open>0\<close> there at every precision. The
  count decides that case correctly (it counts the open window, where the boundary root does not
  appear), so it is called when the sign test declines. Irrational roots never land on the dyadic
  grid; constructed ones can.\<close>

definition pow_sub_loop_tst ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> bool" where
  "pow_sub_loop_tst h A B k xs m \<equiv>
     pow_sub_sign_tst h m
       (pow_sub_num_hi h m (real_of_int A / 2 ^ k))
       (pow_sub_num_lo h m (real_of_int B / 2 ^ k)) xs
     \<or> (descartes_preprocess
           (pow_sub_num_hi h m (real_of_int A / 2 ^ k) ^ h) (2 ^ (h * m))
           (pow_sub_num_lo h m (real_of_int B / 2 ^ k) ^ h) (2 ^ (h * m)) xs = 1
         \<and> pow_sub_num_hi h m (real_of_int A / 2 ^ k) ^ h
             < pow_sub_num_lo h m (real_of_int B / 2 ^ k) ^ h)"

section \<open>The loop condition — PURE, so a plain WHILEIT suffices\<close>

text \<open>Unlike \<open>root_floor_gmp2\<close>, whose condition is GMP arithmetic and therefore needs
  @{const monadic_WHILEIT}, this condition reads only the machine-word precision and the
  accepted flag. The GMP work is entirely in the BODY.\<close>

definition pow_sub_search_cond :: "nat \<Rightarrow> nat \<times> bool \<Rightarrow> bool" where
  "pow_sub_search_cond mcap st \<longleftrightarrow> (let (m, ok) = st in \<not> ok \<and> m < mcap)"

sepref_register "PR_CONST pow_sub_search_cond" :: "nat \<Rightarrow> nat \<times> bool \<Rightarrow> bool"

abbreviation pow_sub_search_state_assn where
  "pow_sub_search_state_assn \<equiv> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"

sepref_definition pow_sub_search_cond_impl [llvm_inline] is
  "uncurry (RETURN oo pow_sub_search_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_search_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_search_cond_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow_sub_search_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_search_cond_impl,
    uncurry (RETURN oo (PR_CONST pow_sub_search_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_search_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_search_cond_impl.refine by (simp add: PR_CONST_def)

section \<open>The body: emit, certify, discard\<close>

text \<open>\<^bold>\<open>The HNR precondition is STATE-INDEPENDENT\<close> — it never mentions \<open>m\<close>. The two
  state-dependent needs, \<open>h \<cdot> m < max_snat\<close> (the emit and certify ops' bound) and
  \<open>m + 1 < max_snat\<close> (the increment), are ASSERTs INSIDE the body; @{thm hn_ASSERT_bind} turns
  them into assumptions at synthesis, and they are discharged in the enclosing program's
  refinement proof from the invariant \<open>m \<le> mcap\<close> plus the caller's \<open>h \<cdot> mcap < max_snat\<close>.
  This is the rule that cost two sessions to learn; see \<open>Power_Sub_Detect_Impl\<close>.

  \<^bold>\<open>Ownership\<close>: \<open>A\<close>, \<open>B\<close> and \<open>xs\<close> are KEPT — the loop re-emits from them at every precision.
  The window endpoints the emit op allocates are OWNED and discarded here, on both branches,
  because certify KEEPS them.\<close>

definition pow_sub_search_body_mop ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<times> bool \<Rightarrow> (nat \<times> bool) nres" where
  "pow_sub_search_body_mop h A B k xs st \<equiv> doN {
     let (m, ok) = st;
     ASSERT (0 < h \<and> 0 \<le> A \<and> 0 \<le> B
             \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> h * m < max_snat LENGTH(gmp_poly_len)
             \<and> h * m * length xs < max_snat LENGTH(gmp_poly_len)
             \<and> 0 < length xs
             \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
     lr \<leftarrow> (PR_CONST pow_sub_backmap_iv_monadic) h m A B k;
     let (L, R) = lr;
     c1 \<leftarrow> (PR_CONST pow_sub_certify_sign_monadic) h m L R xs;
     c \<leftarrow> (if c1 then RETURN True
            else (PR_CONST pow_sub_certify_monadic) h m L R xs);
     (PR_CONST mpzb_discard_monadic) L;
     (PR_CONST mpzb_discard_monadic) R;
     ASSERT (m + 1 < max_snat LENGTH(gmp_poly_len));
     if c then RETURN (m, True) else RETURN (m + 1, False)
   }"

lemma pow_sub_search_body_correct:
  assumes h: "0 < h" and A0: "0 \<le> A" and B0: "0 \<le> B"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and hm: "h * m < max_snat LENGTH(gmp_poly_len)"
    and eb: "h * m * length xs < max_snat LENGTH(gmp_poly_len)"
    and len0: "0 < length xs"
    and len: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and m1: "m + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_search_body_mop h A B k xs (m, ok)
           \<le> SPEC (\<lambda>(m', ok'). ok' = pow_sub_loop_tst h A B k xs m
                                \<and> (ok' \<longrightarrow> m' = m)
                                \<and> (\<not> ok' \<longrightarrow> m' = m + 1))"
  \<comment> \<open>stated WITHOUT an \<open>if\<close> on the right: with one there, \<open>refine_vcg\<close> case-splits it
     before it walks the binds, and the emit/certify rules then have nothing to fire on\<close>
proof -
  have emit: "pow_sub_backmap_iv_monadic h m A B k
      \<le> SPEC (\<lambda>(l, r). pow_sub_hi h m (real_of_int A / 2 ^ k) = real_of_int l / 2 ^ m
                        \<and> pow_sub_lo h m (real_of_int B / 2 ^ k) = real_of_int r / 2 ^ m)"
    by (rule pow_sub_backmap_iv_monadic_correct[OF h A0 B0 hb k hm refl refl])
  show ?thesis
    unfolding pow_sub_search_body_mop_def PR_CONST_def mpzb_discard_monadic_def
    apply (simp only: Let_def prod.case)
    using h A0 B0 hb k hm eb len0 len m1
    apply (refine_vcg)
    \<comment> \<open>\<open>emit[THEN order_trans]\<close> in \<open>refine_vcg\<close>'s rule list does NOT fire here — the bind
       leaves the emit under a nested \<open>SPEC\<close>, so it is applied by hand, and \<open>refine_vcg\<close> is
       re-entered underneath it to walk the discards, the inner ASSERT and the branch\<close>
    apply (all \<open>(auto; fail)
                | (rule order_trans[OF emit],
                   refine_vcg pow_sub_certify_sign_monadic_correct[OF h hb hm len0 len eb,
                                THEN order_trans]
                              pow_sub_certify_monadic_correct[OF h hb hm len,
                                THEN order_trans],
                   auto simp: pow_sub_loop_tst_def
                        dest!: pow_sub_num_hi_unique pow_sub_num_lo_unique)\<close>)
    done
qed

sepref_register "PR_CONST pow_sub_search_body_mop"
  :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<times> bool \<Rightarrow> (nat \<times> bool) nres"

sepref_definition pow_sub_search_body_impl [llvm_code] is
  "uncurry5 pow_sub_search_body_mop" ::
  "[\<lambda>(((((h, A), B), k), xs), st). 0 < h \<and> 0 \<le> A \<and> 0 \<le> B
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length xs
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      pow_sub_search_state_assn\<^sup>d \<rightarrow> pow_sub_search_state_assn"
  unfolding pow_sub_search_body_mop_def
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

lemma pow_sub_search_body_impl_hnr[sepref_fr_rules]:
  "(uncurry5 pow_sub_search_body_impl, uncurry5 (PR_CONST pow_sub_search_body_mop)) \<in>
    [\<lambda>(((((h, A), B), k), xs), st). 0 < h \<and> 0 \<le> A \<and> 0 \<le> B
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length xs
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      pow_sub_search_state_assn\<^sup>d \<rightarrow> pow_sub_search_state_assn"
  using pow_sub_search_body_impl.refine by (simp add: PR_CONST_def)

section \<open>The search\<close>

definition pow_sub_search_monadic ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> (nat \<times> bool) nres" where
  "pow_sub_search_monadic h A B k xs mcap \<equiv> doN {
     ASSERT (0 < h \<and> 0 \<le> A \<and> 0 \<le> B
             \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k \<le> mcap
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> h * mcap < max_snat LENGTH(gmp_poly_len)
             \<and> h * mcap * length xs < max_snat LENGTH(gmp_poly_len)
             \<and> mcap < max_snat LENGTH(gmp_poly_len)
             \<and> 0 < length xs
             \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
     st \<leftarrow> WHILEIT
        (\<lambda>(m, ok). k \<le> m \<and> m \<le> mcap \<and> (ok \<longrightarrow> pow_sub_loop_tst h A B k xs m))
        (\<lambda>st. (PR_CONST pow_sub_search_cond) mcap st)
        (\<lambda>st. (PR_CONST pow_sub_search_body_mop) h A B k xs st)
        (k, False);
     RETURN st
   }"

text \<open>\<^bold>\<open>Soundness, unconditionally.\<close> When the flag is set, the pure test holds at the reported
  precision, so the emitted window carries a Descartes count of one, and
  \<open>descartes_preprocess_one_root\<close> (\<open>Power_Sub_Certify_Impl\<close>) takes that to \<open>roots_in = 1\<close>.
  \<^bold>\<open>Completeness, that the flag is eventually set, is not claimed\<close> (see this theory's header). The
  measure is \<open>mcap - m\<close>, so termination needs no witness.

  \<^bold>\<open>The loop starts at \<open>k\<close>, the caller's own exponent.\<close> The caller's \<open>Q\<close>-interval is already known
  to precision \<open>2\<^sup>-\<^sup>k\<close>, so each \<open>m < k\<close> would cost a bisection \<open>h\<close>-th root and a certification test for
  nothing. With the start at \<open>k\<close>, \<open>mcap\<close> reads as \<open>k + \<Delta>\<close>, which is why the cap is passed as an
  absolute ceiling with \<open>k \<le> mcap\<close> asserted rather than as an iteration count. The invariant gains
  \<open>k \<le> m\<close>; soundness is per-\<open>m\<close>, so nothing else changes.\<close>

lemma pow_sub_search_monadic_correct:
  assumes h: "0 < h" and A0: "0 \<le> A" and B0: "0 \<le> B"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and kmc: "k \<le> mcap"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and hmc: "h * mcap < max_snat LENGTH(gmp_poly_len)"
    and eb: "h * mcap * length xs < max_snat LENGTH(gmp_poly_len)"
    and mc: "mcap < max_snat LENGTH(gmp_poly_len)"
    and len0: "0 < length xs"
    and len: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_search_monadic h A B k xs mcap
           \<le> SPEC (\<lambda>(m, ok). k \<le> m \<and> m \<le> mcap
                              \<and> (ok \<longrightarrow> pow_sub_loop_tst h A B k xs m))"
proof -
  \<comment> \<open>the body's two state-dependent bounds, derived ONCE from the cap: \<open>h \<cdot> a \<le> h \<cdot> mcap\<close>
     and \<open>a + 1 \<le> mcap\<close>. This is what the cap buys — with an unbounded search neither is
     available, which is why \<open>find_least_impl\<close> cannot be synthesised as written.\<close>
  have body: "\<And>a. a < mcap \<Longrightarrow>
      pow_sub_search_body_mop h A B k xs (a, False)
        \<le> SPEC (\<lambda>(m', ok'). ok' = pow_sub_loop_tst h A B k xs a
                             \<and> (ok' \<longrightarrow> m' = a)
                             \<and> (\<not> ok' \<longrightarrow> m' = a + 1))"
  proof -
    fix a :: nat assume alt: "a < mcap"
    have hle: "h * a \<le> h * mcap" using alt by (simp add: mult_le_mono2 less_imp_le)
    have hma: "h * a < max_snat LENGTH(gmp_poly_len)"
      using hle hmc by (rule order_le_less_trans)
    have a1: "a + 1 < max_snat LENGTH(gmp_poly_len)" using alt mc by simp
    have hle2: "h * a * length xs \<le> h * mcap * length xs"
      using alt by (simp add: mult_le_mono2 less_imp_le)
    have hma2: "h * a * length xs < max_snat LENGTH(gmp_poly_len)"
      using hle2 eb by (rule order_le_less_trans)
    show "pow_sub_search_body_mop h A B k xs (a, False)
            \<le> SPEC (\<lambda>(m', ok'). ok' = pow_sub_loop_tst h A B k xs a
                                 \<and> (ok' \<longrightarrow> m' = a)
                                 \<and> (\<not> ok' \<longrightarrow> m' = a + 1))"
      by (rule pow_sub_search_body_correct[OF h A0 B0 hb k hma hma2 len0 len a1])
  qed
  show ?thesis
    unfolding pow_sub_search_monadic_def pow_sub_search_cond_def PR_CONST_def
    using h A0 B0 hb kmc k hmc eb mc len0 len
    apply (refine_vcg
           WHILEIT_rule[where R = "measure (\<lambda>(m, ok). (mcap - m) + (if ok then 0 else 1))"])
    apply (all \<open>(auto simp: Let_def intro!: order_trans[OF body])\<close>)
    done
qed

section \<open>The assembly\<close>

sepref_register "PR_CONST pow_sub_search_monadic"
  :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> (nat \<times> bool) nres"

sepref_definition pow_sub_search_impl [llvm_code] is
  "uncurry5 pow_sub_search_monadic" ::
  "[\<lambda>(((((h, A), B), k), xs), mcap). 0 < h \<and> 0 \<le> A \<and> 0 \<le> B
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * mcap < max_snat LENGTH(gmp_poly_len)
       \<and> h * mcap * length xs < max_snat LENGTH(gmp_poly_len)
       \<and> mcap < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length xs
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> pow_sub_search_state_assn"
  unfolding pow_sub_search_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    pow_sub_search_cond_impl_hnr pow_sub_search_body_impl_hnr
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

lemma pow_sub_search_impl_hnr[sepref_fr_rules]:
  "(uncurry5 pow_sub_search_impl, uncurry5 (PR_CONST pow_sub_search_monadic)) \<in>
    [\<lambda>(((((h, A), B), k), xs), mcap). 0 < h \<and> 0 \<le> A \<and> 0 \<le> B
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * mcap < max_snat LENGTH(gmp_poly_len)
       \<and> h * mcap * length xs < max_snat LENGTH(gmp_poly_len)
       \<and> mcap < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length xs
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> pow_sub_search_state_assn"
  using pow_sub_search_impl.refine by (simp add: PR_CONST_def)

end
