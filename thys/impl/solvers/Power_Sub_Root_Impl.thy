theory Power_Sub_Root_Impl
  imports
    "IsaRRI_LLVM.Dyadic_Interval"
    "IsaRRI_Spec.Power_Sub_Loop"
begin

text \<open>Integer \<open>h\<close>-th root, monadic layer (below Sepref).

  The specification says \<open>pow_sub_lo h m a = \<lfloor>a\<^sup>1\<^sup>/\<^sup>h \<cdot> 2\<^sup>m\<rfloor> / 2\<^sup>m\<close>, which mentions @{const powr}, an
  uncomputable real. \<open>Power_Sub_Loop.pow_sub_root_test_dyadic\<close> shows that the membership test is an
  exact integer inequality on the dyadic endpoints the pipeline carries. This theory finds that
  integer and proves the search returns the floor: a binary search whose every operation is
  integer arithmetic (\<open>mpz_mul\<close>, \<open>mpz_mul_2exp\<close>, a comparison), so it needs no new GMP primitive.

  The monadic definitions live in \<open>IsaRRI_LLVM\<close> because \<open>IsaRRI_Spec\<close> is pure HOL and has no
  \<open>nres\<close>.\<close>

section \<open>The test, and the specification of the search\<close>

definition root_test :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "root_test h m A k n \<longleftrightarrow> n ^ h * 2 ^ k \<le> A * 2 ^ (h * m)"

text \<open>\<^bold>\<open>All the numerics.\<close> \<open>n \<^sup>h\<close> is repeated \<open>mpz_mul\<close>; the two \<open>2\<^sup>\<cdot>\<close> factors are
  \<open>mpz_mul_2exp\<close>; the \<open>\<le>\<close> is one comparison. The test is exact, so the certificate is exact.\<close>

definition root_floor_spec :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int nres" where
  "root_floor_spec h m A k \<equiv>
     SPEC (\<lambda>n. 0 \<le> n \<and> root_test h m A k n \<and> \<not> root_test h m A k (n + 1))"

text \<open>\<^bold>\<open>This specification pins the SPEC-layer value\<close>, which is the only thing that makes the
  search worth doing. Note what is NOT here: no \<open>powr\<close>, no root, no real number. The connection
  is made once, below, and never again.\<close>

lemma root_floor_spec_is_pow_sub_lo:
  fixes A :: int
  assumes h: "0 < h" and A0: "0 \<le> A" and adef: "a = real_of_int A / 2 ^ k"
  shows "root_floor_spec h m A k
           \<le> SPEC (\<lambda>n. pow_sub_lo h m a = real_of_int n / 2 ^ m)"
  unfolding root_floor_spec_def
proof (rule SPEC_rule)
    fix n :: int
    assume A: "0 \<le> n \<and> root_test h m A k n \<and> \<not> root_test h m A k (n + 1)"
    then have n0: "0 \<le> n" and t: "root_test h m A k n"
      and nt: "\<not> root_test h m A k (n + 1)" by auto
    have n10: "0 \<le> n + 1" using n0 by simp
    have le: "real_of_int n \<le> (a powr (1 / real h)) * 2 ^ m"
      using pow_sub_root_test_dyadic[OF h n0 A0 adef] t by (simp add: root_test_def)
    have nle: "\<not> real_of_int (n + 1) \<le> (a powr (1 / real h)) * 2 ^ m"
      using pow_sub_root_test_dyadic[OF h n10 A0 adef] nt by (simp add: root_test_def)
    have le': "n \<le> \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>"
      using le by (simp add: le_floor_iff)
    have nle': "\<not> n + 1 \<le> \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>"
      using nle by (simp add: le_floor_iff)
    from le' nle' have "n = \<lfloor>(a powr (1 / real h)) * 2 ^ m\<rfloor>" by simp
    then show "pow_sub_lo h m a = real_of_int n / 2 ^ m"
      unfolding pow_sub_lo_def by simp
qed

section \<open>The binary search\<close>

text \<open>Invariant: \<open>lo\<close> passes the test, \<open>hi\<close> fails it, \<open>lo < hi\<close>. The post-condition falls out
  when the gap closes to 1.

  \<^bold>\<open>The initial upper bound needs no analysis and no bit-length reasoning\<close>: for \<open>1 \<le> n\<close> and
  \<open>1 \<le> h\<close> we have \<open>n \<le> n\<^sup>h\<close>, so \<open>hi = 1 + A \<cdot> 2\<^sup>h\<^sup>m\<close> fails the test outright. It is a
  gross over-estimate, but the search is logarithmic in it, and choosing it this way keeps a
  bit-length estimate — which would be a second thing to prove — out of the loop entirely.\<close>

definition root_floor_impl :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int nres" where
  "root_floor_impl h m A k \<equiv> do {
     ASSERT (0 < h \<and> 0 \<le> A);
     let hi0 = 1 + A * 2 ^ (h * m);
     (lo, hi) \<leftarrow> WHILEIT
        (\<lambda>(lo, hi). 0 \<le> lo \<and> lo < hi
                    \<and> root_test h m A k lo \<and> \<not> root_test h m A k hi)
        (\<lambda>(lo, hi). 1 < hi - lo)
        (\<lambda>(lo, hi). do {
            let mid = (lo + hi) div 2;
            if root_test h m A k mid then RETURN (mid, hi) else RETURN (lo, mid)
         })
        (0, hi0);
     RETURN lo
   }"

lemma root_test_zero:
  assumes h: "0 < h" and A0: "0 \<le> A"
  shows "root_test h m A k 0"
proof -
  have z: "(0::int) ^ h = 0" using h by (rule zero_power)
  have "0 \<le> A * 2 ^ (h * m)" using A0 by simp
  then show ?thesis unfolding root_test_def by (simp add: z)
qed

lemma root_test_hi0_fails:
  assumes h: "0 < h" and A0: "0 \<le> A"
  shows "\<not> root_test h m A k (1 + A * 2 ^ (h * m))"
proof -
  define B where "B = 1 + A * 2 ^ (h * m)"
  have B1: "1 \<le> B" unfolding B_def using A0 by simp
  have "B \<le> B ^ h" using B1 h by (simp add: self_le_power)
  also have "B ^ h \<le> B ^ h * 2 ^ k" using B1 by simp
  finally have "B \<le> B ^ h * 2 ^ k" .
  moreover have "A * 2 ^ (h * m) < B" unfolding B_def by simp
  ultimately show ?thesis unfolding root_test_def B_def by simp
qed

lemma hi0_pos:
  fixes A :: int
  assumes "0 \<le> A"
  shows "0 < 1 + A * 2 ^ (h * m)"
proof -
  have "0 \<le> A * 2 ^ (h * m)" using assms by (simp add: zero_le_mult_iff)
  then show ?thesis by simp
qed

lemma mid_lower: "1 < hi - lo \<Longrightarrow> lo < (lo + hi) div 2" for lo hi :: int
  by presburger

lemma mid_upper: "1 < hi - lo \<Longrightarrow> (lo + hi) div 2 < hi" for lo hi :: int
  by presburger

lemma post_gap_one:
  fixes lo hi :: int
  assumes lt: "lo < hi" and stop: "\<not> 1 < hi - lo"
    and nt: "\<not> root_test h m A k hi"
  shows "\<not> root_test h m A k (lo + 1)"
proof -
  have "hi = lo + 1" using lt stop by linarith
  with nt show ?thesis by simp
qed
  \<comment> \<open>the loop exits with the gap at exactly 1, so \<open>hi\<close> IS \<open>lo + 1\<close> and the invariant's
     \<open>\<not> root_test hi\<close> is literally the post-condition\<close>

lemma root_floor_impl_correct:
  assumes h: "0 < h" and A0: "0 \<le> A"
  shows "root_floor_impl h m A k \<le> root_floor_spec h m A k"
  unfolding root_floor_impl_def root_floor_spec_def
  apply (refine_vcg
         WHILEIT_rule[where R = "measure (\<lambda>(lo, hi). nat (hi - lo))"])
  subgoal using h .
  subgoal using A0 .
  subgoal by simp
  subgoal by simp
  subgoal using hi0_pos[OF A0, where h = h and m = m] by simp
  subgoal using root_test_zero[OF h A0, where m = m and k = k] by simp
  subgoal using root_test_hi0_fails[OF h A0, where m = m and k = k] by simp
  subgoal by (auto simp: mid_lower)
  subgoal by (auto simp: mid_upper)
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: mid_lower mid_upper)
  subgoal by auto
  subgoal by (auto simp: mid_lower)
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: mid_lower mid_upper)
  subgoal by auto
  subgoal by auto
  subgoal for s lo hi using post_gap_one[where lo = lo and hi = hi] by auto
  done

text \<open>\<^bold>\<open>What the loop does not need.\<close> No invariant about \<open>powr\<close>, no precision estimate, no
  root-separation quantity. The two integer comparisons of \<open>root_floor_spec\<close> pin the answer
  (\<open>Power_Sub_Loop.pow_sub_lo_num_unique\<close>), and everything real-valued is discharged once, in
  \<open>root_floor_spec_is_pow_sub_lo\<close>.\<close>

corollary root_floor_impl_is_pow_sub_lo:
  fixes A :: int
  assumes h: "0 < h" and A0: "0 \<le> A" and adef: "a = real_of_int A / 2 ^ k"
  shows "root_floor_impl h m A k
           \<le> SPEC (\<lambda>n. pow_sub_lo h m a = real_of_int n / 2 ^ m)"
  using root_floor_impl_correct[OF h A0]
        root_floor_spec_is_pow_sub_lo[OF h A0 adef]
  by (rule order_trans)

section \<open>The ceiling half\<close>

text \<open>@{const pow_sub_hi} is the SAME search plus one exact comparison: the ceiling equals the
  floor when the test is tight at \<open>n\<close> (i.e. \<open>n\<^sup>h \<cdot> 2\<^sup>k = A \<cdot> 2\<^sup>h\<^sup>m\<close>, meaning the
  \<open>h\<close>-th root was exactly representable), and the floor plus one otherwise. That is exactly the
  branch \<open>pow_sub_degenerate_exists\<close> reads to decide between its two arms, so the impl computes
  the flag once and both consumers use it.\<close>

definition root_exact :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "root_exact h m A k n \<longleftrightarrow> n ^ h * 2 ^ k = A * 2 ^ (h * m)"

definition root_ceil_impl :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int nres" where
  "root_ceil_impl h m A k \<equiv> do {
     n \<leftarrow> root_floor_impl h m A k;
     RETURN (if root_exact h m A k n then n else n + 1)
   }"

section \<open>The hybrid precision search\<close>

text \<open>\<^bold>\<open>The loop that raises \<open>m\<close> until the certificate reads 1.\<close> Its termination is not a
  measure on the data — it is the EXISTENCE theorem from the spec layer
  (\<open>pow_sub_shrink_exists\<close> / \<open>pow_sub_degenerate_exists\<close>). That is the same shape as the
  solver's escalation ladder: the bound is non-computable and need only exist.

  Stated generically over the test, because the test is the only part that differs between the
  proper and the degenerate case, and because at the Sepref layer it becomes a monadic call to
  the existing Descartes count on the REDUCED polynomial — no new numerical machinery.\<close>

definition find_least_impl :: "(nat \<Rightarrow> bool) \<Rightarrow> nat nres" where
  "find_least_impl tst \<equiv> do {
     ASSERT (\<exists>m. tst m);
     m \<leftarrow> WHILEIT (\<lambda>m. \<forall>j < m. \<not> tst j) (\<lambda>m. \<not> tst m) (\<lambda>m. RETURN (m + 1)) 0;
     RETURN m
   }"

lemma wit_gt:
  fixes s M :: nat
  assumes w: "tst M" and inv: "\<forall>j < s. \<not> tst j" and ns: "\<not> tst s"
  shows "s < M"
proof (rule ccontr)
  assume "\<not> s < M"
  then have le: "M \<le> s" by (simp add: not_less)
  show False
  proof (cases "M = s")
    case True
    with w ns show False by simp
  next
    case False
    with le have "M < s" by simp
    with inv w show False by simp
  qed
qed
  \<comment> \<open>\<^bold>\<open>The variant, without needing the LEAST witness.\<close> Any witness bounds the search: the
     loop stops at the FIRST \<open>m\<close> that passes, so it cannot have walked past \<open>m0\<close>.\<close>

lemma find_least_impl_correct:
  assumes ex: "\<exists>m. tst m"
  shows "find_least_impl tst \<le> SPEC tst"
proof -
  from ex obtain m0 where m0: "tst m0" ..
  show ?thesis
    unfolding find_least_impl_def
    apply (refine_vcg WHILEIT_rule[where R = "measure (\<lambda>m. m0 - m)"])
    subgoal using ex .
    subgoal by simp
    subgoal by simp
    subgoal by (auto simp: less_Suc_eq)
    subgoal for s using wit_gt[where tst = tst and M = m0 and s = s] m0 by simp
    subgoal by simp
    done
qed
  \<comment> \<open>the search is climbing towards a witness it cannot compute, which is exactly why the loop
     is hybrid rather than carrying a precision formula\<close>

text \<open>\<^bold>\<open>Instantiation 1 — a proper \<open>Q\<close>-interval.\<close> No endpoint hypothesis appears, because the
  shrinking construction needs none (\<open>Power_Sub_Loop\<close>).\<close>

theorem backmap_search_proper:
  fixes P Q :: "real poly" and a b :: real
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and a0: "0 \<le> a" and ab: "a < b"
    and core: "roots_in Q a b = 1"
  shows "find_least_impl (\<lambda>m. dsc_pair_ok P (pow_sub_hi h m a, pow_sub_lo h m b))
           \<le> SPEC (\<lambda>m. dsc_pair_ok P (pow_sub_hi h m a, pow_sub_lo h m b))"
proof -
  from pow_sub_shrink_exists[OF h Pdef sf a0 ab core]
  have ex: "\<exists>m. dsc_pair_ok P (pow_sub_hi h m a, pow_sub_lo h m b)" by blast
  show ?thesis by (rule find_least_impl_correct[OF ex])
qed

text \<open>\<^bold>\<open>Instantiation 2 — a degenerate \<open>Q\<close>-pair\<close> (an exact \<open>Q\<close>-root). Same program, same
  emitted shape: the pair is \<open>(floor, ceiling)\<close>, which collapses to a degenerate \<open>P\<close>-pair exactly
  when the \<open>h\<close>-th root is representable.\<close>

theorem backmap_search_degenerate:
  fixes P Q :: "real poly" and a :: real
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and a0: "0 \<le> a" and root: "poly Q a = 0"
  shows "find_least_impl (\<lambda>m. dsc_pair_ok P (pow_sub_lo h m a, pow_sub_hi h m a))
           \<le> SPEC (\<lambda>m. dsc_pair_ok P (pow_sub_lo h m a, pow_sub_hi h m a))"
proof -
  from pow_sub_degenerate_exists[OF h Pdef sf a0 root]
  have ex: "\<exists>m. dsc_pair_ok P (pow_sub_lo h m a, pow_sub_hi h m a)" by blast
  show ?thesis by (rule find_least_impl_correct[OF ex])
qed

text \<open>\<^bold>\<open>What these two theorems do not say.\<close> They say the search returns a precision at which the
  emitted pair isolates; they do not bound that precision. Any bound would have to be computed from
  \<open>Q\<close>'s root separation, which is not demanded of callers.\<close>


section \<open>Down to GMP: the \<open>h\<close>-th power, built from \<open>mpz_mul\<close>\<close>

text \<open>There is no \<open>mpz_pow\<close> binding, and none is added, so \<open>n\<^sup>h\<close> is \<open>h\<close> multiplications.

  \<^bold>\<open>Ownership\<close>: \<open>mpz_mul.amop_r1\<close> is destructive in its first argument and keeps the second, which
  is the accumulator shape: \<open>acc\<close> is owned and rewritten, \<open>x\<close> is borrowed and survives all \<open>h\<close>
  iterations, as in \<open>poly_scale_body_mop_monadic\<close>'s \<open>acc \<leftarrow> mpz_mul.amop_r1 acc c\<close>.\<close>

definition mpz_pow_nat_monadic :: "int \<Rightarrow> nat \<Rightarrow> int nres" where
  "mpz_pow_nat_monadic x e \<equiv> do {
     ASSERT (0 < e \<and> e < max_snat LENGTH(gmp_poly_len));
     (acc, _) \<leftarrow> WHILEIT (\<lambda>(acc, i). 1 \<le> i \<and> i \<le> e \<and> acc = x ^ i)
        (\<lambda>(acc, i). i < e)
        (\<lambda>(acc, i). do {
            acc \<leftarrow> (PR_CONST mpz_mul.amop_r1) acc x;
            ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
            RETURN (acc, i + 1)
         })
        (COPY x, 1);
     RETURN acc
   }"
  \<comment> \<open>\<^bold>\<open>Starts at a COPY of \<open>x\<close>, not at the constant 1\<close>: the only mpz constant the framework
     introduces is @{const op_mpz_new} (zero), so a \<open>1\<close> would cost a fresh allocation plus an
     \<open>mpz_add_ui\<close>. \<open>0 < e\<close> holds at every call site (it is \<open>h\<close>, and every theorem in this track
     assumes \<open>0 < h\<close>).\<close>

lemma mpz_pow_nat_monadic_correct:
  assumes e: "0 < e" and eb: "e < max_snat LENGTH(gmp_poly_len)"
  shows "mpz_pow_nat_monadic x e \<le> RETURN (x ^ e)"
  unfolding mpz_pow_nat_monadic_def mpz_mul.amop_r1_def mpz_mul.aop_r1_def PR_CONST_def
    COPY_def
  apply (refine_vcg WHILEIT_rule[where R = "measure (\<lambda>(acc, i). e - i)"])
  subgoal using e .
  subgoal using eb .
  subgoal by simp
  subgoal by simp
  subgoal using e by simp
  subgoal by auto
  subgoal by simp
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done



text \<open>\<^bold>\<open>Sepref.\<close> Two registrations, never one — a missing \<open>sepref_register\<close> surfaces as
  "Failed to apply initial proof method". Shape copied
  from \<open>mpz_shift_left_snat_monadic\<close>: the operand is KEPT (\<open>\<^sup>k\<close>) because the loop reads it
  \<open>e\<close> times, and the result is a fresh owned handle.\<close>

sepref_register "PR_CONST mpz_pow_nat_monadic" :: "int \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition mpz_pow_nat_impl [llvm_code] is
  "uncurry mpz_pow_nat_monadic" ::
  "[\<lambda>(_, e). 0 < e \<and> e < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  unfolding mpz_pow_nat_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_snat_const "TYPE(gmp_poly_len)")
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

lemma mpz_pow_nat_impl_hnr[sepref_fr_rules]:
  "(uncurry mpz_pow_nat_impl, uncurry (PR_CONST mpz_pow_nat_monadic)) \<in>
    [\<lambda>(_, e). 0 < e \<and> e < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  using mpz_pow_nat_impl.refine
  by (simp add: PR_CONST_def)

section \<open>The test, as GMP operations\<close>

text \<open>\<^bold>\<open>The right-hand side is computed ONCE and kept borrowed for the whole search.\<close> That is
  forced by ownership, not by taste: \<open>mpz_shift_left_snat_monadic\<close> is destructive in its operand
  (\<open>mpzb_assn\<^sup>d\<close>), so shifting \<open>A\<close> inside the loop would consume the caller's coefficient. The
  comparison is a subtraction plus @{const mpz_sgn_mop} — the tree has no \<open>mpz_cmp\<close> monadic op,
  and \<open>mpz_sub.amop_r1\<close> is destructive in the first argument and KEEPS the second, which is
  exactly the borrowed-rhs shape (\<open>Carried_Kernel.carried_init_inplace_monadic\<close> uses the same
  pair).\<close>

definition root_test_monadic :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool nres" where
  "root_test_monadic h k rhs n \<equiv> do {
     ASSERT (0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len));
     p \<leftarrow> (PR_CONST mpz_pow_nat_monadic) n h;
     l \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) p k;
     d \<leftarrow> (PR_CONST mpz_sub.amop_r1) l rhs;
     sg \<leftarrow> (PR_CONST mpz_sgn_mop) d;
     (PR_CONST mpzb_discard_monadic) d;
     RETURN (sg \<le> 0)
   }"

lemma root_test_monadic_correct:
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
  shows "root_test_monadic h k rhs n \<le> RETURN (n ^ h * 2 ^ k \<le> rhs)"
  unfolding root_test_monadic_def PR_CONST_def mpz_sgn_mop_def
    mpz_sub.amop_r1_def mpz_sub.aop_r1_def mpzb_discard_monadic_def
  using h hb k
  apply (refine_vcg
         mpz_pow_nat_monadic_correct[OF h hb, THEN order_trans]
         mpz_shift_left_snat_monadic_spec_plain[OF k, THEN order_trans])
  apply (auto simp: sgn_if)
  done
  \<comment> \<open>the comparison is \<open>sgn (l - rhs) \<le> 0\<close> because the tree has no monadic \<open>mpz_cmp\<close>; that is
     the same idiom \<open>Carried_Kernel\<close> uses\<close>



text \<open>\<^bold>\<open>Sepref for the test.\<close> \<open>rhs\<close> and \<open>n\<close> are both KEPT: the search calls this once per
  iteration with the same \<open>rhs\<close>, and \<open>n\<close> is a loop-state value the caller still owns. The only
  owned intermediates are the power, the shift and the difference, and the difference is
  discarded explicitly (@{const mpzb_discard_monadic}).\<close>

sepref_register "PR_CONST root_test_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool nres"

sepref_definition root_test_impl [llvm_code] is
  "uncurry3 root_test_monadic" ::
  "[\<lambda>(((h, k), rhs), n). 0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
                          \<and> k < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding root_test_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma root_test_impl_hnr[sepref_fr_rules]:
  "(uncurry3 root_test_impl, uncurry3 (PR_CONST root_test_monadic)) \<in>
    [\<lambda>(((h, k), rhs), n). 0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
                          \<and> k < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> bool1_assn"
  using root_test_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Two small GMP ops the loop's arithmetic needs\<close>

text \<open>A registered op of its own rather than inline in the loop body: inline arithmetic in a
  heap-monadic body defeats Sepref's opt phase (as for \<open>scale_more_mop\<close>). One GMP call.

  \<^bold>\<open>There is no successor op.\<close> \<open>rhs + 1\<close> would be \<open>mpz_add_ui\<close>, whose second operand is a
  \<open>uint\<close>, and the framework folds constants only for \<open>sint\<close>/\<open>snat\<close>/\<open>unat\<close>, so a literal \<open>1\<close> there
  cannot be annotated. The search's upper bound is therefore \<open>2 \<cdot> rhs\<close> (\<open>mpz_mul_2exp\<close> by 1, whose
  operand is a \<open>unat\<close> bit count), with \<open>rhs = 0\<close> as its own branch (there the answer is \<open>0\<close>, built
  by @{const op_mpz_new}).\<close>

definition mpz_halve_monadic :: "int \<Rightarrow> int nres" where
  "mpz_halve_monadic x \<equiv> (PR_CONST mpz_fdiv_q_2exp.amop_r1) x 1"

lemma mpz_halve_monadic_spec_plain[refine_vcg]:
  "mpz_halve_monadic x \<le> RETURN (x div 2)"
  unfolding mpz_halve_monadic_def mpz_fdiv_q_2exp.amop_r1_def
    mpz_fdiv_q_2exp.aop_r1_def PR_CONST_def
  by refine_vcg (simp_all add: snd_notzero_def)

sepref_register "PR_CONST mpz_halve_monadic" :: "int \<Rightarrow> int nres"

sepref_definition mpz_halve_impl [llvm_inline] is
  "mpz_halve_monadic" :: "mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  unfolding mpz_halve_monadic_def
  apply (annot_unat_const "TYPE(gmp_bitcnt_len)")
  by sepref

lemma mpz_halve_impl_hnr[sepref_fr_rules]:
  "(mpz_halve_impl, PR_CONST mpz_halve_monadic) \<in> mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  using mpz_halve_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The loop condition is GMP arithmetic too\<close> (\<open>1 < hi - lo\<close> compares two mpz values), so it
  gets its own registered op, as for \<open>half_eval_cond\<close> and \<open>scale_more_mop\<close>.

  It is phrased as \<open>0 < (hi - lo) div 2\<close> rather than \<open>1 < hi - lo\<close> for the same constant-folding
  reason as above: comparing against an mpz \<open>1\<close> would need a literal the framework cannot annotate.
  Halving first turns the test into a comparison against zero, which is @{const mpz_sgn_mop}, and for
  \<open>lo \<le> hi\<close> the two are equivalent, since \<open>2 \<le> hi - lo \<longleftrightarrow> 1 \<le> (hi - lo) div 2\<close>.\<close>

definition gap_more_mop :: "int \<Rightarrow> int \<Rightarrow> bool nres" where
  "gap_more_mop lo hi \<equiv> do {
     d \<leftarrow> (PR_CONST mpz_sub.amop_r1) (COPY hi) lo;
     d2 \<leftarrow> (PR_CONST mpz_halve_monadic) d;
     sg \<leftarrow> (PR_CONST mpz_sgn_mop) d2;
     (PR_CONST mpzb_discard_monadic) d2;
     RETURN (0 < sg)
   }"

lemma gap_more_mop_correct:
  assumes le: "lo \<le> hi"
  shows "gap_more_mop lo hi \<le> RETURN (1 < hi - lo)"
  unfolding gap_more_mop_def PR_CONST_def COPY_def mpz_sgn_mop_def
    mpz_sub.amop_r1_def mpz_sub.aop_r1_def mpzb_discard_monadic_def
  apply (refine_vcg mpz_halve_monadic_spec_plain[THEN order_trans])
  apply (auto simp: sgn_if)
  done

sepref_register "PR_CONST gap_more_mop" :: "int \<Rightarrow> int \<Rightarrow> bool nres"

sepref_definition gap_more_impl [llvm_code] is
  "uncurry gap_more_mop" :: "mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding gap_more_mop_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma gap_more_impl_hnr[sepref_fr_rules]:
  "(uncurry gap_more_impl, uncurry (PR_CONST gap_more_mop)) \<in>
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using gap_more_impl.refine by (simp add: PR_CONST_def)

section \<open>The search with the GMP test plugged in\<close>

text \<open>The same loop and invariant, with the test as a monadic GMP call rather than a pure
  predicate, which is what the Sepref layer translates. The right-hand side \<open>A \<cdot> 2\<^sup>h\<^sup>m\<close> is computed
  once, before the loop, and passed borrowed to every test.

  \<^bold>\<open>Still abstract at this layer\<close>: the initial \<open>hi\<^sub>0 = rhs + 1\<close> and the midpoint \<open>(lo + hi) div 2\<close>
  (\<open>mpz_add\<close> then \<open>mpz_fdiv_q_2exp\<close> by 1). They are pure steps here because the refinement monad does
  not enforce ownership, so writing them as monadic calls would prove nothing the Sepref obligation
  does not re-prove.\<close>

definition root_floor_gmp :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int nres" where
  "root_floor_gmp h m A k \<equiv> do {
     ASSERT (0 < h \<and> 0 \<le> A \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> h * m < max_snat LENGTH(gmp_poly_len));
     rhs \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) (COPY A) (h * m);
     sg \<leftarrow> (PR_CONST mpz_sgn_mop) rhs;
     if sg = 0 then do {
       (PR_CONST mpzb_discard_monadic) rhs;
       RETURN op_mpz_new
     } else do {
       hi0 \<leftarrow> (PR_CONST mpz_double_shift_monadic) (COPY rhs);
       (lo, hi) \<leftarrow> WHILEIT
          (\<lambda>(lo, hi). 0 \<le> lo \<and> lo < hi
                      \<and> root_test h m A k lo \<and> \<not> root_test h m A k hi)
          (\<lambda>(lo, hi). 1 < hi - lo)
          (\<lambda>(lo, hi). do {
              t \<leftarrow> (PR_CONST mpz_add.amop_r1) (COPY lo) hi;
              mid \<leftarrow> (PR_CONST mpz_halve_monadic) t;
              b \<leftarrow> (PR_CONST root_test_monadic) h k rhs mid;
              if b then do {
                (PR_CONST mpzb_discard_monadic) lo;
                RETURN (mid, hi)
              } else do {
                (PR_CONST mpzb_discard_monadic) hi;
                RETURN (lo, mid)
              }
           })
          (op_mpz_new, hi0);
       (PR_CONST mpzb_discard_monadic) hi;
       (PR_CONST mpzb_discard_monadic) rhs;
       RETURN lo
     }
   }"
  \<comment> \<open>\<^bold>\<open>Every owned handle is accounted for.\<close> \<open>rhs\<close> is ours and lives across the whole
     search (borrowed by each test), so it is discarded on BOTH exits. In the body \<open>lo\<close> and
     \<open>hi\<close> are owned loop state, so the branch that replaces one discards the other — without
     that, Sepref's frame solver has an unconsumed \<open>mpzb_assn\<close> and the synthesis fails.
     \<open>COPY\<close> marks the reads that must NOT consume: \<open>A\<close> is the caller's coefficient, and \<open>lo\<close>
     survives its own midpoint computation because \<open>mpz_add\<close> is destructive in the first
     operand.\<close>

lemma rhs_nonneg: "0 \<le> A \<Longrightarrow> 0 \<le> A * 2 ^ (h * m)" for A :: int
  by (simp add: zero_le_mult_iff)

lemma rhs_pos_of_sgn:
  fixes A :: int
  assumes A0: "0 \<le> A" and sg: "sgn (A * 2 ^ (h * m)) \<noteq> 0"
  shows "0 < A * 2 ^ (h * m)"
proof -
  have "0 \<le> A * 2 ^ (h * m)" using A0 by (simp add: zero_le_mult_iff)
  with sg show ?thesis by (auto simp: sgn_if split: if_splits)
qed

lemma root_test_succ_of_rhs_zero:
  assumes h: "0 < h" and z: "sgn (A * 2 ^ (h * m)) = 0"
  shows "\<not> root_test h m A k (0 + 1)"
proof -
  have "A * 2 ^ (h * m) = 0" using z by (simp add: sgn_eq_0_iff)
  moreover have "(0::int) < 1 ^ h * 2 ^ k" by simp
  ultimately show ?thesis unfolding root_test_def by simp
qed

lemma root_test_double_fails:
  fixes A :: int
  assumes h: "0 < h" and pos: "0 < A * 2 ^ (h * m)"
  shows "\<not> root_test h m A k (2 * (A * 2 ^ (h * m)))"
proof -
  define R where "R = A * 2 ^ (h * m)"
  have R1: "1 \<le> R" unfolding R_def using pos by simp
  define D where "D = 2 * R"
  have D1: "1 \<le> D" unfolding D_def using R1 by simp
  have "D \<le> D ^ h" using D1 h by (simp add: self_le_power)
  also have "D ^ h \<le> D ^ h * 2 ^ k" using D1 by simp
  finally have "D \<le> D ^ h * 2 ^ k" .
  moreover have "R < D" unfolding D_def using R1 by simp
  ultimately show ?thesis unfolding root_test_def R_def[symmetric] D_def[symmetric] by simp
qed

lemma root_test_eq_rhs:
  "root_test h m A k n \<longleftrightarrow> n ^ h * 2 ^ k \<le> A * 2 ^ (h * m)"
  by (simp add: root_test_def)

lemma root_floor_gmp_correct:
  assumes h: "0 < h" and A0: "0 \<le> A"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and hm: "h * m < max_snat LENGTH(gmp_poly_len)"
  shows "root_floor_gmp h m A k \<le> root_floor_spec h m A k"
  unfolding root_floor_gmp_def root_floor_spec_def COPY_def PR_CONST_def
    mpz_sgn_mop_def mpzb_discard_monadic_def op_mpz_new_def
    mpz_add.amop_r1_def mpz_add.aop_r1_def
  apply (refine_vcg
         mpz_shift_left_snat_monadic_spec_plain[THEN order_trans]
         mpz_double_shift_monadic_spec_plain[THEN order_trans]
         mpz_halve_monadic_spec_plain[THEN order_trans]
         WHILEIT_rule[where R = "measure (\<lambda>(lo, hi). nat (hi - lo))"]
         root_test_monadic_correct[OF h hb k, THEN order_trans])
  subgoal using h .
  subgoal using A0 .
  subgoal using hb .
  subgoal using k .
  subgoal using hm .
  subgoal using hm by simp
  subgoal by simp
  subgoal using root_test_zero[OF h A0, where m = m and k = k] by simp
  subgoal using root_test_succ_of_rhs_zero[OF h, where A = A and m = m and k = k] by simp
  subgoal by simp
  subgoal by simp
  subgoal using rhs_pos_of_sgn[OF A0, where h = h and m = m] by simp
  subgoal using root_test_zero[OF h A0, where m = m and k = k] by simp
  subgoal using root_test_double_fails[OF h, where A = A and m = m and k = k]
                rhs_pos_of_sgn[OF A0, where h = h and m = m] by simp
  subgoal by simp
  subgoal by (auto simp: mid_lower root_test_def)
  subgoal by (auto simp: mid_upper root_test_def)
  subgoal by (auto simp: root_test_def)
  subgoal by (auto simp: root_test_def)
  subgoal by (auto simp: mid_lower mid_upper root_test_def)
  subgoal by (auto simp: mid_lower root_test_def)
  subgoal by (auto simp: root_test_def)
  subgoal by (auto simp: root_test_def)
  subgoal by (auto simp: root_test_def)
  subgoal by (auto simp: mid_lower mid_upper root_test_def)
  subgoal by auto
  subgoal by auto
  subgoal for s lo hi using post_gap_one[where lo = lo and hi = hi] by auto
  done


section \<open>The Sepref-facing variant: a MONADIC loop condition\<close>

text \<open>\<^bold>\<open>Why a second program.\<close> @{const WHILEIT}'s condition is a pure term, and here that term
  (\<open>1 < hi - lo\<close>) is GMP arithmetic — Sepref cannot translate it inline. The framework's answer
  is @{const monadic_WHILEIT}, whose condition is itself an \<open>nres\<close> (the shape the sorting
  examples use, \<open>Sorting_Insertion_Sort\<close>). The correctness proof is NOT redone: the pure-condition
  loop is already proved total, and \<open>monadic_WHILEIT_refine_WHILEIT\<close> transports it, with the
  condition obligation discharged by \<open>gap_more_mop_correct\<close> — whose \<open>lo \<le> hi\<close> side condition is
  exactly what the loop invariant carries.\<close>

definition root_floor_gmp2 :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int nres" where
  "root_floor_gmp2 h m A k \<equiv> do {
     ASSERT (0 < h \<and> 0 \<le> A \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> h * m < max_snat LENGTH(gmp_poly_len));
     rhs \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) (COPY A) (h * m);
     sg \<leftarrow> (PR_CONST mpz_sgn_mop) rhs;
     if sg = 0 then do {
       (PR_CONST mpzb_discard_monadic) rhs;
       RETURN op_mpz_new
     } else do {
       hi0 \<leftarrow> (PR_CONST mpz_double_shift_monadic) (COPY rhs);
       (lo, hi) \<leftarrow> monadic_WHILEIT
          (\<lambda>(lo, hi). 0 \<le> lo \<and> lo < hi
                      \<and> root_test h m A k lo \<and> \<not> root_test h m A k hi)
          (\<lambda>(lo, hi). (PR_CONST gap_more_mop) lo hi)
          (\<lambda>(lo, hi). do {
              t \<leftarrow> (PR_CONST mpz_add.amop_r1) (COPY lo) hi;
              mid \<leftarrow> (PR_CONST mpz_halve_monadic) t;
              b \<leftarrow> (PR_CONST root_test_monadic) h k rhs mid;
              if b then do {
                (PR_CONST mpzb_discard_monadic) lo;
                RETURN (mid, hi)
              } else do {
                (PR_CONST mpzb_discard_monadic) hi;
                RETURN (lo, mid)
              }
           })
          (op_mpz_new, hi0);
       (PR_CONST mpzb_discard_monadic) hi;
       (PR_CONST mpzb_discard_monadic) rhs;
       RETURN lo
     }
   }"

lemma root_floor_gmp2_refine_Id:
  "root_floor_gmp2 h m A k \<le> \<Down>Id (root_floor_gmp h m A k)"
  unfolding root_floor_gmp2_def root_floor_gmp_def PR_CONST_def
  apply refine_rcg
  apply refine_dref_type
  apply (all \<open>(rule order_trans[OF gap_more_mop_correct])?\<close>)
  apply (auto simp: less_imp_le)
  done



text \<open>\<^bold>\<open>The synthesised search.\<close> \<open>A\<close> is KEPT — it is the caller's coefficient and the entry must
  not consume it — and everything the search allocates (the shifted right-hand side, the two
  endpoints, every midpoint) is discarded on both exits.\<close>

sepref_register "PR_CONST root_floor_gmp2" :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition root_floor_gmp_impl [llvm_code] is
  "uncurry3 root_floor_gmp2" ::
  "[\<lambda>(((h, m), A), k). 0 < h \<and> 0 \<le> A \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  unfolding root_floor_gmp2_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma root_floor_gmp_impl_hnr[sepref_fr_rules]:
  "(uncurry3 root_floor_gmp_impl, uncurry3 (PR_CONST root_floor_gmp2)) \<in>
    [\<lambda>(((h, m), A), k). 0 < h \<and> 0 \<le> A \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  using root_floor_gmp_impl.refine
  by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The chain, end to end.\<close> The synthesised LLVM search returns the numerator of
  @{const pow_sub_lo} — i.e. the spec-layer back-map endpoint — for any dyadic \<open>a = A / 2\<^sup>k\<close>.\<close>

corollary root_floor_gmp2_is_pow_sub_lo:
  fixes A :: int
  assumes h: "0 < h" and A0: "0 \<le> A"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and hm: "h * m < max_snat LENGTH(gmp_poly_len)"
    and adef: "a = real_of_int A / 2 ^ k"
  shows "root_floor_gmp2 h m A k
           \<le> SPEC (\<lambda>n. pow_sub_lo h m a = real_of_int n / 2 ^ m)"
proof -
  have "root_floor_gmp2 h m A k \<le> root_floor_gmp h m A k"
    using root_floor_gmp2_refine_Id[of h m A k] by simp
  also have "\<dots> \<le> root_floor_spec h m A k"
    by (rule root_floor_gmp_correct[OF h A0 hb k hm])
  also have "\<dots> \<le> SPEC (\<lambda>n. pow_sub_lo h m a = real_of_int n / 2 ^ m)"
    by (rule root_floor_spec_is_pow_sub_lo[OF h A0 adef])
  finally show ?thesis .
qed


end
