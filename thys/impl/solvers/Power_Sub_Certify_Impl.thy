theory Power_Sub_Certify_Impl
  imports Power_Sub_Emit_Impl "IsaRRI_LLVM.Interval_Eval"
begin

text \<open>Certification: the emitted window's acceptance test (op \<open>pow_sub_certify_monadic\<close>).

  The shrinking loop tests the window itself for \<open>roots_in Q = 1\<close>, with no endpoint hypothesis.

  \<^bold>\<open>The window is taken in \<open>Q\<close>-space.\<close> \<open>pow_sub_roots_in_eq\<close> gives
  \<open>roots_in P u v = roots_in Q (u\<^sup>h) (v\<^sup>h)\<close>, so with \<open>lo = L / 2\<^sup>m\<close> and \<open>hi = R / 2\<^sup>m\<close> the test interval
  is \<open>(L\<^sup>h / 2\<^sup>h\<^sup>\<cdot>\<^sup>m, R\<^sup>h / 2\<^sup>h\<^sup>\<cdot>\<^sup>m)\<close>: exact integers over a shared power of two, so there is no rounding.

  \<^bold>\<open>Which count op.\<close> @{const descartes_transform_monadic}, whose four endpoint arguments are
  \<open>mpzb_assn\<close>; not \<open>fast_descartes_interval\<close>, whose endpoints are \<open>gmp_slong_assn\<close> machine words, which
  \<open>L\<^sup>h\<close> need not fit.\<close>

section \<open>The count-is-one bridge\<close>

text \<open>\<^bold>\<open>Descartes' rule, assembled from the four facts that already exist.\<close> The count is an
  upper bound congruent mod 2 to the true root count, so \<open>= 1\<close> pins it exactly. This lemma is
  the reason certify can live in THIS session: it needs @{const descartes_preprocess} (shared
  base, \<open>Fast_Descartes\<close>) and \<open>Bernstein_changes\<close> (\<open>Dsc_Misc\<close>, spec) at the same time, and
  only the impl session sees both.\<close>

lemma descartes_preprocess_one_root:
  fixes P0 :: "int poly" and na da nb db :: int
  assumes len: "0 < length (coeffs P0)"
    and da: "0 < da" and db: "0 < db"
    and lt: "na * db < nb * da"
    and one: "descartes_preprocess na da nb db (coeffs P0) = 1"
  shows "roots_in (map_poly of_int P0 :: real poly)
           (real_of_int na / real_of_int da) (real_of_int nb / real_of_int db) = 1"
proof -
  define a where "a = rat_of_int na / rat_of_int da"
  define b where "b = rat_of_int nb / rat_of_int db"
  have P0nz: "P0 \<noteq> 0" using len by auto
  have ab: "a < b"
  proof -
    have "rat_of_int na * rat_of_int db < rat_of_int nb * rat_of_int da"
      using lt by (metis of_int_less_iff of_int_mult)
    moreover have "(0::rat) < rat_of_int da" using da by simp
    moreover have "(0::rat) < rat_of_int db" using db by simp
    ultimately show ?thesis
      unfolding a_def b_def by (simp add: field_simps)
  qed
  \<comment> \<open>impl count \<open>\<rightarrow>\<close> the abstract list count\<close>
  have step1: "descartes_list_int a b (coeffs P0) = 1"
    using descartes_preprocess_eq_fast[OF len da db lt] one
    unfolding a_def b_def by simp
  \<comment> \<open>list count \<open>\<rightarrow>\<close> the real-poly sign-variation count\<close>
  have step2: "descartes_roots_test_sc (of_rat a) (of_rat b)
                 (map_poly of_int P0 :: real poly) = 1"
    using descartes_roots_test_sc_of_int[OF ab P0nz] step1 by simp
  \<comment> \<open>sign-variation count \<open>\<rightarrow>\<close> Bernstein changes\<close>
  have step3: "Bernstein_changes (degree (map_poly of_int P0 :: real poly))
                 (of_rat a) (of_rat b) (map_poly of_int P0 :: real poly) = 1"
    using descartes_roots_test_sc_eq_Bernstein_changes
            [of "of_rat a" "of_rat b" "map_poly of_int P0 :: real poly"] step2
    by simp
  \<comment> \<open>Bernstein changes \<open>\<rightarrow>\<close> the root count\<close>
  have Pnz: "(map_poly of_int P0 :: real poly) \<noteq> 0" using P0nz by simp
  have abr: "(of_rat a :: real) < of_rat b" using ab by (simp add: of_rat_less)
  have "roots_in (map_poly of_int P0 :: real poly) (of_rat a) (of_rat b) = 1"
    by (rule Bernstein_changes_1_one_root[OF order_refl Pnz abr step3])
  moreover have "(of_rat a :: real) = real_of_int na / real_of_int da"
    unfolding a_def by (simp add: of_rat_divide)
  moreover have "(of_rat b :: real) = real_of_int nb / real_of_int db"
    unfolding b_def by (simp add: of_rat_divide)
  ultimately show ?thesis by simp
qed

section \<open>The op\<close>

text \<open>\<^bold>\<open>Ownership.\<close> \<open>L\<close>, \<open>R\<close> and the reduced polynomial \<open>xs\<close> are all KEPT — the caller re-emits
  them at a higher precision when this test rejects. Everything the op allocates (the two
  powers, the two shared denominators, the three width intermediates) is discarded on the one
  exit. @{const descartes_transform_monadic} KEEPS all four of its endpoint arguments, which is
  why they are discarded here rather than by it.\<close>

definition pow_sub_certify_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
  "pow_sub_certify_monadic h m L R xs \<equiv> doN {
     ASSERT (0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> h * m < max_snat LENGTH(gmp_poly_len)
             \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
     na \<leftarrow> (PR_CONST mpz_pow_nat_monadic) L h;
     nb \<leftarrow> (PR_CONST mpz_pow_nat_monadic) R h;
     one_a \<leftarrow> RETURN (mpz_from_int 1);
     da \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) one_a (h * m);
     one_b \<leftarrow> RETURN (mpz_from_int 1);
     db \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) one_b (h * m);
     t1 \<leftarrow> (PR_CONST mpz_mul.amop_r1) (COPY nb) da;
     t2 \<leftarrow> (PR_CONST mpz_mul.amop_r1) (COPY na) db;
     nw \<leftarrow> (PR_CONST mpz_sub.amop_r1) t1 t2;
     (PR_CONST mpzb_discard_monadic) t2;
     w \<leftarrow> (PR_CONST mpz_sgn_mop) nw;
     cnt \<leftarrow> (PR_CONST descartes_transform_monadic) na da nw db xs;
     (PR_CONST mpzb_discard_monadic) na;
     (PR_CONST mpzb_discard_monadic) nb;
     (PR_CONST mpzb_discard_monadic) da;
     (PR_CONST mpzb_discard_monadic) db;
     (PR_CONST mpzb_discard_monadic) nw;
     RETURN (cnt = 1 \<and> 0 < w)
   }"

lemma pow_sub_certify_monadic_correct:
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and hm: "h * m < max_snat LENGTH(gmp_poly_len)"
    and len: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_certify_monadic h m L R xs
           \<le> RETURN (descartes_preprocess (L ^ h) (2 ^ (h * m))
                       (R ^ h) (2 ^ (h * m)) xs = 1
                     \<and> L ^ h < R ^ h)"
  unfolding pow_sub_certify_monadic_def PR_CONST_def descartes_preprocess_def
    mpzb_discard_monadic_def mpz_from_int_def mpz_sgn_mop_def
    mpz_mul.amop_r1_def mpz_mul.aop_r1_def
    mpz_sub.amop_r1_def mpz_sub.aop_r1_def COPY_def
  using h hb hm len
  apply (refine_vcg
         mpz_pow_nat_monadic_correct[OF h hb, THEN order_trans]
         mpz_shift_left_snat_monadic_spec_plain[OF hm, THEN order_trans]
         descartes_transform_monadic_correct[THEN order_trans])
  \<comment> \<open>\<open>sgn_greater\<close> turns the op's \<open>0 < sgn (R\<^sup>h\<cdot>2\<^sup>h\<^sup>\<cdot>\<^sup>m - L\<^sup>h\<cdot>2\<^sup>h\<^sup>\<cdot>\<^sup>m)\<close> into the spec's \<open>L\<^sup>h < R\<^sup>h\<close>;
     the \<open>2\<^sup>h\<^sup>\<cdot>\<^sup>m\<close> factor cancels because it is positive\<close>
  apply (all \<open>(simp add: top_fun_def algebra_simps sgn_greater; fail)
              | simp add: top_fun_def sgn_greater\<close>)
  done

section \<open>What the test certifies\<close>

text \<open>\<^bold>\<open>Certify \<open>\<Longrightarrow>\<close> the \<open>Q\<close>-window isolates.\<close> The \<open>P\<close>-side statement (and hence
  @{const dsc_pair_ok}) follows by \<open>pow_sub_roots_in_eq\<close>; it is stated separately because it needs
  \<open>P = Q \<circ>\<^sub>p monom 1 h\<close> in scope, which the op does not have.\<close>

lemma pow_sub_certify_isolates:
  fixes Q0 :: "int poly" and L R :: int
  assumes len: "0 < length (coeffs Q0)"
    and hm: "0 < (2::int) ^ (h * m)"
    and lt: "L ^ h * 2 ^ (h * m) < R ^ h * 2 ^ (h * m)"
    and one: "descartes_preprocess (L ^ h) (2 ^ (h * m))
                (R ^ h) (2 ^ (h * m)) (coeffs Q0) = 1"
  shows "roots_in (map_poly of_int Q0 :: real poly)
           (real_of_int (L ^ h) / 2 ^ (h * m))
           (real_of_int (R ^ h) / 2 ^ (h * m)) = 1"
  using descartes_preprocess_one_root[OF len hm hm lt one] by simp

section \<open>Sepref\<close>

sepref_register "PR_CONST pow_sub_certify_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

sepref_definition pow_sub_certify_impl [llvm_code] is
  "uncurry4 pow_sub_certify_monadic" ::
  "[\<lambda>((((h, m), L), R), xs). 0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding pow_sub_certify_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_sint_const gmp_int_t)
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow_sub_certify_impl_hnr[sepref_fr_rules]:
  "(uncurry4 pow_sub_certify_impl, uncurry4 (PR_CONST pow_sub_certify_monadic)) \<in>
    [\<lambda>((((h, m), L), R), xs). 0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using pow_sub_certify_impl.refine
  by (simp add: PR_CONST_def)


section \<open>The SIGN certificate — what the PROPER branch uses instead of the count\<close>

text \<open>\<^bold>\<open>A cheaper certificate on the proper branch.\<close> The count above costs one
  \<open>descartes_transform\<close> of the whole reduced polynomial per emitted interval: \<open>O(n\<^sup>2)\<close> coefficient
  operations per interval, and \<open>O(n)\<close> intervals, so cubic overall, whereas the solver's own per-node
  count works on the carried, truncated node polynomial.

  \<^bold>\<open>The cheaper certificate is not weaker.\<close> The shrunk window is a subinterval of the \<open>Q\<close>-interval
  the reduced solve emitted, and that interval carries exactly one root. So
  \<^item> \<^bold>\<open>at most one\<close> is free: @{thm [source] Dsc_Misc.proots_count_mono} on the subset;
  \<^item> \<^bold>\<open>at least one\<close> is a sign change at the two endpoints: @{thm [source] Polynomial.poly_IVT}.
  Two homogeneous Horner evaluations, \<open>O(n)\<close> coefficient operations, replace an \<open>O(n\<^sup>2)\<close> transform.

  \<^bold>\<open>It also removes a gap.\<close> The Descartes count is an upper bound congruent mod 2, so \<open>count = 1\<close> is
  strictly stronger than \<open>roots_in = 1\<close>. A sign change within an interval known to hold one root is
  equivalent to bracketing that root, so the test succeeds exactly when the shrunk window still holds
  it, which the shrink's convergence delivers.

  \<^bold>\<open>The degenerate branch keeps the count.\<close> Its window widens around an exact \<open>Q\<close>-root, so it is not
  contained in any interval known to hold one root; "at most one" is not free there, and a sign
  change would only give an odd number.

  The Horner loop, its invariant \<open>acc / d\<^sup>i = poly Q (n/d)\<close> and the step lemmas are those of
  @{theory IsaRRI_LLVM.Interval_Eval} (@{const poly_hom_eval_zero_mpz_monadic} is the same loop with a
  zero test on the accumulator). Only the finish differs: it returns \<open>mpz_sgn acc\<close> rather than
  \<open>mpz_sgn acc = 0\<close>.\<close>

subsection \<open>The Horner loop, SPECIALISED to a power-of-two denominator\<close>

text \<open>\<^bold>\<open>Why not reuse @{const poly_hom_eval_zero_mpz_monadic}'s loop unchanged.\<close> It is general in the
  denominator \<open>d\<close>, so it carries \<open>dpow = d\<^sup>i\<^sup>+\<^sup>1\<close> as an \<open>mpz\<close> and computes \<open>acc += c\<^sub>i \<cdot> dpow\<close>. Every window
  here has \<open>d = 2\<^sup>h\<^sup>\<cdot>\<^sup>m\<close>, so \<open>dpow\<close> is a power of two and that multiplication is a shift that GMP does not
  detect; this loop shifts instead.

  \<^bold>\<open>What the specialisation costs.\<close> The invariant, the step lemma and the initialisation are
  @{theory IsaRRI_LLVM.Interval_Eval}'s, reused at \<open>d = 2\<^sup>e\<close>: @{thm [source] poly_hom_eval_inv_step} is
  stated for a general \<open>d\<close>, and \<open>(2\<^sup>e)\<^sup>i\<^sup>+\<^sup>1 = 2\<^sup>e\<^sup>\<cdot>\<^sup>(\<^sup>i\<^sup>+\<^sup>1\<^sup>)\<close> is @{thm power_mult}. The cost is a machine-word
  bound: the shift amount is an \<open>snat\<close>, so \<open>e \<cdot> length xs < max_snat\<close> has to be carried, where the
  multiplying form needed none because \<open>dpow\<close> is an \<open>mpz\<close>. That bound appears only in
  correctness-lemma hypotheses: the shift's precondition mentions the loop state, so it is an internal
  \<open>ASSERT\<close>, and @{thm hn_ASSERT_bind} hands it to the enclosing refinement proof rather than to an HNR
  precondition.

  \<^bold>\<open>The coefficient is copied rather than read through a focused pointer.\<close> Four existing ops
  compose: copy the coefficient, shift it, add, discard. The copy is \<open>b\<close> bits against the shift's
  \<open>b + s\<close>.\<close>

abbreviation pow_sub_shift_state_assn where
  "pow_sub_shift_state_assn \<equiv>
     snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a mpzb_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"

text \<open>The state is \<open>(i, acc, s)\<close> with \<open>s\<close> the CURRENT shift amount, \<open>e \<cdot> (i+1)\<close>, carried as a
  machine word and stepped by \<open>+ e\<close> — never recomputed as a product, so no snat multiplication
  reaches the loop body.\<close>

definition pow_sub_shift_cond :: "nat \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> bool" where
  "pow_sub_shift_cond bd st \<longleftrightarrow> (let (i, acc, s) = st in i < bd)"

sepref_register "PR_CONST pow_sub_shift_cond" :: "nat \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> bool"

sepref_definition pow_sub_shift_cond_impl [llvm_inline] is
  "uncurry (RETURN oo pow_sub_shift_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_shift_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_shift_cond_def Let_def
  by sepref

lemma pow_sub_shift_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_shift_cond_impl,
    uncurry (RETURN oo (PR_CONST pow_sub_shift_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_shift_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_shift_cond_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>Ownership.\<close> \<open>acc\<close> is owned loop state and is consumed by both arithmetic steps;
  \<open>c\<close> is a fresh copy, consumed by the shift; \<open>t\<close> is the shift's owned result and is discarded
  after the add. \<open>xs\<close> and \<open>gn\<close> are KEPT.\<close>

definition pow_sub_shift_body_mop ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> (nat \<times> int \<times> nat) nres" where
  "pow_sub_shift_body_mop xs bd n e st \<equiv> doN {
     let (i, acc, s) = st;
     ASSERT (bd + 1 = length xs);
     ASSERT (i < bd);
     ASSERT (bd - (i + 1) < length xs);
     ASSERT (s < max_snat LENGTH(gmp_poly_len));
     ASSERT (s + e < max_snat LENGTH(gmp_poly_len));
     ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
     acc \<leftarrow> (PR_CONST mpz_mul.amop_r1) acc n;
     c \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs (bd - (i + 1));
     t \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) c s;
     acc \<leftarrow> (PR_CONST mpz_add.amop_r1) acc t;
     (PR_CONST mpzb_discard_monadic) t;
     RETURN (i + 1, acc, s + e)
   }"

sepref_register "PR_CONST pow_sub_shift_body_mop"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> (nat \<times> int \<times> nat) nres"

text \<open>The invariant is @{const poly_hom_eval_inv} at \<open>d = 2\<^sup>e\<close>, with the \<open>dpow\<close> component
  supplied as \<open>2\<^sup>s\<close> — so the step lemma applies unchanged and nothing about the Horner
  recurrence is re-proved here.\<close>

definition pow_sub_shift_inv ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> bool" where
  "pow_sub_shift_inv xs bd n e st \<equiv>
     (let (i, acc, s) = st in
        s = e * Suc i \<and>
        poly_hom_eval_inv xs bd n (2 ^ e) (i, acc, (2 ^ e) ^ Suc i))"

text \<open>\<^bold>\<open>Stated on an UNDESTRUCTURED state\<close>, exactly as
  @{thm [source] poly_hom_eval_body_mop_monadic_spec_decrease} is — the call site inside
  \<open>WHILET_rule\<close> hands over a bare \<open>st\<close>, and a lemma phrased on \<open>(i, acc, s)\<close> simply does not
  apply there. The three machine-word bounds are DERIVED here from the single product
  hypothesis rather than demanded of the caller.\<close>

lemma pow_sub_shift_body_step_s:
  assumes i_lt: "i < bd"
    and len: "bd + 1 = length xs"
    and inv: "rat_of_int acc / rat_of_int ((2 ^ e) ^ i) =
      poly (map_poly rat_of_int (Poly (drop (bd - i) xs)))
        (rat_of_int n / rat_of_int (2 ^ e))"
  shows "(rat_of_int acc * rat_of_int n +
            rat_of_int (xs ! (bd - Suc i)) * (2::rat) ^ (e + e * i)) /
         ((2 ^ e) * (2 ^ e) ^ i) =
      poly (map_poly rat_of_int (Poly (drop (bd - Suc i) xs)))
        (rat_of_int n / rat_of_int (2 ^ e))"
proof -
  have d0: "(2::int) ^ e \<noteq> 0" by simp
  have step0: "rat_of_int (acc * n + xs ! (bd - Suc i) * ((2::int) ^ e) ^ Suc i) /
        rat_of_int (((2::int) ^ e) ^ Suc i) =
      poly (map_poly rat_of_int (Poly (drop (bd - Suc i) xs)))
        (rat_of_int n / rat_of_int (2 ^ e))"
    by (rule poly_hom_eval_inv_step[OF d0 i_lt len inv])
  have num_s: "rat_of_int acc * rat_of_int n +
        rat_of_int (xs ! (bd - Suc i)) * (2::rat) ^ (e + e * i) =
      rat_of_int (acc * n + xs ! (bd - Suc i) * ((2::int) ^ e) ^ Suc i)"
  proof -
    have a1: "rat_of_int (acc * n + xs ! (bd - Suc i) * ((2::int) ^ e) ^ Suc i) =
        rat_of_int acc * rat_of_int n +
          rat_of_int (xs ! (bd - Suc i)) * rat_of_int (((2::int) ^ e) ^ Suc i)"
      by (simp add: of_int_add of_int_mult)
    have a2: "rat_of_int (((2::int) ^ e) ^ Suc i) = (2::rat) ^ (e + e * i)"
    proof -
      have "rat_of_int (((2::int) ^ e) ^ Suc i) = ((2::rat) ^ e) ^ Suc i"
        by (simp add: of_int_power)
      also have "((2::rat) ^ e) ^ Suc i = 2 ^ (e * Suc i)"
        by (metis power_mult)
      also have "2 ^ (e * Suc i) = 2 ^ (e + e * i)"
        by (simp add: mult_Suc_right)
      finally show ?thesis .
    qed
    show ?thesis using a1 a2 by (simp add: mult_ac)
  qed
  have den_s: "(2::rat) ^ e * (2 ^ e) ^ i =
      rat_of_int (((2::int) ^ e) ^ Suc i)"
  proof -
    have "rat_of_int (((2::int) ^ e) ^ Suc i) = ((2::rat) ^ e) ^ Suc i"
      by (simp add: of_int_power)
    also have "((2::rat) ^ e) ^ Suc i = 2 ^ e * (2 ^ e) ^ i"
      by (simp add: power_Suc)
    finally show ?thesis by simp
  qed
  show ?thesis
    using step0 num_s den_s by metis
qed

lemma pow_sub_shift_body_correct:
  assumes inv: "pow_sub_shift_inv xs bd n e st"
    and cond: "pow_sub_shift_cond bd st"
    and eb: "e * length xs < max_snat LENGTH(gmp_poly_len)"
    and lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_shift_body_mop xs bd n e st
           \<le> SPEC (\<lambda>st'. pow_sub_shift_inv xs bd n e st'
                            \<and> (case (st, st') of ((i, _, _), (i', _, _)) \<Rightarrow>
                                 bd - i' < bd - i))"
  \<comment> \<open>the \<open><\<close> sits OUTSIDE both \<open>case\<close>s, which is the shape \<open>WHILET_rule\<close>'s measure goal
     carries. Nesting it inside leaves a set-inclusion that differs only in where the cases
     sit, and no \<open>prod.splits\<close> closer reconciles it cheaply\<close>
proof -
  obtain i acc s where st_eq: "st = (i, acc, s)" by (cases st) auto
  have cond': "i < bd" using cond st_eq unfolding pow_sub_shift_cond_def by simp
  have inv': "pow_sub_shift_inv xs bd n e (i, acc, s)" using inv st_eq by simp
  have both: "s = e * Suc i
      \<and> poly_hom_eval_inv xs bd n (2 ^ e) (i, acc, (2 ^ e) ^ Suc i)"
    using inv' unfolding pow_sub_shift_inv_def by (simp add: Let_def)
  have s_eq: "s = e * Suc i" using both by blast
  have hom: "poly_hom_eval_inv xs bd n (2 ^ e) (i, acc, (2 ^ e) ^ Suc i)"
    using both by blast
  have len: "bd + 1 = length xs"
    and acc_eq: "rat_of_int acc / rat_of_int ((2 ^ e) ^ i) =
      poly (map_poly rat_of_int (Poly (drop (bd - i) xs)))
        (rat_of_int n / rat_of_int (2 ^ e))"
    using hom unfolding poly_hom_eval_inv_def by (simp_all add: Let_def)
  have blen: "bd + 1 = length xs"
    using both unfolding poly_hom_eval_inv_def by (simp add: Let_def)
  \<comment> \<open>the specialisation's word bounds, all three from \<open>e \<cdot> length xs\<close> and \<open>i < bd\<close>\<close>
  have sb: "s < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "Suc i \<le> length xs" using cond' blen by simp
    then have "e * Suc i \<le> e * length xs" by (rule mult_le_mono2)
    then show ?thesis using eb s_eq by simp
  qed
  have sb2: "s + e < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "Suc (Suc i) \<le> length xs" using cond' blen by simp
    then have "e * Suc (Suc i) \<le> e * length xs" by (rule mult_le_mono2)
    then show ?thesis using eb s_eq by simp
  qed
  have i1: "i + 1 < max_snat LENGTH(gmp_poly_len)" using cond' blen lenb by simp
  have d0: "(2::int) ^ e \<noteq> 0" by simp
  \<comment> \<open>the one arithmetic fact the specialisation rests on: the shift IS the power\<close>
  have pow: "(2::int) ^ s = ((2::int) ^ e) ^ Suc i"
    using s_eq by (simp add: power_add power_mult)
  have step: "(rat_of_int acc * rat_of_int n +
              rat_of_int (xs ! (bd - Suc i)) * (2::rat) ^ (e + e * i)) /
             (2 ^ e * (2 ^ e) ^ i) =
      poly (map_poly rat_of_int (Poly (drop (bd - Suc i) xs)))
        (rat_of_int n / rat_of_int (2 ^ e))"
    by (rule pow_sub_shift_body_step_s[OF cond' len acc_eq])
  show ?thesis
    unfolding st_eq
    unfolding pow_sub_shift_body_mop_def pow_sub_shift_inv_def
      poly_hom_eval_inv_def PR_CONST_def mpzb_discard_monadic_def
      mpz_mul.amop_r1_def mpz_mul.aop_r1_def
      mpz_add.amop_r1_def mpz_add.aop_r1_def
      poly_copy_coeff_monadic_def
    using cond' len sb sb2 i1 hom s_eq
    apply (refine_vcg mpz_shift_left_snat_monadic_spec_plain[OF sb, THEN order_trans])
    apply (all \<open>(auto simp: Let_def poly_hom_eval_inv_def algebra_simps
                            power_add power_mult s_eq pow step; fail)?\<close>)
    subgoal
      apply (rule order_trans)
       apply (rule mpz_shift_left_snat_monadic_spec_plain)
        apply assumption
      apply (rule RETURN_rule)
      apply (auto simp: step split: prod.splits)
      by (metis half_1 llvm_num_const_simps(1) llvm_num_const_simps(45)
          llvm_num_const_simps(72) llvm_num_const_simps(95) local.step of_int_0
          of_int_1 of_int_eq_numeral_iff of_int_numeral of_int_power st_eq)
    done
qed

sepref_definition pow_sub_shift_body_impl [llvm_inline] is
  "uncurry4 pow_sub_shift_body_mop" ::
  "[\<lambda>((((xs, bd), _), _), _). bd + 1 = length xs]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_shift_state_assn\<^sup>d
      \<rightarrow> pow_sub_shift_state_assn"
  unfolding pow_sub_shift_body_mop_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
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

lemma pow_sub_shift_body_impl_hnr[sepref_fr_rules]:
  "(uncurry4 pow_sub_shift_body_impl, uncurry4 (PR_CONST pow_sub_shift_body_mop)) \<in>
    [\<lambda>((((xs, bd), _), _), _). bd + 1 = length xs]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_shift_state_assn\<^sup>d
      \<rightarrow> pow_sub_shift_state_assn"
  using pow_sub_shift_body_impl.refine by (simp add: PR_CONST_def)

subsection \<open>The finish: the accumulator's sign, not its zero-ness\<close>

text \<open>@{const poly_hom_eval_finish_monadic}'s body with \<open>ll_icmp_eq s 0\<close> dropped, and one owned
  argument instead of two — the specialised loop has no \<open>gd\<close> to free, because its denominator
  never became an \<open>mpz\<close>.\<close>

definition pow_sub_sign_finish_monadic ::
  "int \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> int nres" where
  "pow_sub_sign_finish_monadic gn st \<equiv> doN {
     let (i, acc, s) = st;
     r \<leftarrow> RETURN ((PR_CONST mpz_sgn) acc);
     (PR_CONST mpzb_discard_monadic) acc;
     (PR_CONST mpzb_discard_monadic) gn;
     RETURN r
   }"

sepref_register "PR_CONST pow_sub_sign_finish_monadic"
  :: "int \<Rightarrow> nat \<times> int \<times> nat \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]:
  "pow_sub_sign_finish_impl gn st \<equiv> doM {
    let (i, acc, s) = st;
    r \<leftarrow> mpzb_sgn_impl acc;
    mpzb_discard_impl acc;
    mpzb_discard_impl gn;
    Mreturn r
  }"

lemma pow_sub_sign_finish_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_sign_finish_impl,
    uncurry (PR_CONST pow_sub_sign_finish_monadic)) \<in>
    mpzb_assn\<^sup>d *\<^sub>a pow_sub_shift_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_sint_assn"
  unfolding pow_sub_sign_finish_impl_def
    pow_sub_sign_finish_monadic_def PR_CONST_def
    mpzb_discard_impl_def
  apply sepref_to_hoare
  apply (clarsimp simp: refine_pw_simps)
  apply vcg'
  apply (all \<open>(vcg')?\<close>)
  apply (auto simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps pure_def
    mpzb_discard_monadic_def sint_rel_def sint.rel_def br_def)
  done

text \<open>\<^bold>\<open>The sign of the accumulator is the sign of the value\<close>, because the invariant's denominator is
  a positive power of two. Stated as a classification trichotomy: three equivalences rather than an
  equation between an \<open>int\<close> sign and a \<open>rat\<close> sign, which would need a coercion at every use.\<close>

lemma pow_sub_sign_finish_monadic_spec:
  assumes inv0: "pow_sub_shift_inv xs bd n e st"
    and ncond0: "\<not> pow_sub_shift_cond bd st"
  shows "pow_sub_sign_finish_monadic gn st \<le>
    SPEC (\<lambda>r. (r < 0) = (poly (map_poly rat_of_int (Poly xs))
                            (rat_of_int n / rat_of_int (2 ^ e)) < 0)
            \<and> (r = 0) = (poly (map_poly rat_of_int (Poly xs))
                            (rat_of_int n / rat_of_int (2 ^ e)) = 0)
            \<and> (0 < r) = (0 < poly (map_poly rat_of_int (Poly xs))
                            (rat_of_int n / rat_of_int (2 ^ e))))"
proof -
  obtain i acc s where st_eq: "st = (i, acc, s)" by (cases st) auto
  have ncond: "\<not> i < bd"
    using ncond0 st_eq unfolding pow_sub_shift_cond_def by simp
  have both: "s = e * Suc i
      \<and> poly_hom_eval_inv xs bd n (2 ^ e) (i, acc, (2 ^ e) ^ Suc i)"
    using inv0 st_eq unfolding pow_sub_shift_inv_def by (simp add: Let_def)
  have hom: "poly_hom_eval_inv xs bd n (2 ^ e) (i, acc, (2 ^ e) ^ Suc i)"
    using both by blast
  have ile: "i \<le> bd"
    and acc_eq: "rat_of_int acc / rat_of_int (((2::int) ^ e) ^ i) =
      poly (map_poly rat_of_int (Poly (drop (bd - i) xs)))
        (rat_of_int n / rat_of_int (2 ^ e))"
    using hom unfolding poly_hom_eval_inv_def by (simp_all add: Let_def)
  have i_eq: "i = bd" using ile ncond by simp
  have den: "0 < rat_of_int (((2::int) ^ e) ^ bd)" by simp
  have acc_poly: "rat_of_int acc / rat_of_int (((2::int) ^ e) ^ bd) =
    poly (map_poly rat_of_int (Poly xs)) (rat_of_int n / rat_of_int (2 ^ e))"
    using acc_eq i_eq by simp
  have tri:
    "(sgn acc < 0) = (poly (map_poly rat_of_int (Poly xs))
                        (rat_of_int n / rat_of_int (2 ^ e)) < 0)
   \<and> (sgn acc = 0) = (poly (map_poly rat_of_int (Poly xs))
                        (rat_of_int n / rat_of_int (2 ^ e)) = 0)
   \<and> (0 < sgn acc) = (0 < poly (map_poly rat_of_int (Poly xs))
                        (rat_of_int n / rat_of_int (2 ^ e)))"
    using den unfolding acc_poly[symmetric]
    by (auto simp: sgn_if divide_less_0_iff zero_less_divide_iff)
  show ?thesis
    unfolding st_eq pow_sub_sign_finish_monadic_def
      mpzb_discard_monadic_def PR_CONST_def mpz_sgn_def
    using tri by (simp add: refine_pw_simps)
qed

subsection \<open>The evaluation: one Horner pass, returning a sign\<close>

text \<open>\<open>n\<close> and \<open>xs\<close> are KEPT — the certify calls this twice against the same polynomial, and the
  search calls it again at the next precision. \<open>e\<close> is the base-two exponent of the denominator,
  a machine word, so the denominator is never materialised at all.\<close>

definition pow_sub_eval_sign_monadic ::
  "int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> int nres" where
  "pow_sub_eval_sign_monadic n e xs \<equiv> doN {
     len \<leftarrow> (PR_CONST poly_length_monadic) xs;
     ASSERT (len = length xs);
     ASSERT (0 < len);
     ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
     ASSERT (e * len < max_snat LENGTH(gmp_poly_len));
     let bd = len - 1;
     gn \<leftarrow> RETURN (COPY n);
     acc \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs bd;
     st \<leftarrow> WHILET
        (\<lambda>st. (PR_CONST pow_sub_shift_cond) bd st)
        (\<lambda>st. (PR_CONST pow_sub_shift_body_mop) xs bd gn e st)
        (0, acc, e);
     (PR_CONST pow_sub_sign_finish_monadic) gn st
   }"

sepref_register "PR_CONST pow_sub_eval_sign_monadic"
  :: "int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> int nres"

text \<open>\<^bold>\<open>\<open>e \<cdot> length xs < max_snat\<close> is the specialisation's one extra hypothesis\<close>; it bounds every shift
  the loop performs: \<open>s = e \<cdot> (i+1) \<le> e \<cdot> length xs\<close>.\<close>

lemma pow_sub_eval_sign_monadic_spec:
  assumes len0: "0 < length xs"
    and bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and ebound: "e * length xs < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_eval_sign_monadic n e xs \<le>
    SPEC (\<lambda>r. (r < 0) = (poly (map_poly rat_of_int (Poly xs))
                            (rat_of_int n / rat_of_int (2 ^ e)) < 0)
            \<and> (r = 0) = (poly (map_poly rat_of_int (Poly xs))
                            (rat_of_int n / rat_of_int (2 ^ e)) = 0)
            \<and> (0 < r) = (0 < poly (map_poly rat_of_int (Poly xs))
                            (rat_of_int n / rat_of_int (2 ^ e))))"
proof -
  show ?thesis
    using assms
    unfolding pow_sub_eval_sign_monadic_def
      poly_length_monadic_def poly_copy_coeff_monadic_def
      pow_sub_shift_cond_def PR_CONST_def COPY_def
    apply (refine_vcg WHILET_rule[
      where I="pow_sub_shift_inv xs (length xs - 1) n e"
        and R="measure (\<lambda>(i, _::int, _::nat). length xs - 1 - i)"])
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal
      unfolding pow_sub_shift_inv_def poly_hom_eval_inv_def
      using poly_hom_eval_init[of "length xs - 1" xs "2 ^ e" n]
      by (auto simp: last_conv_nth)
    \<comment> \<open>the two residual obligations are the WHILET rule's body and exit, dispatched positionally as in
       @{thm [source] poly_hom_eval_zero_mpz_monadic_spec}: an explicit \<open>order_trans\<close> through the
       body's or finish's specification lemma, its hypotheses from the goal context, and the SPEC
       containment by the invariant or relation unfolding\<close>
    subgoal
      apply (rule order_trans)
       apply (rule pow_sub_shift_body_correct)
         apply (auto simp: pow_sub_shift_cond_def pow_sub_shift_inv_def split: prod.splits)
      done
    subgoal
      apply (rule order_trans)
       apply (rule pow_sub_sign_finish_monadic_spec)
        apply assumption
       apply (auto simp: pow_sub_shift_cond_def)
      done
    done
qed

sepref_definition pow_sub_eval_sign_impl [llvm_code] is
  "uncurry2 pow_sub_eval_sign_monadic" ::
  "[\<lambda>((_, _), xs).
      0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_sint_assn"
  unfolding pow_sub_eval_sign_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemma pow_sub_eval_sign_impl_hnr[sepref_fr_rules]:
  "(uncurry2 pow_sub_eval_sign_impl,
    uncurry2 (PR_CONST pow_sub_eval_sign_monadic)) \<in>
    [\<lambda>((_, _), xs).
      0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_sint_assn"
  using pow_sub_eval_sign_impl.refine
  by (simp add: PR_CONST_def)


subsection \<open>The pair test\<close>

text \<open>A registered op of its own rather than a conjunction in the certify's tail: three comparisons and
  two conjunctions as a multi-op \<open>RETURN\<close> tail does not translate (the same reason
  \<open>pow_sub_iv_degen_mop\<close> exists). Both arguments are machine \<open>sint\<close>s.\<close>

text \<open>\<^bold>\<open>The test is ``opposite strict signs'', not \<open>s \<noteq> t\<close>.\<close> The evaluation op is specified only to
  classify its value's sign; nothing in its specification says the result is \<open>-1/0/1\<close>, and \<open>s \<noteq> t\<close>
  would be true for two negatives of different magnitudes. So the test is phrased on the three atoms
  the classification provides.

  \<^bold>\<open>The window must also be ordered, and this route checks that at run time.\<close> A sign change says a
  root lies between the two points, not which point is on the left. When the shrink inverts
  (\<open>\<lceil>\<cdot>\<rceil> > \<lfloor>\<cdot>\<rfloor>\<close>, i.e. no grid point of precision \<open>m\<close> lies inside the window) the two points still
  straddle the root, and the emitted \<open>P\<close>-pair would be backwards. \<open>L\<^sup>h < R\<^sup>h\<close> is also a hypothesis of
  @{thm [source] pow_sub_certify_isolates}, so the guard is folded in here, at one \<open>mpz\<close> comparison
  per interval; \<open>w\<close> is that comparison's sign.\<close>

definition pow_sub_sgn_change_mop :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool nres" where
  "pow_sub_sgn_change_mop w s t \<equiv>
     RETURN (0 < w \<and> (s < 0 \<and> 0 < t \<or> 0 < s \<and> t < 0))"

sepref_register "PR_CONST pow_sub_sgn_change_mop" :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool nres"

sepref_definition pow_sub_sgn_change_impl [llvm_inline] is
  "uncurry2 pow_sub_sgn_change_mop" ::
  "gmp_sint_assn\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_sgn_change_mop_def
  apply (annot_sint_const gmp_int_t)?
  by sepref

lemma pow_sub_sgn_change_impl_hnr[sepref_fr_rules]:
  "(uncurry2 pow_sub_sgn_change_impl, uncurry2 (PR_CONST pow_sub_sgn_change_mop)) \<in>
    gmp_sint_assn\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_sgn_change_impl.refine
  by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>Two trichotomy classifications make a product test.\<close> Each returned \<open>int\<close> is only known
  to CLASSIFY its value's sign, never to equal it, so the bridge is a case split and not a
  coercion.\<close>

lemma pow_sub_sgn_change_iff:
  fixes v w :: rat and s t :: int
  assumes s: "(s < 0) = (v < 0)" "(0 < s) = (0 < v)"
    and t: "(t < 0) = (w < 0)" "(0 < t) = (0 < w)"
  shows "(s < 0 \<and> 0 < t \<or> 0 < s \<and> t < 0) = (v * w < 0)"
  using s t by (auto simp: mult_less_0_iff)

subsection \<open>The certify op\<close>

text \<open>The window is taken in \<open>Q\<close>-space exactly as @{const pow_sub_certify_monadic} takes it:
  \<open>(L\<^sup>h / 2\<^sup>h\<^sup>\<cdot>\<^sup>m, R\<^sup>h / 2\<^sup>h\<^sup>\<cdot>\<^sup>m)\<close>, exact integers over a shared power of two. \<open>L\<close>, \<open>R\<close> and \<open>xs\<close> are
  KEPT; the two powers and the shared denominator are allocated here and discarded here.\<close>

definition pow_sub_sign_tst ::
  "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool" where
  "pow_sub_sign_tst h m L R xs \<equiv>
     L ^ h < R ^ h
     \<and> poly (map_poly rat_of_int (Poly xs))
         (rat_of_int (L ^ h) / rat_of_int (2 ^ (h * m)))
       * poly (map_poly rat_of_int (Poly xs))
         (rat_of_int (R ^ h) / rat_of_int (2 ^ (h * m)))
       < 0"

definition pow_sub_certify_sign_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
  "pow_sub_certify_sign_monadic h m L R xs \<equiv> doN {
     ASSERT (0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> h * m < max_snat LENGTH(gmp_poly_len)
             \<and> 0 < length xs
             \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)
             \<and> h * m * length xs < max_snat LENGTH(gmp_poly_len));
     na \<leftarrow> (PR_CONST mpz_pow_nat_monadic) L h;
     nb \<leftarrow> (PR_CONST mpz_pow_nat_monadic) R h;
     wd \<leftarrow> (PR_CONST mpz_sub.amop_r1) (COPY nb) na;
     w \<leftarrow> (PR_CONST mpz_sgn_mop) wd;
     (PR_CONST mpzb_discard_monadic) wd;
     sa \<leftarrow> (PR_CONST pow_sub_eval_sign_monadic) na (h * m) xs;
     sb \<leftarrow> (PR_CONST pow_sub_eval_sign_monadic) nb (h * m) xs;
     (PR_CONST mpzb_discard_monadic) na;
     (PR_CONST mpzb_discard_monadic) nb;
     (PR_CONST pow_sub_sgn_change_mop) w sa sb
   }"

lemma pow_sub_certify_sign_monadic_correct:
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and hm: "h * m < max_snat LENGTH(gmp_poly_len)"
    and len0: "0 < length xs"
    and len: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and ebound: "h * m * length xs < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_certify_sign_monadic h m L R xs
           \<le> RETURN (pow_sub_sign_tst h m L R xs)"
proof -
  note ev = pow_sub_eval_sign_monadic_spec[OF len0 len ebound]
  show ?thesis
    unfolding pow_sub_certify_sign_monadic_def pow_sub_sign_tst_def
      PR_CONST_def mpzb_discard_monadic_def mpz_from_int_def
      pow_sub_sgn_change_mop_def mpz_sgn_mop_def
      mpz_sub.amop_r1_def mpz_sub.aop_r1_def COPY_def
    using h hb hm len0 len ebound
    apply (refine_vcg
           mpz_pow_nat_monadic_correct[OF h hb, THEN order_trans])
    \<comment> \<open>the two evaluations sit under a nested \<open>SPEC\<close>, so \<open>refine_vcg\<close> cannot fire them from
       its rule list — the same by-hand shape \<open>pow_sub_search_body_correct\<close> needs\<close>
    apply (all \<open>(simp add: top_fun_def; fail)
                | (rule order_trans[OF ev],
                   refine_vcg ev[THEN order_trans],
                   auto simp: top_fun_def mult_less_0_iff sgn_if
                        split: if_splits)\<close>)
    done
qed

sepref_register "PR_CONST pow_sub_certify_sign_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

sepref_definition pow_sub_certify_sign_impl [llvm_code] is
  "uncurry4 pow_sub_certify_sign_monadic" ::
  "[\<lambda>((((h, m), L), R), xs). 0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length xs
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)
       \<and> h * m * length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding pow_sub_certify_sign_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_sint_const gmp_int_t)?
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow_sub_certify_sign_impl_hnr[sepref_fr_rules]:
  "(uncurry4 pow_sub_certify_sign_impl,
    uncurry4 (PR_CONST pow_sub_certify_sign_monadic)) \<in>
    [\<lambda>((((h, m), L), R), xs). 0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length xs
       \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)
       \<and> h * m * length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> bool1_assn"
  using pow_sub_certify_sign_impl.refine
  by (simp add: PR_CONST_def)

subsection \<open>What the sign test certifies\<close>

text \<open>\<^bold>\<open>The counterpart of @{thm [source] pow_sub_certify_isolates} for the sign route\<close>, and
  the one structural difference between the two: this one needs the ENCLOSING interval's
  isolation as a hypothesis. That is not a weakening — the composite's soundness rests on the
  reduced solve's own isolation either way — but it is where the "at most one" comes from, and
  a future end-to-end theorem has to supply it from the reduced arm's @{const dsc_pair_ok}.\<close>

text \<open>@{thm [source] Dsc_Misc.proots_count_mono} is fixed to \<open>complex poly\<close> — it is used there
  only through the one-circle machinery, which lifts to \<open>\<complex>\<close> first. \<open>roots_in\<close> is real, so the
  real instance is proved here, by the same three steps; the only type-specific input is
  finiteness of a nonzero polynomial's root set.\<close>

lemma proots_count_mono_real:
  fixes P :: "real poly"
  assumes P0: "P \<noteq> 0" and sub: "A \<subseteq> B"
  shows "proots_count P A \<le> proots_count P B"
proof -
  have sub_rw: "proots_within P A \<subseteq> proots_within P B"
    using sub by (auto simp: proots_within_def)
  have finB: "finite (proots_within P B)"
  proof -
    have "proots_within P B \<subseteq> {x. poly P x = 0}"
      by (auto simp: proots_within_def)
    then show ?thesis
      using poly_roots_finite[OF P0] finite_subset by blast
  qed
  have "proots_count P A = (\<Sum>z\<in>proots_within P A. order z P)"
    by (simp add: proots_count_def)
  also have "\<dots> \<le> (\<Sum>z\<in>proots_within P B. order z P)"
    by (rule sum_mono2[OF finB sub_rw]) simp
  also have "\<dots> = proots_count P B"
    by (simp add: proots_count_def)
  finally show ?thesis .
qed

lemma roots_in_one_of_sign_change:
  fixes P :: "real poly"
  assumes P0: "P \<noteq> 0"
    and uv: "u < v"
    and lo: "a \<le> u" and hi: "v \<le> b"
    and one: "roots_in P a b = 1"
    and chg: "poly P u * poly P v < 0"
  shows "roots_in P u v = 1"
proof -
  obtain z where z: "u < z" "z < v" "poly P z = 0"
    using poly_IVT[OF uv chg] by blast
  have ge: "0 < proots_count P {x. u < x \<and> x < v}"
    using proots_count_of_root[OF P0, of z "{x. u < x \<and> x < v}"] z by simp
  have sub: "{x. u < x \<and> x < v} \<subseteq> {x. a < x \<and> x < b}"
    using lo hi by auto
  have le: "proots_count P {x. u < x \<and> x < v} \<le> proots_count P {x. a < x \<and> x < b}"
    by (rule proots_count_mono_real[OF P0 sub])
  show ?thesis
    using ge le one unfolding roots_in_def by simp
qed

end
