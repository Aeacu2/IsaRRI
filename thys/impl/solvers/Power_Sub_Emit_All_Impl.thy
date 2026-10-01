theory Power_Sub_Emit_All_Impl
  imports Power_Sub_Degen_Impl
begin

text \<open>Back-mapping of the whole positive half. It takes the reduced solve's positive-half interval
  vector and returns one \<open>P\<close>-side vector, which serves as both the positive windows and their mirrors,
  plus a single \<open>ok\<close> flag.

  \<^bold>\<open>Three design choices, each removing a synthesis hazard.\<close>

  \<^item> \<^bold>\<open>The per-interval GMP work is in three ops that touch no loop state\<close>: \<open>pow_sub_iv_degen_mop\<close>,
    \<open>pow_sub_iv_search_mop\<close>, \<open>pow_sub_iv_emit_mop\<close>. Each is a straight-line program with one branch. The
    loop body is a copy-get, three calls and two pushes. (Why three ops rather than one: see below.)
  \<^item> \<^bold>\<open>The loop body has no branch.\<close> On \<open>ok = False\<close> the per-interval op still returns a well-typed owned
    pair, and the body pushes it like any other. That is sound because the entry discards the whole
    vector when the flag is false, so a partially back-mapped output is never returned. A branch in the
    body would put a conditional push on an owned vector, i.e. two different owned states on the arms.
  \<^item> \<^bold>\<open>One vector is built, and the mirror is the same vector stored twice.\<close> The interface keeps the
    negative half in reflected coordinates (the root of negative-half interval \<open>i\<close> lies in
    \<open>[-rnb\<^sub>i/2\<^sup>k\<^sup>i, -lna\<^sub>i/2\<^sup>k\<^sup>i]\<close>), so for even \<open>h\<close> the mirror of \<open>(L, R, m)\<close> is that same triple: no negation
    and no second traversal. The exported wrapper stores this one vector into both the positive and the
    negative output triples. A loop state carrying two independently owned vectors in a 4-tuple does not
    synthesise, while one owned component does (as in @{const pow_sub_extract_monadic}).

  \<^bold>\<open>Why a mirror\<close>: for even \<open>h\<close> every positive root \<open>y\<close> of \<open>Q\<close> lifts to both \<open>\<plusminus>y\<^sup>1\<^sup>/\<^sup>h\<close>
  (\<open>pow_sub_preimage_card\<close>), so an entry emitting only the positive window would drop half the real
  roots. Both windows come from the same \<open>m\<close> (@{thm [source] pow_sub_shrink_exists_mirror}), so one
  precision loop per interval suffices.\<close>

section \<open>What one interval's emission establishes\<close>

text \<open>The bundle the loop carries in its invariant and the entry consumes. It is phrased on
  the PURE tests the two searches decide, because that is what the ops actually return; the
  step from here to @{const dsc_pair_ok} needs \<open>P = Q \<circ>\<^sub>p monom 1 h\<close> in scope and so belongs to
  the entry (\<open>pow_sub_emit_ok_pair_ok\<close>, in the entry theory, does exactly that).\<close>

definition pow_sub_emit_ok ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> int) \<times> nat \<Rightarrow> (int \<times> int) \<times> nat \<Rightarrow> bool" where
  "pow_sub_emit_ok h q iv out \<equiv>
     (let ((A, B), k) = iv; ((L, R), m) = out in
        if A = B
        then pow_sub_deg_tst h A k q m
             \<and> L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)
             \<and> R = (if L ^ h * 2 ^ k = A * 2 ^ (h * m) then L else 1 + L)
        else pow_sub_loop_tst h A B k q m
             \<and> L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)
             \<and> R = pow_sub_num_lo h m (real_of_int B / 2 ^ k))"

section \<open>One interval: search, then emit at the accepted precision\<close>

text \<open>\<^bold>\<open>Ownership.\<close> \<open>A\<close>, \<open>B\<close> and \<open>q\<close> are KEPT — the caller owns the interval it read out of the
  reduced arm's vector and frees it itself. \<open>L\<close> and \<open>R\<close> are freshly allocated and returned
  OWNED. The difference used for the degeneracy test is owned and discarded here.

  \<^bold>\<open>The emit is re-run at the accepted \<open>m\<close> rather than threaded out of the search loop.\<close> That
  costs one extra bisection \<open>h\<close>-th root per interval — negligible beside the Descartes count
  the search already paid — and it keeps the search's state a pure \<open>(nat \<times> bool)\<close>, which is
  what let it synthesise at all.\<close>

text \<open>\<^bold>\<open>The per-interval work is three registered ops, not one.\<close> One op doing the degeneracy test, search
  and emission and returning \<open>(L, R, m, ok)\<close> does not translate: monadify decomposes the 4-tuple into
  nested \<open>Pair\<close> binds, and a multi-op \<open>RETURN\<close> tail has to be a single registered op; a separate \<open>pack\<close> op
  for the tuple does not fire at the call sites. What works is every op returning a pair or a scalar, as
  @{const pow_sub_backmap_iv_monadic} (owned pair) and @{const pow_sub_search_monadic} (pure pair) do.
  So the work is split by result kind:

  \<^item> \<open>pow_sub_iv_degen_mop\<close>: the \<open>A = B\<close> test, a scalar bool. \<open>sg = 0\<close> as the last step of an op synthesises
    (as in @{const root_exact_monadic}), but in mid-chain feeding an \<open>if\<close> it is left as a bare boolean
    bind.
  \<^item> \<open>pow_sub_iv_search_mop\<close>: picks the degenerate or the proper search. A pure \<open>(nat \<times> bool)\<close>.
  \<^item> \<open>pow_sub_iv_emit_mop\<close>: picks the widening or the shrinking emission at the accepted \<open>m\<close>. An owned
    \<open>(int \<times> int)\<close>.

  The degeneracy flag is computed once and passed to the other two, so the \<open>mpz\<close> comparison happens once
  per interval.\<close>

definition pow_sub_iv_degen_mop :: "int \<Rightarrow> int \<Rightarrow> bool nres" where
  "pow_sub_iv_degen_mop A B \<equiv> doN {
     d \<leftarrow> (PR_CONST mpz_sub.amop_r1) (COPY B) A;
     sg \<leftarrow> (PR_CONST mpz_sgn_mop) d;
     (PR_CONST mpzb_discard_monadic) d;
     RETURN (sg = 0)
   }"

lemma pow_sub_iv_degen_mop_correct:
  "pow_sub_iv_degen_mop A B \<le> RETURN (A = B)"
  unfolding pow_sub_iv_degen_mop_def PR_CONST_def mpz_sgn_mop_def
    mpz_sub.amop_r1_def mpz_sub.aop_r1_def mpzb_discard_monadic_def COPY_def
  by refine_vcg (auto simp: sgn_if)

sepref_register "PR_CONST pow_sub_iv_degen_mop" :: "int \<Rightarrow> int \<Rightarrow> bool nres"

sepref_definition pow_sub_iv_degen_impl [llvm_code] is
  "uncurry pow_sub_iv_degen_mop" ::
  "mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_iv_degen_mop_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma pow_sub_iv_degen_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_iv_degen_impl, uncurry (PR_CONST pow_sub_iv_degen_mop)) \<in>
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_iv_degen_impl.refine by (simp add: PR_CONST_def)

text \<open>The widening emit, the degenerate branch's counterpart to
  @{const pow_sub_backmap_iv_monadic}: both endpoints come from the SAME \<open>A\<close>, the low one by
  bisection and the high one by the exactness test that @{const pow_sub_ceil_monadic} already
  performs — so this costs one bisection, not two.\<close>

definition pow_sub_backmap_deg_iv_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (int \<times> int) nres" where
  "pow_sub_backmap_deg_iv_monadic h m A k \<equiv> do {
     ASSERT (0 < h \<and> 0 \<le> A \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> h * m < max_snat LENGTH(gmp_poly_len));
     L \<leftarrow> (PR_CONST root_floor_gmp2) h m A k;
     R \<leftarrow> (PR_CONST pow_sub_ceil_monadic) h m A k;
     RETURN (L, R)
   }"

sepref_register "PR_CONST pow_sub_backmap_deg_iv_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (int \<times> int) nres"

sepref_definition pow_sub_backmap_deg_iv_impl [llvm_code] is
  "uncurry3 pow_sub_backmap_deg_iv_monadic" ::
  "[\<lambda>(((h, m), A), k). 0 < h \<and> 0 \<le> A
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k
    \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  unfolding pow_sub_backmap_deg_iv_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_sint_const gmp_int_t)?
  by sepref

lemma pow_sub_backmap_deg_iv_impl_hnr[sepref_fr_rules]:
  "(uncurry3 pow_sub_backmap_deg_iv_impl,
    uncurry3 (PR_CONST pow_sub_backmap_deg_iv_monadic)) \<in>
    [\<lambda>(((h, m), A), k). 0 < h \<and> 0 \<le> A
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k
    \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  using pow_sub_backmap_deg_iv_impl.refine by (simp add: PR_CONST_def)

definition pow_sub_iv_search_mop ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (nat \<times> bool) nres" where
  "pow_sub_iv_search_mop h q dlt A B k dg \<equiv> doN {
     ASSERT (0 < h \<and> 0 \<le> A \<and> 0 \<le> B
             \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> k + dlt < max_snat LENGTH(gmp_poly_len)
             \<and> h * (k + dlt) < max_snat LENGTH(gmp_poly_len)
             \<and> h * (k + dlt) * length q < max_snat LENGTH(gmp_poly_len)
             \<and> 0 < length q
             \<and> length q + 1 < max_snat LENGTH(gmp_poly_len));
     mcap \<leftarrow> RETURN (k + dlt);
     ASSERT (k \<le> mcap \<and> mcap < max_snat LENGTH(gmp_poly_len)
             \<and> h * mcap < max_snat LENGTH(gmp_poly_len)
             \<and> h * mcap * length q < max_snat LENGTH(gmp_poly_len));
     if dg then (PR_CONST pow_sub_deg_search_monadic) h A k q mcap
     else (PR_CONST pow_sub_search_monadic) h A B k q mcap
   }"
  \<comment> \<open>\<^bold>\<open>\<open>mcap\<close> is BOUND, then ASSERTed — it is never written \<open>k + dlt\<close> at a call site.\<close> The
     searches' HNR preconditions are stated on their \<open>mcap\<close> argument, and a side condition on
     an EXPRESSION cannot be discharged from an ASSERT about that expression: translation only
     ever sees \<open>bind_ref_tag\<close> for a bind result, a tag and not an equation. Binding first and
     asserting on the BOUND VARIABLE is the fix @{const pow_sub_extract_monadic} needed for its
     \<open>outlen\<close>, and framework limit 3's corollary states it in general.\<close>

sepref_register "PR_CONST pow_sub_iv_search_mop"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (nat \<times> bool) nres"

sepref_definition pow_sub_iv_search_impl [llvm_code] is
  "uncurry6 pow_sub_iv_search_mop" ::
  "[\<lambda>((((((h, q), dlt), A), B), k), dg). 0 < h \<and> 0 \<le> A \<and> 0 \<le> B
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> k + dlt < max_snat LENGTH(gmp_poly_len)
       \<and> h * (k + dlt) < max_snat LENGTH(gmp_poly_len)
       \<and> h * (k + dlt) * length q < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length q
       \<and> length q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k
    \<rightarrow> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  unfolding pow_sub_iv_search_mop_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow_sub_iv_search_impl_hnr[sepref_fr_rules]:
  "(uncurry6 pow_sub_iv_search_impl, uncurry6 (PR_CONST pow_sub_iv_search_mop)) \<in>
    [\<lambda>((((((h, q), dlt), A), B), k), dg). 0 < h \<and> 0 \<le> A \<and> 0 \<le> B
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> k + dlt < max_snat LENGTH(gmp_poly_len)
       \<and> h * (k + dlt) < max_snat LENGTH(gmp_poly_len)
       \<and> h * (k + dlt) * length q < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length q
       \<and> length q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k
    \<rightarrow> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  using pow_sub_iv_search_impl.refine by (simp add: PR_CONST_def)

definition pow_sub_iv_emit_mop ::
  "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (int \<times> int) nres" where
  "pow_sub_iv_emit_mop h m A B k dg \<equiv> doN {
     ASSERT (0 < h \<and> 0 \<le> A \<and> 0 \<le> B
             \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> h * m < max_snat LENGTH(gmp_poly_len));
     if dg then (PR_CONST pow_sub_backmap_deg_iv_monadic) h m A k
     else (PR_CONST pow_sub_backmap_iv_monadic) h m A B k
   }"

sepref_register "PR_CONST pow_sub_iv_emit_mop"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (int \<times> int) nres"

sepref_definition pow_sub_iv_emit_impl [llvm_code] is
  "uncurry5 pow_sub_iv_emit_mop" ::
  "[\<lambda>(((((h, m), A), B), k), dg). 0 < h \<and> 0 \<le> A \<and> 0 \<le> B
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k
    \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  unfolding pow_sub_iv_emit_mop_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma pow_sub_iv_emit_impl_hnr[sepref_fr_rules]:
  "(uncurry5 pow_sub_iv_emit_impl, uncurry5 (PR_CONST pow_sub_iv_emit_mop)) \<in>
    [\<lambda>(((((h, m), A), B), k), dg). 0 < h \<and> 0 \<le> A \<and> 0 \<le> B
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k
    \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  using pow_sub_iv_emit_impl.refine by (simp add: PR_CONST_def)

section \<open>The loop over the reduced arm's positive half\<close>

text \<open>\<^bold>\<open>The state is \<open>nat \<times> (bool \<times> vec)\<close>\<close>: a pure scalar on the left and every compound nested to the right,
  the association \<open>dyadic_loop_state\<close> (\<open>nat \<times> (vec \<times> vec)\<close>) and @{const pow_sub_extract_state_assn}
  (\<open>nat \<times> gmp_poly\<close>) use. The association is not what matters for synthesis; the vector push is (see the
  tail op below).\<close>

abbreviation pow_sub_emit_state_assn where
  "pow_sub_emit_state_assn \<equiv>
     snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a (bool1_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn)"

definition pow_sub_emit_cond :: "nat \<Rightarrow> nat \<times> bool \<times> _ \<Rightarrow> bool" where
  "pow_sub_emit_cond n st \<longleftrightarrow> (let (i, _, _) = st in i < n)"

sepref_register "PR_CONST pow_sub_emit_cond"

sepref_definition pow_sub_emit_cond_impl [llvm_inline] is
  "uncurry (RETURN oo pow_sub_emit_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_emit_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_emit_cond_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow_sub_emit_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_emit_cond_impl, uncurry (RETURN oo (PR_CONST pow_sub_emit_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_emit_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_emit_cond_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The body.\<close> No declared precondition may mention the loop state (framework limit 3),
  so the index bound and the two capacity bounds are ASSERTs INSIDE — @{thm hn_ASSERT_bind}
  turns them into assumptions at synthesis and the enclosing program discharges them from the
  invariant \<open>i \<le> n\<close> plus the caller's own bounds.

  \<^bold>\<open>Ownership.\<close> \<open>accQ\<close> and \<open>q\<close> are KEPT; \<open>dyadic_interval_vec_copy_get_monadic\<close> hands back
  OWNED copies of the endpoints, which are discarded here once the per-interval op has read
  them. \<open>L\<close> and \<open>R\<close> are owned; the positive vector takes COPIES and the negative vector
  consumes the originals, so each is pushed exactly once and freed by whoever frees the
  vector.\<close>

text \<open>\<^bold>\<open>The structure follows \<open>Dyadic_Solver.dyadic_loop_body_idx_monadic\<close>\<close>, which also reads a
  @{typ gmp_dyadic_interval_vec} inside a loop:

  \<^enum> \<^bold>\<open>The body ends in a single registered op that takes the state bundled as its first argument\<close> and
    returns the state (\<open>dyadic_zero_noden_monadic (i, todo, acc) l r k\<close> there). There is no tuple
    \<open>RETURN\<close> in the loop body.
  \<^enum> \<^bold>\<open>That tail op is small\<close>: destructure, discard the owned \<open>mpz\<close>s, \<open>RETURN (i + 1, todo, acc)\<close>. A flat
    3-tuple and an inline \<open>i + 1\<close> in a final \<open>RETURN\<close> are fine, provided the op containing the tuple does
    nothing else.
  \<^enum> \<^bold>\<open>The copy-get result is consumed by \<open>case ep of (l, r, k) \<Rightarrow> doN {\<dots>}\<close>\<close>, with the rest of the body
    inside the case, not by a \<open>let\<close> followed by a flat sequence.
  \<^enum> \<^bold>\<open>The index bound is asserted through a \<open>case\<close>, not a projection\<close>:
    \<open>ASSERT (case todo of (lns, rns, ks) \<Rightarrow> i < length lns \<and> \<dots>)\<close>.
  \<^enum> \<^bold>\<open>The unfolds are \<open>invar_def\<close>, \<open>pushable_def\<close> and \<open>Let_def\<close>, and the closer is
    \<open>sepref_dbg_trans_keep\<close>\<close>, not \<open>trans\<close>.

  The two small arithmetic ops below (\<open>pow_sub_succ_mop\<close>, \<open>pow_sub_and_mop\<close>) keep inline arithmetic out of
  the wide body.\<close>

definition pow_sub_succ_mop :: "nat \<Rightarrow> nat nres" where
  "pow_sub_succ_mop i \<equiv> doN {
     ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
     RETURN (i + 1)
   }"

sepref_register "PR_CONST pow_sub_succ_mop" :: "nat \<Rightarrow> nat nres"

sepref_definition pow_sub_succ_impl [llvm_inline] is
  "pow_sub_succ_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding pow_sub_succ_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma pow_sub_succ_impl_hnr[sepref_fr_rules]:
  "(pow_sub_succ_impl, PR_CONST pow_sub_succ_mop) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using pow_sub_succ_impl.refine by (simp add: PR_CONST_def)

definition pow_sub_and_mop :: "bool \<Rightarrow> bool \<Rightarrow> bool nres" where
  "pow_sub_and_mop a b \<equiv> RETURN (a \<and> b)"

sepref_register "PR_CONST pow_sub_and_mop" :: "bool \<Rightarrow> bool \<Rightarrow> bool nres"

sepref_definition pow_sub_and_impl [llvm_inline] is
  "uncurry pow_sub_and_mop" ::
  "bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_and_mop_def
  by sepref

lemma pow_sub_and_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_and_impl, uncurry (PR_CONST pow_sub_and_mop)) \<in>
    bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_and_impl.refine by (simp add: PR_CONST_def)

text \<open>The tail op, in the shape of \<open>dyadic_one_noden_monadic\<close>: state bundled and first, then the
  per-interval values; destructure, append column-wise, return the rebuilt state.

  \<^bold>\<open>It appends the three columns itself rather than calling \<open>dyadic_interval_vec_push_monadic\<close> on the
  bundle\<close>, which is why it synthesises: calling the vector push wrapper from a nested loop state leaves
  unresolved ownership goals for the nested state, whereas inline column appends let
  \<open>ASSERT pushable\<close> feed the primitive operations directly. The computation is the same: \<open>Dyadic_Interval\<close>
  defines the wrapper as exactly these three appends in this order under the same two ASSERTs, so the
  wrapper's specification lemma describes this op.\<close>

definition pow_sub_emit_push_mop ::
  "nat \<times> bool \<times> gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
     (nat \<times> bool \<times> gmp_dyadic_interval_vec) nres" where
  "pow_sub_emit_push_mop st L R m ok' \<equiv> doN {
     let (i, ok, out) = st;
     let (lns, rns, ks) = out;
     ASSERT (dyadic_interval_vec_pushable out);
     lns \<leftarrow> (PR_CONST poly_push_coeff_monadic) lns L;
     rns \<leftarrow> (PR_CONST poly_push_coeff_monadic) rns R;
     ASSERT (length ks + 1 < max_snat LENGTH(gmp_poly_len));
     ks \<leftarrow> mop_list_append ks m;
     i' \<leftarrow> (PR_CONST pow_sub_succ_mop) i;
     ok'' \<leftarrow> (PR_CONST pow_sub_and_mop) ok ok';
     RETURN (i', ok'', (lns, rns, ks))
   }"

sepref_register "PR_CONST pow_sub_emit_push_mop"
  :: "nat \<times> bool \<times> gmp_dyadic_interval_vec \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
      (nat \<times> bool \<times> gmp_dyadic_interval_vec) nres"

text \<open>\<^bold>\<open>Signature and closer as for \<open>dyadic_zero_noden_impl\<close>\<close>: the numeric bound is an HNR precondition
  reached through a \<open>case\<close> on the bundled state, not an internal ASSERT with a bare \<open>\<rightarrow>\<^sub>a\<close>, and the closer is
  the explicit \<open>sepref_dbg_*\<close> chain, because \<open>by sepref\<close> fails at the initial method on an op with owned
  \<open>mpz\<close> arguments. \<open>pushable_def\<close> is unfolded here, since this op pushes inline.\<close>

sepref_definition pow_sub_emit_push_impl [llvm_code] is
  "uncurry4 pow_sub_emit_push_mop" ::
  "[\<lambda>((((st, _), _), _), _). case st of (i, _, _) \<Rightarrow>
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    pow_sub_emit_state_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>
      pow_sub_emit_state_assn"
  unfolding pow_sub_emit_push_mop_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

lemma pow_sub_emit_push_impl_hnr[sepref_fr_rules]:
  "(uncurry4 pow_sub_emit_push_impl, uncurry4 (PR_CONST pow_sub_emit_push_mop)) \<in>
    [\<lambda>((((st, _), _), _), _). case st of (i, _, _) \<Rightarrow>
      i + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    pow_sub_emit_state_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>
      pow_sub_emit_state_assn"
  using pow_sub_emit_push_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The body.\<close> No declared precondition may mention the loop state (framework limit 3),
  so the state-dependent bounds are ASSERTs INSIDE.\<close>

definition pow_sub_emit_body_mop ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> nat \<Rightarrow>
     nat \<times> bool \<times> gmp_dyadic_interval_vec \<Rightarrow>
     (nat \<times> bool \<times> gmp_dyadic_interval_vec) nres" where
  "pow_sub_emit_body_mop h q dlt accQ n st \<equiv> doN {
     let (i, ok, out) = st;
     ASSERT (0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> 0 < length q
             \<and> length q + 1 < max_snat LENGTH(gmp_poly_len)
             \<and> i < n
             \<and> i + 1 < max_snat LENGTH(gmp_poly_len)
             \<and> dyadic_interval_vec_pushable out);
     ASSERT (case accQ of (lns, rns, ks) \<Rightarrow>
               i < length lns \<and> i < length rns \<and> i < length ks);
     abk \<leftarrow> (PR_CONST dyadic_interval_vec_copy_get_monadic) accQ i;
     case abk of (A, B, k) \<Rightarrow> doN {
ASSERT (0 \<le> A \<and> 0 \<le> B
                \<and> k < max_snat LENGTH(gmp_poly_len)
                \<and> k + dlt < max_snat LENGTH(gmp_poly_len)
                \<and> h * (k + dlt) < max_snat LENGTH(gmp_poly_len)
                \<and> h * (k + dlt) * length q < max_snat LENGTH(gmp_poly_len));
       dg \<leftarrow> (PR_CONST pow_sub_iv_degen_mop) A B;
       sr \<leftarrow> (PR_CONST pow_sub_iv_search_mop) h q dlt A B k dg;
       case sr of (m, ok') \<Rightarrow> doN {
         ASSERT (h * m < max_snat LENGTH(gmp_poly_len));
         lr \<leftarrow> (PR_CONST pow_sub_iv_emit_mop) h m A B k dg;
         case lr of (L, R) \<Rightarrow> doN {
           (PR_CONST mpzb_discard_monadic) A;
           (PR_CONST mpzb_discard_monadic) B;
           (PR_CONST pow_sub_emit_push_mop) (i, ok, out) L R m ok'
         }
       }
     }
   }"

sepref_register "PR_CONST pow_sub_emit_body_mop"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> nat \<Rightarrow>
      nat \<times> bool \<times> gmp_dyadic_interval_vec \<Rightarrow>
      (nat \<times> bool \<times> gmp_dyadic_interval_vec) nres"

text \<open>\<^bold>\<open>Recipe cloned from \<open>dyadic_loop_body_idx_impl\<close>\<close>: the declared precondition mentions only
  the loop-INVARIANT-free arguments (framework limit 3), \<open>pushable_def\<close> and \<open>Let_def\<close> are
  unfolded, and the closer is \<open>sepref_dbg_trans_keep\<close> — \<open>trans\<close>, not \<open>trans_keep\<close>, is what the
  per-interval leaf ops use; a body whose sub-ops each carry side conditions needs the keep
  form to leave them visible.\<close>

sepref_definition pow_sub_emit_body_impl [llvm_inline] is
  "uncurry5 pow_sub_emit_body_mop" ::
  "[\<lambda>(((((h, q), dlt), accQ), n), st). 0 < h
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length q
       \<and> length q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_emit_state_assn\<^sup>d \<rightarrow>
      pow_sub_emit_state_assn"
  unfolding pow_sub_emit_body_mop_def
  unfolding dyadic_interval_vec_pushable_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemma pow_sub_emit_body_impl_hnr[sepref_fr_rules]:
  "(uncurry5 pow_sub_emit_body_impl, uncurry5 (PR_CONST pow_sub_emit_body_mop)) \<in>
    [\<lambda>(((((h, q), dlt), accQ), n), st). 0 < h
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length q
       \<and> length q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_emit_state_assn\<^sup>d \<rightarrow>
      pow_sub_emit_state_assn"
  using pow_sub_emit_body_impl.refine by (simp add: PR_CONST_def)

text \<open>The post-loop projection: the state is taken destructively, so the tail is a registered op rather
  than an inline destructure, as for @{const pow_sub_extract_result_mop}.\<close>

definition pow_sub_emit_result_mop ::
  "nat \<times> bool \<times> gmp_dyadic_interval_vec \<Rightarrow>
     (gmp_dyadic_interval_vec \<times> bool) nres" where
  "pow_sub_emit_result_mop st \<equiv> (let (i, ok, out) = st in RETURN (out, ok))"

sepref_register "PR_CONST pow_sub_emit_result_mop"

sepref_definition pow_sub_emit_result_impl [llvm_inline] is
  "pow_sub_emit_result_mop" ::
  "pow_sub_emit_state_assn\<^sup>d \<rightarrow>\<^sub>a
     gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  unfolding pow_sub_emit_result_mop_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma pow_sub_emit_result_impl_hnr[sepref_fr_rules]:
  "(pow_sub_emit_result_impl, PR_CONST pow_sub_emit_result_mop) \<in>
    pow_sub_emit_state_assn\<^sup>d \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  using pow_sub_emit_result_impl.refine by (simp add: PR_CONST_def)

definition pow_sub_backmap_run_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> nat \<Rightarrow>
     (gmp_dyadic_interval_vec \<times> bool) nres" where
  "pow_sub_backmap_run_monadic h q dlt accQ n \<equiv> doN {
     ASSERT (0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> 0 < length q
             \<and> length q + 1 < max_snat LENGTH(gmp_poly_len));
     ASSERT (n = length (fst accQ) \<and> n + 1 < max_snat LENGTH(gmp_poly_len));
     out \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) n;
     st \<leftarrow> WHILEIT
        (\<lambda>(i, ok, out). i \<le> n)
        (\<lambda>st. (PR_CONST pow_sub_emit_cond) n st)
        (\<lambda>st. (PR_CONST pow_sub_emit_body_mop) h q dlt accQ n st)
        (0, True, out);
     (PR_CONST pow_sub_emit_result_mop) st
   }"

sepref_register "PR_CONST pow_sub_backmap_run_monadic"

sepref_definition pow_sub_backmap_run_impl [llvm_code] is
  "uncurry4 pow_sub_backmap_run_monadic" ::
  "[\<lambda>((((h, q), dlt), accQ), n). 0 < h
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length q
       \<and> length q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k
    \<rightarrow> gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  unfolding pow_sub_backmap_run_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    pow_sub_emit_cond_impl_hnr pow_sub_emit_body_impl_hnr pow_sub_emit_result_impl_hnr
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

lemma pow_sub_backmap_run_impl_hnr[sepref_fr_rules]:
  "(uncurry4 pow_sub_backmap_run_impl, uncurry4 (PR_CONST pow_sub_backmap_run_monadic)) \<in>
    [\<lambda>((((h, q), dlt), accQ), n). 0 < h
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length q
       \<and> length q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k
    \<rightarrow> gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  using pow_sub_backmap_run_impl.refine by (simp add: PR_CONST_def)

section \<open>The room guard: the six per-interval preconditions, decided at run time\<close>

text \<open>\<^bold>\<open>Why this is a runtime test and not a proof.\<close> @{const pow_sub_emit_body_mop} ASSERTs six facts about
  each interval it reads from the reduced solve: \<open>0 \<le> A\<close>, \<open>0 \<le> B\<close>, and four word-capacity bounds on the
  precision column \<open>k\<close>. They are the hypothesis bundle \<open>pow_sub_iv_pre\<close> of \<open>Power_Sub_Sound\<close>, and the
  entry's soundness theorem has to discharge them. The reduced solve's specification does not supply
  them: it states @{const dsc_pair_ok} and root coverage per emitted interval, and neither constrains the
  sign of an endpoint or the size of \<open>k\<close>.

  Two of the six are true but not exported (the positive half is anchored on \<open>[0, 2\<^sup>k\<^sup>p\<^sup>o\<^sup>s]\<close>, a fact inside the
  keystone's accumulator invariant). The other four are not derivable: the pipeline guarantees only
  \<open>k * (length rp - 1) < max_snat\<close> (\<open>hybrid_loop_step_pre\<close>), while certification needs
  \<open>h * (k + dlt) * length q < max_snat\<close>, larger by a factor of \<open>h\<close>. So this is a capacity obligation, and the
  only ways to meet it are an uncheckable caller obligation or a runtime test. This is the runtime test.

  \<^bold>\<open>The test covers the whole vector and the fallback is wholesale\<close>: one \<open>O(n)\<close> pre-pass of two \<open>mpz_sgn\<close>
  reads and one word comparison per interval. On failure the back-map is skipped and \<open>ok = False\<close>, the
  same path the entry takes when no substitution applies, so there is no new failure mode or output shape.

  \<^bold>\<open>The limits make the four bounds pure arithmetic on literals\<close>, so that no product computed at run
  time can itself overflow: with \<open>h < 1024\<close>, \<open>dlt < 1024\<close>, \<open>length q < 2\<^sup>2\<^sup>0\<close> and \<open>k < 2\<^sup>2\<^sup>0\<close>,
  \<open>h * (k + dlt) * length q < 2\<^sup>5\<^sup>1\<close>, inside \<open>max_snat 64 = 2\<^sup>6\<^sup>3\<close>. Refusing to substitute is always sound, so
  these are policy constants, but they are also proof-side guards.\<close>

definition pow_sub_room_sgn_mop :: "int \<Rightarrow> int \<Rightarrow> bool nres" where
  "pow_sub_room_sgn_mop sa sb \<equiv> RETURN (0 \<le> sa \<and> 0 \<le> sb)"

sepref_register "PR_CONST pow_sub_room_sgn_mop" :: "int \<Rightarrow> int \<Rightarrow> bool nres"

sepref_definition pow_sub_room_sgn_impl [llvm_inline] is
  "uncurry pow_sub_room_sgn_mop" ::
  "gmp_sint_assn\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_room_sgn_mop_def
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma pow_sub_room_sgn_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_room_sgn_impl, uncurry (PR_CONST pow_sub_room_sgn_mop)) \<in>
    gmp_sint_assn\<^sup>k *\<^sub>a gmp_sint_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_room_sgn_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>Separate from the sign test\<close>: this one compares an \<open>snat\<close> with an \<open>snat\<close> literal and that one
  compares \<open>sint\<close>s with an \<open>sint\<close> zero, so fusing them would put \<open>annot_snat_const\<close> and \<open>annot_sint_const\<close> on
  one op, two constant-folding passes over the same term. Two small ops and one @{const pow_sub_and_mop}
  avoid that.\<close>

definition pow_sub_room_k_mop :: "nat \<Rightarrow> bool nres" where
  "pow_sub_room_k_mop k \<equiv> RETURN (k < 1048576)"

sepref_register "PR_CONST pow_sub_room_k_mop" :: "nat \<Rightarrow> bool nres"

sepref_definition pow_sub_room_k_impl [llvm_inline] is
  "pow_sub_room_k_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_room_k_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma pow_sub_room_k_impl_hnr[sepref_fr_rules]:
  "(pow_sub_room_k_impl, PR_CONST pow_sub_room_k_mop) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_room_k_impl.refine by (simp add: PR_CONST_def)

text \<open>The three per-CALL limits, tested once rather than per interval.\<close>

definition pow_sub_room_hd_mop :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
  "pow_sub_room_hd_mop h dlt lenq \<equiv> RETURN (h < 1024 \<and> dlt < 1024 \<and> lenq < 1048576)"

sepref_register "PR_CONST pow_sub_room_hd_mop" :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres"

sepref_definition pow_sub_room_hd_impl [llvm_inline] is
  "uncurry2 pow_sub_room_hd_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_room_hd_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma pow_sub_room_hd_impl_hnr[sepref_fr_rules]:
  "(uncurry2 pow_sub_room_hd_impl, uncurry2 (PR_CONST pow_sub_room_hd_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_room_hd_impl.refine by (simp add: PR_CONST_def)

abbreviation pow_sub_room_state_assn where
  "pow_sub_room_state_assn \<equiv> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"

definition pow_sub_room_cond :: "nat \<Rightarrow> nat \<times> bool \<Rightarrow> bool" where
  "pow_sub_room_cond n st \<longleftrightarrow> (let (i, _) = st in i < n)"

sepref_register "PR_CONST pow_sub_room_cond"

sepref_definition pow_sub_room_cond_impl [llvm_inline] is
  "uncurry (RETURN oo pow_sub_room_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_room_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_room_cond_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow_sub_room_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_room_cond_impl, uncurry (RETURN oo (PR_CONST pow_sub_room_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_room_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_room_cond_impl.refine by (simp add: PR_CONST_def)

text \<open>The tail op, state bundled and FIRST — the same shape
  @{const pow_sub_emit_push_mop} has, for the same reason.\<close>

definition pow_sub_room_step_mop ::
  "nat \<times> bool \<Rightarrow> bool \<Rightarrow> (nat \<times> bool) nres" where
  "pow_sub_room_step_mop st g \<equiv> doN {
     let (i, ok) = st;
     i' \<leftarrow> (PR_CONST pow_sub_succ_mop) i;
     ok' \<leftarrow> (PR_CONST pow_sub_and_mop) ok g;
     RETURN (i', ok')
   }"

sepref_register "PR_CONST pow_sub_room_step_mop"
  :: "nat \<times> bool \<Rightarrow> bool \<Rightarrow> (nat \<times> bool) nres"

sepref_definition pow_sub_room_step_impl [llvm_inline] is
  "uncurry pow_sub_room_step_mop" ::
  "pow_sub_room_state_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a pow_sub_room_state_assn"
  unfolding pow_sub_room_step_mop_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow_sub_room_step_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_room_step_impl, uncurry (PR_CONST pow_sub_room_step_mop)) \<in>
    pow_sub_room_state_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a pow_sub_room_state_assn"
  using pow_sub_room_step_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The guard body\<close>: @{const pow_sub_emit_body_mop}'s structure with the per-interval work replaced by
  two sign reads. \<open>accQ\<close> is kept throughout.

  \<^bold>\<open>It reads the columns with @{const poly_coeff_sgn_monadic}\<close>, not \<open>dyadic_interval_vec_copy_get_monadic\<close>.
  The copy-get is two @{const poly_copy_coeff_monadic}s, and \<open>poly_copy_coeff_impl\<close> is
  \<open>arl_nth; mpzb_copy\<close>, an \<open>mpz_init_set\<close> (an allocation and a limb copy) that this op would immediately
  discard. \<open>poly_coeff_sgn_impl\<close> is \<open>arl_nth; mpzb_sgn_impl\<close>, an \<open>O(1)\<close> read of the sign with no allocation.

  The columns are destructured and passed separately, as for @{const pow_sub_emit_push_mop}.
  \<open>0 \<le> sgn x \<longleftrightarrow> 0 \<le> x\<close>, so @{const pow_sub_room_sgn_mop} reads a \<open>gmp_sint_assn\<close> pair, which
  @{thm [source] poly_coeff_sgn_impl_hnr} returns.\<close>

definition pow_sub_room_body_mop ::
  "nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> nat \<times> bool \<Rightarrow> (nat \<times> bool) nres" where
  "pow_sub_room_body_mop n accQ st \<equiv> doN {
     let (i, ok) = st;
     let (lns, rns, ks) = accQ;
     ASSERT (i < n \<and> i + 1 < max_snat LENGTH(gmp_poly_len));
     ASSERT (i < length lns \<and> i < length rns \<and> i < length ks);
     sa \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) lns i;
     sb \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) rns i;
     k \<leftarrow> mop_list_get ks i;
     g1 \<leftarrow> (PR_CONST pow_sub_room_sgn_mop) sa sb;
     g2 \<leftarrow> (PR_CONST pow_sub_room_k_mop) k;
     g \<leftarrow> (PR_CONST pow_sub_and_mop) g1 g2;
     (PR_CONST pow_sub_room_step_mop) (i, ok) g
   }"

sepref_register "PR_CONST pow_sub_room_body_mop"
  :: "nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> nat \<times> bool \<Rightarrow> (nat \<times> bool) nres"

sepref_definition pow_sub_room_body_impl [llvm_inline] is
  "uncurry2 pow_sub_room_body_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>k *\<^sub>a
     pow_sub_room_state_assn\<^sup>k \<rightarrow>\<^sub>a pow_sub_room_state_assn"
  unfolding pow_sub_room_body_mop_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  supply [sepref_frame_free_rules] = mk_free_is_pure
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

lemma pow_sub_room_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 pow_sub_room_body_impl, uncurry2 (PR_CONST pow_sub_room_body_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>k *\<^sub>a
      pow_sub_room_state_assn\<^sup>k \<rightarrow>\<^sub>a pow_sub_room_state_assn"
  using pow_sub_room_body_impl.refine by (simp add: PR_CONST_def)

definition pow_sub_room_result_mop :: "nat \<times> bool \<Rightarrow> bool nres" where
  "pow_sub_room_result_mop st \<equiv> (let (i, ok) = st in RETURN ok)"

sepref_register "PR_CONST pow_sub_room_result_mop" :: "nat \<times> bool \<Rightarrow> bool nres"

sepref_definition pow_sub_room_result_impl [llvm_inline] is
  "pow_sub_room_result_mop" ::
  "pow_sub_room_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_room_result_mop_def
  unfolding Let_def
  by sepref

lemma pow_sub_room_result_impl_hnr[sepref_fr_rules]:
  "(pow_sub_room_result_impl, PR_CONST pow_sub_room_result_mop) \<in>
    pow_sub_room_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_room_result_impl.refine by (simp add: PR_CONST_def)

definition pow_sub_room_all_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> nat \<Rightarrow> bool nres" where
  "pow_sub_room_all_monadic h dlt lenq accQ n \<equiv> doN {
     ASSERT (n = length (fst accQ) \<and> n + 1 < max_snat LENGTH(gmp_poly_len));
     g0 \<leftarrow> (PR_CONST pow_sub_room_hd_mop) h dlt lenq;
     st \<leftarrow> WHILEIT
        (\<lambda>(i, ok). i \<le> n)
        (\<lambda>st. (PR_CONST pow_sub_room_cond) n st)
        (\<lambda>st. (PR_CONST pow_sub_room_body_mop) n accQ st)
        (0, g0);
     (PR_CONST pow_sub_room_result_mop) st
   }"

sepref_register "PR_CONST pow_sub_room_all_monadic"

sepref_definition pow_sub_room_all_impl [llvm_code] is
  "uncurry4 pow_sub_room_all_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_room_all_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    pow_sub_room_cond_impl_hnr pow_sub_room_body_impl_hnr pow_sub_room_result_impl_hnr
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

lemma pow_sub_room_all_impl_hnr[sepref_fr_rules]:
  "(uncurry4 pow_sub_room_all_impl, uncurry4 (PR_CONST pow_sub_room_all_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_room_all_impl.refine by (simp add: PR_CONST_def)

text \<open>The refused arm. It allocates an empty vector rather than returning nothing because both arms of the
  branch below must carry the same owned shape, as \<open>pow_sub_entry_bail_mop\<close> does in the entry.\<close>

definition pow_sub_backmap_skip_mop ::
  "nat \<Rightarrow> (gmp_dyadic_interval_vec \<times> bool) nres" where
  "pow_sub_backmap_skip_mop n \<equiv> doN {
     out \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) n;
     RETURN (out, False)
   }"

sepref_register "PR_CONST pow_sub_backmap_skip_mop"
  :: "nat \<Rightarrow> (gmp_dyadic_interval_vec \<times> bool) nres"

sepref_definition pow_sub_backmap_skip_impl [llvm_inline] is
  "pow_sub_backmap_skip_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
     gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  unfolding pow_sub_backmap_skip_mop_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma pow_sub_backmap_skip_impl_hnr[sepref_fr_rules]:
  "(pow_sub_backmap_skip_impl, PR_CONST pow_sub_backmap_skip_mop) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  using pow_sub_backmap_skip_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The entry point, unchanged in name and signature\<close> — the guard and the branch are internal,
  so \<open>Power_Sub_Entry_Impl.thy\<close> (which only \<open>export.sh full\<close> compiles) does not move. Each
  \<open>if\<close>-arm is a SINGLE registered op call, and the branch condition is a bound variable.\<close>

definition pow_sub_backmap_all_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow>
     (gmp_dyadic_interval_vec \<times> bool) nres" where
  "pow_sub_backmap_all_monadic h q dlt accQ \<equiv> doN {
     ASSERT (0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> 0 < length q
             \<and> length q + 1 < max_snat LENGTH(gmp_poly_len));
     lenq \<leftarrow> (PR_CONST poly_length_monadic) q;
     ASSERT (lenq = length q);
     n \<leftarrow> (PR_CONST dyadic_interval_vec_length_monadic) accQ;
     ASSERT (n = length (fst accQ) \<and> n + 1 < max_snat LENGTH(gmp_poly_len));
     g \<leftarrow> (PR_CONST pow_sub_room_all_monadic) h dlt lenq accQ n;
     if g then (PR_CONST pow_sub_backmap_run_monadic) h q dlt accQ n
     else (PR_CONST pow_sub_backmap_skip_mop) n
   }"

sepref_register "PR_CONST pow_sub_backmap_all_monadic"

sepref_definition pow_sub_backmap_all_impl [llvm_code] is
  "uncurry3 pow_sub_backmap_all_monadic" ::
  "[\<lambda>(((h, q), dlt), accQ). 0 < h
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length q
       \<and> length q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>k
    \<rightarrow> gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  unfolding pow_sub_backmap_all_monadic_def
  unfolding Let_def
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

lemma pow_sub_backmap_all_impl_hnr[sepref_fr_rules]:
  "(uncurry3 pow_sub_backmap_all_impl, uncurry3 (PR_CONST pow_sub_backmap_all_monadic)) \<in>
    [\<lambda>(((h, q), dlt), accQ). 0 < h
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> 0 < length q
       \<and> length q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_dyadic_interval_vec_assn\<^sup>k
    \<rightarrow> gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  using pow_sub_backmap_all_impl.refine by (simp add: PR_CONST_def)

end
