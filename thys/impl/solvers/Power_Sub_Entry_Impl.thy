theory Power_Sub_Entry_Impl
  imports Power_Sub_Emit_All_Impl Hybrid_Solver_Pipeline
begin

text \<open>The power-substitution entry. Detect \<open>h\<close> with \<open>P(x) = Q(x\<^sup>h)\<close>, extract \<open>Q\<close>, solve the reduced
  polynomial with the deflating pipeline, and back-map \<open>Q\<close>'s positive windows to \<open>P\<close>'s. It returns one
  interval vector (serving as both the positive windows and their mirrors, see \<open>Power_Sub_Emit_All_Impl\<close>),
  the reduced solve's origin flag, and an \<open>ok\<close> flag.

  \<^bold>\<open>What this entry does not do.\<close>

  \<^item> \<^bold>\<open>Odd \<open>h\<close> is not substituted.\<close> For odd \<open>h\<close> the negative roots of \<open>Q\<close> lift and the map is injective
    through the origin, so there is no mirror; the entry accepts only \<open>2 \<le> h \<and> even h\<close> (see the
    applicability test below).
  \<^item> \<^bold>\<open>The fallback on \<open>ok = False\<close> is the caller's.\<close> On \<open>ok = False\<close> the precision search reached its cap and
    the output must not be used; the exported wrapper then solves \<open>P\<close> with the deflating pipeline. Doing the
    fallback inside this op would put two independently allocated owned vectors on the two arms of one
    branch.
  \<^item> \<^bold>\<open>\<open>dlt\<close> is an argument, not a constant\<close>, supplied by the caller. It is also a proof-side guard (see the
    room guard in \<open>Power_Sub_Emit_All_Impl\<close>).

  \<^bold>\<open>The claim is isolation, not a multiset equality\<close>: a substitution returns different intervals, so a
  multiset equality against \<open>dsc_int\<close>'s own intervals cannot hold.\<close>

section \<open>Applicability: \<open>h \<ge> 2\<close> and \<open>h\<close> EVEN\<close>

text \<open>A registered op of its own, because a bare comparison feeding an \<open>if\<close> in mid-chain is an inline test
  in a heap body (as for \<open>pow_sub_iv_degen_mop\<close>).

  \<^bold>\<open>Parity needs no new operation\<close>: \<open>h\<close> is even iff \<open>gcd(h, 2) = 2\<close>, and \<open>snat_gcd_monadic\<close> exists
  (detection is built on it).

  \<^bold>\<open>The substitution uses the detected exponent\<close> (subject to the cap below), not \<open>2\<close>: every op below is
  general in \<open>h\<close> (\<open>pow_sub_extract_monadic\<close> strides by \<open>h\<close>, \<open>pow_sub_backmap_all_monadic\<close> takes \<open>h\<close>, and the
  bisection \<open>h\<close>-th root is general).\<close>

text \<open>\<^bold>\<open>The exponent used is \<open>d = gcd(h, hcap)\<close>, not \<open>h\<close>.\<close>

  \<^bold>\<open>Any divisor is legitimate.\<close> If \<open>P(x) = Q(x\<^sup>h)\<close> and \<open>d\<close> divides \<open>h\<close>, then \<open>P(x) = R(x\<^sup>d)\<close> for
  \<open>R(y) = Q(y\<^sup>h\<^sup>/\<^sup>d)\<close>. So the entry may substitute with any divisor of the detected \<open>h\<close>.

  \<^bold>\<open>Why not the largest.\<close> The back-map does not take roots: it bisects in \<open>x\<close>-space and decides membership
  with \<open>a < m\<^sup>d < b\<close>, which costs a \<open>d\<close>-th power of a big integer per bisection step. So the back-map's cost
  grows with \<open>d\<close> while the reduced solve shrinks, and for large \<open>d\<close> the back-map dominates.

  \<^bold>\<open>\<open>gcd(h, hcap)\<close> with \<open>hcap\<close> a power of two\<close>, in one op:
  \<^item> returns the largest power-of-two divisor of \<open>h\<close>, capped at \<open>hcap\<close> (\<open>gcd(4,16) = 4\<close>, \<open>gcd(50,16) = 2\<close>,
    \<open>gcd(6400,16) = 16\<close>);
  \<^item> the result divides \<open>h\<close>, so the substitution is valid;
  \<^item> the parity of \<open>d\<close> is tested separately (below), since \<open>hcap\<close> is supplied by the caller and need not be a
    power of two.

  \<open>hcap\<close> is an argument supplied by the caller. Any value keeps the answer correct, because every candidate
  is a divisor of \<open>h\<close> and odd candidates are refused.\<close>

definition pow_sub_entry_exp_mop :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where
  "pow_sub_entry_exp_mop h hcap \<equiv> (PR_CONST snat_gcd_monadic) h hcap"

sepref_register "PR_CONST pow_sub_entry_exp_mop" :: "nat \<Rightarrow> nat \<Rightarrow> nat nres"

sepref_definition pow_sub_entry_exp_impl [llvm_inline] is
  "uncurry pow_sub_entry_exp_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k
     \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding pow_sub_entry_exp_mop_def
  by sepref

lemma pow_sub_entry_exp_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_entry_exp_impl, uncurry (PR_CONST pow_sub_entry_exp_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k
      \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using pow_sub_entry_exp_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The size floor \<open>nfloor\<close>.\<close> The entry pays a fixed overhead on every call (detection, extraction, a
  second output vector and the mirroring), independent of the exponent, so below a size floor substitution
  is not worth attempting.

  The floor is tested after detection: \<open>pow_sub_entry_monadic\<close> below runs \<open>pow_sub_h_monadic\<close> first and then
  \<open>pow_sub_entry_applicable_mop\<close>. Detection's gcd accumulator is absorbing at 1, so on any polynomial with a
  nonzero linear coefficient the loop exits after two iterations.

  \<open>nfloor\<close> is an argument supplied by the caller, and correctness does not depend on it: refusing to
  substitute is always sound.\<close>

text \<open>\<^bold>\<open>The parity test \<open>2 \<le> par\<close>, and why it is needed for soundness.\<close>

  \<open>2 \<le> d\<close> alone does not imply that \<open>d\<close> is even unless \<open>hcap\<close> is a power of two, and \<open>hcap\<close> is supplied by
  the caller. Counterexample: \<open>P(x) = x\<^sup>6 + 992x\<^sup>3 - 8000 = (x-2)(x+10)(\<dots>)\<close>, real roots \<open>+2\<close> and \<open>-10\<close>, detected
  \<open>h = 3\<close>. With \<open>hcap = 9\<close>, \<open>d = gcd(3, 9) = 3\<close> is odd and \<open>\<ge> 2\<close>; substituting would return a positive window
  bracketing \<open>+2\<close> together with its mirror \<open>[-6, 0]\<close>, in which \<open>P\<close> has no root, and miss the root at \<open>-10\<close>.

  \<^bold>\<open>Why odd \<open>d\<close> fails.\<close> For odd \<open>d\<close>, \<open>x \<mapsto> x\<^sup>d\<close> is a bijection on \<open>\<real>\<close>, so the negative roots of the reduced
  polynomial lift to the negative roots of \<open>P\<close>; but this entry discards the reduced solve's negative vector
  and mirrors the positive one, which is correct only when \<open>x \<mapsto> x\<^sup>d\<close> is 2-to-1 through the origin, i.e. when
  \<open>d\<close> is even.

  \<^bold>\<open>The condition is on \<open>d\<close>, not on \<open>h\<close>\<close>, since the back-map uses \<open>d\<close>: \<open>h = 6\<close> with \<open>hcap = 9\<close> gives \<open>d = 3\<close>.

  \<open>d\<close> is even iff \<open>gcd(d, 2) = 2\<close>; the caller computes \<open>par = gcd(d, 2)\<close> and this op tests \<open>2 \<le> par\<close>.

  \<open>2 \<le> h\<close> is still needed: detection returns \<open>h = 0\<close> on a constant, and \<open>gcd(0, hcap) = hcap\<close>, so \<open>h = 0\<close>
  would otherwise pass at any even \<open>hcap\<close>.\<close>

definition pow_sub_entry_applicable_mop ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
  "pow_sub_entry_applicable_mop h par d nfloor len \<equiv>
     RETURN (2 \<le> h \<and> 2 \<le> par \<and> 2 \<le> d \<and> nfloor \<le> len)"

sepref_register "PR_CONST pow_sub_entry_applicable_mop"
  :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres"

sepref_definition pow_sub_entry_applicable_impl [llvm_inline] is
  "uncurry4 pow_sub_entry_applicable_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k
     \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_entry_applicable_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma pow_sub_entry_applicable_impl_hnr[sepref_fr_rules]:
  "(uncurry4 pow_sub_entry_applicable_impl,
    uncurry4 (PR_CONST pow_sub_entry_applicable_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k
      \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_entry_applicable_impl.refine by (simp add: PR_CONST_def)

text \<open>The reading \<open>2 \<le> gcd d 2 \<longleftrightarrow> even d\<close> is not stated as a lemma here: this theory is on the export
  build path, and the simp proof of it is slow. It belongs with the soundness proofs that use it.\<close>

section \<open>The substituting arm\<close>

text \<open>\<^bold>\<open>Ownership.\<close> \<open>xs\<close> is KEPT (the caller owns the input coefficients). \<open>q\<close> is freshly
  allocated by the extraction and freed here. The reduced solve returns THREE owned things:
  \<open>Q\<close>'s positive vector (consumed by the back-map, which KEEPS it, so this op frees it),
  \<open>Q\<close>'s negative vector (\<^bold>\<open>freed unused\<close> — for even \<open>h\<close> a negative \<open>Q\<close>-root has no real \<open>h\<close>-th
  root, so it lifts to nothing), and the origin flag, which is pure and passes through.

  \<^bold>\<open>Every bound result is ASSERTed on the BOUND VARIABLE, never on the expression that produced
  it\<close> — a monadic bind result carries only \<open>bind_ref_tag\<close>, a tag and not an equation, so an
  \<open>ASSERT\<close> about \<open>length (extract h xs)\<close> could not discharge the back-map's HNR precondition on
  \<open>q\<close>. Same fix as \<open>pow_sub_iv_search_mop\<close>'s \<open>mcap\<close> and \<open>pow_sub_extract_monadic\<close>'s \<open>outlen\<close>.\<close>

definition pow_sub_entry_sub_mop ::
  "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow>
     (gmp_dyadic_interval_vec \<times> bool \<times> bool) nres" where
  "pow_sub_entry_sub_mop h dlt xs \<equiv> doN {
     ASSERT (0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> 0 < length xs \<and> length xs < max_snat LENGTH(gmp_poly_len));
     q \<leftarrow> (PR_CONST pow_sub_extract_monadic) h xs;
     ASSERT (0 < length q
             \<and> length q + 1 < max_snat LENGTH(gmp_poly_len));
     \<comment> \<open>The inner solve is the deflating pipeline.\<close>
     r \<leftarrow> (PR_CONST defl_isolate_all_split_main) q;
     case r of (accQP, accQN, xs0) \<Rightarrow> doN {
       (PR_CONST dyadic_interval_vec_free_monadic) accQN;
       ob \<leftarrow> (PR_CONST pow_sub_backmap_all_monadic) h q dlt accQP;
       case ob of (out, ok) \<Rightarrow> doN {
         (PR_CONST dyadic_interval_vec_free_monadic) accQP;
         (PR_CONST poly_free_monadic) q;
         RETURN (out, xs0, ok)
       }
     }
   }"

sepref_register "PR_CONST pow_sub_entry_sub_mop"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> bool \<times> bool) nres"

text \<open>\<^bold>\<open>No declared HNR precondition: the bounds are the internal ASSERTs above.\<close> A declared
  \<open>0 < h \<and> h < max_snat \<dots>\<close> precondition leaves both arms of the entry's branch untranslated: at the call site
  \<open>h\<close> is known only as \<open>bind_ref_tag xa (pow_sub_entry_applicable_mop $ x)\<close>, a tag rather than an equation, so
  \<open>0 < h\<close> is not derivable there; with \<open>trans_keep\<close> the unsolved side condition leaves the arm schematic, and
  \<open>sepref_dbg_opt\<close> fails on the merge. With no declared precondition, @{thm hn_ASSERT_bind} turns the internal
  ASSERTs into assumptions that feed the callees' preconditions, as in the loop bodies below.

  Abstractly this op fails when \<open>h = 0\<close>. That is intended: it is called only when the applicability test
  holds, and that branch condition is available to the abstract correctness proof; only synthesis cannot
  see it.\<close>

sepref_definition pow_sub_entry_sub_impl [llvm_code] is
  "uncurry2 pow_sub_entry_sub_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn"
  unfolding pow_sub_entry_sub_mop_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  (* The callee HNR is supplied explicitly. *)
  supply [sepref_fr_rules] = defl_isolate_all_split_main_impl_hnr
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

lemma pow_sub_entry_sub_impl_hnr[sepref_fr_rules]:
  "(uncurry2 pow_sub_entry_sub_impl, uncurry2 (PR_CONST pow_sub_entry_sub_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn"
  using pow_sub_entry_sub_impl.refine by (simp add: PR_CONST_def)

section \<open>The non-substituting arm\<close>

text \<open>Returns an empty vector and \<open>ok = False\<close>. It allocates rather than returning nothing because both
  arms of the entry's branch must return the same owned shape; an \<open>if\<close> whose arms carry different ownership
  does not translate. The allocation is one empty array-list pair, paid only on the non-substituting path.\<close>

definition pow_sub_entry_bail_mop ::
  "nat \<Rightarrow> (gmp_dyadic_interval_vec \<times> bool \<times> bool) nres" where
  "pow_sub_entry_bail_mop n \<equiv> doN {
     out \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) n;
     RETURN (out, False, False)
   }"

sepref_register "PR_CONST pow_sub_entry_bail_mop"
  :: "nat \<Rightarrow> (gmp_dyadic_interval_vec \<times> bool \<times> bool) nres"

sepref_definition pow_sub_entry_bail_impl [llvm_inline] is
  "pow_sub_entry_bail_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
     gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn"
  unfolding pow_sub_entry_bail_mop_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma pow_sub_entry_bail_impl_hnr[sepref_fr_rules]:
  "(pow_sub_entry_bail_impl, PR_CONST pow_sub_entry_bail_mop) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn"
  using pow_sub_entry_bail_impl.refine by (simp add: PR_CONST_def)

section \<open>The entry\<close>

text \<open>\<^bold>\<open>Each \<open>if\<close>-arm is a single registered op call\<close>, and the branch condition is a bound variable, not an
  inline comparison. The exponent is passed to the substituting arm as a variable, so no numeral has to
  reach the call site.\<close>

definition pow_sub_entry_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> bool \<times> bool) nres" where
  "pow_sub_entry_monadic nfloor hcap dlt xs \<equiv> doN {
     ASSERT (0 < length xs \<and> length xs < max_snat LENGTH(gmp_poly_len));
     len \<leftarrow> (PR_CONST poly_length_monadic) xs;
     ASSERT (len = length xs);
     h \<leftarrow> (PR_CONST pow_sub_h_monadic) xs;
     ASSERT (h < max_snat LENGTH(gmp_poly_len));
     d \<leftarrow> (PR_CONST pow_sub_entry_exp_mop) h hcap;
     ASSERT (d < max_snat LENGTH(gmp_poly_len));
     par \<leftarrow> (PR_CONST snat_gcd_monadic) d 2;
     ASSERT (par < max_snat LENGTH(gmp_poly_len));
     b \<leftarrow> (PR_CONST pow_sub_entry_applicable_mop) h par d nfloor len;
     if b then (PR_CONST pow_sub_entry_sub_mop) d dlt xs
     else (PR_CONST pow_sub_entry_bail_mop) d
   }"

sepref_register "PR_CONST pow_sub_entry_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> bool \<times> bool) nres"

sepref_definition pow_sub_entry_impl [llvm_code] is
  "uncurry3 pow_sub_entry_monadic" ::
  "[\<lambda>(((nfloor, hcap), dlt), xs).
      0 < length xs \<and> length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn"
  unfolding pow_sub_entry_monadic_def
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

lemma pow_sub_entry_impl_hnr[sepref_fr_rules]:
  "(uncurry3 pow_sub_entry_impl, uncurry3 (PR_CONST pow_sub_entry_monadic)) \<in>
    [\<lambda>(((nfloor, hcap), dlt), xs).
      0 < length xs \<and> length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn \<times>\<^sub>a bool1_assn"
  using pow_sub_entry_impl.refine by (simp add: PR_CONST_def)

end
