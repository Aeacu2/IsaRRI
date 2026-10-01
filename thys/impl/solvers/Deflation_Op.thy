theory Deflation_Op
  imports IsaRRI_LLVM.Poly_Ops "IsaRRI_Spec.Deflation_Kernel"
begin

section \<open>The monadic deflation op\<close>

text \<open>Refines @{const defl_half_list}, the division of the node's carried (local-frame, integer)
  polynomial by \<open>1 - 2x\<close>, as one left-to-right pass over the coefficient vector.

  \<^bold>\<open>The accumulator is carried in the loop state, as an \<open>int\<close>\<close>, like
  @{const poly_ruffini_with_prev_monadic}'s \<open>prev\<close>. Reading it back out of the output vector would
  cost a \<open>poly_copy_coeff\<close> (an \<open>mpz_init_set\<close>: an allocation and a limb copy) per iteration for a value
  already held.

  \<^bold>\<open>Two GMP-layer constraints shape the body, both about ownership.\<close>

  \<^item> \<^bold>\<open>There is no mpz subtraction.\<close> \<open>mpz_add_monadic\<close> (\<open>r + a\<close>) and \<open>mpz_addmul_monadic\<close> (\<open>r + a * b\<close>)
    are the primitives; \<open>mpz_sub_ui_snat_monadic\<close> subtracts a small \<open>nat\<close>. This is why the kernel
    divides by \<open>1 - 2x\<close> rather than \<open>2x - 1\<close>: the recurrence becomes \<open>s\<^sub>i = q\<^sub>i + 2s\<^sub>i\<^sub>-\<^sub>1\<close>, two additions.

  \<^item> \<^bold>\<open>The accumulator is consumed last.\<close> @{const poly_push_coeff_monadic} takes its value destructively
    (\<open>mpzb_assn\<^sup>d\<close>: the value is stored into the vector, not copied), so a body that pushes \<open>s\<close> and then
    computes \<open>s' = \<dots> s \<dots>\<close> uses a consumed operand and cannot be synthesised. So both additions come
    first (\<open>s\<close> is in @{const mpz_add_monadic}'s kept position in each) and \<open>s\<close> is pushed afterwards.
    Writing the doubling as \<open>mpz_add_monadic s s\<close> is not synthesisable, since it puts one value in a
    destructive and a kept position at once; \<open>(q + s) + s\<close> keeps the accumulator kept in both.

  \<^bold>\<open>The op returns the certificate with the quotient.\<close> The final accumulator is
  @{const defl_half_cert}, and by @{thm [source] defl_half_cert_eq_zero_iff} the caller decides
  deflation from it with one integer test.\<close>

subsection \<open>The loop\<close>

text \<open>\<^bold>\<open>The loop is shaped for Sepref\<close>: state \<open>(j, dst, s)\<close>, a registered condition, a registered body
  taking the state destructively, and a registered projection for the tail, as in
  \<open>pow_sub_backmap_run_monadic\<close> (\<open>Power_Sub_Emit_All_Impl\<close>). This gets the loop's HNR from
  \<open>sepref_definition\<close> instead of a hand-written loop body and HNR with explicit \<open>exI\<close> witnesses, as
  @{const poly_ruffini_with_prev_monadic} has.\<close>

abbreviation defl_half_state_assn where
"defl_half_state_assn \<equiv>
   snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a mpzb_assn"

definition defl_half_cond :: "nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> bool" where
"defl_half_cond n st \<equiv> (let (j, dst, s) = st in j < n)"

definition defl_half_body_mop ::
  "gmp_poly \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> (nat \<times> gmp_poly \<times> int) nres" where
"defl_half_body_mop xs st \<equiv> doN {
   let (j, dst, s) = st;
   ASSERT (j < length xs);
   ASSERT (j + 1 < max_snat LENGTH(gmp_poly_len));
   ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
   q \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs j;
   a \<leftarrow> (PR_CONST mpz_add_monadic) q s;
   s' \<leftarrow> (PR_CONST mpz_add_monadic) a s;
   dst \<leftarrow> (PR_CONST poly_push_coeff_monadic) dst s;
   RETURN (j + 1, dst, s')
 }"

definition defl_half_result_mop ::
  "nat \<times> gmp_poly \<times> int \<Rightarrow> (gmp_poly \<times> int) nres" where
"defl_half_result_mop st \<equiv> (let (j, dst, s) = st in RETURN (dst, s))"

text \<open>The invariant, stated so that the body step IS @{thm defl_half_aux.simps}: what has been
  emitted, concatenated with what the remaining suffix will emit, is the whole quotient — and the
  accumulator's own remainder over the suffix is the whole certificate.\<close>

definition defl_half_invar :: "gmp_poly \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> bool" where
"defl_half_invar xs st \<longleftrightarrow>
   (let (j, dst, s) = st in
      1 \<le> j \<and> j \<le> length xs
      \<and> length dst = j - 1
      \<and> dst @ defl_half_aux s (drop j xs) = defl_half_list xs
      \<and> defl_half_rem s (drop j xs) = defl_half_cert xs)"

definition defl_half_monadic :: "gmp_poly \<Rightarrow> (gmp_poly \<times> int) nres" where
"defl_half_monadic xs \<equiv> doN {
   ASSERT (xs \<noteq> []);
   ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
   n \<leftarrow> (PR_CONST poly_length_monadic) xs;
   s0 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 0;
   dst0 \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
   st \<leftarrow> WHILEIT (defl_half_invar xs)
            (\<lambda>st. (PR_CONST defl_half_cond) n st)
            (\<lambda>st. (PR_CONST defl_half_body_mop) xs st)
            (1, dst0, s0);
   (PR_CONST defl_half_result_mop) st
 }"

subsection \<open>Correctness\<close>

lemma defl_half_invar_init:
  assumes "xs \<noteq> []"
  shows "defl_half_invar xs (1, [], xs ! 0)"
proof -
  obtain q qs' where xs: "xs = q # qs'" using assms by (cases xs) auto
  have "drop 1 xs = qs'" by (simp add: xs)
  moreover have "xs ! 0 = q" by (simp add: xs)
  ultimately show ?thesis
    by (simp add: defl_half_invar_def xs defl_half_list_def defl_half_cert_def)
qed

text \<open>\<^bold>\<open>Stated in simp-normal form, \<open>2 * s + xs ! j\<close>, not in the shape the body computes
  (\<open>(xs ! j + s) + s\<close>).\<close> \<open>simp_all\<close> in the VCG below normalises the goal's accumulator to
  \<open>2 * s + xs ! j\<close>, so a lemma in the body's shape would not match.

  The two \<open>drop\<close> lemmas close the step goals: they are pure rewrites on @{const defl_half_aux} /
  @{const defl_half_rem}, so they fire whether or not the invariant has been unfolded.\<close>

lemma defl_half_aux_drop_step:
  assumes "j < length xs"
  shows "defl_half_aux s (drop j xs) = s # defl_half_aux (2 * s + xs ! j) (drop (Suc j) xs)"
proof -
  have "drop j xs = xs ! j # drop (Suc j) xs"
    using assms by (simp add: Cons_nth_drop_Suc)
  thus ?thesis by (simp add: algebra_simps)
qed

lemma defl_half_rem_drop_step:
  assumes "j < length xs"
  shows "defl_half_rem s (drop j xs) = defl_half_rem (2 * s + xs ! j) (drop (Suc j) xs)"
proof -
  have "drop j xs = xs ! j # drop (Suc j) xs"
    using assms by (simp add: Cons_nth_drop_Suc)
  thus ?thesis by (simp add: algebra_simps)
qed

lemma defl_half_invar_step:
  assumes inv: "defl_half_invar xs (j, dst, s)"
      and lt:  "j < length xs"
  shows "defl_half_invar xs (Suc j, dst @ [s], 2 * s + xs ! j)"
  using inv lt
  by (auto simp: defl_half_invar_def defl_half_aux_drop_step defl_half_rem_drop_step)

lemma defl_half_invar_exit:
  assumes inv: "defl_half_invar xs (j, dst, s)"
      and done_: "\<not> j < length xs"
  shows "dst = defl_half_list xs \<and> s = defl_half_cert xs"
proof -
  from inv have jn: "j \<le> length xs"
            and dq: "dst @ defl_half_aux s (drop j xs) = defl_half_list xs"
            and dr: "defl_half_rem s (drop j xs) = defl_half_cert xs"
    by (auto simp: defl_half_invar_def)
  from jn done_ have "drop j xs = []" by simp
  thus ?thesis using dq dr by simp
qed

theorem defl_half_monadic_correct:
  assumes ne: "xs \<noteq> []"
      and bnd: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_half_monadic xs
           \<le> SPEC (\<lambda>(dst, c). dst = defl_half_list xs \<and> c = defl_half_cert xs)"
  unfolding defl_half_monadic_def defl_half_body_mop_def defl_half_cond_def
            defl_half_result_mop_def
            poly_length_monadic_def poly_copy_coeff_monadic_def
            poly_empty_sz_monadic_def poly_push_coeff_monadic_def
            mpz_add_monadic_def PR_CONST_def
  apply (refine_vcg
           WHILEIT_rule[where R = "measure (\<lambda>(j, dst, s). length xs - j)"])
  using ne bnd
  \<comment> \<open>\<open>simp_all\<close>, then ONE ordering-INDEPENDENT closer: a fixed \<open>subgoal\<close> chain depends on how
      many goals \<open>simp_all\<close> closes, while \<open>auto\<close> is goal-global.\<close>
  apply (simp_all add: defl_half_invar_init defl_half_invar_step)
  by (auto simp: defl_half_invar_def defl_half_list_def defl_half_cert_def neq_Nil_conv
                 defl_half_aux_drop_step defl_half_rem_drop_step
           dest: defl_half_invar_exit)

text \<open>\<^bold>\<open>What this buys, stated as the caller will use it.\<close> On a zero certificate the op has
  produced an exact quotient — and by @{thm [source] defl_half_cert_eq_zero_iff} a zero
  certificate is EQUIVALENT to \<open>1/2\<close> being a root, so the runtime test refuses nothing the
  abstract recursion would have deflated.\<close>

corollary defl_half_monadic_exact:
  assumes ne: "xs \<noteq> []"
      and bnd: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_half_monadic xs
           \<le> SPEC (\<lambda>(dst, c). c = 0 \<longrightarrow> Poly xs = [:1, -2:] * Poly dst)"
  apply (rule order_trans[OF defl_half_monadic_correct[OF ne bnd]])
  by (auto simp: defl_half_exact)

subsection \<open>The certificate ALONE — no quotient, no allocation\<close>

text \<open>\<^bold>\<open>Why this op exists.\<close> @{const defl_half_monadic} produces the quotient and the certificate in
  one pass. But the caller needs the quotient only when the certificate vanishes, and building it costs
  a fresh vector plus one \<open>mpz_init_set\<close> per coefficient (@{const poly_copy_coeff_monadic} into
  @{const poly_push_coeff_monadic}), all freed again on the path that does not deflate.

  This op runs the same recurrence carrying only the accumulator, so the path that does not deflate
  allocates one \<open>mpz\<close> and touches no vector. The input is borrowed throughout.\<close>

definition defl_cert_body :: "gmp_poly \<Rightarrow> nat \<times> int \<Rightarrow> (nat \<times> int) nres" where
"defl_cert_body xs st \<equiv> doN {
   let (j, s) = st;
   ASSERT (j < length xs);
   ASSERT (j + 1 < max_snat LENGTH(gmp_poly_len));
   q \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs j;
   a \<leftarrow> (PR_CONST mpz_add_monadic) q s;
   s' \<leftarrow> (PR_CONST mpz_add_monadic) a s;
   \<comment> \<open>Nothing consumes the old accumulator here — there is no push — so it must be freed
      explicitly. It sits in the KEPT slot of both additions, exactly as in
      @{const defl_half_body_mop}, and is discarded only after the second one has read it.\<close>
   (PR_CONST mpzb_discard_monadic) s;
   RETURN (j + 1, s')
 }"

definition defl_cert_invar :: "gmp_poly \<Rightarrow> nat \<times> int \<Rightarrow> bool" where
"defl_cert_invar xs st \<longleftrightarrow>
   (let (j, s) = st in
      1 \<le> j \<and> j \<le> length xs
      \<and> defl_half_rem s (drop j xs) = defl_half_cert xs)"

abbreviation defl_cert_state_assn where
"defl_cert_state_assn \<equiv> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a mpzb_assn"

definition defl_cert_cond :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> bool" where
"defl_cert_cond n st \<equiv> (let (j, s) = st in j < n)"

definition defl_cert_result_mop :: "nat \<times> int \<Rightarrow> int nres" where
"defl_cert_result_mop st \<equiv> (let (j, s) = st in RETURN s)"

definition defl_cert_monadic :: "gmp_poly \<Rightarrow> int nres" where
"defl_cert_monadic xs \<equiv> doN {
   ASSERT (xs \<noteq> []);
   ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
   n \<leftarrow> (PR_CONST poly_length_monadic) xs;
   s0 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 0;
   st \<leftarrow> WHILEIT (defl_cert_invar xs)
            (\<lambda>st. (PR_CONST defl_cert_cond) n st)
            (\<lambda>st. (PR_CONST defl_cert_body) xs st)
            (1, s0);
   (PR_CONST defl_cert_result_mop) st
 }"

lemma defl_cert_invar_init:
  assumes "xs \<noteq> []"
  shows "defl_cert_invar xs (1, xs ! 0)"
proof -
  obtain q qs' where xs: "xs = q # qs'" using assms by (cases xs) auto
  show ?thesis by (simp add: defl_cert_invar_def xs defl_half_cert_def)
qed

lemma defl_cert_invar_step:
  assumes inv: "defl_cert_invar xs (j, s)"
      and lt:  "j < length xs"
  shows "defl_cert_invar xs (Suc j, 2 * s + xs ! j)"
  using inv lt by (auto simp: defl_cert_invar_def defl_half_rem_drop_step)

lemma defl_cert_invar_exit:
  assumes inv: "defl_cert_invar xs (j, s)"
      and done_: "\<not> j < length xs"
  shows "s = defl_half_cert xs"
proof -
  from inv have jn: "j \<le> length xs"
            and dr: "defl_half_rem s (drop j xs) = defl_half_cert xs"
    by (auto simp: defl_cert_invar_def)
  from jn done_ have "drop j xs = []" by simp
  thus ?thesis using dr by simp
qed

theorem defl_cert_monadic_correct:
  assumes ne: "xs \<noteq> []"
      and bnd: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_cert_monadic xs \<le> SPEC (\<lambda>c. c = defl_half_cert xs)"
  unfolding defl_cert_monadic_def defl_cert_body_def defl_cert_cond_def
            defl_cert_result_mop_def
            poly_length_monadic_def poly_copy_coeff_monadic_def
            mpz_add_monadic_def mpzb_discard_monadic_def PR_CONST_def
  apply (refine_vcg
           WHILEIT_rule[where R = "measure (\<lambda>(j, s). length xs - j)"])
  using ne bnd
  apply (simp_all add: defl_cert_invar_init defl_cert_invar_step)
  by (auto simp: defl_cert_invar_def defl_half_cert_def neq_Nil_conv
                 defl_half_rem_drop_step
           dest: defl_cert_invar_exit)

subsection \<open>Synthesis\<close>

text \<open>\<^bold>\<open>Four registered ops, then the loop.\<close> Each of the three inner ops has both a
  \<open>sepref_register\<close> and a \<open>[sepref_fr_rules]\<close> HNR; with only one of the two, synthesis fails with
  \<^emph>\<open>"Failed to apply initial proof method"\<close>, which does not name the missing registration.

  The \<open>sepref_dbg_*\<close> chain replaces a bare \<open>by sepref\<close> on the two ops with side conditions, because a
  body op fires only if all its side conditions solve, and the non-\<open>dbg\<close> step does not show which one
  failed.\<close>

sepref_register "PR_CONST defl_half_cond"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> bool"

sepref_definition defl_half_cond_impl [llvm_inline] is
  "uncurry (RETURN oo defl_half_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a defl_half_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding defl_half_cond_def
  unfolding Let_def
  by sepref

lemma defl_half_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry defl_half_cond_impl, uncurry (RETURN oo (PR_CONST defl_half_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a defl_half_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using defl_half_cond_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The body's declared precondition mentions only \<open>xs\<close>, never the state.\<close> The state-dependent
  facts (\<open>j < length xs\<close>, \<open>j + 1 < max_snat\<close>, and the push's capacity) are ASSERTed inside the op, the
  only place they can live: at synthesis time the body runs under the invariant alone, and the loop
  condition is not in scope.\<close>

sepref_register "PR_CONST defl_half_body_mop"
  :: "gmp_poly \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> (nat \<times> gmp_poly \<times> int) nres"

sepref_definition defl_half_body_impl [llvm_inline] is
  "uncurry defl_half_body_mop" ::
  "[\<lambda>(xs, st). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a defl_half_state_assn\<^sup>d \<rightarrow> defl_half_state_assn"
  unfolding defl_half_body_mop_def
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

lemma defl_half_body_impl_hnr[sepref_fr_rules]:
  "(uncurry defl_half_body_impl, uncurry (PR_CONST defl_half_body_mop)) \<in>
    [\<lambda>(xs, st). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a defl_half_state_assn\<^sup>d \<rightarrow> defl_half_state_assn"
  using defl_half_body_impl.refine by (simp add: PR_CONST_def)

text \<open>The post-loop projection is a registered op, not an inline destructure: the state is taken
  DESTRUCTIVELY, and the discarded component is the pure index.\<close>

sepref_register "PR_CONST defl_half_result_mop"
  :: "nat \<times> gmp_poly \<times> int \<Rightarrow> (gmp_poly \<times> int) nres"

sepref_definition defl_half_result_impl [llvm_inline] is
  "defl_half_result_mop" ::
  "defl_half_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  unfolding defl_half_result_mop_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma defl_half_result_impl_hnr[sepref_fr_rules]:
  "(defl_half_result_impl, PR_CONST defl_half_result_mop) \<in>
    defl_half_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  using defl_half_result_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_half_monadic"
  :: "gmp_poly \<Rightarrow> (gmp_poly \<times> int) nres"

sepref_definition defl_half_impl [llvm_code] is
  "defl_half_monadic" ::
  "[\<lambda>xs. xs \<noteq> [] \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  unfolding defl_half_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    defl_half_cond_impl_hnr defl_half_body_impl_hnr defl_half_result_impl_hnr
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

lemma defl_half_impl_hnr[sepref_fr_rules]:
  "(defl_half_impl, PR_CONST defl_half_monadic) \<in>
    [\<lambda>xs. xs \<noteq> [] \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  using defl_half_impl.refine by (simp add: PR_CONST_def)

subsection \<open>Synthesis — the certificate-only pass\<close>

sepref_register "PR_CONST defl_cert_cond" :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> bool"

sepref_definition defl_cert_cond_impl [llvm_inline] is
  "uncurry (RETURN oo defl_cert_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a defl_cert_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding defl_cert_cond_def
  unfolding Let_def
  by sepref

lemma defl_cert_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry defl_cert_cond_impl, uncurry (RETURN oo (PR_CONST defl_cert_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a defl_cert_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using defl_cert_cond_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_cert_body"
  :: "gmp_poly \<Rightarrow> nat \<times> int \<Rightarrow> (nat \<times> int) nres"

sepref_definition defl_cert_body_impl [llvm_inline] is
  "uncurry defl_cert_body" ::
  "[\<lambda>(xs, st). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a defl_cert_state_assn\<^sup>d \<rightarrow> defl_cert_state_assn"
  unfolding defl_cert_body_def
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

lemma defl_cert_body_impl_hnr[sepref_fr_rules]:
  "(uncurry defl_cert_body_impl, uncurry (PR_CONST defl_cert_body)) \<in>
    [\<lambda>(xs, st). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a defl_cert_state_assn\<^sup>d \<rightarrow> defl_cert_state_assn"
  using defl_cert_body_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_cert_result_mop" :: "nat \<times> int \<Rightarrow> int nres"

sepref_definition defl_cert_result_impl [llvm_inline] is
  "defl_cert_result_mop" ::
  "defl_cert_state_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  unfolding defl_cert_result_mop_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma defl_cert_result_impl_hnr[sepref_fr_rules]:
  "(defl_cert_result_impl, PR_CONST defl_cert_result_mop) \<in>
    defl_cert_state_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  using defl_cert_result_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_cert_monadic" :: "gmp_poly \<Rightarrow> int nres"

sepref_definition defl_cert_impl [llvm_code] is
  "defl_cert_monadic" ::
  "[\<lambda>xs. xs \<noteq> [] \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> mpzb_assn"
  unfolding defl_cert_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    defl_cert_cond_impl_hnr defl_cert_body_impl_hnr defl_cert_result_impl_hnr
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

lemma defl_cert_impl_hnr[sepref_fr_rules]:
  "(defl_cert_impl, PR_CONST defl_cert_monadic) \<in>
    [\<lambda>xs. xs \<noteq> [] \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> mpzb_assn"
  using defl_cert_impl.refine by (simp add: PR_CONST_def)

section \<open>The left child's pass: division by \<open>1 - x\<close>\<close>

text \<open>\<^bold>\<open>Why deflation acts on the children.\<close> @{const defl_cert_monadic} decides the branch before the
  children are built, but it need not: \<open>carried_right xs ! 0\<close>, which \<open>truncate_children_mid_monadic\<close>
  reads (borrowed, without cost) from an already-built child, is the same integer
  (\<open>Deflation_Bridge.carried_right_nth0_eq_defl_one_cert\<close>). So the decision is free, and the deflation
  moves onto the children, where the shed root lies at a box endpoint:

    \<^item> the right child is divisible by \<open>x\<close>: drop the head, no arithmetic;
    \<^item> the left child is divisible by \<open>1 - x\<close>: this op.

  A node that does not shed runs no deflation code.

  \<^bold>\<open>One addition per coefficient\<close>, against the midpoint kernel's two, and the accumulator is a
  partial sum rather than a doubling, so it does not gain a bit per step. Ownership is as in the
  midpoint op: \<open>poly_push_coeff_monadic\<close> takes its value destructively, so the addition that reads \<open>s\<close>
  comes first and the push last.\<close>

subsection \<open>The loop\<close>

definition defl_one_cond :: "nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> bool" where
"defl_one_cond n st \<equiv> (let (j, dst, s) = st in j < n)"

definition defl_one_body_mop ::
  "gmp_poly \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> (nat \<times> gmp_poly \<times> int) nres" where
"defl_one_body_mop xs st \<equiv> doN {
   let (j, dst, s) = st;
   ASSERT (j < length xs);
   ASSERT (j + 1 < max_snat LENGTH(gmp_poly_len));
   ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
   q \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs j;
   s' \<leftarrow> (PR_CONST mpz_add_monadic) q s;
   dst \<leftarrow> (PR_CONST poly_push_coeff_monadic) dst s;
   RETURN (j + 1, dst, s')
 }"

definition defl_one_result_mop ::
  "nat \<times> gmp_poly \<times> int \<Rightarrow> (gmp_poly \<times> int) nres" where
"defl_one_result_mop st \<equiv> (let (j, dst, s) = st in RETURN (dst, s))"

definition defl_one_invar :: "gmp_poly \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> bool" where
"defl_one_invar xs st \<longleftrightarrow>
   (let (j, dst, s) = st in
      1 \<le> j \<and> j \<le> length xs
      \<and> length dst = j - 1
      \<and> dst @ defl_one_aux s (drop j xs) = defl_one_list xs
      \<and> defl_one_rem s (drop j xs) = defl_one_cert xs)"

definition defl_one_monadic :: "gmp_poly \<Rightarrow> (gmp_poly \<times> int) nres" where
"defl_one_monadic xs \<equiv> doN {
   ASSERT (xs \<noteq> []);
   ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
   n \<leftarrow> (PR_CONST poly_length_monadic) xs;
   s0 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 0;
   dst0 \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
   st \<leftarrow> WHILEIT (defl_one_invar xs)
            (\<lambda>st. (PR_CONST defl_one_cond) n st)
            (\<lambda>st. (PR_CONST defl_one_body_mop) xs st)
            (1, dst0, s0);
   (PR_CONST defl_one_result_mop) st
 }"

subsection \<open>Correctness\<close>

lemma defl_one_invar_init:
  assumes ne: "xs \<noteq> []"
  shows "defl_one_invar xs (1, [], xs ! 0)"
  using ne
  by (cases xs) (auto simp: defl_one_invar_def defl_one_list_def defl_one_cert_def
                            drop_Suc)

text \<open>The two \<open>drop\<close> rewrites again, and again stated on the recursive functions rather than on
  the invariant, so they fire whether or not the invariant has been unfolded.
  The accumulator is written \<open>xs ! j + s\<close>, which is the body's literal order and — unlike
  the doubling step above — is ALSO what \<open>simp_all\<close> leaves standing here: there is no numeral to
  collect, so nothing reorders the sum. Stated as \<open>s + xs ! j\<close>, the step goals would differ from
  their own hypotheses by \<open>add.commute\<close> alone.\<close>

lemma defl_one_aux_drop_step:
  assumes "j < length xs"
  shows "defl_one_aux s (drop j xs) = s # defl_one_aux (xs ! j + s) (drop (Suc j) xs)"
proof -
  have "drop j xs = xs ! j # drop (Suc j) xs"
    using assms by (simp add: Cons_nth_drop_Suc)
  thus ?thesis by (simp add: algebra_simps)
qed

lemma defl_one_rem_drop_step:
  assumes "j < length xs"
  shows "defl_one_rem s (drop j xs) = defl_one_rem (xs ! j + s) (drop (Suc j) xs)"
proof -
  have "drop j xs = xs ! j # drop (Suc j) xs"
    using assms by (simp add: Cons_nth_drop_Suc)
  thus ?thesis by (simp add: algebra_simps)
qed

lemma defl_one_invar_step:
  assumes inv: "defl_one_invar xs (j, dst, s)"
      and lt:  "j < length xs"
  shows "defl_one_invar xs (Suc j, dst @ [s], xs ! j + s)"
  using inv lt
  by (auto simp: defl_one_invar_def defl_one_aux_drop_step defl_one_rem_drop_step)

lemma defl_one_invar_exit:
  assumes inv: "defl_one_invar xs (j, dst, s)"
      and done_: "\<not> j < length xs"
  shows "dst = defl_one_list xs \<and> s = defl_one_cert xs"
proof -
  from inv have jn: "j \<le> length xs"
            and dq: "dst @ defl_one_aux s (drop j xs) = defl_one_list xs"
            and dr: "defl_one_rem s (drop j xs) = defl_one_cert xs"
    by (auto simp: defl_one_invar_def)
  from jn done_ have "drop j xs = []" by simp
  thus ?thesis using dq dr by simp
qed

theorem defl_one_monadic_correct:
  assumes ne: "xs \<noteq> []"
      and bnd: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_one_monadic xs
           \<le> SPEC (\<lambda>(dst, c). dst = defl_one_list xs \<and> c = defl_one_cert xs)"
  unfolding defl_one_monadic_def defl_one_body_mop_def defl_one_cond_def
            defl_one_result_mop_def
            poly_length_monadic_def poly_copy_coeff_monadic_def
            poly_empty_sz_monadic_def poly_push_coeff_monadic_def
            mpz_add_monadic_def PR_CONST_def
  apply (refine_vcg
           WHILEIT_rule[where R = "measure (\<lambda>(j, dst, s). length xs - j)"])
  using ne bnd
  apply (simp_all add: defl_one_invar_init defl_one_invar_step)
  by (auto simp: defl_one_invar_def defl_one_list_def defl_one_cert_def neq_Nil_conv
                 defl_one_aux_drop_step defl_one_rem_drop_step
           dest: defl_one_invar_exit)

text \<open>\<^bold>\<open>The form the caller consumes.\<close> The caller does not test this certificate — it already
  holds the value, as \<open>mids\<close> — so what it needs is the exactness that follows from the read
  being zero. \<open>Deflation_Bridge.defl_left_child_exact\<close> is the same statement with the read
  substituted for the certificate.\<close>

corollary defl_one_monadic_exact:
  assumes ne: "xs \<noteq> []"
      and bnd: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_one_monadic xs
           \<le> SPEC (\<lambda>(dst, c). c = poly (Poly xs) 1
                              \<and> (c = 0 \<longrightarrow> Poly xs = [:1, -1:] * Poly dst))"
  apply (rule order_trans[OF defl_one_monadic_correct[OF ne bnd]])
  by (auto simp: defl_one_exact defl_one_cert_eq_poly_1)

subsection \<open>Synthesis\<close>

text \<open>The state has the half pass's shape exactly, so it reuses @{term defl_half_state_assn} rather than
  declaring an identical twin — one abbreviation, two loops.\<close>

sepref_register "PR_CONST defl_one_cond"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> bool"

sepref_definition defl_one_cond_impl [llvm_inline] is
  "uncurry (RETURN oo defl_one_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a defl_half_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding defl_one_cond_def
  unfolding Let_def
  by sepref

lemma defl_one_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry defl_one_cond_impl, uncurry (RETURN oo (PR_CONST defl_one_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a defl_half_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using defl_one_cond_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_one_body_mop"
  :: "gmp_poly \<Rightarrow> nat \<times> gmp_poly \<times> int \<Rightarrow> (nat \<times> gmp_poly \<times> int) nres"

sepref_definition defl_one_body_impl [llvm_inline] is
  "uncurry defl_one_body_mop" ::
  "[\<lambda>(xs, st). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a defl_half_state_assn\<^sup>d \<rightarrow> defl_half_state_assn"
  unfolding defl_one_body_mop_def
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

lemma defl_one_body_impl_hnr[sepref_fr_rules]:
  "(uncurry defl_one_body_impl, uncurry (PR_CONST defl_one_body_mop)) \<in>
    [\<lambda>(xs, st). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a defl_half_state_assn\<^sup>d \<rightarrow> defl_half_state_assn"
  using defl_one_body_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_one_result_mop"
  :: "nat \<times> gmp_poly \<times> int \<Rightarrow> (gmp_poly \<times> int) nres"

sepref_definition defl_one_result_impl [llvm_inline] is
  "defl_one_result_mop" ::
  "defl_half_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  unfolding defl_one_result_mop_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma defl_one_result_impl_hnr[sepref_fr_rules]:
  "(defl_one_result_impl, PR_CONST defl_one_result_mop) \<in>
    defl_half_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  using defl_one_result_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_one_monadic"
  :: "gmp_poly \<Rightarrow> (gmp_poly \<times> int) nres"

sepref_definition defl_one_impl [llvm_code] is
  "defl_one_monadic" ::
  "[\<lambda>xs. xs \<noteq> [] \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  unfolding defl_one_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    defl_one_cond_impl_hnr defl_one_body_impl_hnr defl_one_result_impl_hnr
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

lemma defl_one_impl_hnr[sepref_fr_rules]:
  "(defl_one_impl, PR_CONST defl_one_monadic) \<in>
    [\<lambda>xs. xs \<noteq> [] \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn \<times>\<^sub>a mpzb_assn"
  using defl_one_impl.refine by (simp add: PR_CONST_def)

section \<open>The right child's deflation: dropping the head\<close>

text \<open>The right child's shed root is at its box's left endpoint, so the divisor is \<open>x\<close> and the quotient
  is @{term "tl xs"} (\<open>Deflation_Kernel.defl_drop0_exact\<close>). There is no arithmetic, but there is no
  \<open>tl\<close> on a \<open>gmp_poly\<close> either, so this loop builds the tail from the existing vector primitives, at \<open>n\<close>
  \<open>mpz_init_set\<close>s and no additions. The cost is incurred only on a node that sheds.\<close>

abbreviation defl_drop_state_assn where
"defl_drop_state_assn \<equiv> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"

definition defl_drop_cond :: "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool" where
"defl_drop_cond n st \<equiv> (let (j, dst) = st in j < n)"

definition defl_drop_body_mop ::
  "gmp_poly \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> (nat \<times> gmp_poly) nres" where
"defl_drop_body_mop xs st \<equiv> doN {
   let (j, dst) = st;
   ASSERT (j < length xs);
   ASSERT (j + 1 < max_snat LENGTH(gmp_poly_len));
   ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
   q \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs j;
   \<comment> \<open>\<^bold>\<open>Negate while copying.\<close> The right child comes out \<open>-2\<close> times the one the deflate-then-dilate
      order produces, so the subsequent halving divides by \<open>-2\<close>. The sign matters because
      \<open>carried_retrunc_mop\<close> drops low bits, i.e. floors: a small positive coefficient truncates to \<open>0\<close>
      while its negation truncates to \<open>-1\<close>, and the next level's dilation multiplies each such unit by
      \<open>2\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>-\<^sup>i\<^sup>)\<close>. Negating here costs one in-place \<open>mpz_neg\<close> on a value already owned
      (\<open>mpz_neg.amop_r\<close>, as in \<open>Newton\<close>), with no second pass.\<close>
   q \<leftarrow> (PR_CONST mpz_neg.amop_r) q;
   dst \<leftarrow> (PR_CONST poly_push_coeff_monadic) dst q;
   RETURN (j + 1, dst)
 }"

definition defl_drop_result_mop :: "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres" where
"defl_drop_result_mop st \<equiv> (let (j, dst) = st in RETURN dst)"

definition defl_drop_invar :: "gmp_poly \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool" where
"defl_drop_invar xs st \<longleftrightarrow>
   (let (j, dst) = st in
      1 \<le> j \<and> j \<le> length xs \<and> dst = map uminus (take (j - 1) (tl xs)))"

definition defl_drop_monadic :: "gmp_poly \<Rightarrow> gmp_poly nres" where
"defl_drop_monadic xs \<equiv> doN {
   ASSERT (xs \<noteq> []);
   ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
   n \<leftarrow> (PR_CONST poly_length_monadic) xs;
   dst0 \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
   st \<leftarrow> WHILEIT (defl_drop_invar xs)
            (\<lambda>st. (PR_CONST defl_drop_cond) n st)
            (\<lambda>st. (PR_CONST defl_drop_body_mop) xs st)
            (1, dst0);
   (PR_CONST defl_drop_result_mop) st
 }"

subsection \<open>Correctness\<close>

lemma defl_drop_invar_init:
  assumes ne: "xs \<noteq> []"
  shows "defl_drop_invar xs (1, [])"
  using ne by (cases xs) (auto simp: defl_drop_invar_def)

lemma defl_drop_take_step:
  assumes lt: "j < length xs" and one: "1 \<le> j"
  shows "take (j - 1) (tl xs) @ [xs ! j] = take j (tl xs)"
proof -
  \<comment> \<open>Decompose the list rather than reasoning about \<open>tl\<close> through an index lemma: with
      \<open>xs = x # ys\<close> the step is \<open>take_Suc_conv_app_nth\<close> on \<open>ys\<close> and nothing else.
      Going via \<open>nth_tl\<close> left \<open>tl xs ! i = xs ! Suc i\<close> open under its own premise.\<close>
  obtain i where ji: "j = Suc i" using one by (cases j) auto
  obtain x ys where xs_eq: "xs = x # ys" using lt by (cases xs) auto
  have ilen: "i < length ys" using lt ji xs_eq by simp
  have "take i ys @ [ys ! i] = take (Suc i) ys"
    using ilen by (simp add: take_Suc_conv_app_nth)
  thus ?thesis using ji xs_eq by simp
qed

text \<open>\<open>defl_drop_take_step\<close> is applied by \<open>OF\<close>, not put in a simp set: the goal reaches the closer
  with \<open>j - Suc 0\<close> while the rule is stored with \<open>j - 1\<close>, so as a conditional rewrite it would not
  match.\<close>

lemma defl_drop_invar_step:
  assumes inv: "defl_drop_invar xs (j, dst)"
      and lt:  "j < length xs"
  shows "defl_drop_invar xs (Suc j, dst @ [- (xs ! j)])"
proof -
  from inv have one: "1 \<le> j" and dq: "dst = map uminus (take (j - 1) (tl xs))"
    by (auto simp: defl_drop_invar_def)
  have "dst @ [- (xs ! j)] = map uminus (take (j - 1) (tl xs) @ [xs ! j])"
    using dq by simp
  also have "\<dots> = map uminus (take j (tl xs))"
    using defl_drop_take_step[OF lt one] by simp
  finally show ?thesis using lt by (simp add: defl_drop_invar_def)
qed

lemma defl_drop_invar_exit:
  assumes inv: "defl_drop_invar xs (j, dst)"
      and done_: "\<not> j < length xs"
  shows "dst = map uminus (tl xs)"
proof -
  from inv have jn: "j \<le> length xs" and dq: "dst = map uminus (take (j - 1) (tl xs))"
    by (auto simp: defl_drop_invar_def)
  from jn done_ have "j = length xs" by simp
  thus ?thesis using dq by simp
qed

theorem defl_drop_monadic_correct:
  assumes ne: "xs \<noteq> []"
      and bnd: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_drop_monadic xs \<le> SPEC (\<lambda>dst. dst = map uminus (tl xs))"
  unfolding defl_drop_monadic_def defl_drop_body_mop_def defl_drop_cond_def
            defl_drop_result_mop_def
            poly_length_monadic_def poly_copy_coeff_monadic_def
            poly_empty_sz_monadic_def poly_push_coeff_monadic_def
            mpz_neg.amop_r_def mpz_neg.aop_r_def PR_CONST_def
  apply (refine_vcg
           WHILEIT_rule[where R = "measure (\<lambda>(j, dst). length xs - j)"])
  using ne bnd
  apply (simp_all add: defl_drop_invar_init defl_drop_invar_step)
  by (auto simp: defl_drop_invar_def defl_drop_take_step
           dest: defl_drop_invar_exit)

text \<open>\<^bold>\<open>The form the caller consumes\<close>: on a zero read the right child is exactly \<open>x\<close> times
  what this returns, so no root strictly inside its box moves.\<close>

lemma defl_Poly_map_uminus: "Poly (map uminus ys) = - Poly (ys :: int list)"
  by (induction ys) simp_all

corollary defl_drop_monadic_exact:
  assumes ne: "xs \<noteq> []"
      and bnd: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
      and hd0: "xs ! 0 = 0"
  shows "defl_drop_monadic xs
           \<le> SPEC (\<lambda>dst. dst = map uminus (tl xs) \<and> Poly xs = [:0, - 1:] * Poly dst)"
proof (rule order_trans[OF defl_drop_monadic_correct[OF ne bnd]], rule SPEC_rule)
  fix dst :: "int list"
  assume d: "dst = map uminus (tl xs)"
  have "Poly xs = [:0, 1:] * Poly (tl xs)" by (rule defl_drop0_exact[OF ne hd0])
  also have "\<dots> = [:0, - 1:] * Poly (map uminus (tl xs))"
    by (simp only: defl_Poly_map_uminus) (simp add: algebra_simps)
  finally show "dst = map uminus (tl xs) \<and> Poly xs = [:0, - 1:] * Poly dst"
    using d by simp
qed

subsection \<open>Synthesis\<close>

sepref_register "PR_CONST defl_drop_cond"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool"

sepref_definition defl_drop_cond_impl [llvm_inline] is
  "uncurry (RETURN oo defl_drop_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a defl_drop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding defl_drop_cond_def
  unfolding Let_def
  by sepref

lemma defl_drop_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry defl_drop_cond_impl, uncurry (RETURN oo (PR_CONST defl_drop_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a defl_drop_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using defl_drop_cond_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_drop_body_mop"
  :: "gmp_poly \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> (nat \<times> gmp_poly) nres"

sepref_definition defl_drop_body_impl [llvm_inline] is
  "uncurry defl_drop_body_mop" ::
  "[\<lambda>(xs, st). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a defl_drop_state_assn\<^sup>d \<rightarrow> defl_drop_state_assn"
  unfolding defl_drop_body_mop_def
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

lemma defl_drop_body_impl_hnr[sepref_fr_rules]:
  "(uncurry defl_drop_body_impl, uncurry (PR_CONST defl_drop_body_mop)) \<in>
    [\<lambda>(xs, st). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a defl_drop_state_assn\<^sup>d \<rightarrow> defl_drop_state_assn"
  using defl_drop_body_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_drop_result_mop"
  :: "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition defl_drop_result_impl [llvm_inline] is
  "defl_drop_result_mop" ::
  "defl_drop_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  unfolding defl_drop_result_mop_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma defl_drop_result_impl_hnr[sepref_fr_rules]:
  "(defl_drop_result_impl, PR_CONST defl_drop_result_mop) \<in>
    defl_drop_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  using defl_drop_result_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST defl_drop_monadic" :: "gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition defl_drop_impl [llvm_code] is
  "defl_drop_monadic" ::
  "[\<lambda>xs. xs \<noteq> [] \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding defl_drop_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    defl_drop_cond_impl_hnr defl_drop_body_impl_hnr defl_drop_result_impl_hnr
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

lemma defl_drop_impl_hnr[sepref_fr_rules]:
  "(defl_drop_impl, PR_CONST defl_drop_monadic) \<in>
    [\<lambda>xs. xs \<noteq> [] \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using defl_drop_impl.refine by (simp add: PR_CONST_def)

end
