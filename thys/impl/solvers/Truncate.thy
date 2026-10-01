theory Truncate
  imports Count Truncate_Spec
begin

text \<open>Carried shift truncation: the monadic layer.

  The node polynomial may be a truncated stand-in for the exact carried polynomial, related by
  @{const node_frame} (the \<open>g = 0\<close> sentinel means exact). This theory provides four ops:
  \<^item> \<open>truncate_ethorner_count_gtrunc_monadic\<close>: the guarded ET-Horner kernel with its per-position threshold
    widened by the node's carried slack \<open>g\<close>, and no truncation pre-pass (the node polynomial already is the
    truncation);
  \<^item> \<open>carried_descartes_count_g_monadic\<close>: the count dispatch; \<open>g = 0\<close> \<Rightarrow>
    @{const carried_descartes_count_trunc_monadic} (internally decisive); \<open>g \<ge> 1\<close> \<Rightarrow> the widened kernel,
    returning a decisiveness flag the caller must act on (escalate when false, since the node holds no exact
    polynomial to fall back to);
  \<^item> \<open>carried_retrunc_mop\<close>: the re-truncation at push time, gated on the bit length of the dominant index-0
    coefficient, with \<open>g\<close> reset when it fires;
  \<^item> \<open>carried_escalate_exact_monadic\<close>: the exact rebuild from the borrowed root over the node's own dyadic
    box (frees the truncated polynomial, then @{const carried_init_inplace_monadic}; restores \<open>g = 0\<close> up to a
    positive scalar no sign consumer observes).

  \<open>poly_ethorner_count_gtrunc_monadic_classify\<close> and \<open>carried_descartes_count_g_monadic_classify\<close> need explicit
  bounds on \<open>g\<close> and on a product, because the kernel's internal ASSERTs require them and \<open>gframe\<close>/\<open>node_frame\<close>
  do not bound \<open>g\<close>; \<open>carried_retrunc_mop_frame\<close> uses \<open>gframe_retrunc_dom\<close> (\<open>Truncate_Spec\<close>, the \<open>t < g\<close>
  complement of \<open>gframe_trunc\<close>'s \<open>g \<le> t\<close>) for the two-branch reset formula of \<open>retrunc_reset_mop\<close>. A root that
  is owned by the loop body is handled with the \<open>_keep\<close> variant.\<close>

section \<open>The g-widened guarded ET-Horner kernel\<close>

text \<open>Clone of the truncated ET-Horner count kernel of \<open>Count.thy\<close>
  (\<open>poly_ethorner_count_trunc_monadic\<close>) with two deltas:
  (1) the body's trust threshold is \<open>g + min (min (i+1) (len-(i+1)) * bthr) len\<close>
  (the node's carried slack on top of the count's own shift error — spec:
  @{const trusted_sgn_g}); (2) the boundary coefficient's trust is \<open>g < bitlen\<close>
  instead of "nonzero" (\<open>trunc_thresh len (len-1) = 0\<close>, so at \<open>g = 0\<close> both deltas
  collapse to that kernel). The cond and result mops are REUSED unchanged
  (@{const ethorner_count_trunc_cond}, @{const ethorner_count_trunc_result_mop_monadic});
  only the body mop is new.\<close>

text \<open>Written directly in the synthesisable shape: only registered pure-op calls, ASSERTs and
  destructuring in the heap body, no inline \<open>let\<close> arithmetic. The \<open>g\<close> widening is one extra pure step
  (\<open>bt \<leftarrow> trunc_thresh_mop \<dots>; bt \<leftarrow> RETURN (g + bt)\<close>) on top of \<open>trunc_thresh_mop\<close>/\<open>trunc_update_mop\<close>, which
  already have \<open>[sepref_fr_rules]\<close>.\<close>
definition truncate_ethorner_count_gtrunc_body_mop_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly
   \<Rightarrow> ((nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly) nres" where
"truncate_ethorner_count_gtrunc_body_mop_monadic len bthr g st \<equiv> doN {
  let (st1, xs) = st;
  let (i, last_s, cnt, amb) = st1;
  ASSERT (length xs = len);
  ASSERT (1 < len);
  ASSERT (i + 1 < len);
  ASSERT (cnt < 2);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (len < max_snat LENGTH(gmp_poly_len));
  ASSERT (len * bthr < max_snat LENGTH(gmp_poly_len));
  xs' \<leftarrow> (PR_CONST poly_ethorner_inner_loop_monadic) len i xs;
  ASSERT (i < length xs');
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs' i;
  bl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs' i;
  bt0 \<leftarrow> (PR_CONST trunc_thresh_mop) i len bthr;
  ASSERT (g + bt0 < max_snat LENGTH(gmp_poly_len));
  bt \<leftarrow> RETURN (g + bt0);
  (new_last_s, new_cnt, new_amb) \<leftarrow>
    (PR_CONST trunc_update_mop) s bl bt last_s cnt amb;
  RETURN ((i + 1, new_last_s, new_cnt, new_amb), xs')
}"

sepref_register "PR_CONST truncate_ethorner_count_gtrunc_body_mop_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly
     \<Rightarrow> ((nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly) nres"

sepref_definition truncate_ethorner_count_gtrunc_body_impl [llvm_inline] is
  "uncurry3 truncate_ethorner_count_gtrunc_body_mop_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a ethorner_trunc_state_assn\<^sup>d \<rightarrow>\<^sub>a
    ethorner_trunc_state_assn"
  unfolding truncate_ethorner_count_gtrunc_body_mop_monadic_def Let_def
  apply (annot_sint_const gmp_int_t)?
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma ethorner_count_gtrunc_body_impl_hnr[sepref_fr_rules]:
  "(uncurry3 truncate_ethorner_count_gtrunc_body_impl,
    uncurry3 (PR_CONST truncate_ethorner_count_gtrunc_body_mop_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a ethorner_trunc_state_assn\<^sup>d \<rightarrow>\<^sub>a
      ethorner_trunc_state_assn"
  using truncate_ethorner_count_gtrunc_body_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The outer widened count: consumes (and frees) the reversed carried poly,
  returns \<open>(cnt + extra_f, amb)\<close>. The boundary \<open>extra_f\<close> bit fires only when the
  lead itself is g-trusted (an untrusted lead seeds \<open>amb\<close> from the start, exactly
  like the plain truncated count's zero-lead case).\<close>
text \<open>The leading-coefficient trust test as its own pure op: a value feeding a WHILET's initial state
  must be bound by an op, not computed by a \<open>let\<close>. The widened compound boolean \<open>0 < s \<or> (s < 0 \<and> g < bl)\<close>
  would otherwise feed the initial tuple via a \<open>let\<close>. Same trust shape as \<open>trunc_update_mop\<close>'s inline test.\<close>
text \<open>\<open>bl\<close> is a \<open>gmp_size\<close> (\<open>unat\<close>-represented, like \<open>trunc_update_mop\<close>'s \<open>bl\<close> and the return value of
  \<open>poly_coeff_bitlen2_monadic\<close>), and \<open>g\<close> is an \<open>snat\<close>. Comparing them uses the \<open>op_snat_unat_conv\<close> bridge
  \<open>trunc_update_mop\<close> uses (\<open>btu \<leftarrow> RETURN (op_snat_unat_conv bt); \<dots> btu < bl\<close>); a bare \<open>g < bl\<close> across
  representations does not synthesise.\<close>
definition lead_trust_mop :: "int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
"lead_trust_mop s bl g \<equiv> doN {
  gu \<leftarrow> RETURN (op_snat_unat_conv g);
  RETURN (0 < s \<or> (s < 0 \<and> gu < bl))
}"

sepref_register "PR_CONST lead_trust_mop" :: "int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres"

sepref_definition lead_trust_impl [llvm_inline] is
  "uncurry2 lead_trust_mop" ::
  "gmp_sint_assn\<^sup>k *\<^sub>a gmp_size_assn\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding lead_trust_mop_def
  apply (annot_sint_const gmp_int_t)?
  by sepref

lemma lead_trust_impl_hnr[sepref_fr_rules]:
  "(uncurry2 lead_trust_impl, uncurry2 (PR_CONST lead_trust_mop)) \<in>
    gmp_sint_assn\<^sup>k *\<^sub>a gmp_size_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using lead_trust_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Even a TRIVIAL operation (here: negation) applied to a bound value before its
  first use inside a heap-carrying tuple/program needs its OWN registered op — the
  same "MOP-bind everything feeding a WHILET init/branch" discipline, one step
  further than \<open>lead_trust_mop\<close> alone fixed (confirmed by a second build failure:
  \<open>\<not> lead_tr\<close> inline in the WHILET's init tuple was still unresolved even with
  \<open>lead_tr\<close> itself bound).\<close>
definition bool_not_mop :: "bool \<Rightarrow> bool nres" where
  "bool_not_mop b \<equiv> RETURN (\<not> b)"

sepref_register "PR_CONST bool_not_mop" :: "bool \<Rightarrow> bool nres"

sepref_definition bool_not_impl [llvm_inline] is
  "bool_not_mop" :: "bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding bool_not_mop_def by sepref

lemma bool_not_impl_hnr[sepref_fr_rules]:
  "(bool_not_impl, PR_CONST bool_not_mop) \<in> bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using bool_not_impl.refine by (simp add: PR_CONST_def)

definition truncate_ethorner_count_gtrunc_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> (nat \<times> bool) nres" where
"truncate_ethorner_count_gtrunc_monadic g xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  if len \<le> 1 then doN { (PR_CONST poly_free_monadic) xs; RETURN (0, False) }
  else doN {
    ASSERT (1 < len);
    bthr \<leftarrow> (PR_CONST snat_bitlen_monadic) len;
    ASSERT (len * bthr < max_snat LENGTH(gmp_poly_len));
    ASSERT (g + len < max_snat LENGTH(gmp_poly_len));
    limit \<leftarrow> RETURN (len - 1);
    ASSERT (limit < length xs);
    s_last \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs limit;
    bl_last \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs limit;
    lead_tr \<leftarrow> (PR_CONST lead_trust_mop) s_last bl_last g;
    lead_amb0 \<leftarrow> (PR_CONST bool_not_mop) lead_tr;
    let init = ((0::nat, 0::int, 0::nat, lead_amb0), xs);
    st \<leftarrow> WHILET
      (\<lambda>st. (PR_CONST ethorner_count_trunc_cond) limit st)
      (\<lambda>st. (PR_CONST truncate_ethorner_count_gtrunc_body_mop_monadic) len bthr g st)
      init;
    (cnt, last_s, amb, xs_final) \<leftarrow>
      (PR_CONST ethorner_count_trunc_result_mop_monadic) st;
    extra_f \<leftarrow> (if lead_tr \<and> last_s \<noteq> 0 \<and> s_last \<noteq> 0 \<and> last_s \<noteq> s_last
                then RETURN (1::nat) else RETURN 0);
    ASSERT (cnt + extra_f < max_snat LENGTH(gmp_poly_len));
    final_cnt \<leftarrow> RETURN (cnt + extra_f);
    (PR_CONST poly_free_monadic) xs_final;
    RETURN (final_cnt, amb)
  }
}"

sepref_register "PR_CONST truncate_ethorner_count_gtrunc_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> (nat \<times> bool) nres"

sepref_definition truncate_ethorner_count_gtrunc_impl [llvm_code] is
  "uncurry truncate_ethorner_count_gtrunc_monadic" ::
  "[\<lambda>(g, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  unfolding truncate_ethorner_count_gtrunc_monadic_def Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] =
    ethorner_count_trunc_cond_impl_hnr
    ethorner_count_gtrunc_body_impl_hnr
    ethorner_count_trunc_result_impl_hnr
    lead_trust_impl_hnr
    bool_not_impl_hnr
  apply (annot_sint_const gmp_int_t)?
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

lemma poly_ethorner_count_gtrunc_impl_hnr[sepref_fr_rules]:
  "(uncurry truncate_ethorner_count_gtrunc_impl,
    uncurry (PR_CONST truncate_ethorner_count_gtrunc_monadic)) \<in>
    [\<lambda>(g, xs). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  using truncate_ethorner_count_gtrunc_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The kernel's runtime trust test (sign and bit-length comparison), packaged as one \<open>tsign_step\<close> on the
  masked coefficient: the \<open>g\<close>-widened twin of @{thm [source] tsign_step_bitlen_form_masked}. It uses only the
  unconditional lower bound (see the masked-coefficient note in \<open>Count_Spec\<close>).\<close>
lemma tsign_step_bitlen_form_g_masked:
  fixes x :: int
  assumes lb: "x \<noteq> 0 \<longrightarrow> 2 ^ (bl - 1) \<le> \<bar>x\<bar>"
  shows "tsign_step (trusted_sgn_g g len i
           (if 0 < sgn x \<or> (sgn x < 0 \<and> g + trunc_thresh len i < bl) then x else 0))
           (ls, cnt, amb)
    = ((if 0 < sgn x \<or> (sgn x < 0 \<and> g + trunc_thresh len i < bl) then sgn x else ls),
       (if (0 < sgn x \<or> (sgn x < 0 \<and> g + trunc_thresh len i < bl)) \<and> ls \<noteq> 0 \<and> sgn x \<noteq> ls
        then cnt + 1 else cnt),
       (amb \<or> \<not> (0 < sgn x \<or> (sgn x < 0 \<and> g + trunc_thresh len i < bl))))"
proof -
  note tst = trusted_sgn_g_bitlen_test_masked[OF lb[rule_format], of g len i]
  show ?thesis
  proof (cases "0 < sgn x \<or> (sgn x < 0 \<and> g + trunc_thresh len i < bl)")
    case True
    then show ?thesis using tst by simp
  next
    case False
    then show ?thesis using tst by auto
  qed
qed

text \<open>Proof-only RAW twin of the body (SAME bind/ASSERT shape as
  @{const truncate_ethorner_count_gtrunc_body_mop_monadic}, with the two registered mop calls
  \<open>trunc_thresh_mop\<close>/\<open>trunc_update_mop\<close> replaced by their closed forms
  @{thm [source] trunc_thresh_mop_eq}/@{thm [source] trunc_update_mop_eq} — the plain count's
  \<open>ethorner_count_trunc_body_impl_form_eq\<close> bridge run in reverse, since this kernel
  is written DIRECTLY in impl-mop form). Never Sepref'd — a device for
  \<open>ethorner_count_gtrunc_body_pres\<close> only.\<close>
definition truncate_ethorner_count_gtrunc_body_raw ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly
   \<Rightarrow> ((nat \<times> int \<times> nat \<times> bool) \<times> gmp_poly) nres" where
"truncate_ethorner_count_gtrunc_body_raw len bthr g st \<equiv> doN {
  let (st1, xs) = st;
  let (i, last_s, cnt, amb) = st1;
  ASSERT (length xs = len);
  ASSERT (1 < len);
  ASSERT (i + 1 < len);
  ASSERT (cnt < 2);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (len < max_snat LENGTH(gmp_poly_len));
  ASSERT (len * bthr < max_snat LENGTH(gmp_poly_len));
  xs' \<leftarrow> (PR_CONST poly_ethorner_inner_loop_monadic) len i xs;
  ASSERT (i < length xs');
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs' i;
  bl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs' i;
  bt0 \<leftarrow> RETURN (min (min (i + 1) (len - (i + 1)) * bthr) len);
  ASSERT (g + bt0 < max_snat LENGTH(gmp_poly_len));
  bt \<leftarrow> RETURN (g + bt0);
  let trusted = (0 < s \<or> (s < 0 \<and> bt < bl));
  let new_amb = (amb \<or> \<not> trusted);
  let new_cnt = (if trusted \<and> last_s \<noteq> 0 \<and> s \<noteq> last_s then cnt + 1 else cnt);
  let new_last_s = (if trusted then s else last_s);
  RETURN ((i + 1, new_last_s, new_cnt, new_amb), xs')
}"

lemma ethorner_count_gtrunc_body_raw_eq:
  "truncate_ethorner_count_gtrunc_body_raw len bthr g st = truncate_ethorner_count_gtrunc_body_mop_monadic len bthr g st"
proof -
  obtain st1 xs where st: "st = (st1, xs)" by (cases st)
  obtain i last_s cnt amb where st1: "st1 = (i, last_s, cnt, amb)"
    by (cases st1) auto
  show ?thesis
    unfolding truncate_ethorner_count_gtrunc_body_raw_def
      truncate_ethorner_count_gtrunc_body_mop_monadic_def PR_CONST_def st st1
    apply (simp only: Let_def prod.case ASSERT_bind_eq_if)
    apply (intro bind_cong if_cong refl)
    subgoal by (simp add: trunc_thresh_mop_eq)
    subgoal by (simp add: trunc_update_mop_eq)
    done
qed

text \<open>One outer-loop body step preserves the \<open>g\<close>-widened invariant and advances \<open>i\<close> —
  the \<open>g\<close>-widened twin of @{thm [source] ethorner_trunc_body_pres}, proved over the
  RAW form and bridged via @{thm [source] ethorner_count_gtrunc_body_raw_eq}.\<close>
lemma ethorner_count_gtrunc_body_pres:
  assumes len2: "2 \<le> length ys'"
    and iU: "i < length ys' - 1"
    and cU: "cnt < 2"
    and lenxs: "length xs = length ys'"
    and xseq: "xs = ethorner_outer_step_fun i ys'"
    and steq: "tmask_state_g g ys' amb0 (ls, cnt, amb) i"
    and bound: "length ys' + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length ys' * nat_bitlen (length ys') < max_snat LENGTH(gmp_poly_len)"
    and gbound: "g + length ys' < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_ethorner_count_gtrunc_body_mop_monadic (length ys') (nat_bitlen (length ys')) g
           ((i, ls, cnt, amb), xs)
    \<le> SPEC (\<lambda>((i', ls', cnt', amb'), xs').
          i' = Suc i \<and> i' \<le> length ys' - 1 \<and> cnt' \<le> 2 \<and> length xs' = length ys'
        \<and> xs' = ethorner_outer_step_fun i' ys'
        \<and> tmask_state_g g ys' amb0 (ls', cnt', amb') i')"
  unfolding ethorner_count_gtrunc_body_raw_eq[symmetric]
proof -
  let ?len = "length ys'"
  let ?T = "taylor_shift_list 1 ys'"
  let ?os = "ethorner_outer_step_fun i ys'"
  have iL: "i < ?len" using iU by simp
  have iLT: "i < length ?T" using iL by simp
  have row: "ethorner_row_fun i ?os = ethorner_outer_step_fun (Suc i) ys'" by simp
  have val_i: "ethorner_row_fun i ?os ! i = ?T ! i"
    using row ethorner_outer_step_nth_final[OF iL] by simp
  \<comment> \<open>the invariant's mask witness at \<open>i\<close>; the step extends it by ONE entry\<close>
  obtain zs where zs: "length zs = i"
    "\<forall>j<i. zs ! j = 0 \<or> zs ! j = ?T ! j"
    "(ls, cnt, amb) = tsign_fold_idx_g g ?len 0 zs (0, 0, amb0)"
    using steq unfolding tmask_state_g_def by blast
  have take_step: "\<And>v. tsign_fold_idx_g g ?len 0 (zs @ [v]) (0, 0, amb0)
      = tsign_step (trusted_sgn_g g ?len i v) (ls, cnt, amb)"
    using tsign_fold_idx_append_g[of g ?len 0 zs _ "(0, 0, amb0)"] zs(1,3) by simp
  show "truncate_ethorner_count_gtrunc_body_raw ?len (nat_bitlen ?len) g ((i, ls, cnt, amb), xs)
    \<le> SPEC (\<lambda>((i', ls', cnt', amb'), xs').
          i' = Suc i \<and> i' \<le> ?len - 1 \<and> cnt' \<le> 2 \<and> length xs' = ?len
        \<and> xs' = ethorner_outer_step_fun i' ys'
        \<and> tmask_state_g g ys' amb0 (ls', cnt', amb') i')"
    unfolding truncate_ethorner_count_gtrunc_body_raw_def poly_coeff_sgn_monadic_def
      poly_coeff_bitlen2_monadic_def mpz_bitlen2_monadic_def PR_CONST_def Let_def
    apply (refine_vcg poly_ethorner_inner_loop_monadic_row[THEN order_trans])
    subgoal using lenxs by auto
    subgoal using len2 by simp
    subgoal using iU by (auto simp: less_diff_conv)
    subgoal using cU by auto
    subgoal using lenxs bound by auto
    subgoal using bound by simp
    subgoal using pbound by simp
    subgoal using len2 by simp
    subgoal using iL by auto
    subgoal using iL lenxs by auto
    subgoal using gbound by (auto simp: min_def)
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> g + min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note pf = prems[folded v_def, folded C_def]
      have "aa = i" using pf by simp
      moreover have "x1a = aa + 1" using pf by simp
      ultimately show ?thesis by linarith
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> g + min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note pf = prems[folded v_def, folded C_def]
      have "x1a = aa + 1" using pf by simp
      then show ?thesis using pf by linarith
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> g + min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note pf = prems[folded v_def, folded C_def]
      have ac2: "ac < 2" using pf by simp
      have x1ceq: "x1c = (if C \<and> ab \<noteq> 0 \<and> sgn v \<noteq> ab then ac + 1 else ac)" using pf by simp
      then have "x1c = ac \<or> x1c = ac + 1" by simp
      then show ?thesis using ac2 by auto
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> g + min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note pf = prems[folded v_def, folded C_def]
      have x2ceq: "x2c = ethorner_row_fun aa b" using pf by simp
      have rowlen: "length (ethorner_row_fun aa b) = length b" by simp
      show ?thesis unfolding x2ceq rowlen using pf by simp
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> g + min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note pf = prems[folded v_def, folded C_def]
      have eq0: "aa = i" "b = xs" using pf by auto
      have x2ceq: "x2c = ethorner_row_fun aa b" using pf by simp
      have "x1a = aa + 1" using pf by simp
      then have sucform: "x1a = Suc aa" by linarith
      show ?thesis
        unfolding sucform using x2ceq xseq eq0 by simp
    qed
    subgoal premises prems for a b aa ba ab bb ac bc x x1 x1a x2 x1b x2a x1c x2b x2c
    proof -
      define v where "v = ethorner_row_fun aa b ! aa"
      define C where "C = (0 < sgn v \<or> sgn v < 0
        \<and> g + min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys') < x)"
      note pf = prems[folded v_def, folded C_def]
      have eq0: "aa = i" "ab = ls" "ac = cnt" "bc = amb" "b = xs" using pf by auto
      have x1aeq: "x1a = aa + 1" using pf by simp
      have comps: "x1b = (if C then sgn v else ab)"
        "x1c = (if C \<and> ab \<noteq> 0 \<and> sgn v \<noteq> ab then ac + 1 else ac)"
        "x2b = (bc \<or> \<not> C)"
        using pf by simp_all
      have lb: "v \<noteq> 0 \<longrightarrow> 2 ^ (x - 1) \<le> \<bar>v\<bar>"
        using pf by auto
      have veq: "v = taylor_shift_list 1 ys' ! i"
        unfolding v_def using eq0 xseq val_i by simp
      have suci: "Suc i = i + 1" by linarith
      have thr: "g + min (min (aa + 1) (length ys' - (aa + 1)) * nat_bitlen (length ys')) (length ys')
          = g + trunc_thresh (length ys') i"
        unfolding trunc_thresh_def by (simp only: suci eq0(1))
      have Ceq: "C = (0 < sgn (taylor_shift_list 1 ys' ! i)
          \<or> sgn (taylor_shift_list 1 ys' ! i) < 0 \<and> g + trunc_thresh (length ys') i < x)"
        unfolding C_def veq thr ..
      \<comment> \<open>the extended mask witness: the true coefficient when trusted, \<open>0\<close> when not\<close>
      define w where "w = (if C then taylor_shift_list 1 ys' ! i else 0)"
      have fold_eq: "tsign_fold_idx_g g (length ys') 0 (zs @ [w]) (0, 0, amb0)
          = ((if C then sgn v else ls),
             (if C \<and> ls \<noteq> 0 \<and> sgn v \<noteq> ls then cnt + 1 else cnt),
             (amb \<or> \<not> C))"
      proof -
        have "tsign_fold_idx_g g (length ys') 0 (zs @ [w]) (0, 0, amb0)
            = tsign_step (trusted_sgn_g g (length ys') i w) (ls, cnt, amb)"
          using take_step[of w] .
        also have "\<dots> = ((if C then sgn (taylor_shift_list 1 ys' ! i) else ls),
             (if C \<and> ls \<noteq> 0 \<and> sgn (taylor_shift_list 1 ys' ! i) \<noteq> ls then cnt + 1 else cnt),
             (amb \<or> \<not> C))"
          unfolding w_def Ceq
          by (rule tsign_step_bitlen_form_g_masked[OF lb[unfolded veq]])
        finally show ?thesis unfolding veq .
      qed
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
      have mstate: "tmask_state_g g ys' amb0
          ((if C then sgn v else ls),
           (if C \<and> ls \<noteq> 0 \<and> sgn v \<noteq> ls then cnt + 1 else cnt),
           (amb \<or> \<not> C)) (Suc i)"
        unfolding tmask_state_g_def
        by (rule exI[where x="zs @ [w]"]) (simp add: zs(1) maskzsw fold_eq)
      show ?thesis
        unfolding comps eq0(2) eq0(3) eq0(4) x1aeq eq0(1)
        using mstate[unfolded suci] by simp
    qed
    done
qed

text \<open>Exit lemma: loop exit (full scan OR early abort) plus the boundary \<open>extra_f\<close>
  step yields the classify facts — the \<open>g\<close>-widened twin of
  @{thm [source] ethorner_trunc_post}.\<close>
lemma ethorner_count_gtrunc_post:
  assumes Xr: "gframe s g Xr ys'"
    and l2: "Suc 0 < length ys'"
    and iinv: "i \<le> length ys' - 1"
    and cle: "cnt \<le> 2"
    and lead_lb: "ys' ! (length ys' - 1) \<noteq> 0 \<longrightarrow>
                    2 ^ (bl - 1) \<le> \<bar>ys' ! (length ys' - 1)\<bar>"
      \<comment> \<open>OBJECT-LEVEL \<open>\<longrightarrow>\<close> deliberately (the @{thm [source] tsign_step_bitlen_form_masked}
         NB applies verbatim): a meta-conditional assumption leaves a vacuous residual
         premise on \<open>[OF \<dots>]\<close> instances, which silently stops them firing\<close>
    and amb0_eq: "amb0 = (\<not> (0 < sgn (ys' ! (length ys' - 1))
                     \<or> sgn (ys' ! (length ys' - 1)) < 0 \<and> g < bl))"
    and steq: "tmask_state_g g ys' amb0 (ls, cnt, amb) i"
    and exit: "\<not> (i < length ys' - 1 \<and> cnt < 2)"
    and efeq: "ef = (if ls \<noteq> 0 \<and> \<not> amb0 \<and> ls \<noteq> sgn (ys' ! (length ys' - 1))
                      then 1 else (0::nat))"
  shows "(2 \<le> cnt + ef \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 Xr)) \<and>
         (\<not> amb \<longrightarrow>
            (cnt + ef = 0) = (sign_changes_fold (taylor_shift_list 1 Xr) = 0) \<and>
            (cnt + ef = 1) = (sign_changes_fold (taylor_shift_list 1 Xr) = 1) \<and>
            (2 \<le> cnt + ef) = (2 \<le> sign_changes_fold (taylor_shift_list 1 Xr)))"
proof -
  define len' where "len' = length ys'"
  define T where "T = taylor_shift_list 1 ys'"
  have lenT: "length T = len'" by (simp add: T_def len'_def)
  have mstate: "tmask_state_g g ys' amb0 (ls, cnt, amb) i" using steq .
  \<comment> \<open>the kernel's leading-coefficient decision is conservative: when it trusts the leading coefficient,
     the abstract trust holds with the same sign. Only the unconditional lower bound of the bit-length
     specification is used; the converse would need the guarded upper bound.\<close>
  have thr0: "trunc_thresh (length ys') (length ys' - 1) = 0"
    unfolding trunc_thresh_def by (cases "length ys'") auto
  have lead: "\<not> amb0 \<Longrightarrow> trusted_sgn_g g (length ys') (length ys' - 1)
                  (ys' ! (length ys' - 1)) = Some (sgn (ys' ! (length ys' - 1)))"
    using trusted_sgn_g_bitlen_test_masked[OF lead_lb[rule_format],
            of g "length ys'" "length ys' - 1"] amb0_eq thr0 by simp
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
    \<comment> \<open>the boundary step's own trust decision. \<open>amb0\<close> is the kernel's decision on the leading coefficient:
       when it distrusts, the boundary carries the mask as a \<open>0\<close> (and \<open>ef = 0\<close>); when it trusts,
       @{thm [source] amb0_eq} says the abstract leading coefficient is trusted with the same sign.\<close>
    define wl where "wl = (if amb0 then 0 else last T)"
    have bstep: "trusted_sgn_g g len' (len' - 1) wl
        = (if amb0 then None else Some (sgn (ys' ! (len' - 1))))"
    proof (cases amb0)
      case True
      then show ?thesis
        unfolding wl_def trusted_sgn_g_def
        using zero_less_power[of "2::int" "g + trunc_thresh len' (len' - 1)"] by simp
    next
      case False
      then show ?thesis unfolding wl_def using lead lastT len'_def by simp
    qed
    \<comment> \<open>count soundness: the invariant's mask, extended by the (masked) boundary
       coefficient, is a mask of the whole shifted node list\<close>
    obtain zs where zs: "length zs = i"
      "\<forall>j<i. zs ! j = 0 \<or> zs ! j = T ! j"
      "(ls, cnt, amb) = tsign_fold_idx_g g len' 0 zs (0, 0, amb0)"
      using mstate unfolding tmask_state_g_def T_def len'_def by blast
    have ws_fold: "tsign_fold_idx_g g len' 0 (zs @ [wl]) (0, 0, amb0)
        = tsign_step (trusted_sgn_g g len' (len' - 1) wl) (ls, cnt, amb)"
      using tsign_fold_idx_append_g[of g len' 0 zs "[wl]" "(0, 0, amb0)"] zs(1,3) full
      by simp
    have ws_cnt: "(\<lambda>(a, b, c). b) (tsign_fold_idx_g g len' 0 (zs @ [wl]) (0, 0, amb0))
        = cnt + ef"
      using efeq unfolding ws_fold bstep by (auto simp: len'_def)
    have ws_len: "length (zs @ [wl]) = length ys'"
      using zs(1) full l2 by (simp add: len'_def)
    have ws_mask: "\<forall>j<length (zs @ [wl]).
        (zs @ [wl]) ! j = 0 \<or> (zs @ [wl]) ! j = taylor_shift_list 1 ys' ! j"
    proof (intro allI impI)
      fix j assume j: "j < length (zs @ [wl])"
      then have ji: "j \<le> i" using zs(1) by simp
      show "(zs @ [wl]) ! j = 0 \<or> (zs @ [wl]) ! j = taylor_shift_list 1 ys' ! j"
      proof (cases "j < i")
        case True
        then have "(zs @ [wl]) ! j = zs ! j" using zs(1) by (simp add: nth_append)
        then show ?thesis using zs(2) True by (simp add: T_def)
      next
        case False
        then have jeq: "j = i" using ji by simp
        have "(zs @ [wl]) ! j = wl" using zs(1) jeq by (simp add: nth_append)
        then show ?thesis unfolding wl_def using lastTnth full jeq by (simp add: T_def)
      qed
    qed
    have ge2: "2 \<le> cnt + ef \<Longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 Xr)"
    proof -
      assume a2: "2 \<le> cnt + ef"
      have "(\<lambda>(a, b, c). b) (tsign_fold_idx_g g (length ys') 0 (zs @ [wl]) (0, 0, amb0))
          \<le> sign_changes_fold (taylor_shift_list 1 Xr)"
        using tsign_mask_cnt_le_full_g[OF Xr ws_len ws_mask, of amb0] .
      then have "cnt + ef \<le> sign_changes_fold (taylor_shift_list 1 Xr)"
        using ws_cnt by (simp add: len'_def)
      then show ?thesis using a2 by simp
    qed
    \<comment> \<open>the decisive case: \<open>\<not>amb\<close> forces the mask to be TRIVIAL, so the exact transfer
       runs on the UNMASKED prefix fold, which is the very fold the trivial mask denotes\<close>
    have exact_eq: "\<not> amb \<Longrightarrow> cnt + ef = sign_changes_fold (taylor_shift_list 1 Xr)"
    proof -
      assume noamb: "\<not> amb"
      have ile: "i \<le> length ys'" using iinv by simp
      have kstate: "(ls, cnt, amb) = tsign_fold_idx_g g len' 0 (butlast T) (0, 0, amb0)"
        using tmask_state_g_not_amb[OF mstate noamb ile] tbutl by (simp add: len'_def T_def)
      obtain lsF cntF ambF where F:
        "tsign_fold_idx_g g len' 0 (butlast T) (0, 0, False) = (lsF, cntF, ambF)"
        by (cases "tsign_fold_idx_g g len' 0 (butlast T) (0, 0, False)") auto
      have fs: "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx_g g len' 0 (butlast T) (0, 0, amb0))
          = (\<lambda>(a, b, c). (a, b)) (tsign_fold_idx_g g len' 0 (butlast T) (0, 0, False))"
        by (rule tsign_fold_idx_fst_snd_cong_g) simp
      have "(ls, cnt) = (lsF, cntF)"
        using arg_cong[OF kstate, of "\<lambda>(a, b, c). (a, b)"] fs F by simp
      then have lseq: "ls = lsF" and cnteq: "cnt = cntF" by auto
      have "amb = (\<lambda>(a, b, c). c) (tsign_fold_idx_g g len' 0 (butlast T) (0, 0, amb0))"
        using arg_cong[OF kstate, of "\<lambda>(a, b, c). c"] by simp
      also have "\<dots> = (amb0 \<or> (\<lambda>(a, b, c). c) (tsign_fold_idx_g g len' 0 (butlast T) (0, 0, False)))"
        by (rule tsign_fold_idx_amb_or_g)
      also have "\<dots> = (amb0 \<or> ambF)" using F by simp
      finally have ambeq: "amb = (amb0 \<or> ambF)" .
      have tc: "trunc_changes_g g len' T
          = (case tsign_step (trusted_sgn_g g len' (len' - 1) (last T)) (lsF, cntF, ambF)
             of (_, c, a) \<Rightarrow> (c, a))"
        using trunc_changes_g_split_last[OF Tne, of g len'] F lenT by simp
      have noamb0: "\<not> amb0" using ambeq noamb by simp
      have main: "trunc_changes_g g len' T = (cnt + ef, amb)"
      proof (cases amb0)
        case True
        then show ?thesis using noamb0 by simp
      next
        case False
        then have someL: "trusted_sgn_g g len' (len' - 1) (last T)
            = Some (sgn (ys' ! (len' - 1)))"
          using lead lastT len'_def by simp
        have step: "tsign_step (trusted_sgn_g g len' (len' - 1) (last T)) (lsF, cntF, ambF)
            = (sgn (ys' ! (len' - 1)),
               (if lsF \<noteq> 0 \<and> sgn (ys' ! (len' - 1)) \<noteq> lsF then cntF + 1 else cntF), ambF)"
          using someL by simp
        have "ef = (if lsF \<noteq> 0 \<and> sgn (ys' ! (len' - 1)) \<noteq> lsF then 1 else 0)"
          using efeq lseq False len'_def by simp
        then show ?thesis
          using tc step cnteq ambeq False by simp
      qed
      show "cnt + ef = sign_changes_fold (taylor_shift_list 1 Xr)"
        using trunc_changes_g_decisive_exact[OF Xr] main T_def len'_def noamb by simp
    qed
    show ?thesis using ge2 exact_eq by auto
  next
    case abort
    have ile: "i \<le> length ys'" using iinv by simp
    have t2: "2 \<le> sign_changes_fold (taylor_shift_list 1 Xr)"
      using tmask_state_g_cnt_le[OF mstate Xr ile] abort by simp
    have cef2: "2 \<le> cnt + ef" using abort by simp
    show ?thesis
    proof (intro conjI impI)
      show "2 \<le> cnt + ef \<Longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 Xr)"
        using t2 by simp
      show "\<not> amb \<Longrightarrow> (cnt + ef = 0) = (sign_changes_fold (taylor_shift_list 1 Xr) = 0)"
        using cef2 t2 by auto
      show "\<not> amb \<Longrightarrow> (cnt + ef = 1) = (sign_changes_fold (taylor_shift_list 1 Xr) = 1)"
        using cef2 t2 by auto
      show "\<not> amb \<Longrightarrow> (2 \<le> cnt + ef) = (2 \<le> sign_changes_fold (taylor_shift_list 1 Xr))"
        using cef2 t2 by auto
    qed
  qed
qed

text \<open>The kernel's scan loop, as a standalone \<open>\<le> SPEC\<close> rule over a free seed \<open>amb0\<close>.

  \<^bold>\<open>Why it is separate.\<close> The \<open>_g\<close> kernel decides the leading coefficient's trust from its bit length
  (threshold \<open>2^g\<close>), and seeds the loop's \<open>amb\<close> with that decision. Since the bit-length specification's upper
  bound is guarded, that decision is only conservative (kernel trust \<Longrightarrow> abstract trust), not provably equal to
  @{const trusted_sgn_g} of the true leading coefficient. So the loop invariant is seeded with the kernel's own
  boolean, which an inline @{thm [source] WHILET_rule} instantiation cannot name. With the loop separate, the seed
  is a lemma parameter, and @{thm [source] ethorner_count_gtrunc_post} consumes it as the implication-form
  hypothesis \<open>amb0_eq\<close>.\<close>
lemma poly_ethorner_count_gtrunc_loop_spec:
  assumes l2: "Suc 0 < length ys"
    and bound: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length ys * nat_bitlen (length ys) < max_snat LENGTH(gmp_poly_len)"
    and gbound: "g + length ys < max_snat LENGTH(gmp_poly_len)"
  shows "WHILET (\<lambda>st. ethorner_count_trunc_cond (length ys - 1) st)
                (\<lambda>st. truncate_ethorner_count_gtrunc_body_mop_monadic (length ys)
                        (nat_bitlen (length ys)) g st)
                ((0, 0, 0, amb0), ys)
     \<le> SPEC (\<lambda>((i, ls, cnt, amb), xsl).
           i \<le> length ys - 1 \<and> cnt \<le> 2 \<and> length xsl = length ys
         \<and> xsl = ethorner_outer_step_fun i ys
         \<and> \<not> (i < length ys - 1 \<and> cnt < 2)
         \<and> tmask_state_g g ys amb0 (ls, cnt, amb) i)"
  apply (refine_vcg WHILET_rule[where
        R="measure (\<lambda>((i, ls, cnt, amb), xsl :: int list). length ys - 1 - i)"
        and I="\<lambda>((i, ls, cnt, amb), xsl).
             i \<le> length ys - 1 \<and> cnt \<le> 2 \<and> length xsl = length ys
           \<and> xsl = ethorner_outer_step_fun i ys
           \<and> tmask_state_g g ys amb0 (ls, cnt, amb) i"])
  \<comment> \<open>13 goals (read off the goal state): 1 wf, 2-6 the init conjuncts, 7 the body,
     8-13 the exit conjuncts (invariant + negated loop condition)\<close>
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: tmask_state_g_init)
  \<comment> \<open>the body: destructure the atomic state so
     @{thm [source] ethorner_count_gtrunc_body_pres} unifies\<close>
  subgoal premises prems for s
  proof -
    obtain i ls cnt amb xsl where seq: "s = ((i, ls, cnt, amb), xsl)"
      by (metis prod.collapse)
    show ?thesis
      using prems
      unfolding seq
      apply (refine_vcg ethorner_count_gtrunc_body_pres)
      using l2 bound pbound gbound
      by (auto simp: seq ethorner_count_trunc_cond_def One_nat_def split: prod.splits)
  qed
  subgoal by (auto simp: ethorner_count_trunc_cond_def split: prod.splits)
  subgoal by (auto simp: ethorner_count_trunc_cond_def split: prod.splits)
  subgoal by (auto simp: ethorner_count_trunc_cond_def split: prod.splits)
  subgoal by (auto simp: ethorner_count_trunc_cond_def split: prod.splits)
  subgoal by (auto simp: ethorner_count_trunc_cond_def split: prod.splits)
  subgoal by (auto simp: ethorner_count_trunc_cond_def split: prod.splits)
  done

(*FASTLOOP_FREEZE_ABOVE*)
text \<open>Kernel classify against the FRAME (the exact reversed list \<open>Xr\<close> is a ghost —
  only the frame relates it to the argument). Statement-shape mirror of
  @{thm [source] poly_ethorner_count_trunc_monadic_classify}. \<open>gbound\<close> is needed because the
  kernel's own \<open>ASSERT (g + len < max_snat ...)\<close> needs SOME bound on \<open>g\<close>, and
  \<open>gframe\<close> alone never supplies one (\<open>g\<close> is a bare mathematical nat there). Every
  real call site (\<open>carried_descartes_count_g_monadic\<close>) only reaches this kernel in
  the \<open>\<not> (4398046511104 \<le> g)\<close> branch of its dispatch, so \<open>gbound\<close> is exactly what
  every caller already has in hand — not a new proof obligation on the loop.\<close>
lemma poly_ethorner_count_gtrunc_monadic_classify:
  assumes "gframe s g Xr ys"
    and "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
    and "g + length ys < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length ys * nat_bitlen (length ys) < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_ethorner_count_gtrunc_monadic g ys \<le> SPEC (\<lambda>(cnt, amb).
           (2 \<le> cnt \<longrightarrow> 2 \<le> sign_changes_fold (taylor_shift_list 1 Xr)) \<and>
           (\<not> amb \<longrightarrow>
              (cnt = 0) = (sign_changes_fold (taylor_shift_list 1 Xr) = 0) \<and>
              (cnt = 1) = (sign_changes_fold (taylor_shift_list 1 Xr) = 1) \<and>
              (2 \<le> cnt) = (2 \<le> sign_changes_fold (taylor_shift_list 1 Xr))))"
proof -
  have snatlen: "length ys < max_snat LENGTH(gmp_poly_len)" using assms(2) by simp
  have lenXr: "length Xr = length ys" using assms(1) unfolding gframe_def by simp
  show ?thesis
    unfolding truncate_ethorner_count_gtrunc_monadic_def
      ethorner_count_trunc_result_mop_monadic_def poly_length_monadic_def
      poly_coeff_sgn_monadic_def poly_coeff_bitlen2_monadic_def mpz_bitlen2_monadic_def
      lead_trust_mop_def bool_not_mop_def op_snat_unat_conv_def PR_CONST_def Let_def
    \<comment> \<open>the loop goes through \<open>poly_ethorner_count_gtrunc_loop_spec\<close> (seed as a parameter), not an
       inline @{thm [source] WHILET_rule}: the seed is the kernel's own decision, which an inline invariant
       cannot name.\<close>
    apply (refine_vcg snat_bitlen_monadic_correct[THEN order_trans]
        poly_ethorner_count_gtrunc_loop_spec[THEN order_trans])
    \<comment> \<open>goals 1-5: the \<open>length ys \<le> 1\<close> short-circuit\<close>
    subgoal by simp
    subgoal by simp
    subgoal using lenXr scf_taylor_short[of Xr] by simp
    subgoal using lenXr scf_taylor_short[of Xr] by simp
    subgoal using lenXr scf_taylor_short[of Xr] by simp
    \<comment> \<open>goals 6-12: side conditions + the loop lemma's own hypotheses\<close>
    subgoal by simp
    subgoal using snatlen by simp
    subgoal using pbound by simp
    subgoal using assms(3) by simp
    subgoal by simp
    subgoal by simp
    subgoal using assms(2) by simp
    \<comment> \<open>goals 13-17: the \<open>ef = 1\<close> boundary branch\<close>
    subgoal premises prems for x xa a b aa ba ab bb ac bc ad bd ae be af bf
      using prems small_lt_max_snat by auto
    subgoal premises prems for x xa a b aa ba ab bb ac bc ad bd ae be af bf x1 x2
    proof -
      define amb0 where "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
        \<or> sgn (ys ! (length ys - 1)) < 0 \<and> id g < x))"
      note pf = prems[folded amb0_def]
      have l2: "Suc 0 < length ys" using pf by simp
      have iinv: "aa \<le> length ys - 1" using pf by simp
      have cle: "ac \<le> 2" using pf by simp
      have exit: "\<not> (aa < length ys - 1 \<and> ac < 2)" using pf by simp
      have steq: "tmask_state_g g ys amb0 (ab, ac, bc) aa" using pf by simp
      have lead_lb: "ys ! (length ys - 1) \<noteq> 0 \<longrightarrow>
          2 ^ (x - 1) \<le> \<bar>ys ! (length ys - 1)\<bar>"
        using pf by blast
      have amb0_eq: "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
          \<or> sgn (ys ! (length ys - 1)) < 0 \<and> g < x))"
        unfolding amb0_def by simp
      have leadtr: "\<not> amb0" using pf unfolding amb0_def by simp
      have efeq: "(1::nat) = (if ab \<noteq> 0 \<and> \<not> amb0
          \<and> ab \<noteq> sgn (ys ! (length ys - 1)) then 1 else 0)"
        using pf leadtr by simp
      note main = ethorner_count_gtrunc_post[OF assms(1) l2 iinv cle lead_lb amb0_eq
          steq exit efeq]
      have cnteq: "x1 = ac + 1" using pf by simp
      have ambeq: "x2 = bc" using pf by simp
      have hx: "2 \<le> x1" using pf by simp
      have h: "2 \<le> ac + 1" using hx cnteq by simp
      show ?thesis using main h by (simp add: One_nat_def)
    qed
    subgoal premises prems for x xa a b aa ba ab bb ac bc ad bd ae be af bf x1 x2
    proof -
      define amb0 where "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
        \<or> sgn (ys ! (length ys - 1)) < 0 \<and> id g < x))"
      note pf = prems[folded amb0_def]
      have l2: "Suc 0 < length ys" using pf by simp
      have iinv: "aa \<le> length ys - 1" using pf by simp
      have cle: "ac \<le> 2" using pf by simp
      have exit: "\<not> (aa < length ys - 1 \<and> ac < 2)" using pf by simp
      have steq: "tmask_state_g g ys amb0 (ab, ac, bc) aa" using pf by simp
      have lead_lb: "ys ! (length ys - 1) \<noteq> 0 \<longrightarrow>
          2 ^ (x - 1) \<le> \<bar>ys ! (length ys - 1)\<bar>"
        using pf by blast
      have amb0_eq: "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
          \<or> sgn (ys ! (length ys - 1)) < 0 \<and> g < x))"
        unfolding amb0_def by simp
      have leadtr: "\<not> amb0" using pf unfolding amb0_def by simp
      have efeq: "(1::nat) = (if ab \<noteq> 0 \<and> \<not> amb0
          \<and> ab \<noteq> sgn (ys ! (length ys - 1)) then 1 else 0)"
        using pf leadtr by simp
      note main = ethorner_count_gtrunc_post[OF assms(1) l2 iinv cle lead_lb amb0_eq
          steq exit efeq]
      have cnteq: "x1 = ac + 1" using pf by simp
      have ambeq: "x2 = bc" using pf by simp
      have hx: "\<not> x2" using pf by simp
      have h: "\<not> bc" using hx ambeq by simp
      show ?thesis using main h cnteq by (simp add: One_nat_def)
    qed
    subgoal premises prems for x xa a b aa ba ab bb ac bc ad bd ae be af bf x1 x2
    proof -
      define amb0 where "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
        \<or> sgn (ys ! (length ys - 1)) < 0 \<and> id g < x))"
      note pf = prems[folded amb0_def]
      have l2: "Suc 0 < length ys" using pf by simp
      have iinv: "aa \<le> length ys - 1" using pf by simp
      have cle: "ac \<le> 2" using pf by simp
      have exit: "\<not> (aa < length ys - 1 \<and> ac < 2)" using pf by simp
      have steq: "tmask_state_g g ys amb0 (ab, ac, bc) aa" using pf by simp
      have lead_lb: "ys ! (length ys - 1) \<noteq> 0 \<longrightarrow>
          2 ^ (x - 1) \<le> \<bar>ys ! (length ys - 1)\<bar>"
        using pf by blast
      have amb0_eq: "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
          \<or> sgn (ys ! (length ys - 1)) < 0 \<and> g < x))"
        unfolding amb0_def by simp
      have leadtr: "\<not> amb0" using pf unfolding amb0_def by simp
      have efeq: "(1::nat) = (if ab \<noteq> 0 \<and> \<not> amb0
          \<and> ab \<noteq> sgn (ys ! (length ys - 1)) then 1 else 0)"
        using pf leadtr by simp
      note main = ethorner_count_gtrunc_post[OF assms(1) l2 iinv cle lead_lb amb0_eq
          steq exit efeq]
      have cnteq: "x1 = ac + 1" using pf by simp
      have ambeq: "x2 = bc" using pf by simp
      have hx: "\<not> x2" using pf by simp
      have h: "\<not> bc" using hx ambeq by simp
      show ?thesis using main h cnteq by (simp add: One_nat_def)
    qed
    subgoal premises prems for x xa a b aa ba ab bb ac bc ad bd ae be af bf x1 x2
    proof -
      define amb0 where "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
        \<or> sgn (ys ! (length ys - 1)) < 0 \<and> id g < x))"
      note pf = prems[folded amb0_def]
      have l2: "Suc 0 < length ys" using pf by simp
      have iinv: "aa \<le> length ys - 1" using pf by simp
      have cle: "ac \<le> 2" using pf by simp
      have exit: "\<not> (aa < length ys - 1 \<and> ac < 2)" using pf by simp
      have steq: "tmask_state_g g ys amb0 (ab, ac, bc) aa" using pf by simp
      have lead_lb: "ys ! (length ys - 1) \<noteq> 0 \<longrightarrow>
          2 ^ (x - 1) \<le> \<bar>ys ! (length ys - 1)\<bar>"
        using pf by blast
      have amb0_eq: "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
          \<or> sgn (ys ! (length ys - 1)) < 0 \<and> g < x))"
        unfolding amb0_def by simp
      have leadtr: "\<not> amb0" using pf unfolding amb0_def by simp
      have efeq: "(1::nat) = (if ab \<noteq> 0 \<and> \<not> amb0
          \<and> ab \<noteq> sgn (ys ! (length ys - 1)) then 1 else 0)"
        using pf leadtr by simp
      note main = ethorner_count_gtrunc_post[OF assms(1) l2 iinv cle lead_lb amb0_eq
          steq exit efeq]
      have cnteq: "x1 = ac + 1" using pf by simp
      have ambeq: "x2 = bc" using pf by simp
      have hx: "\<not> x2" using pf by simp
      have h: "\<not> bc" using hx ambeq by simp
      show ?thesis using main h cnteq by (simp add: One_nat_def)
    qed
    \<comment> \<open>goals 18-22: the \<open>ef = 0\<close> boundary branch\<close>
    subgoal premises prems for x xa a b aa ba ab bb ac bc ad bd ae be af bf
      using prems small_lt_max_snat by auto
    subgoal premises prems for x xa a b aa ba ab bb ac bc ad bd ae be af bf x1 x2
    proof -
      define amb0 where "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
        \<or> sgn (ys ! (length ys - 1)) < 0 \<and> id g < x))"
      note pf = prems[folded amb0_def]
      \<comment> \<open>the loop SPEC returns the count as \<open>x1\<close>; supply the link to \<open>ac\<close> as a simp
         RULE, not an inserted fact -- \<open>simp\<close> rewrites premises with EARLIER premises
         only, and the invariant premise precedes that equation\<close>
      \<comment> \<open>the early-abort sub-case: \<open>simp\<close> collapses the count to the LITERAL 2
         (from \<open>cnt \<le> 2\<close> and the branch's \<open>2 \<le> cnt\<close>), so rewrite the invariant
         FACT with that equation rather than fighting the goal normalisation\<close>
      have ac2: "ac = 2" using pf by simp
      note pf2 = pf[unfolded ac2]
      have x2eq: "x2 = bc" using pf2 by simp
      have afeq: "af = bc" using pf2 by simp
      have l2: "Suc 0 < length ys" using pf by simp
      have iinv: "aa \<le> length ys - 1" using pf2 by simp
      have cle: "(2::nat) \<le> 2" by simp
      have exit: "\<not> (aa < length ys - 1 \<and> (2::nat) < 2)" by simp
      have steq: "tmask_state_g g ys amb0 (ab, 2, bc) aa" using pf2 by simp
      have lead_lb: "ys ! (length ys - 1) \<noteq> 0 \<longrightarrow>
          2 ^ (x - 1) \<le> \<bar>ys ! (length ys - 1)\<bar>"
        using pf2 by blast
      have amb0_eq: "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
          \<or> sgn (ys ! (length ys - 1)) < 0 \<and> g < x))"
        unfolding amb0_def by simp
      have efeq: "(0::nat) = (if ab \<noteq> 0 \<and> \<not> amb0
          \<and> ab \<noteq> sgn (ys ! (length ys - 1)) then 1 else 0)"
        using pf2 by (auto simp: amb0_def)
      note main = ethorner_count_gtrunc_post[OF assms(1) l2 iinv cle lead_lb amb0_eq
          steq exit efeq]
      show ?thesis using main by (simp add: One_nat_def)
    qed
    subgoal premises prems for x xa a b aa ba ab bb ac bc ad bd ae be af bf x1 x2
    proof -
      define amb0 where "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
        \<or> sgn (ys ! (length ys - 1)) < 0 \<and> id g < x))"
      note pf = prems[folded amb0_def]
      \<comment> \<open>the loop SPEC returns the count as \<open>x1\<close>; supply the link to \<open>ac\<close> as a simp
         RULE, not an inserted fact -- \<open>simp\<close> rewrites premises with EARLIER premises
         only, and the invariant premise precedes that equation\<close>
      have x1eq: "x1 = ac" using pf by simp
      have x2eq: "x2 = bc" using pf by simp
      have adeq: "ad = ac" using pf by simp
      have afeq: "af = bc" using pf by simp
      have l2: "Suc 0 < length ys" using pf by simp
      have iinv: "aa \<le> length ys - 1" using pf by (simp add: x1eq adeq)
      have cle: "ac \<le> 2" using pf by (simp add: x1eq adeq)
      have exit: "\<not> (aa < length ys - 1 \<and> ac < 2)" using pf by (simp add: x1eq adeq)
      have steq: "tmask_state_g g ys amb0 (ab, ac, bc) aa" using pf by (simp add: x1eq x2eq adeq afeq)
      have lead_lb: "ys ! (length ys - 1) \<noteq> 0 \<longrightarrow>
          2 ^ (x - 1) \<le> \<bar>ys ! (length ys - 1)\<bar>"
        using pf by blast
      have amb0_eq: "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
          \<or> sgn (ys ! (length ys - 1)) < 0 \<and> g < x))"
        unfolding amb0_def by simp
      have efeq: "(0::nat) = (if ab \<noteq> 0 \<and> \<not> amb0
          \<and> ab \<noteq> sgn (ys ! (length ys - 1)) then 1 else 0)"
        using pf by (auto simp: amb0_def)
      note main = ethorner_count_gtrunc_post[OF assms(1) l2 iinv cle lead_lb amb0_eq
          steq exit efeq]
      have hx: "\<not> x2" using pf by simp
      have h: "\<not> bc" using hx x2eq by simp
      show ?thesis using main h x1eq by (simp add: One_nat_def)
    qed
    subgoal premises prems for x xa a b aa ba ab bb ac bc ad bd ae be af bf x1 x2
    proof -
      define amb0 where "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
        \<or> sgn (ys ! (length ys - 1)) < 0 \<and> id g < x))"
      note pf = prems[folded amb0_def]
      \<comment> \<open>the loop SPEC returns the count as \<open>x1\<close>; supply the link to \<open>ac\<close> as a simp
         RULE, not an inserted fact -- \<open>simp\<close> rewrites premises with EARLIER premises
         only, and the invariant premise precedes that equation\<close>
      have x1eq: "x1 = ac" using pf by simp
      have x2eq: "x2 = bc" using pf by simp
      have adeq: "ad = ac" using pf by simp
      have afeq: "af = bc" using pf by simp
      have l2: "Suc 0 < length ys" using pf by simp
      have iinv: "aa \<le> length ys - 1" using pf by (simp add: x1eq adeq)
      have cle: "ac \<le> 2" using pf by (simp add: x1eq adeq)
      have exit: "\<not> (aa < length ys - 1 \<and> ac < 2)" using pf by (simp add: x1eq adeq)
      have steq: "tmask_state_g g ys amb0 (ab, ac, bc) aa" using pf by (simp add: x1eq x2eq adeq afeq)
      have lead_lb: "ys ! (length ys - 1) \<noteq> 0 \<longrightarrow>
          2 ^ (x - 1) \<le> \<bar>ys ! (length ys - 1)\<bar>"
        using pf by blast
      have amb0_eq: "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
          \<or> sgn (ys ! (length ys - 1)) < 0 \<and> g < x))"
        unfolding amb0_def by simp
      have efeq: "(0::nat) = (if ab \<noteq> 0 \<and> \<not> amb0
          \<and> ab \<noteq> sgn (ys ! (length ys - 1)) then 1 else 0)"
        using pf by (auto simp: amb0_def)
      note main = ethorner_count_gtrunc_post[OF assms(1) l2 iinv cle lead_lb amb0_eq
          steq exit efeq]
      have hx: "\<not> x2" using pf by simp
      have h: "\<not> bc" using hx x2eq by simp
      show ?thesis using main h x1eq by (simp add: One_nat_def)
    qed
    subgoal premises prems for x xa a b aa ba ab bb ac bc ad bd ae be af bf x1 x2
    proof -
      define amb0 where "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
        \<or> sgn (ys ! (length ys - 1)) < 0 \<and> id g < x))"
      note pf = prems[folded amb0_def]
      \<comment> \<open>the loop SPEC returns the count as \<open>x1\<close>; supply the link to \<open>ac\<close> as a simp
         RULE, not an inserted fact -- \<open>simp\<close> rewrites premises with EARLIER premises
         only, and the invariant premise precedes that equation\<close>
      have x1eq: "x1 = ac" using pf by simp
      have x2eq: "x2 = bc" using pf by simp
      have adeq: "ad = ac" using pf by simp
      have afeq: "af = bc" using pf by simp
      have l2: "Suc 0 < length ys" using pf by simp
      have iinv: "aa \<le> length ys - 1" using pf by (simp add: x1eq adeq)
      have cle: "ac \<le> 2" using pf by (simp add: x1eq adeq)
      have exit: "\<not> (aa < length ys - 1 \<and> ac < 2)" using pf by (simp add: x1eq adeq)
      have steq: "tmask_state_g g ys amb0 (ab, ac, bc) aa" using pf by (simp add: x1eq x2eq adeq afeq)
      have lead_lb: "ys ! (length ys - 1) \<noteq> 0 \<longrightarrow>
          2 ^ (x - 1) \<le> \<bar>ys ! (length ys - 1)\<bar>"
        using pf by blast
      have amb0_eq: "amb0 = (\<not> (0 < sgn (ys ! (length ys - 1))
          \<or> sgn (ys ! (length ys - 1)) < 0 \<and> g < x))"
        unfolding amb0_def by simp
      have efeq: "(0::nat) = (if ab \<noteq> 0 \<and> \<not> amb0
          \<and> ab \<noteq> sgn (ys ! (length ys - 1)) then 1 else 0)"
        using pf by (auto simp: amb0_def)
      note main = ethorner_count_gtrunc_post[OF assms(1) l2 iinv cle lead_lb amb0_eq
          steq exit efeq]
      have hx: "\<not> x2" using pf by simp
      have h: "\<not> bc" using hx x2eq by simp
      show ?thesis using main h x1eq by (simp add: One_nat_def)
    qed
    done
qed

section \<open>The count dispatch (what the push site calls)\<close>

text \<open>\<open>xs\<close> borrowed, as in \<open>poly_ethorner_count_trunc_monadic\<close>. Returns \<open>(cnt, decisive)\<close>;
  on \<open>\<not> decisive\<close> the CALLER escalates (rebuild exact from the root, then the plain count). \<open>g = 0\<close>
  dispatches to the plain count — sound ONLY under the sentinel semantics
  (@{const node_frame}: \<open>g = 0\<close> means the argument IS the exact poly).\<close>
definition carried_descartes_count_g_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> (nat \<times> bool) nres" where
"carried_descartes_count_g_monadic xs g \<equiv>
  (if g = 0 then doN {
     cnt \<leftarrow> (PR_CONST carried_descartes_count_trunc_monadic) xs;
     RETURN (cnt, True)
   } else if 4398046511104 \<le> g then doN {
     \<comment> \<open>the EXACT-LOCK sentinel (\<open>2^42\<close>, above the \<open>2^41\<close> guard-saturation cap):
        this subtree escalated once and is locked exact-forever (see the retrunc
        note) — the poly IS exact, so dispatch to the plain count as for \<open>g = 0\<close>.\<close>
     cnt \<leftarrow> (PR_CONST carried_descartes_count_trunc_monadic) xs;
     RETURN (cnt, True)
   } else doN {
     rxs \<leftarrow> (PR_CONST poly_reverse_monadic) xs;
     ASSERT (length rxs + 1 < max_snat LENGTH(gmp_poly_len));
     (cnt, amb) \<leftarrow> (PR_CONST truncate_ethorner_count_gtrunc_monadic) g rxs;
     RETURN (cnt, \<not> amb \<or> 2 \<le> cnt)
   })"

sepref_register "PR_CONST carried_descartes_count_g_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> (nat \<times> bool) nres"

sepref_definition carried_descartes_count_g_impl [llvm_code] is
  "uncurry carried_descartes_count_g_monadic" ::
  "[\<lambda>(xs, g). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  unfolding carried_descartes_count_g_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma carried_descartes_count_g_impl_hnr[sepref_fr_rules]:
  "(uncurry carried_descartes_count_g_impl,
    uncurry (PR_CONST carried_descartes_count_g_monadic)) \<in>
    [\<lambda>(xs, g). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a bool1_assn"
  using carried_descartes_count_g_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The public contract — the classify trichotomy against the EXACT node \<open>X\<close>,
  gated by the decisive flag; the \<open>2 \<le> cnt\<close> lower bound holds unconditionally
  (early-abort soundness). Single length hypothesis, as everywhere.
  Route: \<open>g = 0\<close> branch = @{thm [source] carried_descartes_count_trunc_monadic_classify}
  after \<open>node_frame\<close> collapses \<open>X = xs\<close>; else \<open>gframe_rev\<close> + the kernel classify
  (geometry: \<open>carried_descartes_count X = sign_changes_fold (taylor_shift_list 1 (rev X))\<close>).\<close>
lemma carried_descartes_count_g_monadic_classify:
  assumes frame: "node_frame X xs g"
    and lbound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbound: "length xs * nat_bitlen (length xs) < max_snat LENGTH(gmp_poly_len)"
    and gbound: "g + length xs < max_snat LENGTH(gmp_poly_len)"
    and lock: "4398046511104 \<le> g \<longrightarrow> X = xs"
  shows "carried_descartes_count_g_monadic xs g \<le> SPEC (\<lambda>(cnt, dec).
           (2 \<le> cnt \<longrightarrow> 2 \<le> carried_descartes_count X) \<and>
           (dec \<longrightarrow>
              (cnt = 0) = (carried_descartes_count X = 0) \<and>
              (cnt = 1) = (carried_descartes_count X = 1) \<and>
              (2 \<le> cnt) = (2 \<le> carried_descartes_count X)))"
proof -
  obtain s0 where frame0: "gframe s0 g X xs" using frame node_frameE by blast
  have srev0: "gframe s0 g (rev X) (rev xs)" using gframe_rev[OF frame0] .
  show ?thesis
    unfolding carried_descartes_count_g_monadic_def PR_CONST_def
    apply (refine_vcg poly_reverse_monadic_correct[THEN order_trans]
        carried_descartes_count_trunc_monadic_classify[THEN order_trans]
        poly_ethorner_count_gtrunc_monadic_classify[OF srev0, THEN order_trans])
    subgoal using lbound by simp
    subgoal premises prems for x x1 x2
    proof -
      have xeq: "carried_descartes_count xs = carried_descartes_count X"
        using frame prems unfolding node_frame_def by simp
      show ?thesis using prems xeq by simp
    qed
    subgoal premises prems for x x1 x2
    proof -
      have xeq: "carried_descartes_count xs = carried_descartes_count X"
        using frame prems unfolding node_frame_def by simp
      show ?thesis using prems xeq by simp
    qed
    subgoal premises prems for x x1 x2
    proof -
      have xeq: "carried_descartes_count xs = carried_descartes_count X"
        using frame prems unfolding node_frame_def by simp
      show ?thesis using prems xeq by simp
    qed
    subgoal premises prems for x x1 x2
    proof -
      have xeq: "carried_descartes_count xs = carried_descartes_count X"
        using frame prems unfolding node_frame_def by simp
      show ?thesis using prems xeq by simp
    qed
    subgoal using lbound by simp
    subgoal premises prems for x x1 x2
    proof -
      have xeq: "carried_descartes_count xs = carried_descartes_count X"
        using lock prems by simp
      show ?thesis using prems xeq by simp
    qed
    subgoal premises prems for x x1 x2
    proof -
      have xeq: "carried_descartes_count xs = carried_descartes_count X"
        using lock prems by simp
      show ?thesis using prems xeq by simp
    qed
    subgoal premises prems for x x1 x2
    proof -
      have xeq: "carried_descartes_count xs = carried_descartes_count X"
        using lock prems by simp
      show ?thesis using prems xeq by simp
    qed
    subgoal premises prems for x x1 x2
    proof -
      have xeq: "carried_descartes_count xs = carried_descartes_count X"
        using lock prems by simp
      show ?thesis using prems xeq by simp
    qed
    subgoal using lbound by simp
    subgoal using lbound by simp
    subgoal using gbound by simp
    subgoal using pbound by simp
    subgoal premises prems for x a b x1 x2
      using prems unfolding carried_descartes_count_def by auto
    subgoal premises prems for x a b x1 x2
      using prems unfolding carried_descartes_count_def by auto
    subgoal premises prems for x a b x1 x2
      using prems unfolding carried_descartes_count_def by auto
    subgoal premises prems for x a b x1 x2
      using prems unfolding carried_descartes_count_def by auto
    done
qed


section \<open>The push-site re-truncation (the nb-gate)\<close>

text \<open>The re-truncation gate: fire iff \<open>2*len < nb\<close>, where \<open>nb\<close> is the bit length of the index-0 coefficient.
  The guard \<open>g\<close> does not gate the attempt; the saturating reset below absorbs it.

  \<^bold>\<open>Why not \<open>2*len + g < nb\<close> with \<open>g' := 1\<close>.\<close> After a truncation the index-0 coefficient holds exactly \<open>2*len\<close>
  bits; a left child then gains \<open>n = len-1\<close> bits while its guard gains the same \<open>n\<close> (the same \<open>2^(n-i)\<close> scaling
  drives both: @{const poly_shift_coeff_monadic} shifts coefficient \<open>i\<close> by \<open>n-i\<close>), so \<open>t\<close> and \<open>g\<close> grow in lockstep
  and \<open>t > g\<close> would never hold again: one truncation per path, followed by unbounded growth of \<open>g\<close> and repeated
  ambiguity.

  \<^bold>\<open>Why the leading coefficient is not protected.\<close> The top coefficient (index \<open>len-1\<close>) does not grow down the
  tree (unit scaling gives it \<open>2^0\<close>, and the shift by 1 leaves it unchanged), so it keeps the input's leading
  bit length; requiring it to survive would block almost every truncation. Truncating all coefficients, as
  msolve does, is sound: the list length is unchanged (transforms, counts and evaluation are list operations),
  the count's boundary trust reads the reversed lead, i.e. the index-0 end, and the contribution of a zeroed
  small leading coefficient is far below the guard the frame carries.

  The \<open>g\<close> argument remains in the signature and is unused.\<close>
definition retrunc_attempt_guard_mop :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
"retrunc_attempt_guard_mop len g nb \<equiv> doN {
  top \<leftarrow> RETURN (PR_CONST (trunc_max_snat_incl TYPE(gmp_poly_len)));
  cap2 \<leftarrow> RETURN (top div 2);
  if len \<le> cap2 then doN {
    ASSERT (2 * len < max_snat LENGTH(gmp_poly_len));
    l2 \<leftarrow> RETURN (2 * len);
    ASSERT (l2 \<le> top);
    \<comment> \<open>The fire threshold is \<open>nb > 2*len\<close>. The dominant cost is the shift and count kernels run on whatever
       operand size results, not the truncation pass itself, so letting operands grow further before truncating
       costs more than the skipped pass saves.\<close>
    if l2 < nb then (if nb \<le> top then RETURN True else RETURN False)
    else RETURN False
  } else RETURN False
}"

sepref_register "PR_CONST retrunc_attempt_guard_mop" :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres"

sepref_definition retrunc_attempt_guard_impl [llvm_inline] is
  "uncurry2 retrunc_attempt_guard_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding retrunc_attempt_guard_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma retrunc_attempt_guard_impl_hnr[sepref_fr_rules]:
  "(uncurry2 retrunc_attempt_guard_impl, uncurry2 (PR_CONST retrunc_attempt_guard_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using retrunc_attempt_guard_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The saturating guard reset: truncating \<open>t\<close> bits scales the old one-sided error \<open>< 2^g\<close> down to
  \<open>< 2^(g-t)\<close> and adds a fresh floor error \<open>< 1\<close>, so (one-sided floor division, both contributions in the same
  direction):
    \<open>error' < 1 + 2^(g-t) \<le> 2^1\<close>             when \<open>g \<le> t\<close>   \<Rightarrow> \<open>g' = 1\<close>
    \<open>error' < 1 + 2^(g-t) \<le> 2^(g-t+1)\<close>       when \<open>g > t\<close>   \<Rightarrow> \<open>g' = g - t + 1\<close>.
  With this reset a left child gains \<open>n\<close> coefficient bits and \<open>n\<close> guard bits per level, truncation fires at every
  level with \<open>t = n\<close>, and \<open>g\<close> grows by about 1 per level: operands stay near \<open>2*len\<close> bits, and escalations are
  \<open>O(len)\<close> levels apart.\<close>
definition retrunc_reset_mop :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where
"retrunc_reset_mop g t \<equiv>
  (if g \<le> t then RETURN (Suc 0)
   else doN {
     ASSERT (1 \<le> t);
     ASSERT (t \<le> g);
     ASSERT (g - t + 1 < max_snat LENGTH(gmp_poly_len));
     RETURN (g - t + 1)
   })"

sepref_register "PR_CONST retrunc_reset_mop" :: "nat \<Rightarrow> nat \<Rightarrow> nat nres"

sepref_definition retrunc_reset_impl [llvm_inline] is
  "uncurry retrunc_reset_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  unfolding retrunc_reset_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma retrunc_reset_impl_hnr[sepref_fr_rules]:
  "(uncurry retrunc_reset_impl, uncurry (PR_CONST retrunc_reset_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  using retrunc_reset_impl.refine by (simp add: PR_CONST_def)

text \<open>The gap tail reuses \<open>trunc_gap_mop\<close>: since \<open>trunc_count_margin = 0\<close>,
  \<open>trunc_gap_mop nb len = RETURN (nb - 2*len, nb - 2*len)\<close>, which is the needed gap. There is no
  leading-coefficient survival check (see the gate note above).\<close>
text \<open>\<^bold>\<open>The exact lock.\<close> On a cluster descent the two sign changes live in coefficients about
  \<open>2^(-2*residual)\<close> below the coefficient scale, so no fixed \<open>2*len\<close>-bit precision sees them: the truncated count is
  ambiguous at every cluster node, and each ambiguity forces an \<open>O(deg\<^sup>2*k\<^sup>2)\<close> rebuild from the root, after which the
  child would re-truncate and the cycle repeat. (msolve truncates only for the count and still holds the exact
  polynomial, so its exact fallback is free; carrying the truncation forward is what creates the cycle.) So an
  escalation returns the sentinel \<open>g = 4398046511104 = 2^42\<close> (above the \<open>2^41\<close> guard-saturation cap, below
  \<open>max_snat\<close>), meaning ``exact and locked, never re-truncate''. The child-guard bump preserves it, every sign
  consumer treats it as exact, and this op skips truncation for it. \<open>g = 0\<close> means ``exact and eligible for
  truncation'' (nodes descended from the root without truncation), so decisive subtrees still truncate when
  their budget allows.\<close>
definition carried_retrunc_mop :: "gmp_poly \<Rightarrow> nat \<Rightarrow> (gmp_poly \<times> nat) nres" where
"carried_retrunc_mop xs g \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  if len \<le> 1 then RETURN (xs, g)
  else if 4398046511104 \<le> g then RETURN (xs, g)
  else doN {
    ASSERT (0 < len \<and> len - 1 < length xs);
    (dbl, nb) \<leftarrow> (PR_CONST lead_budget_mop) xs 0;
    attempt \<leftarrow> (PR_CONST retrunc_attempt_guard_mop) len g nb;
    if \<not> attempt then RETURN (xs, g)
    else doN {
      ASSERT (2 * len \<le> nb);
      (t, tu) \<leftarrow> (PR_CONST trunc_gap_mop) nb len;
      ASSERT (0 < t \<and> t < max_snat LENGTH(gmp_poly_len));
      xs \<leftarrow> (PR_CONST poly_trunc_in_place_monadic) t xs;
      g' \<leftarrow> (PR_CONST retrunc_reset_mop) g t;
      RETURN (xs, g')
    }
  }
}"

sepref_register "PR_CONST carried_retrunc_mop"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> (gmp_poly \<times> nat) nres"

sepref_definition carried_retrunc_impl [llvm_code] is
  "uncurry carried_retrunc_mop" ::
  "[\<lambda>(xs, g). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding carried_retrunc_mop_def
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

lemma carried_retrunc_impl_hnr[sepref_fr_rules]:
  "(uncurry carried_retrunc_impl, uncurry (PR_CONST carried_retrunc_mop)) \<in>
    [\<lambda>(xs, g). length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using carried_retrunc_impl.refine
  by (simp add: PR_CONST_def)

text \<open>Frame preservation. Route (simpler than the original sketch): \<open>node_frameE\<close>
  works uniformly at ANY \<open>g\<close> (including \<open>g = 0\<close>, giving \<open>gframe s0 0 X xs\<close> since
  \<open>node_frame\<close>'s \<open>g = 0\<close> branch already forces \<open>X = xs\<close>) — so ONE obtained witness
  \<open>gframe s0 g X xs\<close> feeds BOTH of \<open>retrunc_reset_mop\<close>'s own branches directly,
  no separate \<open>gframe_trunc_exact\<close>/\<open>gframe_mono\<close> detour needed: \<open>g \<le> t\<close> \<Rightarrow>
  @{thm [source] gframe_trunc} (\<open>g' = 1\<close>); \<open>t < g\<close> \<Rightarrow> @{thm [source]
  gframe_retrunc_dom} (\<open>g' = g - t + 1\<close>). No-fire branches are identities.\<close>
lemma carried_retrunc_mop_frame:
  assumes frame: "node_frame X xs g"
    and lbound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and gbound: "g < max_snat LENGTH(gmp_poly_len)"
  shows "carried_retrunc_mop xs g \<le> SPEC (\<lambda>(ys, g'). node_frame X ys g')"
proof -
  obtain s0 where frame0: "gframe s0 g X xs" using frame node_frameE by blast
  show ?thesis
    unfolding carried_retrunc_mop_def poly_length_monadic_def
      retrunc_attempt_guard_mop_def retrunc_reset_mop_def trunc_gap_mop_def PR_CONST_def
    apply (refine_vcg poly_trunc_in_place_correct[THEN order_trans]
        lead_budget_mop_nofail[THEN order_trans])
    apply (all \<open>(simp; fail)?\<close>)
    subgoal using frame by simp
    subgoal using frame by simp
    subgoal by auto
    subgoal by auto
    subgoal using lbound by simp
    subgoal premises prems for x a b aa ba x1 x2
    proof -
      have geq: "g \<le> aa" using prems by simp
      have main: "node_frame X (trunc_list aa xs) (Suc 0)"
        using gframe_trunc[OF frame0 geq] unfolding node_frame_def by auto
      show ?thesis using main prems by simp
    qed
    subgoal using gbound by simp
    subgoal premises prems for x a b aa ba x1 x2
    proof -
      have tleg: "aa \<le> g" using prems by simp
      have main: "node_frame X (trunc_list aa xs) (g - aa + 1)"
        using gframe_retrunc_dom[OF frame0 tleg] unfolding node_frame_def by auto
      show ?thesis using main prems by simp
    qed
    subgoal using frame by simp
    subgoal using frame by simp
    subgoal using frame by simp
    done
qed

section \<open>Escalation — the exact rebuild from the borrowed root\<close>

text \<open>Frees the truncated node polynomial and rebuilds the exact carried polynomial over the node's own
  dyadic box \<open>(l, r, k)\<close> from the borrowed root polynomial \<open>rp\<close> (the variable is not called \<open>root\<close>, which is
  HOL's real \<open>n\<close>-th root constant). \<open>rp\<close> stays owned by the caller (the loop threads it \<open>\<^sup>k\<close>). The result equals
  the exact carried node up to a positive scalar (the \<open>carried_repr_scalar\<close> relation), which no sign or count
  consumer observes; the caller stores \<open>g := 0\<close>.\<close>
definition carried_escalate_exact_monadic ::
  "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
"carried_escalate_exact_monadic rp l r k qt \<equiv> doN {
  (PR_CONST poly_free_monadic) qt;
  ASSERT (0 < length rp);
  ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
  (PR_CONST carried_init_inplace_monadic) l k r rp
}"

sepref_register "PR_CONST carried_escalate_exact_monadic"
  :: "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

text \<open>Route: \<open>poly_free_monadic\<close> is value-transparent at nres level;
  @{thm [source] carried_init_inplace_monadic_correct}.\<close>
lemma carried_escalate_exact_monadic_correct:
  assumes "0 < length rp"
    and "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "carried_escalate_exact_monadic rp l r k qt
       \<le> RETURN (carried_init_same_den l (2 ^ k) r rp)"
  unfolding carried_escalate_exact_monadic_def PR_CONST_def
  apply (refine_vcg carried_init_inplace_monadic_correct[THEN order_trans])
  using assms by auto




section \<open>Dense-child mid-decision primitives\<close>

text \<open>Per-child guard amplification. The carried child transforms amplify the parent's one-sided coefficient
  error, so the child guards grow, by the tight per-transform bounds:
  \<^item> left (unit scaling, @{const poly_shift_coeff_monadic} shifts coefficient \<open>i\<close> by \<open>n-i\<close>, \<open>n = len-1\<close>):
    per-coefficient error \<open>err_i * 2^(n-i) < 2^(g+n-i)\<close>, uniformly \<open>2^(g+n)\<close> \<Rightarrow> \<open>gl = g + (len-1)\<close>;
  \<^item> right (shift by 1 of the scaled left): amplify, then uniformise. The scaling errors decay as \<open>2^(g+n-j)\<close>,
    and \<open>\<Sum>\<^sub>{\<^sub>j\<^sub>\<ge>\<^sub>i\<^sub>} C(j,i) * 2\<^sup>-\<^sup>j = 2\<close> for every \<open>i\<close> (generating function \<open>x^i/(1-x)^(i+1)\<close> at \<open>x = 1/2\<close>), so
    \<open>err_i^right \<le> \<Sum>\<^sub>j C(j,i) * 2^(g+n-j) = 2^(g+n) * 2 = 2^(g+n+1)\<close> \<Rightarrow> \<open>gr = g + len\<close>. (Uniformising first to
    \<open>2^(g+n)\<close> and then paying the binomial row sum \<open>2^n\<close> would give \<open>g + 2n + 1\<close>, which is sound but outgrows the
    real coefficient growth by about \<open>n\<close> bits per level.)
  Without amplification the error would be understated by about \<open>len\<close> bits per level, and the count kernel would
  trust signs that are truncation noise. The \<open>g = 0\<close> sentinel is preserved: the transforms are exact integer
  operations, so an exact parent has exact children. A numeral saturation cap keeps the op total: a saturated
  guard makes every negative sign untrusted, which leads to escalation (conservative, not unsound; positive-sign
  trust does not depend on magnitude, given the direction of the one-sided floor error).

  \<^bold>\<open>Lock payload.\<close> The lock branch returns \<open>g\<close> itself rather than the literal \<open>2^42\<close>. For the truncating solver
  this is the same value: its loop invariant carries \<open>g \<le> 4398046511104\<close> (\<open>Truncate_Loop_Refine\<close>, \<open>g_le\<close>/\<open>gbound\<close>),
  so \<open>g = 2^42\<close> on this branch. The hybrid solver encodes an exact \<open>v\<close>-bound as \<open>g = 2^42 + v\<close> on gate-open nodes,
  and every consumer of \<open>gs\<close> tests the lock by the inequality \<open>2^42 \<le> g\<close> (@{const carried_retrunc_mop},
  @{const carried_descartes_count_g_monadic}, \<open>truncate_mid_test_monadic\<close>,
  \<open>hybrid_cond_escalate\<close>/\<open>hybrid_resolve_count\<close>) and preserves \<open>g\<close>, so the payload is carried unchanged.\<close>
definition truncate_child_guards_mop :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) nres" where
"truncate_child_guards_mop g len \<equiv>
  (if g = 0 then RETURN (g, g)
   else if 4398046511104 \<le> g then RETURN (g, g)
   else if len = 0 then RETURN (g, g)
   else if 1099511627776 \<le> g then RETURN (2199023255552, 2199023255552)
   else if 1099511627776 \<le> len then RETURN (2199023255552, 2199023255552)
   else doN {
     ASSERT (0 < len);
     ASSERT (g < 1099511627776);
     ASSERT (len < 1099511627776);
     ASSERT (g + len < max_snat LENGTH(gmp_poly_len));
     RETURN (g + (len - 1), g + len)
   })"

sepref_register "PR_CONST truncate_child_guards_mop"
  :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) nres"

sepref_definition truncate_child_guards_impl [llvm_inline] is
  "uncurry truncate_child_guards_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  unfolding truncate_child_guards_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma truncate_child_guards_impl_hnr[sepref_fr_rules]:
  "(uncurry truncate_child_guards_impl,
    uncurry (PR_CONST truncate_child_guards_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    (snat_assn' TYPE(gmp_poly_len)) \<times>\<^sub>a (snat_assn' TYPE(gmp_poly_len))"
  using truncate_child_guards_impl.refine by (simp add: PR_CONST_def)

text \<open>The mid-zero test is OUTPUT-BEARING (it decides whether \<open>(m,m)\<close> is reported as an
  exact root, and whether an exact midpoint root survives into the open children at
  all), so on a TRUNCATED node it must be guarded against \<open>g\<close> like every other sign
  consumer: an unguarded test on truncated coefficients misreports exact midpoint roots
  (it did so on Wilkinson-type and quartic inputs). Guard exponent: the cleared-denominator eval at
  \<open>1/2\<close> is \<open>S = \<Sigma> c_i * 2^(len-1-i)\<close>, weights positive summing \<open>< 2^len\<close>, so the
  accumulated one-sided error is \<open>< 2^(g+len)\<close> — threshold \<open>gm = g + len\<close>, saturated
  with the same physically-unreachable numeral cap as @{const truncate_child_guards_mop}
  (a saturated \<open>gm\<close> exceeds any storable bitlen \<Rightarrow> negative evals untrusted \<Rightarrow>
  escalate \<Rightarrow> conservative).\<close>
definition mid_guard_mop :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where
"mid_guard_mop g len \<equiv>
  (if 1099511627776 \<le> g then RETURN 2199023255552
   else if 1099511627776 \<le> len then RETURN 2199023255552
   else doN {
     ASSERT (g < 1099511627776);
     ASSERT (len < 1099511627776);
     ASSERT (g + len < max_snat LENGTH(gmp_poly_len));
     RETURN (g + len)
   })"

sepref_register "PR_CONST mid_guard_mop" :: "nat \<Rightarrow> nat \<Rightarrow> nat nres"

sepref_definition mid_guard_impl [llvm_inline] is
  "uncurry mid_guard_mop" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  unfolding mid_guard_mop_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma mid_guard_impl_hnr[sepref_fr_rules]:
  "(uncurry mid_guard_impl, uncurry (PR_CONST mid_guard_mop)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a
    snat_assn' TYPE(gmp_poly_len)"
  using mid_guard_impl.refine by (simp add: PR_CONST_def)

text \<open>The \<open>_keep\<close> escalation variant for the call inside the loop: \<open>rp\<close> is owned by the body (a loop-state
  component), so the op takes it \<open>\<^sup>d\<close> and returns it in the pair, as @{const carried_descartes_count_keep_monadic}
  does. @{const carried_init_inplace_monadic} only borrows \<open>rp\<close>, so \<open>rp\<close> survives and is handed back.\<close>
definition carried_escalate_keep_monadic ::
  "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> gmp_poly) nres" where
"carried_escalate_keep_monadic rp l r k qt \<equiv> doN {
  (PR_CONST poly_free_monadic) qt;
  ASSERT (0 < length rp);
  ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT (k * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
  qx \<leftarrow> (PR_CONST carried_init_inplace_monadic) l k r rp;
  RETURN (qx, rp)
}"

sepref_register "PR_CONST carried_escalate_keep_monadic"
  :: "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> gmp_poly) nres"

text \<open>Sepref: \<open>rp\<close> is \<open>\<^sup>d\<close> (the \<open>_keep\<close> idiom — @{const carried_descartes_count_keep_monadic}'s
  own signature marks its survived-but-only-read argument \<open>\<^sup>d\<close> too, not \<open>\<^sup>k\<close>) and comes
  back in the result pair; internally \<open>carried_init_inplace_impl\<close> only borrows it
  (\<open>\<^sup>k\<close>), so the frame tracks it as valid throughout and matching on RETURN.\<close>
sepref_definition carried_escalate_keep_impl [llvm_code] is
  "uncurry4 carried_escalate_keep_monadic" ::
  "[\<lambda>((((rp, l), r), k), qt).
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a gmp_poly_assn"
  unfolding carried_escalate_keep_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  supply [sepref_fr_rules] = carried_init_inplace_impl_hnr
  by sepref

lemma carried_escalate_keep_impl_hnr[sepref_fr_rules]:
  "(uncurry4 carried_escalate_keep_impl,
    uncurry4 (PR_CONST carried_escalate_keep_monadic)) \<in>
    [\<lambda>((((rp, l), r), k), qt).
      0 < length rp \<and>
      length rp + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a gmp_poly_assn"
  using carried_escalate_keep_impl.refine
  by (simp add: PR_CONST_def)

section \<open>Midpoint sign from the child's constant coefficient\<close>

text \<open>The guarded midpoint test's numerator is \<open>S = poly (Poly (rev Q)) 2 = (\<Sum>i<len. Q!i * 2^(len-1-i))\<close>. Since
  @{const carried_left_coeff}\<open> Q i = Q!i * 2^(len-1-i)\<close>, \<open>S = sum_list (carried_left Q) = poly (Poly (carried_left Q)) 1\<close>,
  and @{const carried_right}\<open> = taylor_shift_list 1 (carried_left Q)\<close> with @{thm [source] Poly_taylor_shift_list}
  gives coefficient \<open>0\<close> of @{const carried_right}\<open> Q\<close> equal to \<open>S\<close>. So the \<open>O(len)\<close> half-evaluation loop
  (\<open>poly_hom_eval_trust_half_monadic\<close>) reduces to reading the sign and bit length of \<open>(carried_right Q) ! 0\<close>, and
  @{const carried_right}\<open> Q\<close> is the right child \<open>qr\<close> the split builds anyway, so the read is \<open>O(1)\<close> with no
  allocation.

  This op is \<open>truncate_children_monadic\<close> with the two borrowed reads of \<open>qr!0\<close> inserted before the
  re-truncation, so the read sees \<open>qr = carried_right Q\<close> exactly, whose one-sided truncation error is inherited
  from \<open>Q\<close>'s guard \<open>g\<close>: the \<open>g + len\<close> bound @{const mid_guard_mop} certifies. It returns the two truncated children
  and their guards, and \<open>(mids, midbl) = (sgn, bitlen)\<close> of \<open>qr!0\<close>.\<close>
definition truncate_children_mid_monadic ::
  "nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> int \<times> nat) nres" where
"truncate_children_mid_monadic g Q \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) Q;
  ASSERT (len = length Q);
  ASSERT (0 < len);
  (gl0, gr0) \<leftarrow> (PR_CONST truncate_child_guards_mop) g len;
  (ql, qr) \<leftarrow> (PR_CONST carried_left_right_monadic) Q;
  ASSERT (0 < length qr);
  mids \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) qr 0;
  midbl \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) qr 0;
  ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
  (ql, gl) \<leftarrow> (PR_CONST carried_retrunc_mop) ql gl0;
  ASSERT (length qr + 1 < max_snat LENGTH(gmp_poly_len));
  (qr, gr) \<leftarrow> (PR_CONST carried_retrunc_mop) qr gr0;
  RETURN (ql, gl, qr, gr, mids, midbl)
}"

sepref_register "PR_CONST truncate_children_mid_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> nat \<times> gmp_poly \<times> nat \<times> int \<times> nat) nres"

sepref_definition truncate_children_mid_impl [llvm_code] is
  "uncurry truncate_children_mid_monadic" ::
  "[\<lambda>(g, Q). length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
      gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
      gmp_sint_assn \<times>\<^sub>a gmp_size_assn"
  unfolding truncate_children_mid_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma truncate_children_mid_impl_hnr[sepref_fr_rules]:
  "(uncurry truncate_children_mid_impl,
    uncurry (PR_CONST truncate_children_mid_monadic)) \<in>
    [\<lambda>(g, Q). length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
      gmp_poly_assn \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a
      gmp_sint_assn \<times>\<^sub>a gmp_size_assn"
  using truncate_children_mid_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The midpoint decision from the child coefficient's \<open>(mids, midbl) = (sgn, bitlen)\<close>. It follows
  \<open>truncate_mid_test_monadic\<close>'s guard cascade with the \<open>O(1)\<close> reads in place of the half-evaluation, and returns a
  three-way code (the escalation needs the loop-state root \<open>rp\<close> and endpoints, which live in the branch):
  \<^item> \<open>0\<close>: not a root, proceed truncated;
  \<^item> \<open>1\<close>: the midpoint is an exact root;
  \<^item> \<open>2\<close>: ambiguous, the caller escalates (rebuild exact, decide again).
  Exact or locked nodes (\<open>g = 0\<close> or \<open>g \<ge> 2^42\<close>) carry \<open>qr!0 = S\<close> exactly, so the root test is \<open>mids = 0\<close>.
  \<open>2^40 \<le> g < 2^42\<close> is outside the trust window: escalate. Otherwise the trust tests
  @{const mid_guard_mop}/@{const lead_trust_mop} decide: trusted nonzero \<Rightarrow> not a root; ambiguous \<Rightarrow> escalate.\<close>
definition truncate_mid_decide_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat nres" where
"truncate_mid_decide_monadic g len mids midbl \<equiv>
  (if g = 0 then RETURN (if 0 < mids \<or> mids < 0 then 0 else 1)
   else if 4398046511104 \<le> g then RETURN (if 0 < mids \<or> mids < 0 then 0 else 1)
   else if 1099511627776 \<le> g then RETURN 2
   else doN {
     gm \<leftarrow> (PR_CONST mid_guard_mop) g len;
     tr \<leftarrow> (PR_CONST lead_trust_mop) mids midbl gm;
     RETURN (if tr then 0 else 2)
   })"

sepref_register "PR_CONST truncate_mid_decide_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat nres"

sepref_definition truncate_mid_decide_impl [llvm_inline] is
  "uncurry3 truncate_mid_decide_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    gmp_sint_assn\<^sup>k *\<^sub>a gmp_size_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding truncate_mid_decide_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)?
  by sepref

lemma truncate_mid_decide_impl_hnr[sepref_fr_rules]:
  "(uncurry3 truncate_mid_decide_impl,
    uncurry3 (PR_CONST truncate_mid_decide_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_sint_assn\<^sup>k *\<^sub>a gmp_size_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using truncate_mid_decide_impl.refine
  by (simp add: PR_CONST_def)

end
