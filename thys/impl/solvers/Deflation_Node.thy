theory Deflation_Node
  imports Deflation_Op Count
    "IsaRRI_LLVM.Interval_Eval"
    "IsaRRI_LLVM.Snat_Pow2"
begin

text \<open>\<open>Interval_Eval\<close> and \<open>Snat_Pow2\<close> are imported for two constants, \<open>slong_bounds\<close> and
  \<open>snat_to_slong_monadic\<close>, which the zero test on the certificate needs and which \<open>Poly_Ops\<close>'s imports do
  not reach.\<close>

section \<open>The node-level deflation step\<close>

text \<open>@{const defl_half_monadic} is the pass; this op runs it at a node: it decides the midpoint root
  from the certificate and hands back exactly one polynomial with the other freed, so the caller's
  ownership is the same whichever way the test goes.

  \<^bold>\<open>The test is the deflation, in two passes.\<close> By @{thm [source] defl_half_cert_eq_zero_iff} a zero
  certificate is equivalent to the local midpoint \<open>1/2\<close> being a root of the node polynomial, and by
  \<open>defl_step_is_division_by_one_minus_two_x\<close> (\<open>Deflation_Bridge\<close>) that is the global midpoint being a
  root. So an arithmetic-only \<open>O(n)\<close> pass (@{const defl_cert_monadic}) decides the branch, and the
  allocating pass (@{const defl_half_monadic}) runs only when the answer is yes; the runtime test refuses
  nothing the abstract recursion would have deflated.

  \<^bold>\<open>This op is stated for the exact operand only.\<close> On a truncated operand a small nonzero certificate
  may be truncation noise rather than a non-root, just as the guarded midpoint test can return
  ambiguous there. The solver uses the child-side op of the next section, which runs on the exact
  children.\<close>

subsection \<open>The op\<close>

definition defl_node_monadic :: "gmp_poly \<Rightarrow> (gmp_poly \<times> bool) nres" where
"defl_node_monadic Q \<equiv> doN {
   ASSERT (Q \<noteq> []);
   ASSERT (length Q + 1 < max_snat LENGTH(gmp_poly_len));
   ASSERT (slong_bounds (int 0));
   \<comment> \<open>Decide first, with the certificate-only pass: one \<open>mpz\<close>, no vector, \<open>Q\<close> borrowed. Building the
      quotient here would cost a fresh vector and an \<open>mpz_init_set\<close> per coefficient on every exact node,
      discarded wherever the midpoint is not a root.\<close>
   c \<leftarrow> (PR_CONST defl_cert_monadic) Q;
   z \<leftarrow> (PR_CONST snat_to_slong_monadic) 0;
   sg \<leftarrow> (PR_CONST mpz_cmp_si_sgn_monadic) c z;
   (PR_CONST mpzb_discard_monadic) c;
   if sg = 0 then doN {
     \<comment> \<open>Only now is the quotient worth building. The second pass re-derives the certificate
        too; it is discarded, and re-walking \<open>n\<close> coefficients is negligible against the
        \<open>O(n\<^sup>2)\<close> child build this deflation is about to make cheaper.\<close>
     (Qd, c2) \<leftarrow> (PR_CONST defl_half_monadic) Q;
     (PR_CONST mpzb_discard_monadic) c2;
     (PR_CONST poly_free_monadic) Q;
     RETURN (Qd, True)
   } else RETURN (Q, False)
 }"

subsection \<open>Correctness\<close>

text \<open>\<^bold>\<open>The specification pins the output list and mentions no polynomial product.\<close> Stating the fired
  case as \<open>Poly Q = [:1, -2:] * Poly Q'\<close> would hand the VCG's closer a goal whose two sides are
  polynomial products, which \<open>simp\<close> normalises into \<open>pCons\<close>/\<open>smult\<close> form and cannot close. Pinning
  \<open>Q' = defl_half_list Q\<close> is stronger and product-free; the algebraic reading is a corollary proved by
  one controlled \<open>rule\<close> step.\<close>

theorem defl_node_monadic_correct:
  assumes ne: "Q \<noteq> []"
      and bnd: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_node_monadic Q
           \<le> SPEC (\<lambda>(Q', fired).
                 fired = (defl_half_cert Q = 0)
               \<and> (fired \<longrightarrow> Q' = defl_half_list Q)
               \<and> (\<not> fired \<longrightarrow> Q' = Q))"
  unfolding defl_node_monadic_def snat_to_slong_monadic_def
            mpz_cmp_si_sgn_monadic_def mpzb_discard_monadic_def
            snat_sint_cast.mop_def PR_CONST_def
  apply (refine_vcg defl_cert_monadic_correct[OF ne bnd]
                    defl_half_monadic_correct[OF ne bnd])
  using ne bnd
  \<comment> \<open>\<open>simp_all\<close>, then one closer that does not depend on goal order: a positional \<open>subgoal\<close> chain breaks as
      soon as an earlier goal starts closing.\<close>
  apply (simp_all add: slong_bounds_def min_sint_def max_sint_def)
  \<comment> \<open>\<open>sgn_0_0\<close> is what turns the concrete comparison result back into the certificate's
      vanishing: @{const mpz_cmp_si_sgn_monadic} returns \<open>sgn (c - 0)\<close>, so the branch the
      solver takes is \<open>sgn c = 0\<close> and the spec speaks of \<open>c = 0\<close>.\<close>
  by (auto simp: sgn_0_0 split: if_splits)

text \<open>\<^bold>\<open>The algebraic reading\<close>, and the ONE place the product appears. Proved by
  \<open>rule\<close>, never by handing @{thm [source] defl_half_exact} to a \<open>simp\<close>.\<close>

corollary defl_node_monadic_deflates:
  assumes ne: "Q \<noteq> []"
      and bnd: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_node_monadic Q
           \<le> SPEC (\<lambda>(Q', fired).
                 (fired \<longrightarrow> Poly Q = [:1, -2:] * Poly Q'
                            \<and> length Q' = length Q - 1)
               \<and> (\<not> fired \<longrightarrow> Q' = Q))"
proof (rule order_trans[OF defl_node_monadic_correct[OF ne bnd]], rule SPEC_rule)
  fix r :: "gmp_poly \<times> bool"
  assume A: "case r of (Q', fired) \<Rightarrow>
               fired = (defl_half_cert Q = 0)
             \<and> (fired \<longrightarrow> Q' = defl_half_list Q)
             \<and> (\<not> fired \<longrightarrow> Q' = Q)"
  obtain Q' fired where r: "r = (Q', fired)" by (cases r)
  show "case r of (Q', fired) \<Rightarrow>
          (fired \<longrightarrow> Poly Q = [:1, -2:] * Poly Q' \<and> length Q' = length Q - 1)
        \<and> (\<not> fired \<longrightarrow> Q' = Q)"
  proof (cases fired)
    case True
    with A r have c0: "defl_half_cert Q = 0" and q': "Q' = defl_half_list Q" by auto
    have "Poly Q = [:1, -2:] * Poly (defl_half_list Q)" by (rule defl_half_exact[OF c0])
    thus ?thesis using True r q' by (simp add: length_defl_half_list)
  next
    case False
    with A r show ?thesis by auto
  qed
qed

text \<open>\<^bold>\<open>And the flag is the midpoint root test\<close>, which is what licenses replacing the
  \<open>O(1)\<close> read off the built child by this pass. \<open>Deflation_Bridge\<close> carries the other half —
  that the local half IS the global box midpoint.\<close>

corollary defl_node_fires_iff_local_half_root:
  assumes ne: "Q \<noteq> []"
      and bnd: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_node_monadic Q
           \<le> SPEC (\<lambda>(Q', fired).
                 fired = (poly (of_int_poly (Poly Q) :: rat poly) (1/2) = 0))"
  apply (rule order_trans[OF defl_node_monadic_correct[OF ne bnd]])
  by (auto simp: defl_half_cert_eq_zero_iff)

subsection \<open>Synthesis\<close>

sepref_register "PR_CONST defl_node_monadic"
  :: "gmp_poly \<Rightarrow> (gmp_poly \<times> bool) nres"

sepref_definition defl_node_impl [llvm_code] is
  "defl_node_monadic" ::
  "[\<lambda>Q. Q \<noteq> [] \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn \<times>\<^sub>a bool1_assn"
  unfolding defl_node_monadic_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const "TYPE(gmp_int_len)")?
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

lemma defl_node_impl_hnr[sepref_fr_rules]:
  "(defl_node_impl, PR_CONST defl_node_monadic) \<in>
    [\<lambda>Q. Q \<noteq> [] \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>d \<rightarrow> gmp_poly_assn \<times>\<^sub>a bool1_assn"
  using defl_node_impl.refine by (simp add: PR_CONST_def)

section \<open>Deflating the children after the build\<close>

text \<open>\<^bold>\<open>This op is the one the solver calls.\<close> The previous section decides the branch with
  @{const defl_cert_monadic}, an \<open>O(n)\<close> pass whose accumulator gains a bit per step. That pass computes
  \<open>carried_right Q ! 0\<close> (\<open>Deflation_Bridge.carried_right_nth0_eq_defl_one_cert\<close>), and
  \<open>truncate_children_mid_monadic\<close> already reads that value, borrowed and without cost, from a child it
  builds anyway. With this op, a node that does not shed runs no deflation code.

  \<^bold>\<open>Deflating the children needs no rebuild\<close>, because the shed root lies at a box endpoint of each child:

    \<^item> the right child has constant coefficient \<open>0\<close> \<Longrightarrow> divisible by \<open>x\<close> \<Longrightarrow> drop the head;
    \<^item> the left child vanishes at \<open>1\<close> \<Longrightarrow> divisible by \<open>1 - x\<close> \<Longrightarrow> one ascending pass.

  \<^bold>\<open>Both are then halved.\<close> The children above are exactly \<open>2\<close> and \<open>-2\<close> times the ones the
  deflate-then-dilate order produces, because \<open>carried_left\<close>'s scale exponent depends on the length of
  its own input (\<open>xs!i * 2\<^sup>(\<^sup>l\<^sup>e\<^sup>n\<^sup>-\<^sup>S\<^sup>u\<^sup>c\<^sup> \<^sup>i\<^sup>)\<close>): shedding the degree second dilates a length-\<open>n\<close> list where
  shedding it first dilates a length-\<open>n-1\<close> one. \<open>sign_changes\<close> ignores the scalar, but
  \<open>carried_retrunc_mop\<close> drops a fixed number of low bits, so where the smaller coefficient truncates to
  zero the doubled one truncates to \<open>\<plusminus>1\<close>, and the next level's dilation multiplies that unit by
  \<open>2\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>-\<^sup>i\<^sup>)\<close>. Equality up to a scalar is a statement about values, not about representation size.

  Up to the scalars \<open>2\<close> and \<open>-2\<close>, which \<open>sign_changes\<close> does not see, these are the children the
  deflated parent would have produced.

  \<^bold>\<open>The caller passes the exact children.\<close> \<open>carried_retrunc_mop\<close> may truncate a child even when the
  parent is exact, and a truncated operand's certificate proves nothing, so this op runs between the
  build and the retruncation, which is also where the \<open>qr!0\<close> read is taken.\<close>

definition defl_children_monadic ::
  "bool \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> gmp_poly \<times> bool) nres" where
"defl_children_monadic fire ql qr \<equiv> doN {
   ASSERT (ql \<noteq> []);
   ASSERT (qr \<noteq> []);
   ASSERT (length ql + 1 < max_snat LENGTH(gmp_poly_len));
   ASSERT (length qr + 1 < max_snat LENGTH(gmp_poly_len));
   if fire then doN {
     (ql', c) \<leftarrow> (PR_CONST defl_one_monadic) ql;
     (PR_CONST mpzb_discard_monadic) c;
     (PR_CONST poly_free_monadic) ql;
     qr' \<leftarrow> (PR_CONST defl_drop_monadic) qr;
     (PR_CONST poly_free_monadic) qr;
     \<comment> \<open>\<^bold>\<open>Remove the dilation's extra power of two.\<close> Both children come out exactly \<open>2\<close> and \<open>-2\<close> times the
        ones the deflate-then-dilate order produces, and every coefficient is even, so this is an exact
        halving and not a truncation. It is @{const poly_trunc_in_place_monadic} at \<open>t = 1\<close>, and it
        runs only on the firing branch, so \<open>defl_children_monadic False\<close> is a pure \<open>RETURN\<close>.\<close>
     ASSERT (length ql' + 1 < max_snat LENGTH(gmp_poly_len));
     ASSERT (length qr' + 1 < max_snat LENGTH(gmp_poly_len));
     ql' \<leftarrow> (PR_CONST poly_trunc_in_place_monadic) 1 ql';
     qr' \<leftarrow> (PR_CONST poly_trunc_in_place_monadic) 1 qr';
     RETURN (ql', qr', True)
   } else RETURN (ql, qr, False)
 }"

subsection \<open>Correctness\<close>

text \<open>\<^bold>\<open>Pinned outputs, no polynomial product\<close>, for the reason given in the previous section. The
  algebraic reading is the corollary below.\<close>

theorem defl_children_monadic_correct:
  assumes lne: "ql \<noteq> []" and rne: "qr \<noteq> []"
      and lb: "length ql + 1 < max_snat LENGTH(gmp_poly_len)"
      and rb: "length qr + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "defl_children_monadic fire ql qr
           \<le> SPEC (\<lambda>(ql', qr', fired).
                 fired = fire
               \<and> (fire \<longrightarrow> ql' = trunc_list 1 (defl_one_list ql)
                            \<and> qr' = trunc_list 1 (map uminus (tl qr)))
               \<and> (\<not> fire \<longrightarrow> ql' = ql \<and> qr' = qr))"
  unfolding defl_children_monadic_def mpzb_discard_monadic_def poly_free_monadic_def
            PR_CONST_def
  apply (refine_vcg defl_one_monadic_correct[OF lne lb]
                    defl_drop_monadic_correct[OF rne rb]
                    poly_trunc_in_place_correct[THEN order_trans])
  using lne rne lb rb by (simp_all add: length_defl_one_list)

subsection \<open>The halving is exact\<close>

text \<open>\<^bold>\<open>The fact the halving needs\<close> is a hypothesis here, like those of \<open>defl_children_monadic_exact\<close>,
  because its discharge names \<open>carried_left\<close> and is proved in \<open>Deflation_Bridge\<close>.

  \<^bold>\<open>Why it holds\<close> (\<open>carried_left_all_even_of_nth0\<close>): the fire condition is \<open>carried_right Q ! 0 = 0\<close>, and
  that coefficient is the plain sum of \<open>carried_left Q\<close>. Every entry of \<open>carried_left Q\<close> except the last
  carries a factor \<open>2\<^sup>(\<^sup>n\<^sup>-\<^sup>1\<^sup>-\<^sup>i\<^sup>)\<close> with a positive exponent, so the sum being zero forces the last one to be even
  too; hence all of \<open>carried_left Q\<close> is even, and so is every integer-linear image of it: the left child's
  partial sums, and the right child, which is \<open>taylor_shift_list 1\<close> of it.

  This is a soundness obligation: halving an odd coefficient is not a scaling and moves roots.\<close>

lemma trunc_list_1_exact:
  assumes "\<forall>x \<in> set xs. (2::int) dvd x"
  shows "map ((*) 2) (trunc_list 1 xs) = xs"
proof -
  have "map ((*) 2) (trunc_list 1 xs) = map (\<lambda>x. 2 * (x div 2)) xs"
    by (simp add: trunc_list_def)
  also have "\<dots> = xs"
    using assms by (intro map_idI) simp
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>And what it means, given the one read.\<close> Both hypotheses are supplied at the call site
  by \<open>mids = 0\<close>: \<open>qr ! 0 = 0\<close> is that read, and \<open>poly (Poly ql) 1 = 0\<close> is the same integer by
  \<open>Deflation_Bridge.carried_right_nth0_eq_left_poly_1\<close>. Stated here as hypotheses rather than
  derived, because the bridge names \<open>carried_left\<close>/\<open>carried_right\<close> and lives in a session this
  one cannot see (its parent is \<open>IsaRRI_LLVM\<close>).\<close>

lemma defl_drop_neg_exact:
  fixes ys :: "int list"
  assumes ne: "ys \<noteq> []" and hd0: "ys ! 0 = 0"
  shows "Poly ys = [:0, - 1:] * Poly (map uminus (tl ys))"
proof -
  have "Poly ys = [:0, 1:] * Poly (tl ys)" by (rule defl_drop0_exact[OF ne hd0])
  thus ?thesis by (simp only: defl_Poly_map_uminus) (simp add: algebra_simps)
qed

corollary defl_children_monadic_exact:
  assumes lne: "ql \<noteq> []" and rne: "qr \<noteq> []"
      and lb: "length ql + 1 < max_snat LENGTH(gmp_poly_len)"
      and rb: "length qr + 1 < max_snat LENGTH(gmp_poly_len)"
      and l1: "poly (Poly ql) 1 = 0"
      and r0: "qr ! 0 = 0"
      and le: "\<forall>x \<in> set (defl_one_list ql). (2::int) dvd x"
      and re: "\<forall>x \<in> set (map uminus (tl qr)). (2::int) dvd x"
  shows "defl_children_monadic fire ql qr
           \<le> SPEC (\<lambda>(ql', qr', fired).
                 fired \<longrightarrow> Poly ql = [:1, -1:] * Poly (map ((*) 2) ql')
                         \<and> Poly qr = [:0, - 1:] * Poly (map ((*) 2) qr'))"
  apply (rule order_trans[OF defl_children_monadic_correct[OF lne rne lb rb]])
  using defl_one_exact_of_poly_1[OF l1] defl_drop_neg_exact[OF rne r0]
        trunc_list_1_exact[OF le] trunc_list_1_exact[OF re]
  by auto

subsection \<open>Synthesis\<close>

sepref_register "PR_CONST defl_children_monadic"
  :: "bool \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly \<Rightarrow> (gmp_poly \<times> gmp_poly \<times> bool) nres"

sepref_definition defl_children_impl [llvm_code] is
  "uncurry2 defl_children_monadic" ::
  "[\<lambda>((_, ql), qr). ql \<noteq> [] \<and> qr \<noteq> []
       \<and> length ql + 1 < max_snat LENGTH(gmp_poly_len)
       \<and> length qr + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
      gmp_poly_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a bool1_assn"
  unfolding defl_children_monadic_def
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

lemma defl_children_impl_hnr[sepref_fr_rules]:
  "(uncurry2 defl_children_impl, uncurry2 (PR_CONST defl_children_monadic)) \<in>
    [\<lambda>((_, ql), qr). ql \<noteq> [] \<and> qr \<noteq> []
       \<and> length ql + 1 < max_snat LENGTH(gmp_poly_len)
       \<and> length qr + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>d \<rightarrow>
        gmp_poly_assn \<times>\<^sub>a gmp_poly_assn \<times>\<^sub>a bool1_assn"
  using defl_children_impl.refine by (simp add: PR_CONST_def)

end
