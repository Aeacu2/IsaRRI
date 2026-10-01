theory Lowdeg
  imports
    Kiou_Bound
    "IsaRRI_LLVM.Dyadic_Interval"
begin

text \<open>The degree-2 and degree-3 closed forms.

  For these degrees the number of real roots is decided by an exact integer discriminant, and in the
  cases this theory covers the isolating window is the root bound itself: no subdivision and no
  division. The covered cases:
    \<^item> degree 2, \<open>disc2 < 0\<close>: no real roots, emit nothing;
    \<^item> degree 2, \<open>disc2 > 0\<close>, \<open>a\<^sub>0*a\<^sub>2 < 0\<close>: the two roots straddle zero, so the pipeline's split at zero
      separates them and each arm has exactly one root;
    \<^item> degree 2, \<open>disc2 > 0\<close>, roots of one sign: a checked dyadic separator (below);
    \<^item> degree 3, \<open>disc3 < 0\<close>: exactly one real root, on the arm \<open>- sign (a\<^sub>3*a\<^sub>0)\<close> picks.
  Everything else falls through to the bisection solve, so this theory returns a classification;
  the dispatch lives in \<open>Lowdeg_Split\<close>.

  The real-analysis facts behind it are in \<open>IsaRRI_Spec.Lowdeg_Math\<close>; the abstract \<open>\<le> SPEC\<close>
  capstone is \<open>Lowdeg_Reflect\<close>.

  \<^bold>\<open>Why the ops are small.\<close> Each arithmetic step is its own registered op with its own
  \<open>sepref_definition\<close> rather than one long owned-\<open>mpz\<close> \<open>doN\<close> block.

  \<^bold>\<open>Why small constants go through @{const mpz_mul_si.aop_r1}\<close> rather than an \<open>mpz_from_int\<close>
  temporary: \<open>mpz_mul_si\<close> multiplies in place by a machine \<open>long\<close> and allocates nothing, whereas an
  owned temporary per constant is allocator overhead with no arithmetic behind it.\<close>

section \<open>Owned-mpz building blocks\<close>

text \<open>The product ops below multiply an owned mpz by a borrowed coefficient in place (\<open>arl_nth\<close> then
  \<open>mpz_mul.aop_r1_impl\<close>). For an mm locale the combined specification is
  \<open>spec and spec_xm2 and spec_mx2 and spec_mm2 and spec_xmm\<close>, and \<open>aop_r1_impl a b\<close> calls
  \<open>op a a b\<close>, the case where the result aliases the first operand (\<open>spec_mx2\<close>). The rule ladder
  follows \<open>poly_hom_eval_addmul\<close> in \<open>Interval_Eval\<close>, whose postcondition likewise carries an owned
  mpz beside the re-inserted slot.\<close>

section \<open>The BORROWED multiply --- one allocation per product instead of two\<close>

text \<open>\<^bold>\<open>A product op that reads its second operand in place.\<close>  @{const mpz_mul.amop_r1} wants its
  second operand as an owned \<open>mpz\<close> VALUE, which would force a copy out of the array. This op
  multiplies an owned \<open>mpz\<close> by a coefficient read IN PLACE: \<open>arl_nth\<close>, then
  @{const mpz_mul.aop_r1_impl}, which is \<open>a \<leftarrow> a * b\<close> over two pointers. Each product therefore
  avoids one \<open>mpz_init_set\<close> and one free.

  \<^bold>\<open>No new GMP binding.\<close>  @{const mpz_mul.aop_r1_impl} already exists and
  @{thm [source] mpz_mul.vcg_rule} already covers the aliased case
  (\<open>raw_mpz_mul ai ai bi\<close>), so nothing enters the trust base.

  \<^bold>\<open>The ladder is cloned from \<open>poly_hom_eval_addmul_impl_focused_rule\<close>\<close>
  (\<open>Interval_Eval.thy\<close> --- a PLAIN cartouche, not \<open>@{thm [source]}\<close>: that theory is
  not in this one's import closure and a resolving antiquotation would abort the load), NOT from
  the \<open>poly_coeff_bitlen2\<close> template: \<open>bitlen2\<close> returns a machine WORD, so no owned \<open>mpz\<close> ever
  crosses its focus/unfocus, while the addmul ladder carries exactly this shape --- an owned
  \<open>mpz\<close> in the post beside the re-inserted slot.\<close>

definition lowdeg_mulc_monadic :: "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> int nres" where
"lowdeg_mulc_monadic u xs j \<equiv> doN {
  ASSERT (j < length xs);
  RETURN (u * xs ! j)
}"

sepref_register "PR_CONST lowdeg_mulc_monadic" :: "int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]: "lowdeg_mulc_impl u p j \<equiv> doM {
  src \<leftarrow> arl_nth p j;
  mpz_mul.aop_r1_impl u src
}"

lemma lowdeg_mulc_impl_focused_rule:
  fixes p :: gmp_poly_raw and ji :: "gmp_poly_len word"
  assumes "j < length ptrs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>* mpzb_assn u ui \<and>* \<upharpoonleft>snat.assn j ji \<and>*
      mpzb_assn xj (ptrs ! j) \<and>* F)
    (lowdeg_mulc_impl ui p ji)
    (\<lambda>r. raw_al_assn ptrs p \<and>* (mpzb_assn xj (ptrs ! j) \<and>* F) \<and>* mpzb_assn (u * xj) r)"
  using assms
  unfolding lowdeg_mulc_impl_def mpz_mul.aop_r1_impl_def
  supply [vcg_rules] = dsc_arl_nth_rule_bounded[OF assms]
  supply [vcg_rules] = mpz_mul.vcg_rule
  apply vcg'
  apply ((clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sep_conj_c)?)
  apply ((fact Defer_Slot.remove_slot)?)
  done

lemma lowdeg_mulc_impl_ptrs_rule:
  fixes p :: gmp_poly_raw and ji :: "gmp_poly_len word"
  assumes "j < length xs" and "length ptrs = length xs"
  shows "llvm_htriple
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      mpzb_assn u ui \<and>* \<upharpoonleft>snat.assn j ji)
    (lowdeg_mulc_impl ui p ji)
    (\<lambda>r. raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>*
      mpzb_assn (u * xs ! j) r)"
  apply (rule htriple_ent_post)
   prefer 2
   apply (rule htriple_ent_pre)
    prefer 2
    \<comment> \<open>\<^bold>\<open>\<open>u\<close> must be pinned by the \<open>where\<close> clause.\<close>  The addmul analog gets away without
       naming its accumulator because the rule is applied against a pre in which \<open>mpzb_assn acc\<close>
       comes FIRST; here the owned operand sits behind the slot list, so \<open>htriple_ent_pre\<close> leaves
       it SCHEMATIC and the residual entailment is \<open>mpzb_assn ?u \<dots> \<Longrightarrow> mpzb_assn u \<dots>\<close> --- unprovable,
       and it reads as a frame failure rather than a missing instantiation.\<close>
    apply (rule lowdeg_mulc_impl_focused_rule[
      where ptrs=ptrs and j=j and u=u
        and F="\<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn)))
        ((map Some xs)[j := None]) ptrs"
        and xj="xs ! j"])
    using assms apply simp
   using assms
   apply (clarsimp simp: entails_def sep_algebra_simps sep_conj_c
     gmp_poly_slots_focus_coeff)
  using assms
  apply (clarsimp simp: entails_def sep_algebra_simps
    gmp_poly_slots_unfocus_coeff)
  done

text \<open>Length extraction under a trailing frame.  \<open>Interval_Eval.thy\<close> has the same fact under the
  name \<open>gmp_poly_raw_slots_frame_lenD\<close>, but that theory is not in this one's import closure --- and
  a fact cannot be imported by wishing.  Proved here under a lowdeg-local name, because sharing the
  name across two theories that may later co-load is exactly the silent-shadowing landmine lint C9
  exists to stop.\<close>
lemma lowdeg_raw_slots_frame_lenD:
  "pure_part
    (raw_al_assn ptrs p \<and>*
      \<upharpoonleft>(list_assn (oelem_assn (mk_assn mpzb_assn))) (map Some xs) ptrs \<and>* F)
    \<Longrightarrow> length ptrs = length xs"
  by (auto dest!: pure_part_split_conj gmp_poly_slots_len_frameD)

lemma lowdeg_mulc_impl_rule:
  fixes p :: gmp_poly_raw and ji :: "gmp_poly_len word"
  assumes "j < length xs"
  shows "llvm_htriple
    (gmp_poly_assn xs p \<and>* mpzb_assn u ui \<and>* \<upharpoonleft>snat.assn j ji)
    (lowdeg_mulc_impl ui p ji)
    (\<lambda>r. gmp_poly_assn xs p \<and>* mpzb_assn (u * xs ! j) r)"
  using assms
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def
  apply (simp add: sep_algebra_simps)
  apply (rule dsc_htriple_ex_preI)
  subgoal for ptrs
    apply (rule htriple_pure_preI)
    apply (frule lowdeg_raw_slots_frame_lenD)
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule lowdeg_mulc_impl_ptrs_rule[OF assms])
      apply assumption
    apply (clarsimp simp: entails_def sep_algebra_simps)
    subgoal for r s
      apply (rule exI[where x=ptrs])
      apply (simp add: sep_algebra_simps)
      done
    done
  done

lemma lowdeg_mulc_impl_hnr[sepref_fr_rules]:
  "(uncurry2 lowdeg_mulc_impl, uncurry2 (PR_CONST lowdeg_mulc_monadic)) \<in>
    [\<lambda>((u, xs), j). j < length xs]\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  apply sepref_to_hoare
  unfolding lowdeg_mulc_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  subgoal for j ji xs ph1 ph2 ph3 uv uh
    apply (rule htriple_pure_preI)
    apply (frule pure_part_split_conj)
    apply clarsimp
    apply (rule htriple_ent_post)
     prefer 2
     apply (rule htriple_ent_pre)
      prefer 2
      apply (rule lowdeg_mulc_impl_rule[where u=uv])
      apply assumption
    \<comment> \<open>\<^bold>\<open>Two residual goals, closed ORDER-INDEPENDENTLY.\<close>  The pre is \<open>mpzb \<and>* poly\<close> (the hnr's
       argument order) while \<open>lowdeg_mulc_impl_rule\<close> states \<open>poly \<and>* mpzb\<close>, so one goal is a bare
       two-factor COMMUTATION and the other is the \<open>\<exists>\<close>-result post.  The analog needs
       \<open>sep_conj_left_commute\<close> because its pre has three factors; two factors need plain
       \<open>sep_conj_commute\<close>, and it must stay a SEPARATE step --- folded into the \<open>clarsimp\<close> the
       permutative rule diverges over the heap splits (the analog records the same, painfully).\<close>
     \<comment> \<open>\<open>sep_conj_commute\<close> is not in this simp set and must stay a separate step: a permutative rule
        inside a \<open>clarsimp\<close> that is splitting heaps does not terminate in reasonable time.\<close>
     \<comment> \<open>\<^bold>\<open>The two steps are ONE closer, not two.\<close>  \<open>clarsimp\<close> makes PROGRESS on the pre
        entailment (it converts \<open>\<up>snat.assn\<close> into the pure relation) but does not finish it, and a
        step wrapped in \<open>solves\<close> that does not finish is DISCARDED --- so as separate closers the
        first was thrown away and the second met the untouched goal.  Sequenced with \<open>,\<close> the
        progress is kept, while \<open>sep_conj_commute\<close> still never enters the clarsimp's own simp set.\<close>
     apply (all \<open>(solves \<open>clarsimp simp: entails_def sep_algebra_simps
                    snat.assn_is_rel snat_rel_def pure_def,
                  simp add: sep_conj_commute\<close>)?\<close>)
     apply (all \<open>(solves \<open>clarsimp simp: entails_def sep_algebra_simps
                    dest!: pure_part_split_conj\<close>)?\<close>)
    done
  done


text \<open>\<open>xs!i * xs!j\<close> as a fresh owned \<open>mpz\<close>.  Both coefficients are COPIED out of the array
  (@{const poly_copy_coeff_monadic}) because @{const mpz_mul.amop_r1} consumes its first
  operand, and the array's slots must survive.\<close>
definition lowdeg_prod_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int nres" where
"lowdeg_prod_monadic xs i j \<equiv> doN {
  ASSERT (i < length xs);
  ASSERT (j < length xs);
  u \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs i;
  (PR_CONST lowdeg_mulc_monadic) u xs j
}"

lemma lowdeg_prod_monadic_correct:
  assumes "i < length xs" and "j < length xs"
  shows "lowdeg_prod_monadic xs i j \<le> RETURN (xs ! i * xs ! j)"
  using assms
  unfolding lowdeg_prod_monadic_def poly_copy_coeff_monadic_def
    lowdeg_mulc_monadic_def PR_CONST_def
  by refine_vcg auto

sepref_register "PR_CONST lowdeg_prod_monadic" :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition lowdeg_prod_impl [llvm_code] is
  "uncurry2 lowdeg_prod_monadic" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  unfolding lowdeg_prod_monadic_def
  by sepref

lemma lowdeg_prod_impl_hnr[sepref_fr_rules]:
  "(uncurry2 lowdeg_prod_impl, uncurry2 (PR_CONST lowdeg_prod_monadic)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  using lowdeg_prod_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The SQUARE is its own op, and that is an allocation decision.\<close>  @{const
  lowdeg_prod_monadic} copies both operands, so \<open>xs!i * xs!i\<close> through it would copy the same
  coefficient twice.  @{const mpz_mul.aop_r12} squares IN PLACE (it is what
  \<open>gmp_square_plus_ui_monadic\<close> uses), so one copy suffices.  Four of the products in the cubic
  discriminant are squares, and on this workload an avoided \<open>mpz\<close> allocation is worth more than
  the multiply it carries --- see the allocation note in the header.\<close>
definition lowdeg_sq_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int nres" where
"lowdeg_sq_monadic xs i \<equiv> doN {
  ASSERT (i < length xs);
  u \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs i;
  RETURN (mpz_mul.aop_r12 u)
}"

lemma lowdeg_sq_monadic_correct:
  assumes "i < length xs"
  shows "lowdeg_sq_monadic xs i \<le> RETURN (xs ! i * xs ! i)"
  using assms
  unfolding lowdeg_sq_monadic_def poly_copy_coeff_monadic_def
    mpz_mul.aop_r12_def PR_CONST_def
  by refine_vcg auto

sepref_register "PR_CONST lowdeg_sq_monadic" :: "gmp_poly \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition lowdeg_sq_impl [llvm_code] is
  "uncurry lowdeg_sq_monadic" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  unfolding lowdeg_sq_monadic_def
  by sepref

lemma lowdeg_sq_impl_hnr[sepref_fr_rules]:
  "(uncurry lowdeg_sq_impl, uncurry (PR_CONST lowdeg_sq_monadic)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  using lowdeg_sq_impl.refine by (simp add: PR_CONST_def)

section \<open>The degree-2 discriminant\<close>

text \<open>\<open>disc2 = a\<^sub>1\<^sup>2 - 4*a\<^sub>2*a\<^sub>0\<close>, on the three coefficients at \<open>i0 < i1 < i2\<close>.  Taking the
  indices as arguments is what lets the degree-3 discriminant reuse this on \<open>(a\<^sub>1,a\<^sub>2,a\<^sub>3)\<close>.\<close>
definition lowdeg_disc2_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int nres" where
"lowdeg_disc2_monadic xs i0 i1 i2 \<equiv> doN {
  ASSERT (i0 < length xs); ASSERT (i1 < length xs); ASSERT (i2 < length xs);
  z \<leftarrow> (PR_CONST lowdeg_sq_monadic) xs i1;
  t \<leftarrow> (PR_CONST lowdeg_prod_monadic) xs i2 i0;
  t \<leftarrow> RETURN (mpz_mul_si.aop_r1 t (- 4));
  z \<leftarrow> (PR_CONST mpz_add_monadic) z t;
  (PR_CONST mpzb_discard_monadic) t;
  RETURN z
}"

lemma lowdeg_disc2_monadic_correct:
  assumes "i0 < length xs" and "i1 < length xs" and "i2 < length xs"
  shows "lowdeg_disc2_monadic xs i0 i1 i2
           \<le> RETURN (xs ! i1 * xs ! i1 - 4 * (xs ! i2 * xs ! i0))"
  using assms
  unfolding lowdeg_disc2_monadic_def mpz_add_monadic_def mpzb_discard_monadic_def
    mpz_mul_si.aop_r1_def PR_CONST_def
  by (refine_vcg lowdeg_sq_monadic_correct[THEN order_trans]
                 lowdeg_prod_monadic_correct[THEN order_trans]) auto

sepref_register "PR_CONST lowdeg_disc2_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition lowdeg_disc2_impl [llvm_code] is
  "uncurry3 lowdeg_disc2_monadic" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  unfolding lowdeg_disc2_monadic_def
  apply (annot_sint_const gmp_long_t)
  by sepref

lemma lowdeg_disc2_impl_hnr[sepref_fr_rules]:
  "(uncurry3 lowdeg_disc2_impl, uncurry3 (PR_CONST lowdeg_disc2_monadic)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  using lowdeg_disc2_impl.refine by (simp add: PR_CONST_def)

text \<open>Only the SIGN is ever consumed, so the value is freed here rather than handed up.\<close>
definition lowdeg_disc2_sgn_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int nres" where
"lowdeg_disc2_sgn_monadic xs i0 i1 i2 \<equiv> doN {
  z \<leftarrow> (PR_CONST lowdeg_disc2_monadic) xs i0 i1 i2;
  s \<leftarrow> (PR_CONST mpz_sgn_mop) z;
  (PR_CONST mpzb_discard_monadic) z;
  RETURN s
}"

lemma lowdeg_disc2_sgn_monadic_correct:
  assumes "i0 < length xs" and "i1 < length xs" and "i2 < length xs"
  shows "lowdeg_disc2_sgn_monadic xs i0 i1 i2
           \<le> RETURN (sgn (xs ! i1 * xs ! i1 - 4 * (xs ! i2 * xs ! i0)))"
  using assms
  unfolding lowdeg_disc2_sgn_monadic_def mpz_sgn_mop_def mpzb_discard_monadic_def PR_CONST_def
  by (refine_vcg lowdeg_disc2_monadic_correct[THEN order_trans]) auto

sepref_register "PR_CONST lowdeg_disc2_sgn_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition lowdeg_disc2_sgn_impl [llvm_code] is
  "uncurry3 lowdeg_disc2_sgn_monadic" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  unfolding lowdeg_disc2_sgn_monadic_def
  by sepref

lemma lowdeg_disc2_sgn_impl_hnr[sepref_fr_rules]:
  "(uncurry3 lowdeg_disc2_sgn_impl, uncurry3 (PR_CONST lowdeg_disc2_sgn_monadic)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  using lowdeg_disc2_sgn_impl.refine by (simp add: PR_CONST_def)

section \<open>The opposite-sign test\<close>

text \<open>\<open>a\<^sub>i * a\<^sub>j < 0\<close> decided from the two coefficient SIGNS --- no multiplication, and no
  \<open>mpz\<close> at all: @{const poly_coeff_sgn_monadic} is a borrowed read.\<close>
definition lowdeg_opp_sgn_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
"lowdeg_opp_sgn_monadic xs i j \<equiv> doN {
  ASSERT (i < length xs); ASSERT (j < length xs);
  si \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs i;
  sj \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs j;
  RETURN ((si < 0 \<and> 0 < sj) \<or> (0 < si \<and> sj < 0))
}"

lemma lowdeg_opp_sgn_monadic_correct:
  assumes "i < length xs" and "j < length xs"
  shows "lowdeg_opp_sgn_monadic xs i j \<le> RETURN (xs ! i * xs ! j < 0)"
  using assms
  unfolding lowdeg_opp_sgn_monadic_def poly_coeff_sgn_monadic_def PR_CONST_def
  by refine_vcg (auto simp: mult_less_0_iff)

sepref_register "PR_CONST lowdeg_opp_sgn_monadic" :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres"

sepref_definition lowdeg_opp_sgn_impl [llvm_code] is
  "uncurry2 lowdeg_opp_sgn_monadic" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding lowdeg_opp_sgn_monadic_def
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma lowdeg_opp_sgn_impl_hnr[sepref_fr_rules]:
  "(uncurry2 lowdeg_opp_sgn_impl, uncurry2 (PR_CONST lowdeg_opp_sgn_monadic)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using lowdeg_opp_sgn_impl.refine by (simp add: PR_CONST_def)


section \<open>The degree-3 discriminant\<close>

text \<open>\<open>disc3 = 18abcd - 4b\<^sup>3d + b\<^sup>2c\<^sup>2 - 4ac\<^sup>3 - 27a\<^sup>2d\<^sup>2\<close> with \<open>a = xs!3 \<dots> d = xs!0\<close>, computed in
  the regrouped form
      \<open>d*(18abc - 4b\<^sup>3 - 27a\<^sup>2d) + c\<^sup>2*(b\<^sup>2 - 4ac)\<close>
  which reuses @{const lowdeg_disc2_monadic} verbatim for the second bracket (on the indices
  \<open>(c,b,a) = (1,2,3)\<close>) and needs no term of degree higher than three in the coefficients.\<close>

definition lowdeg_prod3_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int nres" where
"lowdeg_prod3_monadic xs i j k \<equiv> doN {
  ASSERT (i < length xs); ASSERT (j < length xs); ASSERT (k < length xs);
  w \<leftarrow> (PR_CONST lowdeg_prod_monadic) xs i j;
  (PR_CONST lowdeg_mulc_monadic) w xs k
}"

lemma lowdeg_prod3_monadic_correct:
  assumes "i < length xs" and "j < length xs" and "k < length xs"
  shows "lowdeg_prod3_monadic xs i j k \<le> RETURN (xs ! i * xs ! j * xs ! k)"
  using assms
  unfolding lowdeg_prod3_monadic_def lowdeg_mulc_monadic_def PR_CONST_def
  by (refine_vcg lowdeg_prod_monadic_correct[THEN order_trans]) auto

sepref_register "PR_CONST lowdeg_prod3_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition lowdeg_prod3_impl [llvm_code] is
  "uncurry3 lowdeg_prod3_monadic" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  unfolding lowdeg_prod3_monadic_def
  by sepref

lemma lowdeg_prod3_impl_hnr[sepref_fr_rules]:
  "(uncurry3 lowdeg_prod3_impl, uncurry3 (PR_CONST lowdeg_prod3_monadic)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  using lowdeg_prod3_impl.refine by (simp add: PR_CONST_def)

text \<open>\<open>xs!i\<^sup>2 * xs!j\<close>: the shape of both \<open>b\<^sup>3\<close> (as \<open>b\<^sup>2*b\<close>) and \<open>a\<^sup>2*d\<close>, at one copy fewer than
  @{const lowdeg_prod3_monadic} would take.\<close>
definition lowdeg_sqmul_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int nres" where
"lowdeg_sqmul_monadic xs i j \<equiv> doN {
  ASSERT (i < length xs); ASSERT (j < length xs);
  w \<leftarrow> (PR_CONST lowdeg_sq_monadic) xs i;
  (PR_CONST lowdeg_mulc_monadic) w xs j
}"

lemma lowdeg_sqmul_monadic_correct:
  assumes "i < length xs" and "j < length xs"
  shows "lowdeg_sqmul_monadic xs i j \<le> RETURN (xs ! i * xs ! i * xs ! j)"
  using assms
  unfolding lowdeg_sqmul_monadic_def lowdeg_mulc_monadic_def PR_CONST_def
  by (refine_vcg lowdeg_sq_monadic_correct[THEN order_trans]) auto

sepref_register "PR_CONST lowdeg_sqmul_monadic" :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition lowdeg_sqmul_impl [llvm_code] is
  "uncurry2 lowdeg_sqmul_monadic" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  unfolding lowdeg_sqmul_monadic_def
  by sepref

lemma lowdeg_sqmul_impl_hnr[sepref_fr_rules]:
  "(uncurry2 lowdeg_sqmul_impl, uncurry2 (PR_CONST lowdeg_sqmul_monadic)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  using lowdeg_sqmul_impl.refine by (simp add: PR_CONST_def)

definition lowdeg_disc3_int :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"lowdeg_disc3_int a b c d = 18*a*b*c*d - 4*b*b*b*d + b*b*c*c - 4*a*c*c*c - 27*a*a*d*d"

lemma lowdeg_disc3_int_regrouped:
  "lowdeg_disc3_int a b c d
     = d*(18*a*b*c - 4*(b*b*b) - 27*(a*a*d)) + (c*c)*(b*b - 4*(a*c))"
  unfolding lowdeg_disc3_int_def by algebra

definition lowdeg_disc3_monadic :: "gmp_poly \<Rightarrow> int nres" where
"lowdeg_disc3_monadic xs \<equiv> doN {
  ASSERT (4 \<le> length xs);
  R  \<leftarrow> (PR_CONST lowdeg_disc2_monadic) xs 1 2 3;
  C2 \<leftarrow> (PR_CONST lowdeg_sq_monadic) xs 1;
  W  \<leftarrow> (PR_CONST lowdeg_prod3_monadic) xs 3 2 1;
  X  \<leftarrow> (PR_CONST lowdeg_sqmul_monadic) xs 2 2;
  Y  \<leftarrow> (PR_CONST lowdeg_sqmul_monadic) xs 3 0;
  S  \<leftarrow> RETURN (mpz_mul_si.aop_r1 W 18);
  X  \<leftarrow> RETURN (mpz_mul_si.aop_r1 X (- 4));
  S  \<leftarrow> (PR_CONST mpz_add_monadic) S X;
  (PR_CONST mpzb_discard_monadic) X;
  Y  \<leftarrow> RETURN (mpz_mul_si.aop_r1 Y (- 27));
  S  \<leftarrow> (PR_CONST mpz_add_monadic) S Y;
  (PR_CONST mpzb_discard_monadic) Y;
  d1 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 0;
  E  \<leftarrow> (PR_CONST mpz_mul.amop_r1) d1 S;
  (PR_CONST mpzb_discard_monadic) S;
  R  \<leftarrow> (PR_CONST mpz_mul.amop_r1) R C2;
  (PR_CONST mpzb_discard_monadic) C2;
  E  \<leftarrow> (PR_CONST mpz_add_monadic) E R;
  (PR_CONST mpzb_discard_monadic) R;
  RETURN E
}"

lemma lowdeg_disc3_monadic_correct:
  assumes "4 \<le> length xs"
  shows "lowdeg_disc3_monadic xs
           \<le> RETURN (lowdeg_disc3_int (xs ! 3) (xs ! 2) (xs ! 1) (xs ! 0))"
proof -
  have b0: "(0::nat) < length xs" and b1: "(1::nat) < length xs"
    and b2: "(2::nat) < length xs" and b3: "(3::nat) < length xs"
    using assms by auto
  show ?thesis
    using assms
    unfolding lowdeg_disc3_monadic_def mpz_add_monadic_def mpzb_discard_monadic_def
      poly_copy_coeff_monadic_def mpz_mul_si.aop_r1_def
      mpz_mul.amop_r1_def mpz_mul.aop_r1_def PR_CONST_def
    by (refine_vcg lowdeg_disc2_monadic_correct[THEN order_trans]
                   lowdeg_sq_monadic_correct[THEN order_trans]
                   lowdeg_sqmul_monadic_correct[THEN order_trans]
                   lowdeg_prod_monadic_correct[THEN order_trans]
                   lowdeg_prod3_monadic_correct[THEN order_trans])
       (auto simp: b0 b1 b2 b3 lowdeg_disc3_int_regrouped)
qed

sepref_register "PR_CONST lowdeg_disc3_monadic" :: "gmp_poly \<Rightarrow> int nres"

sepref_definition lowdeg_disc3_impl [llvm_code] is
  "lowdeg_disc3_monadic" :: "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  unfolding lowdeg_disc3_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_long_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma lowdeg_disc3_impl_hnr[sepref_fr_rules]:
  "(lowdeg_disc3_impl, PR_CONST lowdeg_disc3_monadic) \<in> gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  using lowdeg_disc3_impl.refine by (simp add: PR_CONST_def)

definition lowdeg_disc3_sgn_monadic :: "gmp_poly \<Rightarrow> int nres" where
"lowdeg_disc3_sgn_monadic xs \<equiv> doN {
  z \<leftarrow> (PR_CONST lowdeg_disc3_monadic) xs;
  s \<leftarrow> (PR_CONST mpz_sgn_mop) z;
  (PR_CONST mpzb_discard_monadic) z;
  RETURN s
}"

lemma lowdeg_disc3_sgn_monadic_correct:
  assumes "4 \<le> length xs"
  shows "lowdeg_disc3_sgn_monadic xs
           \<le> RETURN (sgn (lowdeg_disc3_int (xs ! 3) (xs ! 2) (xs ! 1) (xs ! 0)))"
  using assms
  unfolding lowdeg_disc3_sgn_monadic_def mpz_sgn_mop_def mpzb_discard_monadic_def PR_CONST_def
  by (refine_vcg lowdeg_disc3_monadic_correct[THEN order_trans]) auto

sepref_register "PR_CONST lowdeg_disc3_sgn_monadic" :: "gmp_poly \<Rightarrow> int nres"

sepref_definition lowdeg_disc3_sgn_impl [llvm_code] is
  "lowdeg_disc3_sgn_monadic" :: "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  unfolding lowdeg_disc3_sgn_monadic_def
  by sepref

lemma lowdeg_disc3_sgn_impl_hnr[sepref_fr_rules]:
  "(lowdeg_disc3_sgn_impl, PR_CONST lowdeg_disc3_sgn_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  using lowdeg_disc3_sgn_impl.refine by (simp add: PR_CONST_def)


text \<open>The THREE-WAY sign of \<open>a\<^sub>i * a\<^sub>j\<close>: \<open>0\<close> zero, \<open>1\<close> negative, \<open>2\<close> positive.  Degree 3 needs all
  three outcomes (negative root / positive root / root AT the origin), and this returns them
  using only \<open>&lt;\<close> comparisons on the two coefficient signs --- an EQUALITY test against \<open>0\<close> on a
  \<open>gmp_sint\<close> stops Sepref's \<open>trans\<close> phase, while \<open>&lt;\<close> is already registered.\<close>
definition lowdeg_sgn_prod_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where
"lowdeg_sgn_prod_monadic xs i j \<equiv> doN {
  ASSERT (i < length xs); ASSERT (j < length xs);
  si \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs i;
  sj \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs j;
  if (si < 0 \<and> 0 < sj) \<or> (0 < si \<and> sj < 0) then RETURN 1
  else if (si < 0 \<and> sj < 0) \<or> (0 < si \<and> 0 < sj) then RETURN 2
  else RETURN 0
}"

lemma lowdeg_sgn_prod_monadic_correct:
  assumes "i < length xs" and "j < length xs"
  shows "lowdeg_sgn_prod_monadic xs i j
           \<le> RETURN (if xs ! i * xs ! j < 0 then 1 else if 0 < xs ! i * xs ! j then 2 else 0)"
  using assms
  unfolding lowdeg_sgn_prod_monadic_def poly_coeff_sgn_monadic_def PR_CONST_def
  by refine_vcg (auto simp: mult_less_0_iff zero_less_mult_iff)

sepref_register "PR_CONST lowdeg_sgn_prod_monadic" :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres"

sepref_definition lowdeg_sgn_prod_impl [llvm_code] is
  "uncurry2 lowdeg_sgn_prod_monadic" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
     (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding lowdeg_sgn_prod_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma lowdeg_sgn_prod_impl_hnr[sepref_fr_rules]:
  "(uncurry2 lowdeg_sgn_prod_impl, uncurry2 (PR_CONST lowdeg_sgn_prod_monadic)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using lowdeg_sgn_prod_impl.refine by (simp add: PR_CONST_def)

section \<open>The degree-2 SAME-SIGN separator\<close>

text \<open>When \<open>disc2 > 0\<close> but the two roots do not straddle zero, the pipeline's split at zero does not
  separate them and a separator is needed.

  \<^bold>\<open>The criterion is division-free and needs no radical.\<close> \<open>quad_square_id\<close>
  (\<open>IsaRRI_Spec.Lowdeg_Math\<close>) gives \<open>(2*a*t + b)\<^sup>2 - disc2 = 4*a*(a*t\<^sup>2 + b*t + c)\<close>, so \<open>t\<close> lies strictly
  between the two roots exactly when \<open>a * P t < 0\<close>. With \<open>t = q / 2\<^sup>j\<close> that is an integer test:
      \<open>a * (a*q\<^sup>2 + b*q*2\<^sup>j + c*2\<^sup>2\<^sup>j) < 0\<close>.
  The implementation therefore checks its separator rather than carrying a proof about how it chose
  one, and on failure the caller falls through, which is always correct.

  \<^bold>\<open>The \<open>rf\<close> flag is the reflection.\<close> When both roots are negative the arm that emits is the
  reflected one, whose \<open>b\<close> is \<open>-b\<close>; every place \<open>b\<close> enters is parameterised by \<open>rf\<close>, so the check runs
  on the original array without copying the polynomial.\<close>

text \<open>\<^bold>\<open>The separator grid exponent is a constant, and the runtime check makes that safe.\<close> The check
  below demands \<open>|t - v| < sqrt(disc2)/(2*|a|)\<close> for the vertex \<open>v\<close>, and \<open>t = floor(v*2\<^sup>j)/2\<^sup>j\<close> gives
  \<open>|t - v| \<le> 2\<^sup>-\<^sup>j\<close>, so \<open>2\<^sup>j > 2*|a|/sqrt(disc2)\<close> suffices. \<open>disc2\<close> is a positive integer, so
  \<open>sqrt(disc2) \<ge> 1\<close> and \<open>2\<^sup>j > 2*|a|\<close> suffices, which \<open>j = 64\<close> gives for every \<open>|a| < 2\<^sup>6\<^sup>3\<close>.

  An input for which it does not suffice cannot produce a wrong answer: the check decides, and a
  failed check falls through to the bisection solve. So no value of the constant makes an answer
  wrong, only slower.

  A tighter exponent (\<open>j = bl|a| + 2\<close>, or \<open>j = bl|a| + 2 - \<lfloor>(bl(disc2)-1)/2\<rfloor>\<close>) would need
  @{const poly_coeff_bitlen2_monadic}'s result converted by \<open>op_unat_snat_conv\<close> and used in snat
  arithmetic, and that sequence fails in Sepref's monadify phase when the converted value is the
  function's result rather than an argument to a further op.\<close>

definition lowdeg_sep_j :: nat where "lowdeg_sep_j = 64"

text \<open>The separator numerator \<open>q\<close>, so that \<open>t = q / 2\<^sup>j\<close> approximates the vertex \<open>-b/(2a)\<close>.  The
  rounding direction does not matter: the check above decides, so \<open>div\<close> is used as-is with no
  sign normalisation of the divisor.\<close>
definition lowdeg_sep_num_monadic :: "bool \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> int nres" where
"lowdeg_sep_num_monadic rf j xs \<equiv> doN {
  ASSERT (1 < length xs \<and> 2 < length xs);
  b1 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 1;
  b2 \<leftarrow> (if rf then RETURN b1 else (PR_CONST mpz_neg.amop_r) b1);
  N  \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) b2 j;
  a1 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 2;
  Av \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) a1 1;
  q  \<leftarrow> (PR_CONST mpz_fdiv_q.amop_r1) N Av;
  (PR_CONST mpzb_discard_monadic) Av;
  RETURN q
}"

sepref_register "PR_CONST lowdeg_sep_num_monadic"
  :: "bool \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> int nres"

sepref_definition lowdeg_sep_num_impl [llvm_code] is
  "uncurry2 lowdeg_sep_num_monadic" ::
  "bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  unfolding lowdeg_sep_num_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma lowdeg_sep_num_impl_hnr[sepref_fr_rules]:
  "(uncurry2 lowdeg_sep_num_impl, uncurry2 (PR_CONST lowdeg_sep_num_monadic)) \<in>
    bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  using lowdeg_sep_num_impl.refine by (simp add: PR_CONST_def)

text \<open>The RUNTIME CHECK: \<open>a * (a*q\<^sup>2 + b*q*2\<^sup>j + c*2\<^sup>2\<^sup>j) < 0\<close>, decided from the two signs so that no
  product of the two large values is formed.\<close>
definition lowdeg_sep_ok_monadic :: "bool \<Rightarrow> gmp_poly \<Rightarrow> bool nres" where
"lowdeg_sep_ok_monadic rf xs \<equiv> doN {
  ASSERT (0 < length xs \<and> 1 < length xs \<and> 2 < length xs);
  q  \<leftarrow> (PR_CONST lowdeg_sep_num_monadic) rf 64 xs;
  w1 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 2;
  w1 \<leftarrow> (PR_CONST mpz_mul.amop_r1) w1 q;
  w1 \<leftarrow> (PR_CONST mpz_mul.amop_r1) w1 q;
  b1 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 1;
  b2 \<leftarrow> (if rf then (PR_CONST mpz_neg.amop_r) b1 else RETURN b1);
  w2 \<leftarrow> (PR_CONST mpz_mul.amop_r1) b2 q;
  w2 \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) w2 64;
  w1 \<leftarrow> (PR_CONST mpz_add_monadic) w1 w2;
  (PR_CONST mpzb_discard_monadic) w2;
  (PR_CONST mpzb_discard_monadic) q;
  w3 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 0;
  w3 \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) w3 128;
  w1 \<leftarrow> (PR_CONST mpz_add_monadic) w1 w3;
  (PR_CONST mpzb_discard_monadic) w3;
  sW \<leftarrow> (PR_CONST mpz_sgn_mop) w1;
  (PR_CONST mpzb_discard_monadic) w1;
  sa \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs 2;
  RETURN ((sa < 0 \<and> 0 < sW) \<or> (0 < sa \<and> sW < 0))
}"

sepref_register "PR_CONST lowdeg_sep_ok_monadic" :: "bool \<Rightarrow> gmp_poly \<Rightarrow> bool nres"

sepref_definition lowdeg_sep_ok_impl [llvm_code] is
  "uncurry lowdeg_sep_ok_monadic" ::
  "bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding lowdeg_sep_ok_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma lowdeg_sep_ok_impl_hnr[sepref_fr_rules]:
  "(uncurry lowdeg_sep_ok_impl, uncurry (PR_CONST lowdeg_sep_ok_monadic)) \<in>
    bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using lowdeg_sep_ok_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The separator's VALUE, as a pure function.\<close>  Every
  other kernel op in this file is specified as \<open>\<le> RETURN <pure value>\<close> and these two are no
  different; what makes them worth a comment is that the value is what the CORRECTNESS argument
  consumes.  \<open>Lowdeg_Reflect\<close> turns \<open>lowdeg_sep_ok_pure\<close> (below) into the real hypothesis of
  \<open>lowdeg_deg2_two_windows\<close> by scaling with \<open>2\<^sup>2\<^sup>j > 0\<close>: the integer test IS
  \<open>a * P (q / 2\<^sup>j) < 0\<close> cleared of denominators, and nothing else is needed of \<open>q\<close> --- which is
  exactly why the grid exponent may stay a constant.

  \<^bold>\<open>The division carries a side condition and the precondition is what discharges it.\<close>
  @{const mpz_fdiv_q.amop_r1} ASSERTs a nonzero divisor, here \<open>2*a\<close>; \<open>a \<noteq> 0\<close> comes from
  \<open>last xs \<noteq> 0\<close> in \<open>dsc_isolate_all_split_pre\<close> together with the length the classifier has
  already tested, and is NOT re-checked at run time.\<close>
definition lowdeg_sep_q :: "bool \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int" where
"lowdeg_sep_q rf j xs = ((if rf then xs!1 else - (xs!1)) * 2^j) div (xs!2 * 2)"

lemma lowdeg_sep_num_monadic_correct:
  fixes xs :: "int list"
  assumes len1: "1 < length xs" and len2: "2 < length xs" and a: "xs!2 \<noteq> 0"
    and j: "j < max_snat LENGTH(64)"
  shows "lowdeg_sep_num_monadic rf j xs \<le> RETURN (lowdeg_sep_q rf j xs)"
proof -
  have one: "(1::nat) < max_snat LENGTH(64)" by (simp add: max_snat_def)
  show ?thesis
    using assms
    unfolding lowdeg_sep_num_monadic_def lowdeg_sep_q_def poly_copy_coeff_monadic_def
      mpzb_discard_monadic_def mpz_neg.amop_r_def mpz_neg.aop_r_def
      mpz_fdiv_q.amop_r1_def mpz_fdiv_q.aop_r1_def PR_CONST_def
    by (refine_vcg mpz_shift_left_snat_monadic_spec_plain[THEN order_trans])
       (use one in \<open>auto simp: snd_notzero_def\<close>)
qed

text \<open>\<open>W = a*q\<^sup>2 + b*q*2\<^sup>j + c*2\<^sup>2\<^sup>j\<close> --- the polynomial at \<open>q/2\<^sup>j\<close>, cleared of denominators,
  with \<open>b\<close> taken on the arm the caller named.\<close>
definition lowdeg_sep_W :: "bool \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int" where
"lowdeg_sep_W rf j xs =
   (xs!2 * lowdeg_sep_q rf j xs * lowdeg_sep_q rf j xs
    + (if rf then - (xs!1) else xs!1) * lowdeg_sep_q rf j xs * 2^j
    + xs!0 * 2^(2*j))"

text \<open>\<^bold>\<open>Stated in the TWO-SIGN form the implementation returns, not as the product.\<close>  They are
  equivalent (\<open>lowdeg_sep_ok_pure_prod\<close> below, one \<open>mult_less_0_iff\<close> step) and the
  product is the form the mathematics wants --- but as the DEFINITION it costs a proof:
  \<open>simp\<close> distributes \<open>a * (a*q\<^sup>2 + b*q*2\<^sup>j + c*2\<^sup>2\<^sup>j) < 0\<close> over the sum before the sign step can
  fire, and the two sides of the value lemma then differ by a factor of \<open>a\<close> that no rewrite
  puts back.  Defining it in the returned shape keeps that proof syntactic and moves the one
  algebraic step to a lemma of its own.\<close>
definition lowdeg_sep_ok_pure :: "bool \<Rightarrow> int list \<Rightarrow> bool" where
"lowdeg_sep_ok_pure rf xs =
   ((xs!2 < 0 \<and> 0 < lowdeg_sep_W rf lowdeg_sep_j xs)
    \<or> (0 < xs!2 \<and> lowdeg_sep_W rf lowdeg_sep_j xs < 0))"

lemma lowdeg_sep_ok_pure_prod:
  "lowdeg_sep_ok_pure rf xs = (xs!2 * lowdeg_sep_W rf lowdeg_sep_j xs < 0)"
  unfolding lowdeg_sep_ok_pure_def by (auto simp: mult_less_0_iff)

lemma lowdeg_sep_ok_monadic_correct:
  fixes xs :: "int list"
  assumes len0: "0 < length xs" and len1: "1 < length xs" and len2: "2 < length xs"
    and a: "xs!2 \<noteq> 0"
  shows "lowdeg_sep_ok_monadic rf xs \<le> RETURN (lowdeg_sep_ok_pure rf xs)"
proof -
  have j64: "(64::nat) < max_snat LENGTH(64)" by (simp add: max_snat_def)
  have j128: "(128::nat) < max_snat LENGTH(64)" by (simp add: max_snat_def)
  show ?thesis
    using assms
    unfolding lowdeg_sep_ok_monadic_def lowdeg_sep_ok_pure_def lowdeg_sep_W_def
      lowdeg_sep_j_def poly_copy_coeff_monadic_def poly_coeff_sgn_monadic_def
      mpzb_discard_monadic_def mpz_sgn_mop_def mpz_add_monadic_def
      mpz_neg.amop_r_def mpz_neg.aop_r_def
      mpz_mul.amop_r1_def mpz_mul.aop_r1_def PR_CONST_def
    by (refine_vcg lowdeg_sep_num_monadic_correct[THEN order_trans]
          mpz_shift_left_snat_monadic_spec_plain[THEN order_trans])
       (use j64 j128 in auto)
qed

section \<open>Emission\<close>

text \<open>When the arm has exactly one positive root, the Kioustelidis bound is the isolating window, so
  emission is one \<open>2^k\<close> and one push; when the arm has none, the result is the empty vector.
  @{const dyadic_interval_vec_push_monadic} consumes both endpoints, so neither is freed here.\<close>
text \<open>\<^bold>\<open>The allocation-free empty vector.\<close>  @{const dyadic_interval_vec_empty_sz_monadic} takes a
  capacity hint and honours it for the two \<open>mpz\<close>-pointer arrays, but builds the EXPONENT array
  with @{const op_al_empty}, whose capacity is the framework default \<open>8\<close>.  So on an arm that
  emits NOTHING it still costs THREE \<open>isabelle_llvm_calloc\<close> calls --- \<open>1 + 1\<close> pointers and \<open>8\<close>
  words --- for a vector the export wrapper's \<open>hybrid_store_interval_vec\<close> immediately reads
  as empty and frees.

  This op is that same computation with the hint honoured on all THREE arrays, so at \<open>n = 0\<close> it
  allocates nothing whatsoever: \<open>narray_new\<close> codegens \<open>c = 0\<close> to a \<open>null\<close> pointer WITHOUT
  reaching \<open>calloc\<close>, and \<open>isabelle_llvm_free\<close> returns immediately on \<open>null\<close>.  Capacity carries
  no abstract content --- @{thm [source] poly_empty_sz_monadic_def} is \<open>RETURN []\<close> for every \<open>n\<close>,
  and \<open>op_al_empty_sz n = []\<close> --- so the VALUE is identical to the op above and the spec below is
  that op's spec verbatim.  Neither the claim nor any caller obligation can move.

  \<^bold>\<open>Used at \<open>n = 0\<close> ONLY, and only where the arm emits nothing.\<close>  The emitting branches keep
  sizes \<open>1\<close> and \<open>2\<close>.  A capacity-0 array list would in fact be legal to push into
  (\<open>arl_aux_compute_size 0 1\<close> returns the REQUESTED \<open>1\<close>, not \<open>0 * 2\<close>, so the classic
  never-grows bug does not arise), but no branch reached from here pushes.\<close>
definition lowdeg_vec_empty_sz_monadic ::
  "nat \<Rightarrow> gmp_dyadic_interval_vec nres" where
"lowdeg_vec_empty_sz_monadic n \<equiv> doN {
  lns \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
  rns \<leftarrow> (PR_CONST poly_empty_sz_monadic) n;
  let ks = (op_al_empty_sz n :: nat list);
  RETURN (lns, rns, ks)
}"

lemma lowdeg_vec_empty_sz_monadic_spec:
  "lowdeg_vec_empty_sz_monadic n \<le>
    SPEC (\<lambda>v. dyadic_interval_vec_invar v \<and>
      dyadic_interval_vec_triples v = [] \<and>
      dyadic_interval_vec_to_list v = [])"
  unfolding lowdeg_vec_empty_sz_monadic_def
    poly_empty_sz_monadic_def PR_CONST_def
  by refine_vcg auto

sepref_register "PR_CONST lowdeg_vec_empty_sz_monadic"
  :: "nat \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition lowdeg_vec_empty_sz_impl [llvm_inline] is
  "lowdeg_vec_empty_sz_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>d \<rightarrow>\<^sub>a
    gmp_dyadic_interval_vec_assn"
  unfolding lowdeg_vec_empty_sz_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma lowdeg_vec_empty_sz_impl_hnr[sepref_fr_rules]:
  "(lowdeg_vec_empty_sz_impl, PR_CONST lowdeg_vec_empty_sz_monadic) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>d \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn"
  using lowdeg_vec_empty_sz_impl.refine by (simp add: PR_CONST_def)

definition lowdeg_emit_pos_monadic :: "bool \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"lowdeg_emit_pos_monadic one xs \<equiv>
  (if one then doN {
    acc \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 1;
    ASSERT (1 \<le> length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
    k \<leftarrow> (PR_CONST kiou_bound_k_monadic) xs;
    ASSERT (k < max_snat LENGTH(gmp_poly_len));
    hi \<leftarrow> (PR_CONST mpz_pow2_monadic) k;
    lo \<leftarrow> RETURN (mpz_from_int 0);
    ASSERT (dyadic_interval_vec_pushable acc);
    acc \<leftarrow> (PR_CONST dyadic_interval_vec_push_monadic) acc lo hi 0;
    RETURN acc
  } else (PR_CONST lowdeg_vec_empty_sz_monadic) 0)"

sepref_register "PR_CONST lowdeg_emit_pos_monadic"
  :: "bool \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition lowdeg_emit_pos_impl [llvm_code] is
  "uncurry lowdeg_emit_pos_monadic" ::
  "bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding lowdeg_emit_pos_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma lowdeg_emit_pos_impl_hnr[sepref_fr_rules]:
  "(uncurry lowdeg_emit_pos_impl, uncurry (PR_CONST lowdeg_emit_pos_monadic)) \<in>
    bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using lowdeg_emit_pos_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>The same-sign emission: TWO windows on one arm.\<close>  Both roots are positive here, so
  \<open>0 < r\<^sub>- < t < r\<^sub>+ < 2\<^sup>k\<close> and the two windows are \<open>[0, q]\<close> and \<open>[q, 2\<^bsup>k+j\<^esup>]\<close> at the shared exponent
  \<open>j\<close>.  \<open>q\<close> is needed as the HIGH end of the first and the LOW end of the second, and
  @{const dyadic_interval_vec_push_monadic} CONSUMES its endpoints, hence the one \<open>COPY\<close>.
  The caller must have had @{const lowdeg_sep_ok_monadic} return \<open>True\<close> for this polynomial;
  \<open>q\<close> is recomputed here rather than threaded through the classification, which costs one
  division and is what keeps the classification's return a single machine word.\<close>
definition lowdeg_emit_two_pos_monadic :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"lowdeg_emit_two_pos_monadic xs \<equiv> doN {
  ASSERT (1 \<le> length xs \<and> 2 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len));
  q  \<leftarrow> (PR_CONST lowdeg_sep_num_monadic) False 64 xs;
  qc \<leftarrow> RETURN (COPY q);
  k  \<leftarrow> (PR_CONST kiou_bound_k_monadic) xs;
  ASSERT (k < max_snat LENGTH(gmp_poly_len) \<and> k + 64 < max_snat LENGTH(gmp_poly_len));
  hi \<leftarrow> (PR_CONST mpz_pow2_monadic) (k + 64);
  lo \<leftarrow> RETURN (mpz_from_int 0);
  acc \<leftarrow> (PR_CONST dyadic_interval_vec_empty_sz_monadic) 2;
  ASSERT (dyadic_interval_vec_pushable acc);
  acc \<leftarrow> (PR_CONST dyadic_interval_vec_push_monadic) acc lo qc 64;
  ASSERT (dyadic_interval_vec_pushable acc);
  acc \<leftarrow> (PR_CONST dyadic_interval_vec_push_monadic) acc q hi 64;
  RETURN acc
}"

sepref_register "PR_CONST lowdeg_emit_two_pos_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition lowdeg_emit_two_pos_impl [llvm_code] is
  "lowdeg_emit_two_pos_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding lowdeg_emit_two_pos_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma lowdeg_emit_two_pos_impl_hnr[sepref_fr_rules]:
  "(lowdeg_emit_two_pos_impl, PR_CONST lowdeg_emit_two_pos_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using lowdeg_emit_two_pos_impl.refine by (simp add: PR_CONST_def)

end
