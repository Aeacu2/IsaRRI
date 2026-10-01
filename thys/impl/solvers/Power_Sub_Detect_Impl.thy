theory Power_Sub_Detect_Impl
  imports Power_Sub_Root_Impl
begin

text \<open>Detection, the entry's first step (op \<open>pow_sub_h_monadic\<close>).

  \<open>h = Gcd {i. coefficient i \<noteq> 0}\<close>, computed in one \<open>O(n)\<close> pass over the borrowed polynomial.
  Nothing is allocated but a transient per-coefficient copy, freed inside the body; the same shape
  as \<open>Kiou_Bound.kiou_maxfold_monadic\<close>, whose loop state is likewise two machine words.

  \<^bold>\<open>Three things Sepref does not translate\<close>:
  \<^item> \<open>fst st\<close> in a loop condition. Destructure with \<open>let (i, g) = st\<close> and unfold \<open>Let_def\<close>.
  \<^item> \<open>length xs\<close> of a borrowed polynomial, read inside the loop. The length is a parameter, read
    once by @{const poly_length_monadic}.
  \<^item> \<open>gcd\<close> on \<open>snat\<close>: there is no HNR for it, so \<open>snat_gcd_monadic\<close> below brings its own Euclid
    loop. Likewise an sint equality (\<open>sg = 0\<close>) does not translate where the two comparisons
    \<open>sg < 0 \<or> 0 < sg\<close> do.

  \<^bold>\<open>Detection can return \<open>h = 0\<close>, and the power-substitution theorems assume \<open>0 < h\<close>\<close>: a nonzero
  constant has support \<open>{0}\<close> and \<open>Gcd {0} = 0\<close>; the zero polynomial has empty support and
  \<open>Gcd {} = 0\<close> too. The clamp belongs at the call site and is stated here as
  \<open>pow_sub_h_clamped\<close>.\<close>

section \<open>The fold, and why it computes the \<open>Gcd\<close>\<close>

definition pow_sub_h_upto :: "int list \<Rightarrow> nat \<Rightarrow> nat" where
  "pow_sub_h_upto xs i = Gcd {j. j < i \<and> j < length xs \<and> xs ! j \<noteq> 0}"

lemma pow_sub_h_upto_0[simp]: "pow_sub_h_upto xs 0 = 0"
  by (simp add: pow_sub_h_upto_def)

lemma pow_sub_h_upto_Suc:
  assumes i: "i < length xs"
  shows "pow_sub_h_upto xs (Suc i)
           = (if xs ! i = 0 then pow_sub_h_upto xs i else gcd i (pow_sub_h_upto xs i))"
proof (cases "xs ! i = 0")
  case True
  have "{j. j < Suc i \<and> j < length xs \<and> xs ! j \<noteq> 0}
          = {j. j < i \<and> j < length xs \<and> xs ! j \<noteq> 0}"
    using True by (auto simp: less_Suc_eq)
  then show ?thesis using True by (simp add: pow_sub_h_upto_def)
next
  case False
  have "{j. j < Suc i \<and> j < length xs \<and> xs ! j \<noteq> 0}
          = insert i {j. j < i \<and> j < length xs \<and> xs ! j \<noteq> 0}"
    using False i by (auto simp: less_Suc_eq)
  then show ?thesis using False by (simp add: pow_sub_h_upto_def)
qed

lemma pow_sub_h_upto_length: "pow_sub_h_upto xs (length xs) = pow_sub_h xs"
  by (simp add: pow_sub_h_upto_def pow_sub_h_def pow_sub_support_def conj_commute)

text \<open>\<^bold>\<open>The running gcd is absorbing at 1, which licenses the loop's early exit.\<close> Extending the
  prefix can only shrink the gcd in the divisibility order (the index set grows, and the \<open>Gcd\<close> of a
  superset divides the \<open>Gcd\<close> of a subset), so once the prefix gcd reaches 1 no later coefficient
  can change it. With these two facts the loop stops at the first odd index carrying a nonzero
  coefficient, which on an \<open>h = 1\<close> input is typically index 1. The exit costs one comparison per
  iteration and never adds iterations.\<close>

lemma pow_sub_h_upto_dvd:
  assumes "i \<le> j"
  shows "pow_sub_h_upto xs j dvd pow_sub_h_upto xs i"
  unfolding pow_sub_h_upto_def
  using assms by (intro Gcd_greatest) (auto intro: Gcd_dvd)

lemma pow_sub_h_upto_one:
  assumes "i \<le> j" and "pow_sub_h_upto xs i = 1"
  shows "pow_sub_h_upto xs j = 1"
proof -
  \<comment> \<open>\<open>[OF assms(1)]\<close> alone leaves \<open>xs\<close> generalised, so \<open>simp\<close> never applies the \<open>dvd\<close> fact to
     THIS \<open>xs\<close>; the \<open>rule\<close> step pins it.\<close>
  have "pow_sub_h_upto xs j dvd pow_sub_h_upto xs i"
    by (rule pow_sub_h_upto_dvd[OF assms(1)])
  with assms(2) show ?thesis by simp
qed

text \<open>\<^bold>\<open>The exit fact, stated in the FORM THE GOAL ACTUALLY HAS.\<close> The loop condition is
  \<open>i < len \<and> (g < 1 \<or> 1 < g)\<close>, so on the early-exit branch the goal carries TWO separate
  negated comparisons rather than an equation, and in \<open>Suc 0\<close> spelling. \<open>auto\<close> does not fuse
  two negated \<open>nat\<close> inequalities into \<open>= 1\<close>, so a rule whose premise is an EQUATION cannot
  match however true it is — three tactic attempts failed on exactly that before the goal was
  read rather than guessed at. The premises below are copied from the printed goal; the fusing
  happens INSIDE, where \<open>simp\<close> has both in hand.\<close>

lemma pow_sub_h_upto_exit:
  assumes "i \<le> length xs"
    and "\<not> Suc 0 < pow_sub_h_upto xs i"
    and "\<not> pow_sub_h_upto xs i < Suc 0"
  shows "pow_sub_h xs = pow_sub_h_upto xs i"
proof -
  from assms(2,3) have g1: "pow_sub_h_upto xs i = 1" by simp
  have "pow_sub_h_upto xs (length xs) = 1"
    by (rule pow_sub_h_upto_one[OF assms(1) g1])
  with g1 show ?thesis by (simp add: pow_sub_h_upto_length)
qed

section \<open>\<open>gcd\<close> on machine words — the tree has no HNR for it\<close>

text \<open>\<^bold>\<open>Sepref cannot translate \<open>gcd\<close> on \<open>snat\<close>\<close> (the trans phase blocks on \<open>gcd $ i $ g\<close>), so
  detection has to bring its own: plain Euclid, whose every step is a \<open>snat\<close> modulo. The loop
  condition is \<open>0 < y\<close> rather than \<open>y \<noteq> 0\<close> — a comparison, not an equality, which is the same
  reason \<open>Kiou_Bound\<close>'s fold only ever compares signs with \<open><\<close>.\<close>

definition snat_gcd_monadic :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where
  "snat_gcd_monadic a b \<equiv> doN {
     (x, y) \<leftarrow> WHILEIT (\<lambda>(x, y). gcd x y = gcd a b)
        (\<lambda>(x, y). 0 < y)
        (\<lambda>(x, y). doN { ASSERT (0 < y); RETURN (y, x mod y) })
        (a, b);
     RETURN x
   }"

lemma snat_gcd_monadic_correct[refine_vcg]:
  "snat_gcd_monadic a b \<le> RETURN (gcd a b)"
  unfolding snat_gcd_monadic_def
  apply (refine_vcg WHILEIT_rule[where R = "measure snd"])
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (auto simp: gcd_red_nat[symmetric])
  subgoal by (auto simp: mod_less_divisor)
  subgoal by auto
  done

sepref_register "PR_CONST snat_gcd_monadic" :: "nat \<Rightarrow> nat \<Rightarrow> nat nres"

sepref_definition snat_gcd_impl [llvm_code] is
  "uncurry snat_gcd_monadic" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k
     \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding snat_gcd_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma snat_gcd_impl_hnr[sepref_fr_rules]:
  "(uncurry snat_gcd_impl, uncurry (PR_CONST snat_gcd_monadic)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k
      \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using snat_gcd_impl.refine by (simp add: PR_CONST_def)

section \<open>The monadic pass\<close>

text \<open>\<^bold>\<open>The length is a PARAMETER, not \<open>length xs\<close> read in the condition.\<close> Sepref has no way to
  translate \<open>length\<close> of a borrowed poly inside a loop condition — \<open>Kiou_Bound\<close>'s condition takes
  the degree \<open>n\<close> as a machine word for exactly this reason. The caller reads it ONCE with
  @{const poly_length_monadic}.\<close>

definition pow_sub_h_cond :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "pow_sub_h_cond len st \<longleftrightarrow> (let (i, g) = st in i < len \<and> (g < 1 \<or> 1 < g))"

sepref_register "PR_CONST pow_sub_h_cond" :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"

abbreviation pow_sub_h_state_assn where
  "pow_sub_h_state_assn \<equiv>
     snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"

sepref_definition pow_sub_h_cond_impl [llvm_inline] is
  "uncurry (RETURN oo pow_sub_h_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_h_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_h_cond_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow_sub_h_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_h_cond_impl, uncurry (RETURN oo (PR_CONST pow_sub_h_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_h_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_h_cond_impl.refine by (simp add: PR_CONST_def)

text \<open>\<^bold>\<open>Borrow-read the SIGN directly\<close> (@{const poly_coeff_sgn_monadic}) instead of deep-copying
  \<open>xs ! i\<close> and taking \<open>mpz_sgn\<close> of the copy: the tree already has the borrowing op, and the copy
  route allocates and frees an mpz per coefficient for a value it never keeps. Same choice
  \<open>Kiou_Bound\<close>'s fold makes, and for the same reason.

  \<^bold>\<open>The loop state is DESTRUCTIVE (\<open>\<^sup>d\<close>), not kept\<close> — it is a pair of machine words the body
  rewrites. The polynomial stays borrowed (\<open>\<^sup>k\<close>), so the caller keeps it.\<close>

definition pow_sub_h_body_mop :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) nres" where
  "pow_sub_h_body_mop xs len st \<equiv> doN {
     let (i, g) = st;
     ASSERT (i < len);
     ASSERT (i < length xs);
     sg \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs i;
     nz \<leftarrow> RETURN (sg < 0 \<or> 0 < sg);
     g' \<leftarrow> (if nz then (PR_CONST snat_gcd_monadic) i g else RETURN g);
     ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
     RETURN (i + 1, g')
   }"

sepref_register "PR_CONST pow_sub_h_body_mop"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) nres"

text \<open>\<^bold>\<open>The body's HNR precondition must be discharged at the LOOP BOUNDARY, so it may only
  mention the curried arguments\<close> — here \<open>len\<close>, never the loop state \<open>(i, g)\<close>. The reason is
  the shape of @{thm hn_monadic_WHILE_lin}'s \<open>f_ref\<close> premise: the body is translated under
  \<open>\<And>s' s. I s' \<Longrightarrow> \<dots>\<close>, i.e. for a UNIVERSALLY QUANTIFIED state about which only the
  invariant is known. A precondition mentioning \<open>i\<close> would have to follow from the invariant
  alone, and the invariant gives \<open>i \<le> length xs\<close>, not \<open>i < length xs\<close> — that is the loop
  CONDITION, which is not available in \<open>f_ref\<close>. So the state-dependent needs (\<open>i < len\<close>,
  \<open>i < length xs\<close>, \<open>i + 1 < max_snat\<close>) go inside the body as ASSERTs, where
  @{thm hn_ASSERT_bind} turns each into an assumption for the ops that follow — exactly as
  @{text "Kiou_Bound.kiou_maxfold_body_mop_monadic"} does.\<close>

sepref_definition pow_sub_h_body_impl [llvm_code] is
  "uncurry2 pow_sub_h_body_mop" ::
  "[\<lambda>((xs, len), st). len = length xs
                     \<and> len < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      pow_sub_h_state_assn\<^sup>d \<rightarrow> pow_sub_h_state_assn"
  unfolding pow_sub_h_body_mop_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const gmp_int_t)?
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

lemma pow_sub_h_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 pow_sub_h_body_impl, uncurry2 (PR_CONST pow_sub_h_body_mop)) \<in>
    [\<lambda>((xs, len), st). len = length xs
                       \<and> len < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      pow_sub_h_state_assn\<^sup>d \<rightarrow> pow_sub_h_state_assn"
  using pow_sub_h_body_impl.refine by (simp add: PR_CONST_def)

definition pow_sub_h_monadic :: "gmp_poly \<Rightarrow> nat nres" where
  "pow_sub_h_monadic xs \<equiv> doN {
     ASSERT (length xs < max_snat LENGTH(gmp_poly_len));
     len \<leftarrow> (PR_CONST poly_length_monadic) xs;
     ASSERT (len = length xs \<and> len < max_snat LENGTH(gmp_poly_len));
     (_, g) \<leftarrow> WHILEIT
        (\<lambda>st. fst st \<le> length xs \<and> snd st = pow_sub_h_upto xs (fst st))
        (\<lambda>st. (PR_CONST pow_sub_h_cond) len st)
        (\<lambda>st. (PR_CONST pow_sub_h_body_mop) xs len st)
        (0, 0);
     RETURN g
   }"

lemma pow_sub_h_monadic_correct:
  assumes len: "length xs < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_h_monadic xs \<le> RETURN (pow_sub_h xs)"
  unfolding pow_sub_h_monadic_def pow_sub_h_body_mop_def pow_sub_h_cond_def
    PR_CONST_def poly_coeff_sgn_monadic_def poly_length_monadic_def
  apply (refine_vcg
         WHILEIT_rule[where R = "measure (\<lambda>st. length xs - fst st)"]
         snat_gcd_monadic_correct[THEN order_trans])
  subgoal using len .
  subgoal using len by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (auto simp: Let_def)
  subgoal using len by (auto simp: Let_def)
  subgoal by (auto simp: Let_def)
  subgoal by (auto simp: Let_def pow_sub_h_upto_Suc sgn_eq_0_iff gcd.commute)
  subgoal by (auto simp: Let_def)
  subgoal using len by (auto simp: Let_def)
  subgoal by (auto simp: Let_def)
  subgoal by (auto simp: Let_def pow_sub_h_upto_Suc sgn_eq_0_iff)
  subgoal by (auto simp: Let_def)
  \<comment> \<open>The exit subgoal now has TWO ways out, because the condition gained a disjunct:
     the index reached the end, or the running gcd hit 1. The first is
     \<open>pow_sub_h_upto_length\<close> as before; the second needs the absorbing fact chained FORWARD
     to \<open>length xs\<close>, which is why it is supplied as a \<open>dest\<close> with \<open>j\<close> pinned rather than as a
     \<open>simp\<close> rule — its second premise mentions an \<open>i\<close> that the rewrite target does not
     determine, so as a conditional simp rule it could never fire.\<close>
  subgoal by (auto simp: Let_def pow_sub_h_upto_length dest: pow_sub_h_upto_exit)
  done

text \<open>\<^bold>\<open>The top-level pass.\<close> Assembled as \<open>Kiou_Bound.kiou_maxfold_impl\<close> and
  \<open>Count.poly_ethorner_count_trunc_impl\<close> — the same cond+body+WHILE shape.

  \<^bold>\<open>Two things had to hold before the body rule would fire\<close>, and only the first was about
  currying. (i) The precondition may not mention the loop state (see above). (ii) \<^bold>\<open>What it
  DOES mention must be provable from the assumptions in scope at the loop\<close> — and the only
  fact translation has about \<open>len\<close> is \<open>bind_ref_tag len (poly_length_monadic xs)\<close>, a TAG,
  not an equation. Hence the \<open>ASSERT (len = length xs \<and> \<dots>)\<close> above: @{thm hn_ASSERT_bind}
  turns it into a context assumption, and the body's side condition then solves.

  \<^bold>\<open>Why an unsolved side condition BLOCKS rather than being left open:\<close>
  \<open>sepref_dbg_trans_keep\<close> is @{ML Sepref_Translate.trans_keep_tac}, and
  \<open>gen_trans_tac\<close> hardwires the NON-debug \<open>trans_step_tac\<close> in its \<open>PHASES'\<close> list — \<open>dbg\<close>
  only selects the phase tracing. So the op step is \<open>DETERM o SOLVED' (fr_rl_tac
  THEN_ALL_NEW_FWD (SOLVED' side_tac))\<close>: a rule whose side conditions do not all solve
  fires NOT AT ALL, leaving the body schematic and every continuation goal that depends on
  it open. (The rule-fires-but-leaves-goals behaviour belongs to
  \<open>sepref_dbg_trans_step_keep\<close>, one step at a time.)

  The post-loop destructure works inline because the state is PURE — no result op needed
  (that is the owned-poly-state pattern; see Extract).\<close>

sepref_register "PR_CONST pow_sub_h_monadic" :: "gmp_poly \<Rightarrow> nat nres"

sepref_definition pow_sub_h_impl [llvm_code] is
  "pow_sub_h_monadic" ::
  "[\<lambda>xs. length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding pow_sub_h_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    pow_sub_h_cond_impl_hnr pow_sub_h_body_impl_hnr
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

lemma pow_sub_h_impl_hnr[sepref_fr_rules]:
  "(pow_sub_h_impl, PR_CONST pow_sub_h_monadic) \<in>
    [\<lambda>xs. length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using pow_sub_h_impl.refine by (simp add: PR_CONST_def)

section \<open>The clamp at the call site\<close>

text \<open>\<open>h = 0\<close> is not "does not apply" — \<open>h = 1\<close> is. An unclamped \<open>0\<close> flowing into
  \<open>pow_sub_extract\<close> divides by zero, and every theorem in this track assumes \<open>0 < h\<close>. Clamping
  to \<open>max 1\<close> is sound because the only inputs that measure \<open>0\<close> are those whose support is
  contained in \<open>{0}\<close> — a constant or the zero polynomial — where \<open>h = 1\<close> (no substitution) is the
  right answer anyway.\<close>

definition pow_sub_h_clamped :: "gmp_poly \<Rightarrow> nat nres" where
  "pow_sub_h_clamped xs \<equiv> doN {
     h \<leftarrow> pow_sub_h_monadic xs;
     RETURN (max 1 h)
   }"

lemma pow_sub_h_clamped_correct:
  assumes len: "length xs < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_h_clamped xs \<le> SPEC (\<lambda>h. 0 < h \<and> h = max 1 (pow_sub_h xs))"
  unfolding pow_sub_h_clamped_def
  by (refine_vcg pow_sub_h_monadic_correct[OF len, THEN order_trans]) simp_all

end
