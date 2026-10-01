theory Split_Pre_Witness
  imports
    "IsaRRI.Power_Sub_Entry_Sound"
    "IsaRRI_Refine.Lowdeg_Reflect"
begin

text \<open>\<^bold>\<open>Satisfiability witnesses for the precondition definitions.\<close> A precondition that is not
  refutable is not thereby shown satisfiable, so each bundle gets an explicit \<open>xs\<close> with every conjunct
  discharged.

  \<^bold>\<open>Why \<open>xs = [1, 1]\<close>\<close> (i.e. \<open>P = 1 + x\<close>): the \<open>\<mu>\<close> conjunct is stated through @{const delta_P}, hence through
  @{const root_sep}, which is \<open>if card (proots \<dots>) \<ge> 2 then Min (proots_dist_set \<dots>) else 1\<close>. At degree 1 the
  root set is a singleton, so the \<open>else\<close> branch applies and \<open>root_sep = 1\<close> by definition, with no factoring,
  no \<open>Min\<close> over a distance set and no root-location argument. Satisfiability needs only one list.

  \<^bold>\<open>A degree-1 witness shows consistency only.\<close> It shows that the bundle is satisfiable, so the theorems
  assuming it are not vacuous. It does not show that any polynomial of interest satisfies it.\<close>

section \<open>The reflected witness, and the two lists' shapes\<close>

lemma witness_refl_list: "refl_list [1, 1] = [1, - 1]"
  by (simp add: refl_list_eq_scale_poly_list_neg1 scale_poly_list_def)

lemma witness_scale_pos: "scale_poly_list (2 ^ k) [1, 1] = [1, 2 ^ k]"
  by (simp add: scale_poly_list_def)

lemma witness_scale_neg: "scale_poly_list (2 ^ k) [1, - 1] = [1, - (2 ^ k)]"
  by (simp add: scale_poly_list_def)

section \<open>Degree 1 forces the cheap \<open>root_sep\<close> branch\<close>

text \<open>The only real content: a non-constant polynomial of degree 1 has at most one root, so
  @{const root_sep} takes its \<open>else\<close> branch. Stated over an arbitrary \<open>c \<noteq> 0\<close> so both halves
  (\<open>2 ^ k\<close> and \<open>- (2 ^ k)\<close>) reuse it.\<close>

lemma card_proots_le_degree:
  fixes P :: "complex poly"
  assumes "P \<noteq> 0"
  shows "card (proots P) \<le> degree P"
  using assms by (simp add: proots_def poly_roots_degree)

lemma root_sep_degree1:
  fixes P :: "complex poly"
  assumes "degree P = 1"
  shows "root_sep P = 1"
proof -
  have P0: "P \<noteq> 0" using assms by auto
  have "card (proots P) \<le> 1" using card_proots_le_degree[OF P0] assms by simp
  thus ?thesis unfolding root_sep_def by simp
qed

lemma delta_P_degree1:
  fixes P :: "real poly"
  assumes "degree P = 1"
  shows "delta_P P = 1 / (4 * R0)"
proof -
  have d: "degree (map_poly of_real P :: complex poly) = 1"
    using assms by (simp add: degree_map_poly)
  have ne: "(map_poly of_real P :: complex poly) \<noteq> 0" using d by auto
  show ?thesis unfolding delta_P_def using ne root_sep_degree1[OF d] by simp
qed

section \<open>\<open>R0\<close> is between 1 and 2, hence \<open>\<mu> = 4\<close>\<close>

text \<open>\<open>R0 = \<bar>1/2 + (\<surd>3/6) i\<bar> + \<surd>3/3 = 1/\<surd>3 + 1/\<surd>3 = 2/\<surd>3 \<approx> 1.1547\<close>. Only the bracket \<open>1 < R0 \<le> 2\<close> is
  needed: it pins \<open>\<lceil>log\<^sub>2 (4 R0)\<rceil> = 3\<close>, hence \<open>mu (1/(4 R0)) 0 1 = Suc 3 = 4\<close>.\<close>

lemma R0_eq: "R0 = 2 * sqrt 3 / 3"
proof -
  have c: "(1/2 + (sqrt 3 / 6) * \<i>) = Complex (1/2) (sqrt 3 / 6)"
    by (simp add: complex_eq_iff)
  have s3: "sqrt 3 * sqrt 3 = 3" by (simp add: real_sqrt_mult[symmetric])
  have "cmod (1/2 + (sqrt 3 / 6) * \<i>) = sqrt ((1/2)\<^sup>2 + (sqrt 3 / 6)\<^sup>2)"
    unfolding c by (simp add: norm_complex_def)
  also have "(1/2::real)\<^sup>2 + (sqrt 3 / 6)\<^sup>2 = 1 / 3"
    using s3 by (simp add: power2_eq_square)
  also have "sqrt (1 / 3 :: real) = sqrt 3 / 3"
    using s3 by (simp add: real_sqrt_divide real_div_sqrt)
  finally show ?thesis unfolding R0_def by simp
qed

text \<open>\<open>3/2\<close>, not \<open>1\<close>: the \<open>R0 > 1\<close> half needs \<open>3 < 2 \<surd>3\<close>, which \<open>\<surd>3 > 1\<close> does not give.\<close>
lemma sqrt3_bracket: "3 / 2 < sqrt 3 \<and> sqrt 3 < 2"
proof
  show "3 / 2 < sqrt 3" using real_less_rsqrt[of "3/2" 3] by (simp add: power2_eq_square)
  show "sqrt 3 < 2" using real_sqrt_less_mono[of 3 4] by simp
qed

lemma R0_bracket: "1 < R0 \<and> R0 \<le> 2"
  using sqrt3_bracket unfolding R0_eq by simp

text \<open>\<open>\<mu> = mu \<delta> 0 1 = Suc \<lceil>log\<^sub>2 (max 1 (1/\<delta>))\<rceil>\<close> with \<open>1/\<delta> = 4 R0 \<in> (4, 8]\<close>, so the ceiling-log is exactly
  3.\<close>

text \<open>\<^bold>\<open>An upper bound on \<open>\<mu>\<close> is all the capacity conjuncts need\<close>: \<open>k + \<mu> + 1 < max_snat\<close> and
  \<open>2 ^ Suc \<mu> + 1 < max_snat\<close> are both monotone in \<open>\<mu>\<close>. Proving \<open>\<mu> = 4\<close> exactly would also need
  \<open>2 < log\<^sub>2 (4 R0)\<close>, the lower bracket.\<close>

lemma mu_delta_degree1_le: "mu (1 / (4 * R0)) 0 1 \<le> 4"
proof -
  from R0_bracket have lo: "1 < R0" and hi: "R0 \<le> 2" by simp_all
  have pos: "0 < 4 * R0" using lo by simp
  have inv: "(1 - 0) / (1 / (4 * R0)) = 4 * R0" using pos by simp
  have mx: "max 1 (4 * R0) = 4 * R0" using lo by simp
  have l_hi: "log 2 (4 * R0) \<le> 3"
  proof -
    have "(4::real) * R0 \<le> 2 powr 3" using hi by (simp add: powr_realpow)
    thus ?thesis using pos by (simp add: log_le_iff)
  qed
  have "\<lceil>log 2 (4 * R0)\<rceil> \<le> 3" using l_hi by (simp add: ceiling_le_iff)
  hence "nat \<lceil>log 2 (4 * R0)\<rceil> \<le> 3" by simp
  thus ?thesis unfolding mu_def inv mx by simp
qed

text \<open>Read off at the \<open>(0, 1)\<close> interval the pipeline always starts from. \<open>simp\<close>, not
  \<open>unfolding\<close>: \<open>rational_interval_mu_def\<close> leaves \<open>of_rat 0\<close>/\<open>of_rat 1\<close>, which must normalise to
  \<open>0\<close>/\<open>1\<close> before the bound can match.\<close>

lemma rational_interval_mu_degree1_le:
  fixes P :: "real poly"
  assumes "degree P = 1"
  shows "rational_interval_mu (delta_P P) (0, 1) \<le> 4"
  unfolding rational_interval_mu_def delta_P_degree1[OF assms]
  by (simp add: mu_delta_degree1_le)

section \<open>The Kioustelidis bound op on the two witness lists\<close>

text \<open>Both lists are \<open>[1, a]\<close> with \<open>\<bar>a\<bar> = 1\<close>, so \<open>rlead = 1\<close>; the fold runs one iteration at
  \<open>i = 0\<close>. On \<open>[1, 1]\<close> the leading coefficient is positive and \<open>xs ! 0 = 1\<close> does NOT oppose it, so
  \<open>k\<close> stays at its seed \<open>1\<close>. On \<open>[1, - 1]\<close> the leading coefficient is negative, so \<open>xs ! 0 = 1\<close>
  DOES oppose, and \<open>k\<close> becomes \<open>2\<close>.\<close>

text \<open>\<^bold>\<open>\<open>max_snat\<close> is not unfolded inside the exponent.\<close> \<open>kiou_headroom\<close>'s coefficient bound is
  \<open>\<bar>xs ! i\<bar> < 2 ^ (max_snat \<dots> - length xs - 2)\<close>; \<open>simp add: max_snat_def\<close> would turn that into
  \<open>2 ^ (9223372036854775808 - 4)\<close> and try to evaluate it. \<open>0 < exponent\<close> is proved separately (there
  \<open>max_snat_def\<close> is a single numeral), and then \<open>one_less_power\<close> is used without touching the exponent.\<close>

text \<open>\<^bold>\<open>Evaluating @{const kiou_bound_k_monadic} on the two witness lists.\<close>
  @{thm [source] kiou_maxfold_body_mop_monadic_correct} gives the body's value,
  \<open>k' = max k (if kiou_norm xs ! i < 0 then kiou_term r rlead (n - i) else 0)\<close>, with its hypotheses from the
  headroom lemmas below.

    \<^item> \<open>[1, 1]\<close>: \<open>kiou_norm\<close> is the identity (positive leading coefficient), so the guard is false,
      \<open>k' = max k 0 = k\<close>, and \<open>k\<close> stays at its seed: \<open>k = 1\<close>.
    \<^item> \<open>[1, - 1]\<close>: \<open>kiou_norm\<close> negates, so \<open>kiou_norm [1,-1] ! 0 = - 1 < 0\<close>, the guard is true, and with
      \<open>r = rlead = 1\<close>, \<open>d = 1\<close> we get \<open>kiou_term 1 1 1 = 2\<close>: \<open>k = 2\<close>.

  \<^bold>\<open>Proof notes.\<close>
    \<^item> \<open>max_snat\<close> is never unfolded into an exponent (see above).
    \<^item> \<open>1\<close> versus \<open>Suc 0\<close>: \<open>refine_vcg\<close> produces goals in \<open>Suc\<close> form while lemma statements keep numerals,
      and \<open>rule\<close> does not unify them, so \<open>body\<close> takes \<open>Suc 0\<close> for \<open>n\<close>, \<open>witness_len_bound\<close> is stated as
      \<open>Suc (Suc (Suc 0))\<close>, and the fold witnesses are used \<open>[unfolded One_nat_def]\<close>.
    \<^item> The loop state is destructured inside a focus: \<open>subgoal for s\<close>, \<open>cases s\<close>, \<open>clarsimp\<close>, as in
      @{thm [source] kiou_maxfold_monadic_correct}.
    \<^item> \<open>2 ^ m \<le> 1 \<Longrightarrow> m = 0\<close> is \<open>power_le_one_iff\<close>, an equation that rewrites in place.
    \<^item> \<open>apply (rule X; auto)\<close> hides which produced goal failed; the negative witness's \<open>rlead = Suc 0\<close> side
      goal needs an explicit \<open>cases x\<close>.\<close>

lemma witness_headroom_pos: "kiou_headroom [1, 1]"
proof -
  have lenb: "length [1, 1::int] + 3 < max_snat LENGTH(gmp_poly_len)"
    by (simp add: max_snat_def)
  have npos: "0 < max_snat LENGTH(gmp_poly_len) - length [1, 1::int] - 2"
    by (simp add: max_snat_def)
  have one: "(1::int) < 2 ^ (max_snat LENGTH(gmp_poly_len) - length [1, 1::int] - 2)"
    by (rule one_less_power[OF _ npos]) simp
  show ?thesis unfolding kiou_headroom_def using lenb one by (auto simp: nth_Cons')
qed

lemma witness_headroom_neg: "kiou_headroom [1, - 1]"
proof -
  have lenb: "length [1, - 1::int] + 3 < max_snat LENGTH(gmp_poly_len)"
    by (simp add: max_snat_def)
  have npos: "0 < max_snat LENGTH(gmp_poly_len) - length [1, - 1::int] - 2"
    by (simp add: max_snat_def)
  have one: "(1::int) < 2 ^ (max_snat LENGTH(gmp_poly_len) - length [1, - 1::int] - 2)"
    by (rule one_less_power[OF _ npos]) simp
  show ?thesis unfolding kiou_headroom_def using lenb one by (auto simp: nth_Cons')
qed

text \<open>\<open>kiou_norm\<close> normalises to a POSITIVE leading coefficient, so on \<open>[1, - 1]\<close> it negates:
  that is precisely why the two witnesses get different exponents.\<close>

lemma kiou_norm_witness_pos: "kiou_norm [1, 1] = [1, 1]"
  by (simp add: kiou_norm_def)

lemma kiou_norm_witness_neg: "kiou_norm [1, - 1] = [- 1, 1]"
  by (simp add: kiou_norm_def)

lemma kiou_maxfold_witness_pos:
  "kiou_maxfold_monadic [1, 1] 1 False rlead \<le> SPEC (\<lambda>k. k = 1)"
proof -
  have lenb: "length [1, 1::int] + 3 < max_snat LENGTH(gmp_poly_len)"
    by (rule kiou_headroom_lenb[OF witness_headroom_pos])
  have lneg: "False = (last [1, 1::int] < 0)" by simp
  have body: "kiou_maxfold_body_mop_monadic [1, 1] 1 False rlead (i, k) \<le>
      SPEC (\<lambda>st. \<exists>k' r. st = (i + 1, k')
         \<and> \<bar>kiou_norm [1, 1] ! i\<bar> < 2 ^ r
         \<and> (kiou_norm [1, 1] ! i \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>kiou_norm [1, 1] ! i\<bar>)
         \<and> k' = max k (if kiou_norm [1, 1] ! i < 0
                         then kiou_term r rlead (1 - i) else 0))"
    if k1: "1 \<le> k" and il: "i < 1" for i k
    by (rule kiou_maxfold_body_mop_monadic_correct[OF _ k1 il _ lenb lneg])
       (use il kiou_headroom_coeff[OF witness_headroom_pos, of i] in simp_all)
  show ?thesis
    unfolding kiou_maxfold_monadic_def kiou_maxfold_cond_monadic_def PR_CONST_def
    apply (refine_vcg WHILET_rule[where R = "measure (\<lambda>(i, k). 1 - i)"
             and I = "\<lambda>(i, k). i \<le> 1 \<and> k = 1"]
           body[THEN order_trans])
        apply simp
       apply simp
      apply simp
    \<comment> \<open>\<^bold>\<open>Neither \<open>subgoal\<close> nor a \<open>;\<close>-chain here.\<close> The preceding \<open>simp\<close>s destructure the loop state to the
       concrete \<open>(0, Suc 0)\<close>, which lets \<open>body\<close> match; \<open>subgoal\<close> would generalise it back to a variable
       \<open>s_\<close>, after which \<open>body\<close> (stated at the pair \<open>(i, k)\<close>) no longer applies, and a \<open>;\<close>-chained \<open>auto\<close>
       would spill onto the sibling goal. One bare \<open>rule\<close>, then one \<open>auto\<close> for every remaining goal.\<close>
     subgoal for s
       apply (cases s)
       apply (clarsimp simp del: One_nat_def)
       apply (rule order_trans[OF body]; auto simp: kiou_norm_witness_pos)
       done
    apply auto
    done
qed

text \<open>\<^bold>\<open>The bit-length of \<open>\<bar>\<plusminus>1\<bar>\<close> is PINNED to 1 by the two spec conditions\<close> — needed because
  @{thm [source] kiou_maxfold_body_mop_monadic_correct} hands back \<open>r\<close> existentially, and the
  negative witness's exponent depends on its value.\<close>

lemma bitlen_one_pinned:
  fixes r :: nat
  assumes lo: "(1::int) < 2 ^ r" and hi: "(2::int) ^ (r - 1) \<le> 1"
  shows "r = 1"
proof -
  have r1: "1 \<le> r" using lo by (cases r) auto
  have "r - 1 = 0"
  proof (rule ccontr)
    assume "r - 1 \<noteq> 0"
    then obtain m where m: "r - 1 = Suc m" by (cases "r - 1") auto
    have "(2::int) ^ Suc m \<le> 1" using hi m by simp
    moreover have "(1::int) \<le> 2 ^ m" by simp
    ultimately show False by simp
  qed
  thus ?thesis using r1 by simp
qed

lemma kiou_term_witness_neg: "kiou_term 1 1 1 = 2"
  unfolding kiou_term_def by simp

text \<open>\<open>rlead\<close> is a variable constrained by an assumption, not the literal \<open>1\<close>: \<open>refine_vcg\<close> normalises the
  goal's \<open>1 :: nat\<close> to \<open>Suc 0\<close> while the \<open>body\<close> fact keeps \<open>1\<close>, and \<open>rule\<close> does not unify the two.\<close>

lemma kiou_maxfold_witness_neg:
  assumes rl: "rlead = 1"
  shows "kiou_maxfold_monadic [1, - 1] 1 True rlead \<le> SPEC (\<lambda>k. k = 2)"
proof -
  have lenb: "length [1, - 1::int] + 3 < max_snat LENGTH(gmp_poly_len)"
    by (rule kiou_headroom_lenb[OF witness_headroom_neg])
  have lneg: "True = (last [1, - 1::int] < 0)" by simp
  \<comment> \<open>\<open>Suc 0\<close>, not \<open>1\<close>, for \<open>n\<close>: \<open>refine_vcg\<close> hands the body goal over with \<open>Suc 0\<close> and \<open>rule\<close>
     does not unify that with the numeral \<open>1\<close>.\<close>
  have body: "kiou_maxfold_body_mop_monadic [1, - 1] (Suc 0) True rlead (i, k) \<le>
      SPEC (\<lambda>st. \<exists>k' r. st = (i + 1, k')
         \<and> \<bar>kiou_norm [1, - 1] ! i\<bar> < 2 ^ r
         \<and> (kiou_norm [1, - 1] ! i \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>kiou_norm [1, - 1] ! i\<bar>)
         \<and> k' = max k (if kiou_norm [1, - 1] ! i < 0
                         then kiou_term r rlead (Suc 0 - i) else 0))"
    if k1: "1 \<le> k" and il: "i < Suc 0" for i k
    by (rule kiou_maxfold_body_mop_monadic_correct[OF _ k1 il _ lenb lneg])
       (use il kiou_headroom_coeff[OF witness_headroom_neg, of i] in simp_all)
  show ?thesis
    unfolding kiou_maxfold_monadic_def kiou_maxfold_cond_monadic_def PR_CONST_def
    apply (refine_vcg WHILET_rule[where R = "measure (\<lambda>(i, k). 1 - i)"
             and I = "\<lambda>(i, k). (i = 0 \<and> k = 1) \<or> (i = 1 \<and> k = 2)"]
           body[THEN order_trans])
        apply simp
       apply simp
      apply simp
    \<comment> \<open>Same focus-then-destructure shape as the positive twin. The extra content is pinning the
       existential \<open>r\<close>: the body hands back \<open>2 ^ (r - 1) \<le> 1 < 2 ^ r\<close> for \<open>\<bar>kiou_norm ! 0\<bar> = 1\<close>,
       which forces \<open>r = 1\<close>, and then \<open>kiou_term 1 1 1 = 2\<close>.\<close>
     subgoal for s
       apply (cases s)
       apply (clarsimp simp del: One_nat_def)
       apply (rule order_trans[OF body];
              auto simp: kiou_norm_witness_neg kiou_term_def rl power_le_one_iff)
       done
    apply auto
    done
qed

text \<open>\<open>mpz_bitlen2_monadic_full\<close>'s own precondition is \<open>\<bar>m\<bar> < 2 ^ (max_snat - 1)\<close> — another
  exponent that must NOT be evaluated. Same treatment as the headroom lemmas.\<close>

text \<open>The one numeric \<open>max_snat\<close> comparison the outer op needs, derived ONCE so that
  \<open>max_snat_def\<close> never enters an \<open>auto\<close> that also carries an exponent.\<close>

lemma witness_len_bound: "Suc (Suc (Suc 0)) < max_snat LENGTH(gmp_poly_len)"
  \<comment> \<open>In \<open>Suc\<close> form, not as the numeral \<open>3\<close>: the goal \<open>refine_vcg\<close> leaves is literally
     \<open>Suc (Suc (Suc 0)) < max_snat 64\<close>, and a numeral-form fact does not discharge it.\<close>
  by (simp add: max_snat_def)

lemma witness_bitlen_arg:
  fixes a :: int
  assumes "\<bar>a\<bar> = 1"
  shows "\<bar>a\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)"
proof -
  have npos: "0 < max_snat LENGTH(gmp_poly_len) - 1" by (simp add: max_snat_def)
  have "(1::int) < 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)"
    by (rule one_less_power[OF _ npos]) simp
  thus ?thesis using assms by simp
qed

lemma kiou_bound_k_witness_pos: "kiou_bound_k_monadic [1, 1] \<le> SPEC (\<lambda>k. k = 1)"
  unfolding kiou_bound_k_monadic_def poly_length_monadic_def
    poly_coeff_sgn_monadic_def poly_coeff_bitlen2_monadic_def Let_def PR_CONST_def
  \<comment> \<open>\<open>[unfolded One_nat_def]\<close> is load-bearing: \<open>refine_vcg\<close> presents the fold call with \<open>Suc 0\<close>
     for \<open>n\<close> while the witness lemma is stated with the numeral \<open>1\<close>, and \<open>order_trans\<close> will not
     unify those — the hint then silently never fires and the whole fold call survives into the
     final goal.\<close>
  apply (refine_vcg mpz_bitlen2_monadic_full)
  apply (auto simp: witness_bitlen_arg witness_len_bound)
  \<comment> \<open>The fold call is a RESIDUAL that \<open>refine_vcg\<close> does not route, so the witness has to be
     applied by hand. Two normal-form gaps to bridge at once: \<open>[unfolded One_nat_def]\<close> turns the
     lemma's numeral \<open>1\<close> into the goal's \<open>Suc 0\<close>, and \<open>order_trans\<close> (not \<open>rule\<close>) absorbs
     \<open>SPEC (\<lambda>k. k = Suc 0) \<le> RES {Suc 0}\<close>, which are not syntactically equal.\<close>
   subgoal by (simp add: max_snat_def)
  apply (rule order_trans[OF kiou_maxfold_witness_pos[unfolded One_nat_def]]; auto)
  done

lemma kiou_bound_k_witness_neg: "kiou_bound_k_monadic [1, - 1] \<le> SPEC (\<lambda>k. k = 2)"
  unfolding kiou_bound_k_monadic_def poly_length_monadic_def
    poly_coeff_sgn_monadic_def poly_coeff_bitlen2_monadic_def Let_def PR_CONST_def
  apply (refine_vcg mpz_bitlen2_monadic_full)
  apply (auto simp: witness_bitlen_arg witness_len_bound power_le_one_iff)
  \<comment> \<open>Same, plus the witness's own \<open>rlead = Suc 0\<close> side goal, which follows from the residual's
     premises \<open>1 < 2 ^ x\<close> and \<open>x \<le> Suc 0\<close>.\<close>
   subgoal by (simp add: max_snat_def)
  \<comment> \<open>Unlike the positive twin, this witness carries \<open>rlead = 1\<close>, so \<open>order_trans\<close> prepends the
     side goal \<open>x = Suc 0\<close>. \<open>auto\<close> cannot get there from \<open>1 < 2 ^ x\<close> and \<open>x \<le> Suc 0\<close> without
     case-splitting \<open>x\<close> to see that \<open>2 ^ 0 = 1\<close> refutes the first premise — and under
     \<open>apply (rule X; auto)\<close> that failure re-prints the ORIGINAL goal, which reads as if the rule
     never applied.\<close>
  subgoal for x
    apply (cases x)
     apply simp
    apply (rule order_trans[OF kiou_maxfold_witness_neg[unfolded One_nat_def]]; auto)
    done
  done

section \<open>The capacity at the computed exponent\<close>

text \<open>The two capacity conjuncts are monotone in \<open>\<mu>\<close>, so the bound suffices — but the
  \<open>2 ^ Suc \<mu>\<close> step needs \<open>power_increasing\<close> explicitly: \<open>simp\<close> will not weaken an exponent it
  cannot evaluate.\<close>

lemma cap_from_mu_le4:
  fixes m k :: nat
  assumes m: "m \<le> 4" and k: "k \<le> 4"
  shows "k + m + 1 < max_snat LENGTH(gmp_poly_len)
       \<and> int (2 ^ Suc m) + 1 < int (max_snat LENGTH(gmp_poly_len))"
proof -
  have "(2::int) ^ Suc m \<le> 2 ^ Suc 4" using m by (intro power_increasing) simp_all
  thus ?thesis using m k by (simp add: max_snat_def)
qed

lemma split_cap_witness_pos: "split_cap [1, 1] 1"
proof -
  have deg: "degree (map_poly of_int (Poly [1, 2 ^ (1::nat)]) :: real poly) = 1" by simp
  show ?thesis
    unfolding split_cap_def Let_def witness_scale_pos
    using cap_from_mu_le4[OF rational_interval_mu_degree1_le[OF deg], of 1]
    by (simp add: max_snat_def)
qed

lemma split_cap_witness_neg: "split_cap [1, - 1] 2"
proof -
  have deg: "degree (map_poly of_int (Poly [1, - (2 ^ (2::nat))]) :: real poly) = 1" by simp
  show ?thesis
    unfolding split_cap_def Let_def witness_scale_neg
    using cap_from_mu_le4[OF rational_interval_mu_degree1_le[OF deg], of 2]
    by (simp add: max_snat_def)
qed

section \<open>The witness\<close>

text \<open>A degree-1 polynomial over an integral domain is squarefree: a repeated factor \<open>q * q\<close>
  with \<open>degree q > 0\<close> would already have degree \<open>\<ge> 2\<close>, and a nonzero polynomial cannot be
  divided by one of larger degree.\<close>

lemma square_free_degree1:
  fixes p :: "'a::idom poly"
  assumes d: "degree p = 1"
  shows "square_free p"
proof -
  have p0: "p \<noteq> 0" using d by auto
  show ?thesis
    unfolding square_free_def
  proof (intro conjI allI impI)
    show "p \<noteq> 0" by (rule p0)
  next
    fix q :: "'a poly"
    assume dq: "0 < degree q"
    show "\<not> q * q dvd p"
    proof
      assume dvd: "q * q dvd p"
      have q0: "q \<noteq> 0" using dq by auto
      have "degree (q * q) \<le> degree p"
        using dvd p0 by (rule dvd_imp_degree_le)
      moreover have "degree (q * q) = degree q + degree q"
        using q0 by (simp add: degree_mult_eq)
      ultimately show False using d dq by simp
    qed
  qed
qed

theorem dsc_isolate_all_split_pre_satisfiable:
  "dsc_isolate_all_split_pre [1, 1]"
  unfolding dsc_isolate_all_split_pre_def
proof (intro conjI)
  show "2 \<le> length [1, 1::int]" by simp
  show "last [1, 1::int] \<noteq> 0" by simp
  show "kiou_headroom [1, 1]" by (rule witness_headroom_pos)
  show "coeffs (Poly [1, 1::int]) = [1, 1]" by simp
  show "square_free (map_poly of_int (Poly [1, 1::int]) :: real poly)"
    by (rule square_free_degree1) simp
  show "kiou_bound_k_monadic [1, 1] \<le> SPEC (split_cap [1, 1])"
    by (rule order_trans[OF kiou_bound_k_witness_pos])
       (use split_cap_witness_pos in auto)
  show "kiou_bound_k_monadic (refl_list [1, 1]) \<le> SPEC (split_cap (refl_list [1, 1]))"
    unfolding witness_refl_list
    by (rule order_trans[OF kiou_bound_k_witness_neg])
       (use split_cap_witness_neg in auto)
qed

corollary split_pre_not_vacuous: "\<exists>xs. dsc_isolate_all_split_pre xs"
  using dsc_isolate_all_split_pre_satisfiable by blast

section \<open>The hybrid bundle\<close>

text \<open>\<^bold>\<open>The witness above does not cover the hybrid bundle.\<close>
  @{thm [source] dsc_isolate_all_split_pre_satisfiable} discharges @{const dsc_isolate_all_split_pre}. The
  hybrid capstone @{thm [source] hybrid_isolate_all_split_main_correct} and the power-substitution
  entry theorems take the stronger @{const dsc_isolate_all_split_hybrid_pre}, which adds two
  @{const hybrid_depth_cap} clauses, and satisfiability does not transfer to a bundle with more
  conjuncts.

  \<^bold>\<open>Why the extra clauses are easy here.\<close> \<open>hybrid_depth_cap ys k\<close> bounds \<open>kD\<close> by \<open>(2 ^ ecap + 2) * \<mu>\<close>, with
  \<open>\<mu>\<close> taken at the scaled list \<open>scale_poly_list (2 ^ k) ys\<close>. Scaling \<open>[1, 1]\<close> gives \<open>[1, 2 ^ k]\<close>, still of
  degree 1, so the same @{const root_sep} branch applies at every \<open>k\<close> and \<open>\<mu> \<le> 4\<close> uniformly. Hence the cap
  holds for every \<open>k\<close>, and the two \<open>\<le> SPEC\<close> clauses need no value of the Kioustelidis bound. As above, this
  shows consistency only.\<close>

lemma witness_degree1_scaled_pos:
  "degree (map_poly of_int (Poly (scale_poly_list (2 ^ k) [1, 1])) :: real poly) = 1"
proof -
  have "(2::int) ^ k \<noteq> 0" by simp
  thus ?thesis unfolding witness_scale_pos by (simp add: degree_map_poly)
qed

lemma witness_degree1_scaled_neg:
  "degree (map_poly of_int (Poly (scale_poly_list (2 ^ k) [1, - 1])) :: real poly) = 1"
proof -
  have "- ((2::int) ^ k) \<noteq> 0" by simp
  thus ?thesis unfolding witness_scale_neg by (simp add: degree_map_poly)
qed

text \<open>\<^bold>\<open>The \<open>\<mu>\<close> cap at the scaled list, in the \<open>dyadic_iv_\<close> spelling\<close> the depth cap is stated
  in. @{thm [source] dyadic_iv_interval_mu_eq_rational} is the bridge; it is an identity, so this
  is @{thm [source] rational_interval_mu_degree1_le} verbatim.\<close>

lemma witness_mu_scaled_le:
  assumes "degree (map_poly of_int (Poly ys') :: real poly) = 1"
  shows "dyadic_iv_interval_mu (delta_P (map_poly of_int (Poly ys') :: real poly)) (0, 1) \<le> 4"
  unfolding dyadic_iv_interval_mu_eq_rational
  by (rule rational_interval_mu_degree1_le[OF assms])

text \<open>\<^bold>\<open>The arithmetic, once, for both halves.\<close> With \<open>\<mu> \<le> 4\<close> and \<open>2 ^ ecap + 2 = 258\<close> the
  quantified \<open>kD\<close> is capped at \<open>1032\<close>, and both witness lists have length 2 — so the first clause
  is \<open>kD * 1 < max_snat\<close> and the second \<open>(kD + 1) * 2 < 2 ^ 40\<close>. Both are numerals against 1032.\<close>

lemma witness_depth_cap_arith:
  fixes \<delta> :: real
  assumes mu4: "dyadic_iv_interval_mu \<delta> (0, 1) \<le> 4"
    and kD: "int kD \<le> int (2 ^ newton_pol_ecap + 2) * int (dyadic_iv_interval_mu \<delta> (0, 1))"
  shows "kD \<le> 1032"
proof -
  have "int (2 ^ newton_pol_ecap + 2) * int (dyadic_iv_interval_mu \<delta> (0, 1))
          \<le> int (2 ^ newton_pol_ecap + 2) * int 4"
    using mu4 by (intro mult_left_mono) (simp_all add: newton_pol_ecap_def)
  also have "\<dots> = 1032" by (simp add: newton_pol_ecap_def)
  finally have "int kD \<le> 1032" using kD by linarith
  thus ?thesis by linarith
qed

lemma witness_hybrid_depth_cap_pos: "hybrid_depth_cap [1, 1] k"
  unfolding hybrid_depth_cap_def Let_def
proof (intro conjI allI impI)
  fix kD :: nat
  assume h: "int kD \<le> int (2 ^ newton_pol_ecap + 2)
        * int (dyadic_iv_interval_mu
                 (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ k) [1, 1])) :: real poly))
                 (0, 1))"
  have b: "kD \<le> 1032"
    by (rule witness_depth_cap_arith[OF witness_mu_scaled_le[OF witness_degree1_scaled_pos] h])
  show "kD * (length [1, 1::int] - 1) < max_snat LENGTH(gmp_poly_len)"
    using b by (simp add: max_snat_def)
next
  fix kD :: nat
  assume h: "int kD \<le> int (2 ^ newton_pol_ecap + 2)
        * int (dyadic_iv_interval_mu
                 (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ k) [1, 1])) :: real poly))
                 (0, 1))"
  have b: "kD \<le> 1032"
    by (rule witness_depth_cap_arith[OF witness_mu_scaled_le[OF witness_degree1_scaled_pos] h])
  show "(kD + 1) * length [1, 1::int] < 1099511627776" using b by simp
qed

lemma witness_hybrid_depth_cap_neg: "hybrid_depth_cap [1, - 1] k"
  unfolding hybrid_depth_cap_def Let_def
proof (intro conjI allI impI)
  fix kD :: nat
  assume h: "int kD \<le> int (2 ^ newton_pol_ecap + 2)
        * int (dyadic_iv_interval_mu
                 (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ k) [1, - 1])) :: real poly))
                 (0, 1))"
  have b: "kD \<le> 1032"
    by (rule witness_depth_cap_arith[OF witness_mu_scaled_le[OF witness_degree1_scaled_neg] h])
  show "kD * (length [1, - 1::int] - 1) < max_snat LENGTH(gmp_poly_len)"
    using b by (simp add: max_snat_def)
next
  fix kD :: nat
  assume h: "int kD \<le> int (2 ^ newton_pol_ecap + 2)
        * int (dyadic_iv_interval_mu
                 (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ k) [1, - 1])) :: real poly))
                 (0, 1))"
  have b: "kD \<le> 1032"
    by (rule witness_depth_cap_arith[OF witness_mu_scaled_le[OF witness_degree1_scaled_neg] h])
  show "(kD + 1) * length [1, - 1::int] < 1099511627776" using b by simp
qed

theorem dsc_isolate_all_split_hybrid_pre_satisfiable:
  "dsc_isolate_all_split_hybrid_pre [1, 1]"
  unfolding dsc_isolate_all_split_hybrid_pre_def
proof (intro conjI)
  show "dsc_isolate_all_split_pre [1, 1]" by (rule dsc_isolate_all_split_pre_satisfiable)
  show "length [1, 1::int] + 3 < max_snat LENGTH(gmp_poly_len)"
    by (simp add: max_snat_def)
  show "length [1, 1::int] < 1099511627776" by simp
  show "kiou_bound_k_monadic [1, 1] \<le> SPEC (hybrid_depth_cap [1, 1])"
    by (rule order_trans[OF kiou_bound_k_witness_pos])
       (use witness_hybrid_depth_cap_pos in auto)
  show "kiou_bound_k_monadic (refl_list [1, 1]) \<le> SPEC (hybrid_depth_cap (refl_list [1, 1]))"
    unfolding witness_refl_list
    by (rule order_trans[OF kiou_bound_k_witness_neg])
       (use witness_hybrid_depth_cap_neg in auto)
qed

corollary split_hybrid_pre_not_vacuous: "\<exists>xs. dsc_isolate_all_split_hybrid_pre xs"
  using dsc_isolate_all_split_hybrid_pre_satisfiable by blast

text \<open>\<^bold>\<open>Consequence.\<close> The hybrid capstone's hypothesis is inhabited, so
  @{thm [source] hybrid_isolate_all_split_main_correct} is not vacuously true.\<close>

corollary hybrid_capstone_not_vacuous:
  "\<exists>xs. dsc_isolate_all_split_hybrid_pre xs
      \<and> hybrid_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accQ, xs0).
          (\<forall>I \<in> set (dyadic_interval_vec_to_list accP).
            \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J) \<and>
          (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list accP).
              \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)) \<and>
          (\<forall>I \<in> set (dyadic_interval_vec_to_list accQ).
            \<exists>J. I = real_to_rat_pair J \<and>
                dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J) \<and>
          (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list accQ).
              \<exists>J. I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)) \<and>
          xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
  using dsc_isolate_all_split_hybrid_pre_satisfiable
        hybrid_isolate_all_split_main_correct[OF dsc_isolate_all_split_hybrid_pre_satisfiable]
  by blast

section \<open>The deflating bundle\<close>

text \<open>\<^bold>\<open>A witness for the deflating bundle.\<close> Satisfiability does not transfer between
  bundles with different conjuncts, and @{const dsc_isolate_all_split_defl_pre} differs from the hybrid
  bundle in two ways: its two depth caps are quantified over \<open>kD \<le> 258 \<cdot> \<mu>(delta_defl)\<close> rather than
  \<open>258 \<cdot> \<mu>(delta_P)\<close>, and \<open>delta_defl\<close> is the smaller \<open>\<delta>\<close>, hence the larger \<open>kD\<close> range; and it
  lacks @{const split_cap}'s exponential clause. So @{thm [source] split_hybrid_pre_not_vacuous}
  does not transfer as it stands.

  \<^bold>\<open>One witness serves both bundles.\<close> The hybrid bundle's witness is carried over by
  \<open>dsc_isolate_all_split_pre_imp_lin\<close> below. At degree 1, @{thm [source] witness_mu_scaled_le} gives
  \<open>\<mu>(delta_P) \<le> 4\<close>, and @{thm [source] defl_mu_delta_defl_le} bounds \<open>\<mu>(delta_defl)\<close> by
  \<open>max (\<mu>(delta_P)) 4\<close>, so the deflating \<open>\<mu>\<close> is also \<open>\<le> 4\<close> and
  @{thm [source] witness_depth_cap_arith} applies at every \<open>k\<close>. As above, this shows consistency
  only.\<close>

lemma witness_mu_defl_scaled_le:
  assumes d1: "degree (map_poly of_int (Poly ys') :: real poly) = 1"
  shows "dyadic_iv_interval_mu
           (delta_defl (map_poly of_int (Poly ys') :: real poly)) (0, 1) \<le> 4"
proof -
  have "dyadic_iv_interval_mu (delta_defl (map_poly of_int (Poly ys') :: real poly)) (0, 1)
          \<le> max (dyadic_iv_interval_mu
                    (delta_P (map_poly of_int (Poly ys') :: real poly)) (0, 1)) 4"
    by (rule defl_mu_delta_defl_le)
  thus ?thesis using witness_mu_scaled_le[OF d1] by simp
qed

lemma witness_defl_depth_cap_pos: "defl_depth_cap [1, 1] k"
  unfolding defl_depth_cap_def Let_def
proof (intro conjI allI impI)
  fix kD :: nat
  assume h: "int kD \<le> int (2 ^ newton_pol_ecap + 2)
        * int (dyadic_iv_interval_mu
                 (delta_defl
                    (map_poly of_int (Poly (scale_poly_list (2 ^ k) [1, 1])) :: real poly))
                 (0, 1))"
  have b: "kD \<le> 1032"
    by (rule witness_depth_cap_arith[OF witness_mu_defl_scaled_le[OF witness_degree1_scaled_pos] h])
  show "kD * (length [1, 1::int] - 1) < max_snat LENGTH(gmp_poly_len)"
    using b by (simp add: max_snat_def)
next
  fix kD :: nat
  assume h: "int kD \<le> int (2 ^ newton_pol_ecap + 2)
        * int (dyadic_iv_interval_mu
                 (delta_defl
                    (map_poly of_int (Poly (scale_poly_list (2 ^ k) [1, 1])) :: real poly))
                 (0, 1))"
  have b: "kD \<le> 1032"
    by (rule witness_depth_cap_arith[OF witness_mu_defl_scaled_le[OF witness_degree1_scaled_pos] h])
  show "(kD + 1) * length [1, 1::int] < 1099511627776" using b by simp
qed

lemma witness_defl_depth_cap_neg: "defl_depth_cap [1, - 1] k"
  unfolding defl_depth_cap_def Let_def
proof (intro conjI allI impI)
  fix kD :: nat
  assume h: "int kD \<le> int (2 ^ newton_pol_ecap + 2)
        * int (dyadic_iv_interval_mu
                 (delta_defl
                    (map_poly of_int (Poly (scale_poly_list (2 ^ k) [1, - 1])) :: real poly))
                 (0, 1))"
  have b: "kD \<le> 1032"
    by (rule witness_depth_cap_arith[OF witness_mu_defl_scaled_le[OF witness_degree1_scaled_neg] h])
  show "kD * (length [1, - 1::int] - 1) < max_snat LENGTH(gmp_poly_len)"
    using b by (simp add: max_snat_def)
next
  fix kD :: nat
  assume h: "int kD \<le> int (2 ^ newton_pol_ecap + 2)
        * int (dyadic_iv_interval_mu
                 (delta_defl
                    (map_poly of_int (Poly (scale_poly_list (2 ^ k) [1, - 1])) :: real poly))
                 (0, 1))"
  have b: "kD \<le> 1032"
    by (rule witness_depth_cap_arith[OF witness_mu_defl_scaled_le[OF witness_degree1_scaled_neg] h])
  show "(kD + 1) * length [1, - 1::int] < 1099511627776" using b by simp
qed

lemma dsc_isolate_all_split_pre_imp_lin:
  assumes pre: "dsc_isolate_all_split_pre xs"
  shows "dsc_isolate_all_split_lin_pre xs"
proof -
  have l2: "2 \<le> length xs" using pre unfolding dsc_isolate_all_split_pre_def by simp
  have l2r: "2 \<le> length (refl_list xs)" using l2 by simp
  show ?thesis
    using pre unfolding dsc_isolate_all_split_pre_def dsc_isolate_all_split_lin_pre_def
    by (auto elim!: order_trans intro!: SPEC_rule split_cap_imp_lin l2 l2r)
qed

theorem dsc_isolate_all_split_defl_pre_satisfiable:
  "dsc_isolate_all_split_defl_pre [1, 1]"
  unfolding dsc_isolate_all_split_defl_pre_def
proof (intro conjI)
  show "dsc_isolate_all_split_lin_pre [1, 1]"
    by (rule dsc_isolate_all_split_pre_imp_lin[OF dsc_isolate_all_split_pre_satisfiable])
  show "length [1, 1::int] + 3 < max_snat LENGTH(gmp_poly_len)"
    by (simp add: max_snat_def)
  show "length [1, 1::int] < 1099511627776" by simp
  show "kiou_bound_k_monadic [1, 1] \<le> SPEC (defl_depth_cap [1, 1])"
    by (rule order_trans[OF kiou_bound_k_witness_pos])
       (use witness_defl_depth_cap_pos in auto)
  show "kiou_bound_k_monadic (refl_list [1, 1]) \<le> SPEC (defl_depth_cap (refl_list [1, 1]))"
    unfolding witness_refl_list
    by (rule order_trans[OF kiou_bound_k_witness_neg])
       (use witness_defl_depth_cap_neg in auto)
qed

corollary split_defl_pre_not_vacuous: "\<exists>xs. dsc_isolate_all_split_defl_pre xs"
  using dsc_isolate_all_split_defl_pre_satisfiable by blast

text \<open>\<^bold>\<open>The conclusion holds outright\<close>: the deflating capstone's four \<open>qsolve\<close> conjuncts hold at a concrete
  input, so @{thm [source] defl_isolate_all_split_main_correct_qsolve}, which the power-substitution entry
  theorems consume, is not vacuously true.\<close>

corollary defl_capstone_not_vacuous:
  "\<exists>xs. dsc_isolate_all_split_defl_pre xs
      \<and> defl_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accN, xs0).
          dyadic_interval_vec_invar accP \<and>
          length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
          defl_acc_isolates (real_of_int_poly (Poly xs)) accP \<and>
          defl_acc_covers (real_of_int_poly (Poly xs)) 0 accP)"
  using dsc_isolate_all_split_defl_pre_satisfiable
        defl_isolate_all_split_main_correct_qsolve[OF dsc_isolate_all_split_defl_pre_satisfiable]
  by blast

section \<open>The power-substitution entry theorems are not vacuous\<close>

text \<open>\<open>pow_sub_entry_monadic_correct_of_pre\<close> and \<open>_complete_of_pre\<close> consume
  @{thm [source] defl_isolate_all_split_main_correct_qsolve} rather than assuming its conclusion, so the
  witness below is stated with no extra hypothesis: the conclusion holds at a concrete input.

  \<open>qpre\<close> is stated with @{const dsc_isolate_all_split_defl_pre}, because the deflating capstone holds only
  there, and \<open>defl \<longrightarrow> hybrid\<close> is the wrong direction to satisfy a hypothesis quantified over every \<open>q\<close>
  meeting the hybrid bundle. The deflating witness above covers it.\<close>

text \<open>\<open>pow_sub_entry_monadic_correct_of_pre\<close> and \<open>pow_sub_entry_monadic_complete_of_pre\<close> are conditional on
  \<open>dsc_isolate_all_split_defl_pre (pow_sub_extract d xs)\<close>, a precondition on the reduced
  polynomial (every \<open>d\<close>-th coefficient of the input). So again: an explicit \<open>xs\<close>, an explicit \<open>hcap\<close>, every
  hypothesis discharged.

  \<^bold>\<open>The witness is \<open>xs = [1, 0, 1]\<close>, i.e. \<open>P = 1 + x\<^sup>2\<close>, at \<open>hcap = 32\<close>.\<close> Its support is \<open>{0, 2}\<close>, so
  \<open>pow_sub_h = 2\<close>, the clamped exponent is \<open>gcd 2 32 = 2\<close> (even and \<open>\<ge> 2\<close>, so the entry substitutes), and the
  extracted reduced list is \<open>[1, 1]\<close>, which \<open>dsc_isolate_all_split_defl_pre_satisfiable\<close> covers.

  \<^bold>\<open>What this settles.\<close> The entry theorems are not vacuously true: on at least one input the substituting
  path is taken and the conclusions have content. It does not settle whether the hypothesis transports in
  general, and it does not: \<open>\<mu>\<^sub>Q\<close> can exceed \<open>\<mu>\<^sub>P\<close> (\<open>P(x) = (2\<^sup>8\<^sup>0x\<^sup>2 - 1)(2\<^sup>8\<^sup>0x\<^sup>2 - 4)\<close>), so the hypothesis is a genuine
  caller obligation.\<close>

subsection \<open>The witness polynomial is squarefree\<close>

text \<open>\<^bold>\<open>A real polynomial of degree 2 with no real root is squarefree.\<close> A repeated non-unit factor of a
  degree-2 polynomial must be linear, and a linear real polynomial has a real root, which would be a root of
  the product. Stated generally so the numeral work happens once.

  This is @{const squarefree} (\<open>HOL-Computational_Algebra\<close>: every square divisor is a unit), not the AFP's
  @{const square_free} that @{const dsc_isolate_all_split_pre} uses, so \<open>square_free_degree1\<close> above does not
  serve.\<close>

lemma squarefree_deg2_no_real_root:
  fixes p :: "real poly"
  assumes d: "degree p = 2" and nr: "\<And>x :: real. poly p x \<noteq> 0"
  shows "squarefree p"
proof (rule squarefreeI)
  fix q :: "real poly"
  assume dvd: "q\<^sup>2 dvd p"
  have p0: "p \<noteq> 0" using d by auto
  have q0: "q \<noteq> 0"
  proof
    assume "q = 0"
    with dvd have "p = 0" by simp
    with p0 show False ..
  qed
  show "q dvd 1"
  proof (rule ccontr)
    assume nu: "\<not> q dvd 1"
    have dq0: "degree q \<noteq> 0" using nu q0 by (simp add: is_unit_iff_degree)
    have "degree (q\<^sup>2) \<le> degree p" using dvd p0 by (rule dvd_imp_degree_le)
    then have "2 * degree q \<le> 2" using d q0 by (simp add: Polynomial.degree_power_eq)
    with dq0 have dq1: "degree q = 1" by simp
    then obtain a b where qab: "q = [:a, b:]" and b0: "b \<noteq> 0" by (rule degree_eq_oneE)
    \<comment> \<open>the real root of the linear factor — this is the step that needs the field to be REAL\<close>
    have root: "poly q (- a / b) = 0" using qab b0 by simp
    from dvd obtain k where pk: "p = q\<^sup>2 * k" ..
    have "poly p (- a / b) = (poly q (- a / b))\<^sup>2 * poly k (- a / b)"
      by (simp add: pk)
    also have "\<dots> = 0" using root by simp
    finally show False using nr by simp
  qed
qed

lemma witness_pow_sub_poly: "(real_of_int_poly (Poly [1, 0, 1]) :: real poly) = [:1, 0, 1:]"
  by simp

lemma witness_pow_sub_squarefree:
  "squarefree (real_of_int_poly (Poly [1, 0, 1]) :: real poly)"
  unfolding witness_pow_sub_poly
proof (rule squarefree_deg2_no_real_root)
  show "degree ([:1, 0, 1:] :: real poly) = 2" by simp
next
  fix x :: real
  have "poly ([:1, 0, 1:] :: real poly) x = 1 + x * x" by simp
  moreover have "0 \<le> x * x" by simp
  ultimately show "poly ([:1, 0, 1:] :: real poly) x \<noteq> 0" by linarith
qed

subsection \<open>Detection and extraction, evaluated on the witness\<close>

lemma witness_pow_sub_support: "pow_sub_support [1, 0, 1] = {0, 2}"
  unfolding pow_sub_support_def by (auto simp: less_Suc_eq)

lemma witness_pow_sub_h: "pow_sub_h [1, 0, 1] = 2"
  unfolding pow_sub_h_def witness_pow_sub_support by simp

lemma witness_pow_sub_exp: "gcd (pow_sub_h [1, 0, 1]) 32 = 2"
  unfolding witness_pow_sub_h by simp

text \<open>\<open>pow_sub_extract 2 [1,0,1] = map (\<lambda>j. xs ! (j * 2)) [0..<Suc ((3 - 1) div 2)] = [xs ! 0, xs ! 2] = [1, 1]\<close>,
  the witness list above.\<close>

lemma witness_pow_sub_extract: "pow_sub_extract 2 [1, 0, 1] = [1, 1]"
  unfolding pow_sub_extract_def by simp

subsection \<open>The reduced arm's precondition, discharged\<close>

lemma witness_pow_sub_qpre:
  assumes d2: "2 \<le> d" and ev: "even d" and deq: "d = gcd (pow_sub_h [1, 0, 1]) 32"
  shows "dsc_isolate_all_split_defl_pre (pow_sub_extract d [1, 0, 1])"
proof -
  \<comment> \<open>\<open>d\<close> is PINNED by \<open>deq\<close>, so \<open>d2\<close>/\<open>ev\<close> are not needed here — they are carried only because
     the entry theorem's hypothesis is stated with them.\<close>
  have d_eq: "d = 2" using deq witness_pow_sub_exp by simp
  show ?thesis
    unfolding d_eq witness_pow_sub_extract
    by (rule dsc_isolate_all_split_defl_pre_satisfiable)
qed

subsection \<open>The payoff: both entry theorems have content at this input\<close>

text \<open>Stated as the CONCLUSION holding outright, not merely as "the hypotheses are satisfiable".
  The two are different strengths of evidence, and only the former shows the theorem says
  something.\<close>

theorem pow_sub_entry_correct_not_vacuous:
  "pow_sub_entry_monadic nfloor 32 dlt [1, 0, 1] \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>j < length (dyadic_interval_vec_triples out).
                 case dyadic_interval_vec_triples out ! j of ((L, R), m) \<Rightarrow>
                   dsc_pair_ok (real_of_int_poly (Poly [1, 0, 1]) :: real poly)
                               (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
                   \<and> dsc_pair_ok (real_of_int_poly (Poly [1, 0, 1]) :: real poly)
                               (- (real_of_int R / 2 ^ m), - (real_of_int L / 2 ^ m))))"
proof (rule pow_sub_entry_monadic_correct_of_pre)
  show "([1, 0, 1] :: int list) \<noteq> []" by simp
  show "length [1, 0, 1::int] + 1 < max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
  show "(32 :: nat) < max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
  show "last [1, 0, 1::int] \<noteq> 0" by simp
  show "squarefree (real_of_int_poly (Poly [1, 0, 1]) :: real poly)"
    by (rule witness_pow_sub_squarefree)
next
  fix d :: nat
  assume "2 \<le> d" and "even d" and "d = gcd (pow_sub_h [1, 0, 1]) 32"
  thus "dsc_isolate_all_split_defl_pre (pow_sub_extract d [1, 0, 1])"
    by (rule witness_pow_sub_qpre)
qed

theorem pow_sub_entry_complete_not_vacuous:
  "pow_sub_entry_monadic nfloor 32 dlt [1, 0, 1] \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>x::real. poly (real_of_int_poly (Poly [1, 0, 1]) :: real poly) x = 0 \<longrightarrow>
        (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
           \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
           \<and> ((real_of_int L / 2 ^ m \<le> x \<and> x \<le> real_of_int R / 2 ^ m)
              \<or> (- (real_of_int R / 2 ^ m) \<le> x
                 \<and> x \<le> - (real_of_int L / 2 ^ m))))))"
proof (rule pow_sub_entry_monadic_complete_of_pre)
  show "([1, 0, 1] :: int list) \<noteq> []" by simp
  show "length [1, 0, 1::int] + 1 < max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
  show "(32 :: nat) < max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
  show "last [1, 0, 1::int] \<noteq> 0" by simp
  show "squarefree (real_of_int_poly (Poly [1, 0, 1]) :: real poly)"
    by (rule witness_pow_sub_squarefree)
next
  fix d :: nat
  assume "2 \<le> d" and "even d" and "d = gcd (pow_sub_h [1, 0, 1]) 32"
  thus "dsc_isolate_all_split_defl_pre (pow_sub_extract d [1, 0, 1])"
    by (rule witness_pow_sub_qpre)
qed

corollary pow_sub_entry_hypotheses_satisfiable:
  "\<exists>xs hcap. xs \<noteq> [] \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)
     \<and> hcap < max_snat LENGTH(gmp_poly_len) \<and> last xs \<noteq> 0
     \<and> squarefree (real_of_int_poly (Poly xs) :: real poly)
     \<and> 2 \<le> gcd (pow_sub_h xs) hcap \<and> even (gcd (pow_sub_h xs) hcap)
     \<and> (\<forall>d. 2 \<le> d \<longrightarrow> even d \<longrightarrow> d = gcd (pow_sub_h xs) hcap \<longrightarrow>
          dsc_isolate_all_split_defl_pre (pow_sub_extract d xs))"
proof (intro exI conjI allI impI)
  show "([1, 0, 1] :: int list) \<noteq> []" by simp
  show "length [1, 0, 1::int] + 1 < max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
  show "(32 :: nat) < max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
  show "last [1, 0, 1::int] \<noteq> 0" by simp
  show "squarefree (real_of_int_poly (Poly [1, 0, 1]) :: real poly)"
    by (rule witness_pow_sub_squarefree)
  show "2 \<le> gcd (pow_sub_h [1, 0, 1]) 32" using witness_pow_sub_exp by simp
  show "even (gcd (pow_sub_h [1, 0, 1]) 32)" using witness_pow_sub_exp by simp
next
  fix d :: nat
  assume "2 \<le> d" and "even d" and "d = gcd (pow_sub_h [1, 0, 1]) 32"
  thus "dsc_isolate_all_split_defl_pre (pow_sub_extract d [1, 0, 1])"
    by (rule witness_pow_sub_qpre)
qed

section \<open>The low-degree capstone is not vacuous\<close>

text \<open>\<^bold>\<open>Stated as the conclusion holding outright.\<close> @{thm [source] lowdeg_isolate_all_split_main_correct} takes
  \<open>dsc_isolate_all_split_pre\<close>, the constant the bisection capstone takes and
  @{thm [source] dsc_isolate_all_split_pre_satisfiable} discharges at \<open>xs = [1, 1]\<close>; this bundle adds no
  conjuncts, so the transfer problem of the stronger bundles does not arise.

  \<^bold>\<open>At degree 1 this entry falls through.\<close> \<open>length [1,1] = 2\<close>, so @{const lowdeg_class_monadic} returns \<open>0\<close>
  and @{const lowdeg_isolate_all_split_main} hands the input to @{const bisection_isolate_all_split_main}. The
  corollary below therefore shows the capstone is not vacuous without exercising the degree-2/3 closed forms;
  a witness that does would need a length-3 \<open>xs\<close> satisfying the full bundle, i.e. the degree-2
  \<open>root_sep\<close>/\<open>\<mu>\<close>/\<open>split_cap\<close> arguments this theory builds only at degree 1.\<close>

\<comment> \<open>Declared with \<open>lemmas\<close> rather than restated as a \<open>corollary\<close> with the \<open>SPEC\<close> written out again: an
   instantiation of the capstone at the witness cannot drift from its source.\<close>
lemmas lowdeg_capstone_not_vacuous =
  lowdeg_isolate_all_split_main_correct[OF dsc_isolate_all_split_pre_satisfiable]

lemmas lowdeg_capstone_terminates_not_vacuous =
  lowdeg_isolate_all_split_main_terminates[OF dsc_isolate_all_split_pre_satisfiable]

corollary lowdeg_split_pre_not_vacuous: "\<exists>xs. dsc_isolate_all_split_pre xs"
  using dsc_isolate_all_split_pre_satisfiable by blast

end
