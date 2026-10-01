theory Kiou_Bound_Refine
  imports "IsaRRI_LLVM.Kiou_Bound"
begin

text \<open>Refines the Kioustelidis Sepref kernel (\<open>Kiou_Bound\<close>) onto the abstract positive-root bound
  \<open>kiou_k_sound\<close> (\<open>Kiou_Bound_Spec\<close>): every positive real root of \<open>Poly xs\<close> is strictly below \<open>2^k\<close>,
  where \<open>k\<close> is what \<open>kiou_bound_k_monadic\<close> computes.

  \<^bold>\<open>The headroom hypothesis.\<close> The specification of \<open>mpz_bitlen2_monadic\<close> does not bound the
  returned exponent by a machine word, since that would put a practical assumption into the
  trusted binding. So the fact that every coefficient's bit-length fits below \<open>max_snat 64\<close> is an
  explicit hypothesis here (@{term kiou_headroom}), with the same status as the precondition
  \<open>length xs + 1 < max_snat\<close>.\<close>

definition kiou_headroom :: "gmp_poly \<Rightarrow> bool" where
"kiou_headroom xs \<equiv> length xs + 3 < max_snat LENGTH(gmp_poly_len) \<and>
  (\<forall>i < length xs. \<bar>xs ! i\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - length xs - 2))"

lemma kiou_headroom_lenb: "kiou_headroom xs \<Longrightarrow> length xs + 3 < max_snat LENGTH(gmp_poly_len)"
  unfolding kiou_headroom_def by simp

lemma kiou_headroom_coeff:
  "kiou_headroom xs \<Longrightarrow> i < length xs
     \<Longrightarrow> \<bar>xs ! i\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - length xs - 2)"
  unfolding kiou_headroom_def by simp

text \<open>ONE combined \<open>\<le> SPEC\<close> fact bundling every conjunct \<open>mpz_bitlen2_monadic\<close> can supply --
  including the CONDITIONAL machine-word bound (\<open>mpz_bitlen2_monadic_snat_bound\<close>, Array.thy) --
  for a SINGLE bind. \<open>refine_vcg\<close> can only apply ONE \<open>\<le> SPEC\<close> fact per producer call, so
  supplying the three separate facts (\<open>pow2_bound\<close>/\<open>lower\<close>/\<open>snat_bound\<close>) leaves whichever one
  \<open>refine_vcg\<close> happens to pick as the ONLY available hypothesis downstream -- exactly the failure
  this caused (a subgoal needing \<open>r < max_snat\<close> with only the upper-bound fact in scope, which is
  UNPROVABLE alone since the abstract bit-length is nondeterministically bounded only from above).\<close>
lemma mpz_bitlen2_monadic_full:
  assumes "\<bar>m\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)"
  shows "mpz_bitlen2_monadic m \<le> SPEC (\<lambda>r.
      \<bar>m\<bar> < 2 ^ r \<and> (m \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>m\<bar>) \<and> r < max_snat LENGTH(gmp_poly_len))"
  \<comment> \<open>the upper bound is available because this lemma's magnitude hypothesis is strictly
     stronger than the \<open>size_t\<close>-representability guard the bit-length specification carries
     (@{thm [source] bitlen2_snat_guard})\<close>
  using mpz_bitlen2_monadic_pow2_bound[OF bitlen2_snat_guard[OF assms]]
    mpz_bitlen2_monadic_lower[of m] mpz_bitlen2_monadic_snat_bound[OF assms]
  by (auto simp: pw_le_iff refine_pw_simps)

section \<open>Leading-sign normalization: the sign-robustness device\<close>

text \<open>\<open>kiou_norm xs\<close> negates \<open>xs\<close> exactly when its leading coefficient is negative, so its own
  leading coefficient is \<open>\<bar>last xs\<bar> > 0\<close> while the real roots are unchanged (\<open>P\<close> and \<open>-P\<close> have
  the same root set). It is a PROOF-ONLY device -- the executable kernel never builds it.

  Its point is that the sign-robust fold's guard on \<open>xs!i\<close> ("does \<open>xs!i\<close> OPPOSE the leading
  coefficient?", i.e. \<open>if last xs < 0 then 0 < xs!i else xs!i < 0\<close>) is LITERALLY
  \<open>kiou_norm xs ! i < 0\<close>, while \<open>\<bar>kiou_norm xs ! i\<bar> = \<bar>xs!i\<bar>\<close> leaves every bit-length fact
  untouched. So the fold invariant, its step lemma, and the abstract @{thm [source] kiou_k_sound}
  are all reused VERBATIM at \<open>kiou_norm xs\<close>: the Kioustelidis math is never re-derived, and the
  positivity hypothesis it genuinely needs is discharged by construction.\<close>

definition kiou_norm :: "int list \<Rightarrow> int list" where
"kiou_norm xs = (if last xs < 0 then map uminus xs else xs)"

lemma kiou_norm_length[simp]: "length (kiou_norm xs) = length xs"
  unfolding kiou_norm_def by simp

lemma kiou_norm_nth:
  "j < length xs \<Longrightarrow> kiou_norm xs ! j = (if last xs < 0 then - xs ! j else xs ! j)"
  unfolding kiou_norm_def by simp

lemma kiou_norm_abs[simp]: "j < length xs \<Longrightarrow> \<bar>kiou_norm xs ! j\<bar> = \<bar>xs ! j\<bar>"
  by (simp add: kiou_norm_nth)

lemma kiou_norm_zero_iff[simp]: "j < length xs \<Longrightarrow> (kiou_norm xs ! j = 0) = (xs ! j = 0)"
  by (simp add: kiou_norm_nth)

text \<open>The load-bearing identity: the executable guard equals the normalized list's sign test.\<close>
lemma kiou_norm_neg_iff:
  "j < length xs \<Longrightarrow>
     (kiou_norm xs ! j < 0) = (if last xs < 0 then 0 < xs ! j else xs ! j < 0)"
  by (simp add: kiou_norm_nth)

lemma kiou_norm_last:
  assumes "xs \<noteq> []"
  shows "last (kiou_norm xs) = \<bar>last xs\<bar>"
  unfolding kiou_norm_def using assms by (auto simp: last_map)

lemma kiou_norm_last_pos:
  assumes "xs \<noteq> []" and "last xs \<noteq> 0"
  shows "0 < last (kiou_norm xs)"
  using kiou_norm_last[OF assms(1)] assms(2) by simp

lemma kiou_norm_last_nz:
  assumes "xs \<noteq> []" and "last xs \<noteq> 0"
  shows "last (kiou_norm xs) \<noteq> 0"
  using kiou_norm_last_pos[OF assms] by simp

text \<open>Negation preserves the real roots -- what lets the bound computed on \<open>kiou_norm xs\<close> be
  reported as a bound for \<open>xs\<close> itself. (Also reused downstream by \<open>Kiou_Bound_Reflect.thy\<close>.)\<close>
lemma Poly_map_uminus: "Poly (map uminus xs) = - Poly xs"
  by (intro poly_eqI) (simp add: coeff_Poly_eq nth_default_map_eq)

lemma ripoly_map_uminus: "ripoly (Poly (map uminus xs)) y = - ripoly (Poly xs) y"
  by (simp add: Poly_map_uminus of_int_poly_hom.hom_uminus)

lemma kiou_norm_root_iff:
  "(ripoly (Poly (kiou_norm xs)) x = 0) = (ripoly (Poly xs) x = 0)"
  unfolding kiou_norm_def by (simp add: ripoly_map_uminus)

lemma kiou_headroom_kiou_norm[simp]: "kiou_headroom (kiou_norm xs) = kiou_headroom xs"
  unfolding kiou_headroom_def kiou_norm_def by simp

section \<open>The per-coefficient arithmetic op: exact value + machine-word headroom\<close>

text \<open>Given the opposition flag \<open>opp\<close> (does this coefficient oppose the leading one?), bit-length
  \<open>ri\<close>, leading bit-length \<open>rlead\<close>, distance \<open>d = n-i > 0\<close>, and running max \<open>k\<close>,
  @{const kiou_update_mop} returns \<open>max k (if opp then kiou_term ri rlead d else 0)\<close> -- PROVIDED
  enough machine-word headroom on \<open>ri\<close> relative to \<open>d\<close> for its own internal overflow \<open>ASSERT\<close>s
  (the trust-boundary fix moved this from the (unsound) axiom to here, an explicit hypothesis on
  this correctness lemma).\<close>

lemma kiou_update_mop_correct:
  assumes dpos: "0 < d" and kge1: "1 \<le> k"
    and headroom: "ri + 1 + d < max_snat LENGTH(gmp_poly_len)"
  shows "kiou_update_mop opp ri rlead d k
           \<le> SPEC (\<lambda>k'. k' = max k (if opp then kiou_term ri rlead d else 0))"
proof -
  have q_bound: "\<And>q. q = (ri + 1 - rlead + d - 1) div d \<Longrightarrow> q + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    fix q assume "q = (ri + 1 - rlead + d - 1) div d"
    hence "q \<le> ri + 1 - rlead + d - 1" by (simp add: div_le_dividend)
    thus "q + 1 < max_snat LENGTH(gmp_poly_len)" using headroom by linarith
  qed
  show ?thesis
    unfolding kiou_update_mop_def kiou_term_def
    apply (refine_vcg)
    using dpos headroom kge1 q_bound
    by (auto simp: max_def)
qed

section \<open>One max-fold step\<close>

text \<open>The arithmetic core of the per-coefficient headroom check, proved once with its own named
  variables, so that it does not depend on the bound-variable names \<open>refine_vcg\<close> introduces at the
  call site.\<close>

text \<open>Core bit-length \<Rightarrow> exponent bound, stated in the EXACT \<open>Suc (Suc (length xs))\<close> exponent
  form that \<open>refine_vcg\<close> normalises the headroom hypothesis to (so \<open>intro!\<close> unifies without a
  syntactic-form fight -- the trap that ate several build cycles here).\<close>
lemma kiou_exp_lt:
  fixes r :: nat and xsi :: int
  assumes hr: "\<bar>xsi\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - Suc (Suc (length xs)))"
    and lb: "2 ^ (r - Suc 0) \<le> \<bar>xsi\<bar>"
  shows "r - Suc 0 < max_snat LENGTH(gmp_poly_len) - Suc (Suc (length xs))"
proof -
  have B: "(2::int) ^ (r - Suc 0) < 2 ^ (max_snat LENGTH(gmp_poly_len) - Suc (Suc (length xs)))"
    using lb hr by linarith
  show ?thesis by (rule power_less_imp_less_exp[OF _ B]) simp
qed

text \<open>The two shapes \<open>refine_vcg\<close> actually leaves: \<open>r < max_snat\<close> (for the bit-length ASSERT) and
  \<open>Suc (r + n - i) < max_snat\<close> (for the downstream \<open>d = n - i\<close> arithmetic). Both hyps carry
  \<open>xs ! i \<noteq> 0\<close>, so only the nonzero (lower-bound) case arises.\<close>
lemma kiou_snat_step:
  fixes r :: nat and xsi :: int
  assumes hr: "\<bar>xsi\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - Suc (Suc (length xs)))"
    and lenb: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    and lb: "2 ^ (r - Suc 0) \<le> \<bar>xsi\<bar>"
  shows "r < max_snat LENGTH(gmp_poly_len)"
  using kiou_exp_lt[OF hr lb] lenb by linarith

lemma kiou_headroom_step:
  fixes r :: nat and xsi :: int
  assumes hr: "\<bar>xsi\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - Suc (Suc (length xs)))"
    and lenb: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    and d_lt: "n - i < length xs"
    and lb: "2 ^ (r - Suc 0) \<le> \<bar>xsi\<bar>"
  shows "Suc (r + n - i) < max_snat LENGTH(gmp_poly_len)"
  using kiou_exp_lt[OF hr lb] lenb d_lt by linarith

text \<open>ONE loop step, with an EXPLICIT EXISTENTIAL conclusion carrying the fresh witness \<open>r\<close> that
  @{const mpz_bitlen2_monadic} produced for \<open>xs!i\<close> -- this is what lets the whole-fold invariant
  (below) thread a per-index witness function without inventing an abstract "canonical bit-length"
  helper: the witness is simply whatever the SPEC handed us at that step.\<close>

lemma kiou_maxfold_body_mop_monadic_correct:
  assumes n_len: "n < length xs" and kge1: "1 \<le> k" and i_lt: "i < n"
    and headroom: "\<bar>xs ! i\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - length xs - 2)"
    and lenb: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    and lneg: "lead_neg = (last xs < 0)"
  shows "kiou_maxfold_body_mop_monadic xs n lead_neg rlead (i, k) \<le>
    SPEC (\<lambda>st. \<exists>k' r. st = (i + 1, k')
       \<and> \<bar>kiou_norm xs ! i\<bar> < 2 ^ r \<and> (kiou_norm xs ! i \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>kiou_norm xs ! i\<bar>)
       \<and> k' = max k (if kiou_norm xs ! i < 0 then kiou_term r rlead (n - i) else 0))"
proof -
  have dn: "n - i < length xs" using n_len i_lt by simp
  have il: "i < length xs" using i_lt n_len by simp
  have hs: "\<bar>xs ! i\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - Suc (Suc (length xs)))"
    using headroom by (simp add: numeral_2_eq_2)
  have z1: "Suc 0 < max_snat LENGTH(gmp_poly_len)" using lenb by linarith
  have z2: "Suc (Suc (n - i)) < max_snat LENGTH(gmp_poly_len)" using lenb dn by linarith
  have z3: "Suc 0 \<le> k" using kge1 by simp
  have z4: "Suc i < max_snat LENGTH(gmp_poly_len)" using i_lt n_len lenb by linarith
  \<comment> \<open>The executable guard \<open>if lead_neg then 0 < sgn (xs!i) else sgn (xs!i) < 0\<close> is exactly
      \<open>kiou_norm xs ! i < 0\<close> (@{thm [source] kiou_norm_neg_iff} after \<open>sgn_less\<close>/\<open>sgn_greater\<close>),
      and \<open>\<bar>kiou_norm xs ! i\<bar> = \<bar>xs!i\<bar>\<close>, so the bit-length facts pass through unchanged.\<close>
  note norm_simps = lneg kiou_norm_neg_iff[OF il] kiou_norm_abs[OF il] kiou_norm_zero_iff[OF il]
                    sgn_less sgn_greater
  \<comment> \<open>\<^bold>\<open>The \<open>size_t\<close>-representability guard, discharged once for this coefficient.\<close> The
     bit-length specification's upper bound is an implication guarded on
     \<open>\<bar>m\<bar> < 2 ^ (max_unat gmp_size_len - 1)\<close>, so \<open>auto\<close> would case-split it and duplicate every
     subgoal with the negative branch. This node's headroom hypothesis is stronger, so the
     negative branch is vacuous, and supplying that fact up front removes the split. Same shape as
     @{thm [source] mpz_bitlen2_monadic_full}'s hypothesis; the weakening follows
     @{thm [source] bitlen2_snat_guard}'s proof.\<close>
  have hs1: "\<bar>xs ! i\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)"
  proof -
    have "(max_snat LENGTH(gmp_poly_len) - Suc (Suc (length xs)))
            \<le> (max_snat LENGTH(gmp_poly_len) - 1)" by simp
    hence "(2::int) ^ (max_snat LENGTH(gmp_poly_len) - Suc (Suc (length xs)))
             \<le> 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)"
      by (rule power_increasing) simp
    thus ?thesis using hs by linarith
  qed
  have hguard: "\<bar>xs ! i\<bar> < 2 ^ (max_unat gmp_size_len - 1)"
    by (rule bitlen2_snat_guard[OF hs1])
  show ?thesis
    unfolding kiou_maxfold_body_mop_monadic_def poly_coeff_sgn_monadic_def
      poly_coeff_bitlen2_monadic_def mpz_bitlen2_monadic_def
      prod.case Let_def PR_CONST_def
    apply (refine_vcg kiou_update_mop_correct[where d = "n - i"])
    using il i_lt z1 z2 z3 z4 hs hguard lenb dn kge1
    apply (auto simp: norm_simps intro: exI[of _ "Suc 0"])
    subgoal premises p for xa
    proof -
      have B: "(2::int) ^ (xa - Suc 0)
             < 2 ^ (max_snat 64 - Suc (Suc (length xs)))"
        using p by linarith
      have "xa - Suc 0 < max_snat 64 - Suc (Suc (length xs))"
        by (rule power_less_imp_less_exp[OF _ B]) simp
      thus "xa < max_snat 64" using p by linarith
    qed
    subgoal premises p for xa
    proof -
      have B: "(2::int) ^ (xa - Suc 0)
             < 2 ^ (max_snat 64 - Suc (Suc (length xs)))"
        using p by linarith
      have "xa - Suc 0 < max_snat 64 - Suc (Suc (length xs))"
        by (rule power_less_imp_less_exp[OF _ B]) simp
      thus "Suc (xa + n - i) < max_snat 64" using p by linarith
    qed
    done
qed

section \<open>The whole max-fold\<close>

text \<open>Invariant: \<open>1 \<le> k\<close>, \<open>i \<le> n\<close>, and there EXISTS a per-index witness function \<open>ri\<close> making
  BOTH the bit-length upper bound and the Kioustelidis domination hold for every ALREADY-PROCESSED
  index \<open>j < i\<close> against the CURRENT \<open>k\<close>. Because \<open>k\<close> only grows through the fold (each step is a
  \<open>max\<close>) and \<open>rlead + (k-1)*d\<close> is monotone non-decreasing in \<open>k\<close>, an established domination fact
  for an OLDER (smaller) \<open>k\<close> survives to any LATER (bigger) \<open>k\<close> -- so extending the witness with a
  fresh entry at the new index is all a loop step needs to do.\<close>

lemma kiou_dom_mono:
  fixes k k' d rlead :: nat
  assumes "k \<le> k'" and "1 \<le> k"
  shows "rlead + (k - 1) * d \<le> rlead + (k' - 1) * d"
proof -
  have "k - 1 \<le> k' - 1" using assms by linarith
  hence "(k - 1) * d \<le> (k' - 1) * d" by (rule mult_le_mono1)
  thus ?thesis by linarith
qed

definition kiou_maxfold_invar :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
"kiou_maxfold_invar xs n rlead st \<equiv>
  (let (i, k) = st in
    1 \<le> k \<and> i \<le> n \<and>
    (\<exists>ri. \<forall>j < i. \<bar>xs ! j\<bar> < 2 ^ (ri j) \<and> (xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ri j - 1) \<le> \<bar>xs ! j\<bar>)
                 \<and> (xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rlead + (k - 1) * (n - j))))"

text \<open>Extending the witness function \<open>ri\<close> with a fresh entry \<open>r\<close> at the new index \<open>i\<close> preserves the
  invariant's existential fact for \<open>i+1\<close> against the new \<open>k'\<close>. Proved once, outside the WHILET
  body.\<close>
lemma kiou_maxfold_invar_step:
  fixes xs :: gmp_poly and i n k k' r rlead :: nat and ri :: "nat \<Rightarrow> nat"
  assumes pre: "\<forall>j < i. \<bar>xs ! j\<bar> < 2 ^ (ri j) \<and> (xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ri j - 1) \<le> \<bar>xs ! j\<bar>)
                 \<and> (xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rlead + (k - 1) * (n - j))"
    and iltn: "i < n" and k1: "1 \<le> k"
    and post_ub: "\<bar>xs ! i\<bar> < 2 ^ r"
    and post_lb: "xs ! i \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>xs ! i\<bar>"
    and post_k: "k' = max k (if xs ! i < 0 then kiou_term r rlead (n - i) else 0)"
  shows "\<exists>ria. \<forall>j < i + 1. \<bar>xs ! j\<bar> < 2 ^ (ria j) \<and> (xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ria j - 1) \<le> \<bar>xs ! j\<bar>)
                 \<and> (xs ! j < 0 \<longrightarrow> ria j + 1 \<le> rlead + (k' - 1) * (n - j))"
proof (intro exI[of _ "ri(i := r)"] allI impI)
  fix j assume jlt: "j < i + 1"
  let ?ri' = "ri(i := r)"
  show "\<bar>xs ! j\<bar> < 2 ^ (?ri' j) \<and> (xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (?ri' j - 1) \<le> \<bar>xs ! j\<bar>)
          \<and> (xs ! j < 0 \<longrightarrow> ?ri' j + 1 \<le> rlead + (k' - 1) * (n - j))"
  proof (cases "j = i")
    case True
    have "xs ! i < 0 \<longrightarrow> r + 1 \<le> rlead + (k' - 1) * (n - i)"
    proof
      assume neg: "xs ! i < 0"
      have d1: "1 \<le> n - i" using iltn by simp
      have "kiou_term r rlead (n - i) \<le> k'" using post_k neg by (simp add: max_def)
      from kiou_term_dom[OF d1 this] show "r + 1 \<le> rlead + (k' - 1) * (n - i)" .
    qed
    thus ?thesis using True post_ub post_lb by simp
  next
    case False
    hence jlti: "j < i" using jlt by simp
    have kk': "k \<le> k'" using post_k by (simp add: max_def)
    have old: "\<bar>xs ! j\<bar> < 2 ^ (ri j) \<and> (xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ri j - 1) \<le> \<bar>xs ! j\<bar>)
             \<and> (xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rlead + (k - 1) * (n - j))"
      using pre jlti by blast
    have "xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rlead + (k' - 1) * (n - j)"
    proof
      assume "xs ! j < 0"
      hence "ri j + 1 \<le> rlead + (k - 1) * (n - j)" using old by simp
      thus "ri j + 1 \<le> rlead + (k' - 1) * (n - j)"
        using kiou_dom_mono[of k k' rlead "n - j"] kk' k1 by linarith
    qed
    thus ?thesis using old False by simp
  qed
qed

text \<open>The FINAL split-form residual left after \<open>clarsimp\<close> unfolds the body-postcondition's
  \<open>if xs!i<0 then ... else ...\<close> into two implications (one per sign) -- matched EXACTLY to
  that printed form (not the \<open>\<bar>xs!i\<bar>\<close>-abstracted one) so no further case-split/abs_if
  friction is needed at the call site.\<close>
lemma kiou_maxfold_step_final:
  fixes xs :: gmp_poly and i n k b r rlead :: nat
  assumes pre_ex: "\<forall>j < i. \<bar>xs ! j\<bar> < 2 ^ (ri j) \<and> (xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ri j - 1) \<le> \<bar>xs ! j\<bar>)
                 \<and> (xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rlead + (k - 1) * (n - j))"
    and iltn: "i < n" and k1: "1 \<le> k"
    and case_neg: "xs ! i < 0 \<longrightarrow>
        (- xs ! i < 2 ^ r \<and> 2 ^ (r - Suc 0) \<le> - xs ! i \<and> b = max k (kiou_term r rlead (n - i)))"
    and case_pos: "\<not> xs ! i < 0 \<longrightarrow>
        (xs ! i < 2 ^ r \<and> (xs ! i \<noteq> 0 \<longrightarrow> 2 ^ (r - Suc 0) \<le> xs ! i) \<and> b = k)"
  shows "kiou_maxfold_invar xs n rlead (Suc i, b) \<and> n - Suc i < n - i"
proof (cases "xs ! i < 0")
  case True
  hence post_ub: "\<bar>xs ! i\<bar> < 2 ^ r" and post_lb: "xs ! i \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>xs ! i\<bar>"
      and post_k: "b = max k (kiou_term r rlead (n - i))"
    using case_neg by auto
  have bk: "b = max k (if xs ! i < 0 then kiou_term r rlead (n - i) else 0)"
    using True post_k by simp
  have kb1: "1 \<le> b" using bk k1 by simp
  from kiou_maxfold_invar_step[OF pre_ex iltn k1 post_ub post_lb bk]
  show ?thesis using kb1 iltn by (simp add: kiou_maxfold_invar_def)
next
  case False
  hence post_ub: "\<bar>xs ! i\<bar> < 2 ^ r" and post_lb: "xs ! i \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>xs ! i\<bar>"
      and post_k: "b = k"
    using case_pos by auto
  have bk: "b = max k (if xs ! i < 0 then kiou_term r rlead (n - i) else 0)"
    using False post_k k1 by (simp add: max_def)
  have kb1: "1 \<le> b" using bk k1 by simp
  from kiou_maxfold_invar_step[OF pre_ex iltn k1 post_ub post_lb bk]
  show ?thesis using kb1 iltn by (simp add: kiou_maxfold_invar_def)
qed

text \<open>Stated at \<open>kiou_norm xs\<close>: the fold's guard IS that list's sign test, and its absolute
  values agree with \<open>xs\<close>'s. So the invariant @{const kiou_maxfold_invar} and its step lemma
  @{thm [source] kiou_maxfold_step_final} are instantiated at \<open>kiou_norm xs\<close> COMPLETELY UNCHANGED
  -- the sign-robustness costs no new fold reasoning.\<close>
lemma kiou_maxfold_monadic_correct:
  assumes n_len: "n < length xs" and hr: "kiou_headroom xs"
    and lneg: "lead_neg = (last xs < 0)"
  shows "kiou_maxfold_monadic xs n lead_neg rlead \<le>
    SPEC (\<lambda>k. 1 \<le> k \<and>
      (\<exists>ri. \<forall>j < n. \<bar>kiou_norm xs ! j\<bar> < 2 ^ (ri j)
                   \<and> (kiou_norm xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ri j - 1) \<le> \<bar>kiou_norm xs ! j\<bar>)
                   \<and> (kiou_norm xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rlead + (k - 1) * (n - j))))"
  unfolding kiou_maxfold_monadic_def kiou_maxfold_cond_monadic_def PR_CONST_def
  apply (refine_vcg WHILET_rule[where
      R = "measure (\<lambda>(i, k). n - i)" and
      I = "kiou_maxfold_invar (kiou_norm xs) n rlead"])
  subgoal by simp
  subgoal by (clarsimp simp: kiou_maxfold_invar_def)
  subgoal for st
    apply (clarsimp simp: kiou_maxfold_invar_def simp del: One_nat_def)
    subgoal premises pre for i k ri
    proof -
      have iln: "i < length xs" using pre n_len by simp
      have iltn: "i < n" and k1: "1 \<le> k" using pre by simp_all
      have pre_ex: "\<forall>j < i. \<bar>kiou_norm xs ! j\<bar> < 2 ^ (ri j)
                 \<and> (kiou_norm xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ri j - 1) \<le> \<bar>kiou_norm xs ! j\<bar>)
                 \<and> (kiou_norm xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rlead + (k - 1) * (n - j))"
        using pre by blast
      have body: "kiou_maxfold_body_mop_monadic xs n lead_neg rlead (i, k)
           \<le> SPEC (\<lambda>st. \<exists>k' r. st = (i + 1, k')
              \<and> \<bar>kiou_norm xs ! i\<bar> < 2 ^ r
              \<and> (kiou_norm xs ! i \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>kiou_norm xs ! i\<bar>)
              \<and> k' = max k (if kiou_norm xs ! i < 0 then kiou_term r rlead (n - i) else 0))"
        by (rule kiou_maxfold_body_mop_monadic_correct[OF n_len k1 iltn
              kiou_headroom_coeff[OF hr iln] kiou_headroom_lenb[OF hr] lneg])
      \<comment> \<open>Prove the FOLDED body-step first (its statement matches the apply-script, so the
          \<open>subgoal\<close>-terminating \<open>done\<close> refines cleanly), then bridge to \<open>?thesis\<close> — whose
          obligation has \<open>kiou_maxfold_invar\<close> unfolded by the outer \<open>clarsimp\<close>.\<close>
      have step: "kiou_maxfold_body_mop_monadic xs n lead_neg rlead (i, k)
             \<le> SPEC (\<lambda>s'. kiou_maxfold_invar (kiou_norm xs) n rlead s'
                          \<and> (s', (i, k)) \<in> measure (\<lambda>(i, k). n - i))"
        apply (rule order_trans[OF body])
        apply (clarsimp simp: pw_le_iff refine_pw_simps)
        subgoal premises pre for b r
          by (rule kiou_maxfold_step_final[where xs="kiou_norm xs" and i=i and n=n and k=k and b=b and r=r and rlead=rlead,
                OF pre_ex iltn k1 pre(1) pre(2)])
        done
      show ?thesis using step by (simp add: kiou_maxfold_invar_def)
    qed
    done
  \<comment> \<open>Loop exit splits into \<open>1 \<le> k\<close> (trivial from the invariant) and the \<open>\<exists>ri\<close> postcondition,
      which holds because \<open>\<not> i < n\<close> with \<open>i \<le> n\<close> forces \<open>i = n\<close>, so the invariant's per-index
      witness over \<open>j < i\<close> already covers all \<open>j < n\<close>.\<close>
  subgoal for st
    by (clarsimp simp: kiou_maxfold_invar_def kiou_maxfold_cond_monadic_def)
  subgoal premises pre for s a b
  proof -
    from pre(1) pre(3) have an: "a \<le> n"
      and ex: "\<exists>ri. \<forall>j<a. \<bar>kiou_norm xs ! j\<bar> < 2 ^ ri j
                    \<and> (kiou_norm xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ri j - 1) \<le> \<bar>kiou_norm xs ! j\<bar>)
                    \<and> (kiou_norm xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rlead + (b - 1) * (n - j))"
      by (auto simp: kiou_maxfold_invar_def)
    from pre(2) pre(3) an have "a = n" by (auto simp: kiou_maxfold_cond_monadic_def)
    with ex show "\<exists>ri. \<forall>j<n. \<bar>kiou_norm xs ! j\<bar> < 2 ^ ri j
                    \<and> (kiou_norm xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ri j - 1) \<le> \<bar>kiou_norm xs ! j\<bar>)
                    \<and> (kiou_norm xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rlead + (b - 1) * (n - j))" by simp
  qed
  done

section \<open>Top-level soundness: bridge to \<open>kiou_k_sound\<close>\<close>

text \<open>Assembly: the leading coefficient's bit-length \<open>rlead\<close> gives \<open>2^rlead \<le> 2*last xs\<close> (the
  \<open>an_lb\<close> hypothesis of @{thm [source] kiou_k_sound}) directly from the bitlen lower bound (the
  leading coefficient is positive and nonzero by the caller's normalisation precondition, so
  \<open>rlead \<ge> 1\<close> is forced and \<open>2^rlead = 2 \<cdot> 2^(rlead-1) \<le> 2 \<cdot> last xs\<close>). The fold then supplies
  \<open>ri_ub\<close>/\<open>kdom\<close> exactly, closing @{thm [source] kiou_k_sound}.\<close>

text \<open>The bound is taken on \<open>kiou_norm xs\<close>, which has a positive leading coefficient by
  construction and the same real roots, so the abstract @{thm [source] kiou_k_sound} applies to it
  directly, and @{thm [source] kiou_norm_root_iff} carries the conclusion back to \<open>xs\<close>. The
  executable kernel never materialises \<open>kiou_norm xs\<close>: it only compares each coefficient's sign
  with the leading one. \<open>rlead\<close> is the bit-length of \<open>\<bar>last xs\<bar>\<close>, which is why \<open>an_lb\<close> below holds
  for \<open>kiou_norm xs\<close> unchanged.\<close>
lemma kiou_bound_k_monadic_sound:
  fixes xs :: gmp_poly
  assumes len2: "2 \<le> length xs"
    and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs"
  shows "kiou_bound_k_monadic xs \<le>
    SPEC (\<lambda>k. \<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ k)"
proof -
  have xsne: "xs \<noteq> []" using len2 by auto
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  \<comment> \<open>the normalized list: positive leading coefficient, identical real roots\<close>
  have ys_len2: "2 \<le> length (kiou_norm xs)" using len2 by simp
  have ys_pos: "0 < last (kiou_norm xs)" by (rule kiou_norm_last_pos[OF xsne lastnz])
  have ys_lastnz: "last (kiou_norm xs) \<noteq> 0" by (rule kiou_norm_last_nz[OF xsne lastnz])
  have ys_last: "last (kiou_norm xs) = \<bar>last xs\<bar>" by (rule kiou_norm_last[OF xsne])
  show ?thesis
    unfolding kiou_bound_k_monadic_def poly_length_monadic_def
      poly_coeff_sgn_monadic_def poly_coeff_bitlen2_monadic_def Let_def
    \<comment> \<open>The kernel reads sign and bit-length straight off the borrowed slot via
        \<open>poly_coeff_sgn_monadic\<close>/\<open>poly_coeff_bitlen2_monadic\<close>. Both are plain ASSERT+RETURN /
        ASSERT+call wrappers with no fact \<open>refine_vcg\<close> discovers, so they need explicit unfolding.
        \<open>mpz_bitlen2_monadic_full\<close> (not the separate upper and lower facts) is essential: only one
        \<open>\<le> SPEC\<close> fact fires per producer, so splitting it loses one of the two bounds. A second
        \<open>refine_vcg\<close> call is needed because the first only unwinds the leading binds.\<close>
    apply (refine_vcg mpz_bitlen2_monadic_full kiou_maxfold_monadic_correct)
    using xsne apply simp
    using len2 lenb apply simp
    using len2 apply simp
    apply (refine_vcg mpz_bitlen2_monadic_full kiou_maxfold_monadic_correct)
    \<comment> \<open>Goal 1: \<open>mpz_bitlen2_monadic_full\<close>'s own precondition (\<open>|last xs| < 2^(max_snat-1)\<close>),
        discharged from \<open>kiou_headroom\<close> at the last index: its per-coefficient bound is at
        exponent \<open>max_snat - length xs - 2 \<le> max_snat - 1\<close> (headroom's own length bound), so
        \<open>power_increasing\<close> chains the two.\<close>
    subgoal
    proof -
      have le: "max_snat LENGTH(gmp_poly_len) - length xs - 2 \<le> max_snat LENGTH(gmp_poly_len) - 1"
        using kiou_headroom_lenb[OF hr] by simp
      have ilt: "length xs - 1 < length xs" using len2 xsne by simp
      have "\<bar>xs ! (length xs - 1)\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - length xs - 2)"
        using kiou_headroom_coeff[OF hr ilt] by simp
      also have "(2::int) ^ (max_snat LENGTH(gmp_poly_len) - length xs - 2)
                   \<le> 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)"
        using le by (rule power_increasing) simp
      finally show ?thesis by simp
    qed
    \<comment> \<open>Goal 2: the bit-length's own \<open>max_snat\<close> conjunct.\<close>
    subgoal premises p for rl using p by auto
    \<comment> \<open>Goal 3: \<open>length xs - 1 < length xs\<close>, trivial from \<open>len2\<close>.\<close>
    subgoal using len2 by simp
    \<comment> \<open>Goal 4: \<open>kiou_headroom\<close> is already an assumption.\<close>
    subgoal using hr by simp
    \<comment> \<open>Goal 5 (NEW, sign-robustness): @{thm [source] kiou_maxfold_monadic_correct}'s \<open>lead_neg\<close>
        side condition. The kernel's runtime test is \<open>sgn lc < 0\<close> on the leading coefficient,
        which \<open>simp\<close> has already reduced to \<open>xs ! (length xs - 1) < 0\<close>; that is \<open>last xs < 0\<close>.\<close>
    subgoal using xsne by (simp add: last_conv_nth)
    \<comment> \<open>Goal 6: assemble \<open>kiou_k_sound\<close> (at \<open>kiou_norm xs\<close>) from the leading bit-length \<open>rl\<close>
        (giving \<open>an_lb\<close>) and the fold's existential witness \<open>ri\<close> (giving \<open>ri_ub\<close>/\<open>kdom\<close>).\<close>
    subgoal premises p for rl k' x
    proof -
      have alc_eq: "\<bar>xs ! (length xs - 1)\<bar> = \<bar>last xs\<bar>"
        using xsne by (simp add: last_conv_nth)
      have rl_lb: "(2::int) ^ (rl - 1) \<le> \<bar>last xs\<bar>" using p alc_eq lastnz by auto
      have rl1: "1 \<le> rl"
      proof (rule ccontr)
        assume "\<not> 1 \<le> rl"
        hence "rl = 0" by simp
        hence "\<bar>last xs\<bar> < 1" using p alc_eq by auto
        thus False using lastnz by simp
      qed
      have an_lb: "(2::int) ^ rl \<le> 2 * last (kiou_norm xs)"
      proof -
        have "(2::int) ^ rl = 2 * 2 ^ (rl - 1)" using rl1 by (simp add: power_eq_if)
        also have "\<dots> \<le> 2 * \<bar>last xs\<bar>" using rl_lb by simp
        finally show ?thesis using ys_last by simp
      qed
      have k1: "1 \<le> k'" using p by auto
      have ex: "\<exists>ri. \<forall>j < length xs - 1. \<bar>kiou_norm xs ! j\<bar> < 2 ^ ri j
             \<and> (kiou_norm xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ri j - 1) \<le> \<bar>kiou_norm xs ! j\<bar>)
             \<and> (kiou_norm xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rl + (k' - 1) * (length xs - 1 - j))"
        using p by auto
      obtain ri where riall: "\<forall>j < length xs - 1. \<bar>kiou_norm xs ! j\<bar> < 2 ^ ri j
             \<and> (kiou_norm xs ! j \<noteq> 0 \<longrightarrow> 2 ^ (ri j - 1) \<le> \<bar>kiou_norm xs ! j\<bar>)
             \<and> (kiou_norm xs ! j < 0 \<longrightarrow> ri j + 1 \<le> rl + (k' - 1) * (length xs - 1 - j))"
        using ex by auto
      have ri_ub: "\<And>j. j < length (kiou_norm xs) - 1 \<Longrightarrow> \<bar>kiou_norm xs ! j\<bar> < 2 ^ ri j"
        using riall by simp
      have kdom: "\<And>j. j < length (kiou_norm xs) - 1 \<Longrightarrow> kiou_norm xs ! j < 0 \<Longrightarrow>
                     ri j + 1 \<le> rl + (k' - 1) * (length (kiou_norm xs) - 1 - j)"
        using riall by simp
      have root: "ripoly (Poly (kiou_norm xs)) x = 0"
        using p by (simp add: kiou_norm_root_iff)
      have xpos: "0 < x" using p by auto
      show "x < 2 ^ k'"
        by (rule kiou_k_sound[OF ys_len2 ys_lastnz ys_pos k1 an_lb ri_ub kdom xpos root])
    qed
    done
qed

end
