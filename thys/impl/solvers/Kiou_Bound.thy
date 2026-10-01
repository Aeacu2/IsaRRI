theory Kiou_Bound
  imports
    "IsaRRI_LLVM.Poly_Ops"
    "IsaRRI_Spec.Kiou_Bound_Spec"
begin

text \<open>The tight Kioustelidis positive-root bound (msolve's \<open>bound_roots\<close>), verified
  GMP path: from a poly with positive leading coefficient it computes an exponent \<open>k\<close>
  with every positive real root strictly below \<open>2 ^ k\<close>.
  Layer: SEPREF.
  Main exports: \<open>kiou_bound_k_monadic\<close> / \<open>_impl\<close> (the bound), \<open>kiou_maxfold_monadic\<close>
  (the borrowed-poly max-fold it runs on). Soundness: \<open>dsc_gmp_root_bound_k_sound\<close>
  (\<open>refine/root_bound/\<close>).

  Derivation:
  From a gmp_poly (= int list) with POSITIVE leading coefficient it computes a
  natural-number exponent k such that every POSITIVE real root of Poly xs is
  strictly below 2^k:
  n = degree p;  rlead = bitlen(a_n);
  k = max(1, max_{i: a_i<0} kiou_term(bitlen|a_i|, rlead, n-i))
  where kiou_term ri rlead d = 1 if ri+1<=rlead, else 1 + ceildiv(ri+1-rlead, d)
  (Kiou_Bound_Spec.thy). Unlike the Cauchy kernel, every
  per-coefficient contribution here is MACHINE-WORD arithmetic (nat bit-lengths
  and a small ceildiv) -- no GMP bigint division at all; the only GMP ops are
  the sign test, abs, and mpz_bitlen2 (mpz_sizeinbase) on a transient per-coeff
  copy. The polynomial xs is read BY INDEX and stays BORROWED (never cloned or
  consumed): the loop state is a pure (index, running-max) machine-word pair, so
  nothing GMP is carried in the state and no whole-poly allocation happens.
  PRECONDITION: 0 < last xs (positive leading coefficient). The all-roots
  caller normalizes (negates the whole poly once if needed -- roots are
  unaffected) before calling both this kernel and the solver, so this
  precondition is always established at the top of the pipeline, not
  per-call.\<close>

section \<open>Per-coefficient max-fold: \<open>k = max(1, max_i kiou_term(...))\<close>\<close>

text \<open>The fold reads each coefficient of the borrowed polynomial \<open>xs\<close> by index
  (\<open>poly_copy_coeff_monadic\<close>: a transient owned copy that is made absolute, measured and freed
  inside the loop body), so the polynomial is never consumed. The mutable loop state is therefore
  a pair of machine words \<open>(i, k)\<close> (current coefficient index; running maximum exponent), with no
  owned GMP handle in it: a \<open>gmp_poly_assn\<^sup>k\<close> parameter closed over the \<open>WHILET\<close> plus a pure-word
  state, which is the shape Sepref's translation phase handles.

  \<open>n\<close> (the degree) and \<open>rlead\<close> (bit-length of the leading coefficient) are fixed parameters. The
  Kioustelidis term depends on \<open>d = n-i\<close>, the coefficient's distance from the leading term.\<close>

text \<open>The per-coefficient accumulator update, isolated into its own Sepref op: the machine-word
  arithmetic (the ceiling division and its additions, with their no-overflow \<open>ASSERT\<close>s) and the
  sign select are here, so the loop body is GMP ops, one call and a tuple return. Given the flag
  \<open>opp\<close> (does the coefficient oppose the leading coefficient's sign?), its bit-length \<open>ri\<close>, the
  leading bit-length \<open>rlead\<close>, the distance \<open>d = n-i > 0\<close>, and the running maximum \<open>k\<close>, it returns
  \<open>max k (if opp then kiou_term ri rlead d else 0)\<close>. Taking the opposition flag rather than the
  coefficient's sign makes the kernel correct for a leading coefficient of either sign.\<close>

definition kiou_update_mop :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres" where
"kiou_update_mop opp ri rlead d k \<equiv> doN {
  ASSERT (0 < d);
  ASSERT (ri + 1 < max_snat LENGTH(gmp_poly_len));
  a \<leftarrow> RETURN (ri + 1);
  if opp then doN {
    if rlead < a then doN {
      ASSERT (a - rlead + d < max_snat LENGTH(gmp_poly_len));
      q \<leftarrow> RETURN ((a - rlead + d - 1) div d);
      ASSERT (q + 1 < max_snat LENGTH(gmp_poly_len));
      kt \<leftarrow> RETURN (q + 1);
      if k < kt then RETURN kt else RETURN k
    } else RETURN k
  } else RETURN k
}"

sepref_register "PR_CONST kiou_update_mop"
  :: "bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres"

sepref_definition kiou_update_impl [llvm_inline] is
  "uncurry4 kiou_update_mop" ::
  "bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding kiou_update_mop_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const gmp_int_t)?
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

lemma kiou_update_impl_hnr[sepref_fr_rules]:
  "(uncurry4 kiou_update_impl, uncurry4 (PR_CONST kiou_update_mop)) \<in>
    bool1_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using kiou_update_impl.refine by (simp add: PR_CONST_def)

abbreviation kiou_maxfold_state_assn where
  "kiou_maxfold_state_assn \<equiv>
    snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a snat_assn' TYPE(gmp_poly_len)"

definition kiou_maxfold_cond_monadic :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
"kiou_maxfold_cond_monadic n st \<equiv> (let (i, k) = st in i < n)"

sepref_register "PR_CONST kiou_maxfold_cond_monadic" :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"

sepref_definition kiou_maxfold_cond_impl [llvm_inline] is
  "uncurry (RETURN oo kiou_maxfold_cond_monadic)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a kiou_maxfold_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding kiou_maxfold_cond_monadic_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma kiou_maxfold_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry kiou_maxfold_cond_impl,
    uncurry (RETURN oo (PR_CONST kiou_maxfold_cond_monadic))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a kiou_maxfold_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using kiou_maxfold_cond_impl.refine by (simp add: PR_CONST_def)

text \<open>\<open>lead_neg\<close> says the LEADING coefficient is negative. A coefficient OPPOSES the leading
  one exactly when \<open>0 < s\<close> (if \<open>lead_neg\<close>) or \<open>s < 0\<close> (otherwise) -- two comparisons against
  zero, no arithmetic on \<open>s\<close>, hence no sint-overflow obligation. The sign \<open>s\<close> was already read
  on every iteration, so sign-robustness is free.\<close>
definition kiou_maxfold_body_mop_monadic ::
  "gmp_poly \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) nres" where
"kiou_maxfold_body_mop_monadic xs n lead_neg rlead st \<equiv> doN {
  let (i, k) = st;
  ASSERT (i < n);
  ASSERT (i < length xs);
  \<comment> \<open>Borrow-read the sign and bit-length directly (@{const poly_coeff_sgn_monadic},
    @{const poly_coeff_bitlen2_monadic}, Array.thy) instead of deep-copying \<open>xs!i\<close> and
    computing a redundant absolute value: @{const mpz_bitlen2_monadic}'s spec is already
    stated on \<open>|m|\<close>, so the sign is ignored regardless.\<close>
  s \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs i;
  ri \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs i;
  ASSERT (ri < max_snat LENGTH(gmp_poly_len));
  ri2 \<leftarrow> RETURN (op_unat_snat_conv ri);
  d \<leftarrow> RETURN (n - i);
  opp \<leftarrow> RETURN (if lead_neg then 0 < s else s < 0);
  k' \<leftarrow> (PR_CONST kiou_update_mop) opp ri2 rlead d k;
  ASSERT (i + 1 < max_snat LENGTH(gmp_poly_len));
  RETURN (i + 1, k')
}"

sepref_register "PR_CONST kiou_maxfold_body_mop_monadic"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) nres"

sepref_definition kiou_maxfold_body_impl [llvm_inline] is
  "uncurry4 kiou_maxfold_body_mop_monadic" ::
  "[\<lambda>((((xs, n), lead_neg), rlead), i, k). n < length xs]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a kiou_maxfold_state_assn\<^sup>d
    \<rightarrow> kiou_maxfold_state_assn"
  unfolding kiou_maxfold_body_mop_monadic_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  apply (annot_sint_const gmp_int_t)?
  supply [sepref_fr_rules] = kiou_update_impl_hnr
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

lemma kiou_maxfold_body_impl_hnr[sepref_fr_rules]:
  "(uncurry4 kiou_maxfold_body_impl, uncurry4 (PR_CONST kiou_maxfold_body_mop_monadic)) \<in>
    [\<lambda>((((xs, n), lead_neg), rlead), i, k). n < length xs]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a kiou_maxfold_state_assn\<^sup>d
      \<rightarrow> kiou_maxfold_state_assn"
  using kiou_maxfold_body_impl.refine by (simp add: PR_CONST_def)

definition kiou_maxfold_monadic :: "gmp_poly \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat nres" where
"kiou_maxfold_monadic xs n lead_neg rlead \<equiv> doN {
  (_, k) \<leftarrow> WHILET
    (\<lambda>st. (PR_CONST kiou_maxfold_cond_monadic) n st)
    (\<lambda>st. (PR_CONST kiou_maxfold_body_mop_monadic) xs n lead_neg rlead st)
    (0, 1);
  RETURN k
}"

sepref_register "PR_CONST kiou_maxfold_monadic" :: "gmp_poly \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat nres"

sepref_definition kiou_maxfold_impl [llvm_code] is
  "uncurry3 kiou_maxfold_monadic" ::
  "[\<lambda>(((xs, n), lead_neg), rlead). n < length xs]\<^sub>a
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding kiou_maxfold_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_fr_rules] =
    kiou_maxfold_cond_impl_hnr kiou_maxfold_body_impl_hnr
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

lemma kiou_maxfold_impl_hnr[sepref_fr_rules]:
  "(uncurry3 kiou_maxfold_impl, uncurry3 (PR_CONST kiou_maxfold_monadic)) \<in>
    [\<lambda>(((xs, n), lead_neg), rlead). n < length xs]\<^sub>a
      gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using kiou_maxfold_impl.refine by (simp add: PR_CONST_def)

section \<open>Top-level Kioustelidis positive-root exponent\<close>

text \<open>Assembly, with no whole-polynomial allocation (\<open>xs\<close> stays borrowed throughout): read the
  leading coefficient's (index \<open>n = len-1\<close>) sign and bit-length directly off the array slot, then
  fold over indices \<open>0 \<dots> n-1\<close> seeding \<open>k = 1\<close> (a valid bound seed for every degree, including
  the constant case \<open>n = 0\<close> where the loop does not run). \<open>rlead\<close> is taken from \<open>\<bar>lc\<bar>\<close>, and
  \<open>poly_coeff_bitlen2_monadic\<close> and \<open>poly_coeff_sgn_monadic\<close> both read the borrowed slot, so no
  temporary copies are needed.\<close>

definition kiou_bound_k_monadic :: "gmp_poly \<Rightarrow> nat nres" where
"kiou_bound_k_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  ASSERT (1 \<le> len \<and> len + 1 < max_snat LENGTH(gmp_poly_len));
  let n = len - 1;
  ASSERT (n < length xs);
  slead \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs n;
  lead_neg \<leftarrow> RETURN (slead < 0);
  rlead \<leftarrow> (PR_CONST poly_coeff_bitlen2_monadic) xs n;
  ASSERT (rlead < max_snat LENGTH(gmp_poly_len));
  rlead2 \<leftarrow> RETURN (op_unat_snat_conv rlead);
  k \<leftarrow> (PR_CONST kiou_maxfold_monadic) xs n lead_neg rlead2;
  RETURN k
}"

sepref_register "PR_CONST kiou_bound_k_monadic" :: "gmp_poly \<Rightarrow> nat nres"

sepref_definition kiou_bound_k_impl [llvm_code] is
  "kiou_bound_k_monadic" ::
  "[\<lambda>xs. 1 \<le> length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  unfolding kiou_bound_k_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  \<comment> \<open>the \<open>lead_neg \<leftarrow> RETURN (slead < 0)\<close> sign test introduces an \<open>int\<close> literal, which the
    id phase cannot type without this (as in \<open>kiou_maxfold_body_impl\<close>); omitting it surfaces
    as \<open>Failed to apply initial proof method\<close>\<close>
  apply (annot_sint_const gmp_int_t)?
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  by sepref

lemma kiou_bound_k_impl_hnr[sepref_fr_rules]:
  "(kiou_bound_k_impl, PR_CONST kiou_bound_k_monadic) \<in>
    [\<lambda>xs. 1 \<le> length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> snat_assn' TYPE(gmp_poly_len)"
  using kiou_bound_k_impl.refine
  by (simp add: PR_CONST_def)

text \<open>The box endpoint \<open>2^k\<close> (a single GMP shift) and the wiring of this exponent into
  a verified solver are done downstream (the split all-roots wrapper), which imports
  both this theory and the carried-ET solver. This leaf theory delivers the exponent
  kernel @{const kiou_bound_k_monadic} + its HNR; the refinement bridge to
  \<open>kiou_k_sound\<close> (soundness: every positive real root \<open>< 2^k\<close>) is proved in
  \<open>Kiou_Bound_Refine.thy\<close>.\<close>

end
