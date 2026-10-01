theory Scalar
imports Setup
begin

text \<open>Scalar GMP layer: bindings and wrappers over individual \<open>mpzb_assn\<close> values
  (allocation, copy, free, arithmetic ownership variants, sign and comparison).
  Main definitions: the \<open>mpz_\<close> scalar operations and the \<open>gmp_simps\<close>/\<open>gmp_sepref_rules\<close> stores.

  Ownership:
  - a value returned at \<open>mpzb_assn\<close> ownership must eventually be consumed by a later operation
    or freed;
  - destructive GMP variants may reuse one owned argument as the result;
  - a coefficient needed unchanged after an operation is copied first.\<close>

definition gmp_square_plus_ui_monadic :: "int \<Rightarrow> int \<Rightarrow> int nres" where
"gmp_square_plus_ui_monadic x y \<equiv> doN {
  a \<leftarrow> RETURN (mpz_from_int x);
  a \<leftarrow> RETURN (mpz_mul.aop_r12 a);
  RETURN (mpz_add_ui.aop_r1 a y)
}"

sepref_definition gmp_square_plus_ui_impl [llvm_code] is
  "uncurry gmp_square_plus_ui_monadic" ::
  "[\<lambda>(x, y). True]\<^sub>a gmp_slong_assn\<^sup>k *\<^sub>a gmp_ulong_assn\<^sup>k \<rightarrow> mpzb_assn"
  unfolding gmp_square_plus_ui_monadic_def
  by sepref

definition cmp_sign_rel :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"cmp_sign_rel a b r \<longleftrightarrow>
  ((r < 0) = (a < b) \<and> (r = 0) = (a = b) \<and> (0 < r) = (b < a))"

lemma cmp_sign_rel_sgn[simp]: "cmp_sign_rel a b (sgn (a - b))"
  unfolding cmp_sign_rel_def
  by (auto simp: sgn_if)

consts raw_mpz_cmp_si :: "mpz_t \<Rightarrow> gmp_long_t \<Rightarrow> gmp_int_t llM"

specification (raw_mpz_cmp_si)
  raw_mpz_cmp_si_rl[vcg_rules]: "llvm_htriple
    (mpz_assn a ai)
    (raw_mpz_cmp_si ai bi)
    (\<lambda>ri. EXS r. mpz_assn a ai \<and>* gmp_sint_assn r ri \<and>*
      \<up>(cmp_sign_rel a (sint bi) r))"
proof -
  interpret llvm_prim_mem_setup .
  show ?thesis
    apply (rule exI[where x =
      "\<lambda>ai bi. doM {
        a \<leftarrow> gmp_internals.mpz_ld_mpz ai;
        Mreturn (word_of_int (sgn (a - sint bi)))
      }"])
    unfolding cmp_sign_rel_def sint_rel_def sint.rel_def br_def pure_def
    supply [vcg_rules] = gmp_internals.mpz_ld_mpz[THEN gmp_internals.is_loaderD]
    apply vcg'
    apply (auto simp: sgn_if min_sint_def max_sint_def)
    done
qed

lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_cmp_si "''__gmpz_cmp_si''"]

definition mpz_sgn :: "int \<Rightarrow> int" where [simp]:
"mpz_sgn x \<equiv> sgn x"

sepref_register mpz_sgn

definition mpz_sgn_mop :: "int \<Rightarrow> int nres" where
"mpz_sgn_mop x \<equiv> RETURN (sgn x)"

sepref_register "PR_CONST mpz_sgn_mop" :: "int \<Rightarrow> int nres"

definition cmp_result_sgn_monadic :: "int \<Rightarrow> int nres" where
"cmp_result_sgn_monadic r \<equiv>
  (if r = 0 then RETURN 0 else if r < 0 then RETURN (-1) else RETURN 1)"

sepref_register cmp_result_sgn_monadic

definition [llvm_code, llvm_inline]: "cmp_result_sgn_impl r \<equiv> doM {
  is_zero \<leftarrow> ll_cmp (r = (0::gmp_int_t));
  if to_bool is_zero then Mreturn (0::gmp_int_t)
  else doM {
    is_neg \<leftarrow> ll_cmp (r <s (0::gmp_int_t));
    if to_bool is_neg then Mreturn (-1::gmp_int_t) else Mreturn (1::gmp_int_t)
  }
}"

lemma cmp_sign_rel_sgn_eq:
  "cmp_sign_rel x 0 r \<Longrightarrow> sgn r = sgn x"
  unfolding cmp_sign_rel_def
  by (auto simp: sgn_if)

lemma cmp_sign_rel_sgn_diff_eq:
  "cmp_sign_rel x y r \<Longrightarrow> sgn r = sgn (x - y)"
  unfolding cmp_sign_rel_def
  by (auto simp: sgn_if)

lemma cmp_result_sgn_monadic_eq[simp]:
  fixes r :: int
  shows "(if r = 0 then 0 else if r < 0 then -1 else 1) = sgn r"
proof (cases "r = 0")
  case True
  then show ?thesis by (simp add: sgn_0)
next
  case False
  then show ?thesis
  proof (cases "r < 0")
    case True
    then show ?thesis by (simp add: sgn_neg)
  next
    case False
    then have "0 < r" using \<open>r \<noteq> 0\<close> by linarith
    then show ?thesis by (simp add: sgn_pos)
  qed
qed

lemma cmp_result_sgn_impl_rule[vcg_rules]:
  "llvm_htriple
    (gmp_sint_assn r ri)
    (cmp_result_sgn_impl ri)
    (\<lambda>si. gmp_sint_assn (sgn r) si)"
  unfolding cmp_result_sgn_impl_def ll_cmp_def
  apply vcg'
  apply (all \<open>(vcg')?\<close>)
  apply (auto simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps POSTCOND_def STATE_def EXTRACT_def
    sint_rel_def sint.rel_def br_def pure_def sgn_if min_sint_def max_sint_def
    word_sless_alt word_eq_iff_signed wpa_return sint_word_ariths)
  apply (fact Defer_Slot.remove_slot)
  done

definition [llvm_code, llvm_inline]: "mpzb_sgn_impl a \<equiv> doM {
  mpzb_open a;
  r \<leftarrow> raw_mpz_cmp_si a (0::gmp_long_t);
  mpzb_close a;
  cmp_result_sgn_impl r
}"

lemma mpzb_sgn_impl_rule[vcg_rules]:
  "llvm_htriple
    (mpzb_assn x xi)
    (mpzb_sgn_impl xi)
    (\<lambda>ri. mpzb_assn x xi \<and>* gmp_sint_assn (sgn x) ri)"
  unfolding mpzb_sgn_impl_def
  apply vcg'
  apply (clarsimp simp: ENTAILS_def entails_def sep_conj_commute
    cmp_sign_rel_sgn_eq)
  apply (fact Defer_Slot.remove_slot)
  done

lemma mpzb_sgn_impl_hnr[sepref_fr_rules]:
  "(mpzb_sgn_impl, RETURN o PR_CONST mpz_sgn)
    \<in> mpzb_assn\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  apply sepref_to_hoare
  unfolding mpz_sgn_def
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sint_rel_def pure_def)
  done

lemma mpzb_sgn_impl_mop_hnr[sepref_fr_rules]:
  "(mpzb_sgn_impl, PR_CONST mpz_sgn_mop)
    \<in> mpzb_assn\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  apply sepref_to_hoare
  unfolding mpz_sgn_mop_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sint_rel_def pure_def)
  done

definition mpz_cmp_si_sgn_monadic :: "int \<Rightarrow> int \<Rightarrow> int nres" where
"mpz_cmp_si_sgn_monadic x y \<equiv> RETURN (sgn (x - y))"

sepref_register "PR_CONST mpz_cmp_si_sgn_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]: "mpzb_cmp_si_sgn_impl a b \<equiv> doM {
  mpzb_open a;
  r \<leftarrow> raw_mpz_cmp_si a b;
  mpzb_close a;
  cmp_result_sgn_impl r
}"

lemma mpzb_cmp_si_sgn_impl_rule[vcg_rules]:
  "llvm_htriple
    (mpzb_assn x xi)
    (mpzb_cmp_si_sgn_impl xi yi)
    (\<lambda>ri. mpzb_assn x xi \<and>* gmp_sint_assn (sgn (x - sint yi)) ri)"
  unfolding mpzb_cmp_si_sgn_impl_def
  apply vcg'
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    sep_conj_ac cmp_sign_rel_sgn_diff_eq)
  apply (fact Defer_Slot.remove_slot)
  done

lemma mpzb_cmp_si_sgn_impl_hnr[sepref_fr_rules]:
  "(uncurry mpzb_cmp_si_sgn_impl,
    uncurry (PR_CONST mpz_cmp_si_sgn_monadic)) \<in>
    mpzb_assn\<^sup>k *\<^sub>a gmp_slong_assn\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  apply sepref_to_hoare
  unfolding mpz_cmp_si_sgn_monadic_def PR_CONST_def
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sint_rel_def sint.rel_def br_def pure_def)
  done

text \<open>Native two-\<open>mpz\<close> comparison: bind \<open>__gmpz_cmp\<close> as a CONSERVATIVE
  EXTENSION (\<open>specification\<close>; the spec is the sign contract @{const cmp_sign_rel} \<open>a c r\<close>, which is
  TRUE of the real C function for EVERY input — GMP's \<open>__gmpz_cmp\<close> returns a value whose sign is
  that of \<open>a - c\<close>, magnitude unspecified). Direct sibling of @{const raw_mpz_cmp_si}; BOTH inputs
  are BORROWED (KEPT). Callers that need only the trichotomy (\<open>newton_window_cmp_monadic\<close>) read the sign via
  @{const cmp_result_sgn_impl}, which avoids subtracting into a fresh scratch and taking its
  \<open>sgn\<close> (one allocation and one free per compare).\<close>
consts raw_mpz_cmp :: "mpz_t \<Rightarrow> mpz_t \<Rightarrow> gmp_int_t llM"

specification (raw_mpz_cmp)
  raw_mpz_cmp_rl[vcg_rules]: "llvm_htriple
    (mpz_assn a ai \<and>* mpz_assn c ci)
    (raw_mpz_cmp ai ci)
    (\<lambda>ri. EXS r. mpz_assn a ai \<and>* mpz_assn c ci \<and>* gmp_sint_assn r ri \<and>*
      \<up>(cmp_sign_rel a c r))"
proof -
  interpret llvm_prim_mem_setup .
  show ?thesis
    apply (rule exI[where x =
      "\<lambda>ai ci. doM {
        a \<leftarrow> gmp_internals.mpz_ld_mpz ai;
        c \<leftarrow> gmp_internals.mpz_ld_mpz ci;
        Mreturn (word_of_int (sgn (a - c)))
      }"])
    unfolding cmp_sign_rel_def sint_rel_def sint.rel_def br_def pure_def
    supply [vcg_rules] = gmp_internals.mpz_ld_mpz[THEN gmp_internals.is_loaderD]
    apply vcg'
    apply (auto simp: sgn_if min_sint_def max_sint_def)
    done
qed

lemmas [llvm_code_raw] = LLVM_EXTERNALI[of raw_mpz_cmp "''__gmpz_cmp''"]

definition mpz_cmp_sgn_monadic :: "int \<Rightarrow> int \<Rightarrow> int nres" where
"mpz_cmp_sgn_monadic a c \<equiv> RETURN (sgn (a - c))"

sepref_register "PR_CONST mpz_cmp_sgn_monadic" :: "int \<Rightarrow> int \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]: "mpzb_cmp_sgn_impl a c \<equiv> doM {
  mpzb_open a;
  mpzb_open c;
  r \<leftarrow> raw_mpz_cmp a c;
  mpzb_close c;
  mpzb_close a;
  cmp_result_sgn_impl r
}"

lemma mpzb_cmp_sgn_impl_rule[vcg_rules]:
  "llvm_htriple
    (mpzb_assn x xi \<and>* mpzb_assn y yi)
    (mpzb_cmp_sgn_impl xi yi)
    (\<lambda>ri. mpzb_assn x xi \<and>* mpzb_assn y yi \<and>* gmp_sint_assn (sgn (x - y)) ri)"
  unfolding mpzb_cmp_sgn_impl_def
  apply vcg'
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    sep_conj_ac cmp_sign_rel_sgn_diff_eq)
  apply (fact Defer_Slot.remove_slot)
  done

lemma mpzb_cmp_sgn_impl_hnr[sepref_fr_rules]:
  "(uncurry mpzb_cmp_sgn_impl,
    uncurry (PR_CONST mpz_cmp_sgn_monadic)) \<in>
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  apply sepref_to_hoare
  unfolding mpz_cmp_sgn_monadic_def PR_CONST_def
  apply vcg
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pred_lift_extract_simps sint_rel_def sint.rel_def br_def pure_def)
  done

definition mpzb_discard_monadic :: "int \<Rightarrow> unit nres" where
"mpzb_discard_monadic _ \<equiv> RETURN ()"

sepref_register "PR_CONST mpzb_discard_monadic" :: "int \<Rightarrow> unit nres"

definition [llvm_code, llvm_inline]:
  "mpzb_discard_impl p \<equiv> mpzb_free p"

lemma mpzb_discard_impl_hnr[sepref_fr_rules]:
  "(mpzb_discard_impl, PR_CONST mpzb_discard_monadic)
    \<in> mpzb_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  apply sepref_to_hoare
  unfolding mpzb_discard_impl_def mpzb_discard_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  done

definition mpz_add_monadic :: "int \<Rightarrow> int \<Rightarrow> int nres" where
"mpz_add_monadic r a \<equiv> RETURN (r + a)"

sepref_register "PR_CONST mpz_add_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]:
  "mpzb_add_impl r a \<equiv> doM {
    mpzb_open r;
    mpzb_open a;
    raw_mpz_add r r a;
    mpzb_close a;
    mpzb_close r;
    Mreturn r
  }"

lemma mpzb_add_impl_rule[vcg_rules]:
  "llvm_htriple
    (mpzb_assn r ri \<and>* mpzb_assn a ai)
    (mpzb_add_impl ri ai)
    (\<lambda>ri'. mpzb_assn (r + a) ri' \<and>* mpzb_assn a ai \<and>* \<up>(ri' = ri))"
  unfolding mpzb_add_impl_def
  apply vcg'
  apply (clarsimp simp: ENTAILS_def entails_def sep_algebra_simps
    pure_unit_rel_eq_empty)
  apply (fact Defer_Slot.remove_slot)
  done

lemma mpzb_add_impl_hnr[sepref_fr_rules]:
  "(uncurry mpzb_add_impl,
    uncurry (PR_CONST mpz_add_monadic)) \<in>
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  apply sepref_to_hoare
  unfolding mpz_add_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  done

consts raw_mpz_addmul :: "mpz_t \<Rightarrow> mpz_t \<Rightarrow> mpz_t \<Rightarrow> unit llM"

specification (raw_mpz_addmul)
  raw_mpz_addmul_rl[vcg_rules]: "llvm_htriple
    (mpz_assn r ri \<and>* mpz_assn a ai \<and>* mpz_assn b bi)
    (raw_mpz_addmul ri ai bi)
    (\<lambda>_. mpz_assn (r + a * b) ri \<and>* mpz_assn a ai \<and>* mpz_assn b bi)"
proof -
  interpret llvm_prim_mem_setup .
  show ?thesis
    apply (rule exI[where x =
      "\<lambda>ri ai bi. doM {
        r \<leftarrow> gmp_internals.mpz_ld_mpz ri;
        a \<leftarrow> gmp_internals.mpz_ld_mpz ai;
        b \<leftarrow> gmp_internals.mpz_ld_mpz bi;
        gmp_internals.mpz_st_mpz (r + a * b) ri
      }"])
    supply [vcg_rules] =
      gmp_internals.mpz_ld_mpz[THEN gmp_internals.is_loaderD]
      gmp_internals.mpz_st_mpz[THEN gmp_internals.is_storerD]
    apply vcg
    done
qed

lemmas [llvm_code_raw] =
  LLVM_EXTERNALI[of raw_mpz_addmul "''__gmpz_addmul''"]

definition mpz_addmul_monadic :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int nres" where
"mpz_addmul_monadic r a b \<equiv> RETURN (r + a * b)"

sepref_register "PR_CONST mpz_addmul_monadic"
  :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int nres"

definition [llvm_code, llvm_inline]:
  "mpzb_addmul_impl r a b \<equiv> doM {
    mpzb_open r;
    mpzb_open a;
    mpzb_open b;
    raw_mpz_addmul r a b;
    mpzb_close b;
    mpzb_close a;
    mpzb_close r;
    Mreturn r
  }"

lemma mpzb_addmul_impl_rule[vcg_rules]:
  "llvm_htriple
    (mpzb_assn r ri \<and>* mpzb_assn a ai \<and>* mpzb_assn b bi)
    (mpzb_addmul_impl ri ai bi)
    (\<lambda>ri'. mpzb_assn (r + a * b) ri' \<and>* mpzb_assn a ai \<and>*
      mpzb_assn b bi \<and>* \<up>(ri' = ri))"
  unfolding mpzb_addmul_impl_def
  apply vcg'
  done

lemma mpzb_addmul_impl_hnr[sepref_fr_rules]:
  "(uncurry2 mpzb_addmul_impl,
    uncurry2 (PR_CONST mpz_addmul_monadic)) \<in>
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a mpzb_assn"
  apply sepref_to_hoare
  unfolding mpz_addmul_monadic_def PR_CONST_def
  apply (clarsimp simp: refine_pw_simps)
  apply vcg
  done

definition mpz_divexact_pre :: "int \<Rightarrow> int \<Rightarrow> bool" where
"mpz_divexact_pre a b \<equiv> b \<noteq> 0 \<and> b dvd a"

global_interpretation mpz_gcd:
  mpz_binary_spec_mm_axiom Orderings.top gcd
    unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_gcd''"
  defines raw_mpz_gcd = mpz_gcd.op
  by (rule mpz_internal_realize)+

global_interpretation mpz_divexact:
  mpz_binary_spec_mm_axiom mpz_divexact_pre "(div)"
    unit_assn "\<lambda>_ _. ()" "\<lambda>_ _. Mreturn ()" "''__gmpz_divexact''"
  defines raw_mpz_divexact = mpz_divexact.op
  by (rule mpz_internal_realize)+

section \<open>mpz comparison and max-selection\<close>

text \<open>Selection primitives. The HNR is \<open>mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn\<close>: both arguments are
  consumed and one value is returned (suffix \<open>_sel\<close>; a \<open>_keep\<close> suffix would mean the argument is
  returned rather than consumed).\<close>

definition mpz_cmp_monadic :: "int \<Rightarrow> int \<Rightarrow> int nres" where
"mpz_cmp_monadic a c \<equiv> doN {
  z \<leftarrow> RETURN (mpz_from_int 0);
  d \<leftarrow> (PR_CONST mpz_sub.amop) z a c;
  s \<leftarrow> (PR_CONST mpz_sgn_mop) d;
  (PR_CONST mpzb_discard_monadic) d;
  RETURN s
}"

lemma mpz_cmp_monadic_correct: "mpz_cmp_monadic a c \<le> RETURN (sgn (a - c))"
  unfolding mpz_cmp_monadic_def mpz_sgn_mop_def mpzb_discard_monadic_def
    mpz_from_int_def PR_CONST_def mpz_sub.amop_def mpz_sub.aop_def
  by (refine_vcg) auto

sepref_register "PR_CONST mpz_cmp_monadic" :: "int \<Rightarrow> int \<Rightarrow> int nres"

sepref_definition mpz_cmp_impl [llvm_inline] is
  "uncurry mpz_cmp_monadic" :: "mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  unfolding mpz_cmp_monadic_def
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma mpz_cmp_impl_hnr[sepref_fr_rules]:
  "(uncurry mpz_cmp_impl, uncurry (PR_CONST mpz_cmp_monadic)) \<in>
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  using mpz_cmp_impl.refine by (simp add: PR_CONST_def)

definition mpz_max_sel_monadic :: "int \<Rightarrow> int \<Rightarrow> int nres" where
"mpz_max_sel_monadic m v \<equiv> doN {
  s \<leftarrow> (PR_CONST mpz_cmp_monadic) m v;
  if s \<ge> 0 then doN { (PR_CONST mpzb_discard_monadic) v; RETURN m }
  else doN { (PR_CONST mpzb_discard_monadic) m; RETURN v }
}"

lemma mpz_max_sel_monadic_correct: "mpz_max_sel_monadic m v \<le> RETURN (max m v)"
  unfolding mpz_max_sel_monadic_def mpzb_discard_monadic_def PR_CONST_def
  apply (rule order_trans[OF bind_mono(1)[OF mpz_cmp_monadic_correct order_refl]])
  apply (auto simp: refine_pw_simps pw_le_iff max_def sgn_if split: if_splits)
  done

sepref_register "PR_CONST mpz_max_sel_monadic" :: "int \<Rightarrow> int \<Rightarrow> int nres"

sepref_definition mpz_max_sel_impl [llvm_inline] is
  "uncurry mpz_max_sel_monadic" :: "mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  unfolding mpz_max_sel_monadic_def
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma mpz_max_sel_impl_hnr[sepref_fr_rules]:
  "(uncurry mpz_max_sel_impl, uncurry (PR_CONST mpz_max_sel_monadic)) \<in>
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  using mpz_max_sel_impl.refine by (simp add: PR_CONST_def)

end
