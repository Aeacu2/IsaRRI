theory Newton
  imports Count Window_Mono
begin

text \<open>The shared Newton window-probe subsystem: the policy gate, the \<open>gmp_poly option\<close> infrastructure,
  the local Newton \<open>\<lambda>\<close> and snap probes, the owned-mpz comparison/min/max helpers, the window-try kernel,
  and the cascade-bail side and window-choice ops. Every solver that needs a Newton probe (the Newton,
  bail and hybrid solvers) depends on this one module.\<close>

text \<open>\<^bold>\<open>Freeing an owned window option.\<close> Sepref's frame inference must free the option values a
  branch does not return. The framework composes \<open>mk_free_option\<close> (the \<open>dflt_option_private\<close>
  locale supplies it) with \<open>mk_free_pair\<close>, leaving one gap: \<open>MK_FREE\<close> for @{const gmp_poly_assn}.
  The array bindings derive theirs from a \<open>RETURN o _\<close> destructor; @{const poly_free_monadic} is a
  genuine \<open>nres\<close> op (it walks the option slots), so we replay the same derivation by hand from its
  HNR — an owned poly's post-state is \<open>invalid_assn\<close>, which is pure and hence entails \<open>\<box>\<close>.\<close>
lemma gmp_poly_assn_free[sepref_frame_free_rules]:
  "MK_FREE gmp_poly_assn poly_free_impl"
proof -
  note [vcg_rules] = poly_free_impl_hnr[to_hnr, THEN hn_refineD,
      unfolded hn_ctxt_def invalid_assn_def pure_def, simplified]
  show ?thesis by rule vcg
qed

definition newton_pol_emin :: nat where "newton_pol_emin = 3"
definition newton_pol_ecap :: nat where "newton_pol_ecap = 8"
definition newton_pol_sig_thresh :: nat where "newton_pol_sig_thresh = 32"
text \<open>Split delay. The \<open>deg\<close> parameter is unused on purpose: it is where a degree-dependent delay
  \<open>s \<ge> split_delay deg \<approx> log\<^sub>2 deg\<close> (Kobel, Rouillier and Sagraloff, \<section>3.1) would enter; the delay is the
  constant \<open>newton_pol_sig_thresh\<close>. Removing the parameter would change the definition of \<open>newton_pol_gate\<close>,
  which the keystone depends on through \<open>newdsc_pol\<close>.\<close>
definition newton_pol_split_delay :: "nat \<Rightarrow> nat" where
  "newton_pol_split_delay deg = newton_pol_sig_thresh"
\<comment> \<open>There is no gate on the variation count \<open>v\<close> (cluster size): \<open>v\<close> does not separate the cases such a
   gate would have to separate (a genuine cluster of 20 roots and a nested configuration can both have
   \<open>v = 20\<close>). The bail cascade has no blind end-blocks; \<open>Newton_Solver\<close>'s plain cascade guards its blocks on
   \<open>is_None res0 \<and> is_None res1\<close> and keeps them.\<close>
definition newton_pol_dcap :: nat where "newton_pol_dcap = 1099511627776"
definition newton_pol_kcap :: nat where "newton_pol_kcap = 1099511627776"
definition newton_pol_gate :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "newton_pol_gate deg e dk s \<equiv>
     (newton_pol_split_delay deg \<le> s \<or> newton_pol_emin \<le> e) \<and> e \<le> newton_pol_ecap \<and>
     dk \<le> newton_pol_kcap \<and> 1 \<le> deg \<and> deg \<le> newton_pol_dcap"


section \<open>The \<open>gmp_poly option\<close> assertion — @{locale dflt_option} with an \<open>l > c\<close> sentinel\<close>

text \<open>The window ops return \<open>gmp_poly option\<close>. The framework's option support is the
  @{locale dflt_option} locale (an option is the element itself, with one UNREACHABLE
  concrete value playing @{term None} — no boxing; \<open>Some\<close>/\<open>the\<close> are concrete identities).
  Sentinel choice: \<open>(len = 1, cap = 0, data = null)\<close>. @{const arl_assn'} demands
  \<open>l \<le> c\<close>, so this triple satisfies NO abstract list — the locale's \<open>UU\<close> obligation holds
  for every abstract poly. (The naive all-zero \<open>(0,0,null)\<close> FAILS \<open>UU\<close>: @{const narray_assn}
  represents the EMPTY array by \<open>null\<close>, so \<open>[]\<close> maps to it.)\<close>

lemma gmp_poly_assn_sentinel_false:
  "gmp_poly_assn xs (1, 0, null) = sep_false"
  unfolding gmp_poly_assn_def gmp_poly_slots_assn_def arl_assn_def arl_assn'_def
    snat.assn_def
  apply (rule ext)
  apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
  done

text \<open>The \<open>is_dflt\<close> test: exact comparison of all three fields (\<open>CMP\<close> must decide
  \<open>k = dflt\<close> precisely). The null compare reduces via the framework's \<open>ll_ptrcmp_simps\<close>
  vcg-normalize rule (\<open>LLVM_Shallow_RS.thy\<close>): \<open>check_ptrs_cmp\<close> is a no-op when either side
  is \<open>null\<close>, so NO ownership of the data pointer is required — exactly what \<open>CMP\<close>'s \<open>\<box>\<close>
  precondition demands.\<close>
definition gmp_poly_is_none_impl :: "gmp_poly_raw \<Rightarrow> 1 word llM" where
  [llvm_code, llvm_inline]: "gmp_poly_is_none_impl p \<equiv> doM {
    let (l, c, a) = p;
    b1 \<leftarrow> ll_icmp_eq l (signed_nat 1);
    b2 \<leftarrow> ll_icmp_eq c (signed_nat 0);
    b12 \<leftarrow> ll_and b1 b2;
    b3 \<leftarrow> ll_ptrcmp_eq a null;
    ll_and b12 b3
  }"

lemma gmp_poly_is_none_impl_cmp:
  "llvm_htriple \<box> (gmp_poly_is_none_impl k) (\<lambda>r. \<upharpoonleft>bool.assn (k = (1, 0, null)) r)"
proof -
  interpret llvm_prim_arith_setup .
  show ?thesis
    unfolding gmp_poly_is_none_impl_def bool.assn_def
    apply (cases k)
    apply vcg'
    apply (auto simp: signed_nat_def from_bool_def split: if_splits bool.splits)
    done
qed

text \<open>\<^bold>\<open>Exactly ONE option instance, and it is the PAIR.\<close> Two facts force this:
  \<^item> plain @{locale dflt_option} never \<open>sepref_register\<close>s \<open>Some\<close>/\<open>None\<close>/\<open>the\<close>/\<open>is_None\<close>, so
    \<open>RETURN (Some x)\<close> survives \<open>sepref_dbg_trans\<close> unresolved and dies at \<open>sepref_dbg_opt\<close>,
    and \<open>case_option\<close> is unsupported outright. Only @{locale dflt_option_private} registers them.
  \<^item> but \<open>dflt_option_private\<close>'s \<open>Some\<close>/\<open>None\<close>/\<open>the\<close>/\<open>is_None\<close> do NOT depend on the locale's
    parameters, so TWO interpretations SHARE one constant — the \<open>sepref_fr_rules\<close> net then holds
    two rules for the same head and mis-resolves (a poly option gets typed with the pair's assn).
    The locale admits a single instance.

  So \<open>newton_try_window_monadic\<close> itself returns \<open>(int \<times> gmp_poly) option\<close>: it takes the grid
  index \<open>m\<close> as an OWNED mpz, returns \<open>(m, cand)\<close> on ACCEPT, and frees both \<open>m\<close> and the rejected
  candidate on REJECT. \<open>gmp_poly option\<close> never crosses an HNR boundary, so its interpretation is
  not needed at all — @{thm [source] gmp_poly_assn_sentinel_false} and \<open>gmp_poly_is_none_impl\<close>
  survive only as ingredients of the pair's sentinel/\<open>is_dflt\<close> below.\<close>

text \<open>\<open>newton_window_choice_monadic\<close> returns \<open>(int \<times> gmp_poly) option\<close>: the grid index \<open>m\<close> (an owned mpz)
  paired with the accepted window child. A second @{locale dflt_option} instance, with sentinel
  \<open>(null, (1,0,null))\<close>: \<open>UU\<close> is inherited from the polynomial component
  (@{thm [source] gmp_poly_assn_sentinel_false}), and the mpz component does not matter, since
  \<open>P1 a1 c1 ** sep_false = sep_false\<close>.\<close>

lemma mpz_poly_assn_sentinel_false:
  "(mpzb_assn \<times>\<^sub>a gmp_poly_assn) x (null, (1, 0, null)) = sep_false"
  by (cases x) (simp add: prod_assn_def gmp_poly_assn_sentinel_false)

definition gmp_mpoly_is_none_impl :: "mpz_t \<times> gmp_poly_raw \<Rightarrow> 1 word llM" where
  [llvm_code, llvm_inline]: "gmp_mpoly_is_none_impl mp \<equiv> doM {
    let (mz, p) = mp;
    b0 \<leftarrow> ll_ptrcmp_eq mz null;
    b1 \<leftarrow> gmp_poly_is_none_impl p;
    ll_and b0 b1
  }"

text \<open>NB the poly test is UNFOLDED inline rather than supplied as a \<open>vcg_rule\<close>: using the
  \<open>_cmp\<close> htriple leaves an ABSTRACT \<open>1 word\<close> result \<open>r\<close>, and \<open>1 && r \<noteq> 0\<close> then needs a
  1-bit exhaustion the framework has no idiom for. Inlining keeps every \<open>from_bool\<close> literal,
  so the residual is concrete word arithmetic that \<open>auto\<close> discharges.\<close>
lemma gmp_mpoly_is_none_impl_cmp:
  "llvm_htriple \<box> (gmp_mpoly_is_none_impl k) (\<lambda>r. \<upharpoonleft>bool.assn (k = (null, (1, 0, null))) r)"
proof -
  interpret llvm_prim_arith_setup .
  obtain mz p where kp: "k = (mz, p)" by (cases k)
  obtain l c a where pd: "p = (l, c, a)" by (cases p)
  show ?thesis
    unfolding gmp_mpoly_is_none_impl_def gmp_poly_is_none_impl_def bool.assn_def kp pd
    apply vcg'
    apply (auto simp: signed_nat_def from_bool_def split: if_splits bool.splits)
    done
qed

interpretation gmp_mpoly_opt:
  dflt_option_private "(null, (1, 0, null)) :: mpz_t \<times> gmp_poly_raw"
    "mpzb_assn \<times>\<^sub>a gmp_poly_assn" gmp_mpoly_is_none_impl
  apply unfold_locales
  subgoal by (rule mpz_poly_assn_sentinel_false)
  subgoal by (rule gmp_mpoly_is_none_impl_cmp)
  done


definition newton_lambda_loc0 :: "nat \<Rightarrow> gmp_poly \<Rightarrow> bool \<times> int \<times> int" where
  "newton_lambda_loc0 v xs =
     (if xs ! 1 = 0 then (False, 0, 1)
      else (True, - int v * (xs ! 0), xs ! 1))"
definition newton_lambda_loc1 :: "nat \<Rightarrow> gmp_poly \<Rightarrow> bool \<times> int \<times> int" where
  "newton_lambda_loc1 v xs =
     (let (s, ds) = poly_eval1_pair xs
      in if ds = 0 then (False, 0, 1)
         else (True, ds - int v * s, ds))"
definition newton_snap_kn :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "newton_snap_kn e num den =
     (let s = (2 :: int) ^ (2 ^ e + 2)
      in max 2 (min (s - 2) ((num * s) div den)))"


definition newton_lambda_loc0_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> (bool \<times> int \<times> int) nres" where
"newton_lambda_loc0_monadic v xs \<equiv> doN {
  ASSERT (1 < length xs);
  sg \<leftarrow> (PR_CONST poly_coeff_sgn_monadic) xs 1;
  if sg = 0 then doN {
    ASSERT (slong_bounds (int 0));
    z \<leftarrow> (PR_CONST mpz_of_snat_monadic) 0;
    ASSERT (slong_bounds (int 1));
    on1 \<leftarrow> (PR_CONST mpz_of_snat_monadic) 1;
    RETURN (False, z, on1)
  } else doN {
    ASSERT (slong_bounds (int v));
    vi \<leftarrow> (PR_CONST mpz_of_snat_monadic) v;
    ASSERT (slong_bounds (int 0));
    z0 \<leftarrow> (PR_CONST mpz_of_snat_monadic) 0;
    prod \<leftarrow> (PR_CONST poly_hom_eval_addmul_monadic) z0 xs 0 vi;
    (PR_CONST mpzb_discard_monadic) vi;
    neg \<leftarrow> (PR_CONST mpz_neg.amop_r) prod;
    q1 \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs 1;
    RETURN (True, neg, q1)
  }
}"

lemma newton_lambda_loc0_monadic_correct:
  assumes "1 < length xs" and "int v < max_sint LENGTH(gmp_long_len)"
  shows "newton_lambda_loc0_monadic v xs \<le> RETURN (newton_lambda_loc0 v xs)"
  using assms
  unfolding newton_lambda_loc0_monadic_def newton_lambda_loc0_def
    poly_coeff_sgn_monadic_def poly_copy_coeff_monadic_def mpzb_discard_monadic_def
    poly_hom_eval_addmul_monadic_def mpz_neg.amop_r_def mpz_neg.aop_r_def
    PR_CONST_def
  apply (refine_vcg mpz_of_snat_monadic_correct[THEN order_trans])
  by (auto simp: pw_le_iff refine_pw_simps slong_bounds_def max_sint_def min_sint_def sgn_eq_0_iff)

sepref_register "PR_CONST newton_lambda_loc0_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> (bool \<times> int \<times> int) nres"

sepref_definition newton_lambda_loc0_impl [llvm_inline] is
  "uncurry newton_lambda_loc0_monadic" ::
  "[\<lambda>(v, xs). 1 < length xs \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
      bool1_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn"
  unfolding newton_lambda_loc0_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_fr_rules] = poly_coeff_sgn_impl_hnr poly_hom_eval_addmul_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
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

lemma newton_lambda_loc0_impl_hnr[sepref_fr_rules]:
  "(uncurry newton_lambda_loc0_impl, uncurry (PR_CONST newton_lambda_loc0_monadic)) \<in>
    [\<lambda>(v, xs). 1 < length xs \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
        bool1_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn"
  using newton_lambda_loc0_impl.refine
  by (simp add: PR_CONST_def)


definition newton_lambda_loc1_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> (bool \<times> int \<times> int) nres" where
"newton_lambda_loc1_monadic v xs \<equiv> doN {
  \<comment> \<open>Uses the clone-free (s,ds) evaluation @{const poly_eval1_pair_monadic}:
    \<open>\<le> RETURN (poly_eval1_pair xs)\<close>.\<close>
  (s, ds) \<leftarrow> (PR_CONST poly_eval1_pair_monadic) xs;
  sg \<leftarrow> (PR_CONST mpz_sgn_mop) ds;
  if sg = 0 then doN {
    (PR_CONST mpzb_discard_monadic) s;
    (PR_CONST mpzb_discard_monadic) ds;
    ASSERT (slong_bounds (int 0));
    z \<leftarrow> (PR_CONST mpz_of_snat_monadic) 0;
    ASSERT (slong_bounds (int 1));
    on1 \<leftarrow> (PR_CONST mpz_of_snat_monadic) 1;
    RETURN (False, z, on1)
  } else doN {
    ASSERT (slong_bounds (int v));
    vi \<leftarrow> (PR_CONST mpz_of_snat_monadic) v;
    prod \<leftarrow> (PR_CONST mpz_mul.amop_r1) vi s;
    (PR_CONST mpzb_discard_monadic) s;
    dscopy \<leftarrow> RETURN (COPY ds);
    res \<leftarrow> (PR_CONST mpz_sub.amop_r1) dscopy prod;
    (PR_CONST mpzb_discard_monadic) prod;
    RETURN (True, res, ds)
  }
}"

lemma newton_lambda_loc1_monadic_correct:
  assumes "length xs + 2 < max_snat LENGTH(gmp_poly_len)" and "0 < length xs"
    and "int v < max_sint LENGTH(gmp_long_len)"
  shows "newton_lambda_loc1_monadic v xs \<le> RETURN (newton_lambda_loc1 v xs)"
  using assms
  unfolding newton_lambda_loc1_monadic_def newton_lambda_loc1_def
    mpz_sgn_mop_def mpzb_discard_monadic_def COPY_def
    mpz_mul.amop_r1_def mpz_mul.aop_r1_def mpz_sub.amop_r1_def mpz_sub.aop_r1_def
    PR_CONST_def
  apply (refine_vcg poly_eval1_pair_monadic_correct[THEN order_trans]
      mpz_of_snat_monadic_correct[THEN order_trans])
  by (auto simp: pw_le_iff refine_pw_simps slong_bounds_def max_sint_def min_sint_def
      sgn_eq_0_iff split: prod.splits)

sepref_register "PR_CONST newton_lambda_loc1_monadic"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> (bool \<times> int \<times> int) nres"

sepref_definition newton_lambda_loc1_impl [llvm_inline] is
  "uncurry newton_lambda_loc1_monadic" ::
  "[\<lambda>(v, xs). length xs + 2 < max_snat LENGTH(gmp_poly_len) \<and> 0 < length xs
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
      bool1_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn"
  unfolding newton_lambda_loc1_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_fr_rules] = poly_eval1_pair_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
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

lemma newton_lambda_loc1_impl_hnr[sepref_fr_rules]:
  "(uncurry newton_lambda_loc1_impl, uncurry (PR_CONST newton_lambda_loc1_monadic)) \<in>
    [\<lambda>(v, xs). length xs + 2 < max_snat LENGTH(gmp_poly_len) \<and> 0 < length xs
        \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>
        bool1_assn \<times>\<^sub>a mpzb_assn \<times>\<^sub>a mpzb_assn"
  using newton_lambda_loc1_impl.refine
  by (simp add: PR_CONST_def)


definition newton_window_cmp_monadic :: "int \<Rightarrow> int \<Rightarrow> int nres" where
"newton_window_cmp_monadic a c \<equiv> (PR_CONST mpz_cmp_sgn_monadic) a c"

sepref_register "PR_CONST newton_window_cmp_monadic" :: "int \<Rightarrow> int \<Rightarrow> int nres"

lemma newton_window_cmp_monadic_correct: "newton_window_cmp_monadic a c \<le> RETURN (sgn (a - c))"
  unfolding newton_window_cmp_monadic_def mpz_cmp_sgn_monadic_def PR_CONST_def by simp

sepref_definition newton_window_cmp_impl [llvm_inline] is
  "uncurry newton_window_cmp_monadic" :: "mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  unfolding newton_window_cmp_monadic_def
  by sepref

lemma newton_window_cmp_impl_hnr[sepref_fr_rules]:
  "(uncurry newton_window_cmp_impl, uncurry (PR_CONST newton_window_cmp_monadic)) \<in>
    mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow>\<^sub>a gmp_sint_assn"
  using newton_window_cmp_impl.refine by (simp add: PR_CONST_def)


definition newton_window_max_sel_monadic :: "int \<Rightarrow> int \<Rightarrow> int nres" where
"newton_window_max_sel_monadic m v \<equiv> doN {
  s \<leftarrow> (PR_CONST newton_window_cmp_monadic) m v;
  if s \<ge> 0 then doN { (PR_CONST mpzb_discard_monadic) v; RETURN m }
  else doN { (PR_CONST mpzb_discard_monadic) m; RETURN v }
}"

sepref_register "PR_CONST newton_window_max_sel_monadic" :: "int \<Rightarrow> int \<Rightarrow> int nres"

lemma newton_window_max_sel_monadic_correct: "newton_window_max_sel_monadic m v \<le> RETURN (max m v)"
  unfolding newton_window_max_sel_monadic_def mpzb_discard_monadic_def PR_CONST_def
  apply (rule order_trans[OF bind_mono(1)[OF newton_window_cmp_monadic_correct order_refl]])
  apply (auto simp: refine_pw_simps pw_le_iff max_def sgn_if split: if_splits)
  done

sepref_definition newton_window_max_sel_impl [llvm_inline] is
  "uncurry newton_window_max_sel_monadic" :: "mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  unfolding newton_window_max_sel_monadic_def
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma newton_window_max_sel_impl_hnr[sepref_fr_rules]:
  "(uncurry newton_window_max_sel_impl, uncurry (PR_CONST newton_window_max_sel_monadic)) \<in>
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  using newton_window_max_sel_impl.refine by (simp add: PR_CONST_def)


definition newton_window_min_sel_monadic :: "int \<Rightarrow> int \<Rightarrow> int nres" where
"newton_window_min_sel_monadic m v \<equiv> doN {
  s \<leftarrow> (PR_CONST newton_window_cmp_monadic) m v;
  if s \<le> 0 then doN { (PR_CONST mpzb_discard_monadic) v; RETURN m }
  else doN { (PR_CONST mpzb_discard_monadic) m; RETURN v }
}"

sepref_register "PR_CONST newton_window_min_sel_monadic" :: "int \<Rightarrow> int \<Rightarrow> int nres"

lemma newton_window_min_sel_monadic_correct: "newton_window_min_sel_monadic m v \<le> RETURN (min m v)"
  unfolding newton_window_min_sel_monadic_def mpzb_discard_monadic_def PR_CONST_def
  apply (rule order_trans[OF bind_mono(1)[OF newton_window_cmp_monadic_correct order_refl]])
  apply (auto simp: refine_pw_simps pw_le_iff min_def sgn_if split: if_splits)
  done

sepref_definition newton_window_min_sel_impl [llvm_inline] is
  "uncurry newton_window_min_sel_monadic" :: "mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  unfolding newton_window_min_sel_monadic_def
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma newton_window_min_sel_impl_hnr[sepref_fr_rules]:
  "(uncurry newton_window_min_sel_impl, uncurry (PR_CONST newton_window_min_sel_monadic)) \<in>
    mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow>\<^sub>a mpzb_assn"
  using newton_window_min_sel_impl.refine by (simp add: PR_CONST_def)


text \<open>GMP snap: \<open>s = 2^(2^e+2)\<close> (via \<open>mpz_pow2\<close>), \<open>k0 = num*s div den\<close> (mul + fdiv), then the
  clip \<open>max 2 (min (s-2) k0)\<close> in mpz space. Result is an OWNED mpz (int-valued, no word
  downcast — that is the whole point of the \<open>m::int\<close> representation). CONSUMES \<open>num\<close>, \<open>den\<close>.\<close>
definition newton_snap_kn_monadic :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int nres" where
"newton_snap_kn_monadic e num den \<equiv> doN {
  ASSERT (den \<noteq> 0);
  ASSERT (e < LENGTH(gmp_poly_len));
  ASSERT (2 ^ e + 2 < max_snat LENGTH(gmp_poly_len));  \<comment> \<open>pol gate guarantees this\<close>
  \<comment> \<open>\<open>2^e\<close> as a snat is a machine-word SHIFT \<open>1<<e\<close> (Sepref has no snat exponentiation);
     \<open>e \<le> ecap = 8\<close> keeps it in-word. Bound ONCE (\<open>ek\<close>) and reused below -- a repeated
     un-let-bound subterm across two sibling ops can derail Sepref's \<open>trans\<close> search.\<close>
  let ek = ((1::nat) << e) + 2;
  s \<leftarrow> (PR_CONST mpz_pow2_monadic) ek;
  \<comment> \<open>\<open>s\<close> itself is still needed below (\<open>s2 = s - 2\<close>), so it cannot be dropped; but the
    multiply-by-\<open>s\<close> step doesn't need a MATERIALIZED \<open>s\<close> at all -- \<open>num*s\<close> is exactly
    \<open>num\<close> shifted left by \<open>s\<close>'s own exponent, so a direct \<open>mpz_shift_left_snat_monadic\<close>
    replaces both the \<open>COPY\<close> of \<open>s\<close> and the general \<open>mpz_mul\<close> with one shift.\<close>
  prod \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) num ek;
  k0 \<leftarrow> (PR_CONST mpz_fdiv_q.amop_r1) prod den;
  (PR_CONST mpzb_discard_monadic) den;
  \<comment> \<open>\<open>s-2\<close> via the immediate @{const mpz_sub_ui_snat_monadic} (\<open>s\<close> consumed destructively): no materialised
     \<open>2\<close>.\<close>
  s2 \<leftarrow> (PR_CONST mpz_sub_ui_snat_monadic) s 2;
  m1 \<leftarrow> (PR_CONST newton_window_min_sel_monadic) s2 k0;
  ASSERT (slong_bounds (int 2));
  two2 \<leftarrow> (PR_CONST mpz_of_snat_monadic) 2;
  (PR_CONST newton_window_max_sel_monadic) two2 m1
}"

lemma newton_snap_kn_monadic_correct:
  assumes den: "den \<noteq> 0" and eb: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "newton_snap_kn_monadic e num den \<le> RETURN (newton_snap_kn e num den)"
proof -
  have sh: "((1::nat) << e) = 2 ^ e" by (simp add: shiftl_def push_bit_eq_mult)
  have eL: "e < LENGTH(gmp_poly_len)"
  proof -
    have "(2::nat) ^ e < 2 ^ (LENGTH(gmp_poly_len) - 1)"
      using eb by (simp add: max_snat_def)
    hence "e < LENGTH(gmp_poly_len) - 1"
      using power_less_imp_less_exp[of 2 e "LENGTH(gmp_poly_len) - 1"] by simp
    thus ?thesis by simp
  qed
  show ?thesis
    using den eb sh eL
    unfolding newton_snap_kn_monadic_def newton_snap_kn_def Let_def
      mpz_fdiv_q.amop_r1_def mpz_fdiv_q.aop_r1_def
      mpzb_discard_monadic_def PR_CONST_def
    apply (refine_vcg mpz_pow2_monadic_spec[THEN order_trans]
        mpz_shift_left_snat_monadic_spec_plain[THEN order_trans]
        mpz_sub_ui_snat_monadic_spec[THEN order_trans]
        mpz_of_snat_monadic_correct[THEN order_trans]
        newton_window_min_sel_monadic_correct[THEN order_trans]
        newton_window_max_sel_monadic_correct[THEN order_trans])
    apply (auto simp: slong_bounds_def max_sint_def min_sint_def max_snat_def sh)
    done
qed

sepref_register "PR_CONST newton_snap_kn_monadic" :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int nres"

sepref_definition newton_snap_kn_impl [llvm_inline] is
  "uncurry2 newton_snap_kn_monadic" ::
  "[\<lambda>((e, num), den). 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow> mpzb_assn"
  unfolding newton_snap_kn_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_fr_rules] = mpz_shift_left_snat_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
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

lemma newton_snap_kn_impl_hnr[sepref_fr_rules]:
  "(uncurry2 newton_snap_kn_impl, uncurry2 (PR_CONST newton_snap_kn_monadic)) \<in>
    [\<lambda>((e, num), den). 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>d *\<^sub>a mpzb_assn\<^sup>d \<rightarrow> mpzb_assn"
  using newton_snap_kn_impl.refine by (simp add: PR_CONST_def)


definition newton_child_exp :: "nat \<Rightarrow> nat" where
  "newton_child_exp e = (if e \<le> 1 then 1 else e - 1)"

lemma newton_child_exp_eq: "newton_child_exp e = max 1 (e - 1)"
  by (simp add: newton_child_exp_def)

sepref_register "PR_CONST newton_child_exp" :: "nat \<Rightarrow> nat"

sepref_definition newton_child_exp_impl [llvm_inline] is
  "RETURN o newton_child_exp" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding newton_child_exp_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma newton_child_exp_impl_hnr[sepref_fr_rules]:
  "(newton_child_exp_impl, RETURN o PR_CONST newton_child_exp) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using newton_child_exp_impl.refine by (simp add: PR_CONST_def)


text \<open>The gate, indexed by the polynomial length rather than its degree: Sepref reads a
  \<open>gmp_poly_assn\<close>'s length through an \<open>nres\<close> op, and an inline \<open>len - 1\<close> inside the test is an snat
  subtraction that blocks translation. Restating \<open>1 \<le> deg \<and> deg \<le> dcap\<close> as \<open>2 \<le> len \<and> len \<le> dcap + 1\<close> leaves
  only numeral comparisons.\<close>
text \<open>The Sepref-synthesisable twin, indexed by the polynomial length. A runtime-evaluated guard may
  contain only numeral comparisons, and restating \<open>deg \<le> dcap\<close> as \<open>len \<le> dcap + 1\<close> means the implementation
  needs no \<open>len - 1\<close> snat subtraction.\<close>
definition newton_pol_gate_len :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "newton_pol_gate_len len e dk s \<equiv>
     (newton_pol_sig_thresh \<le> s \<or> newton_pol_emin \<le> e) \<and> e \<le> newton_pol_ecap \<and>
     dk \<le> newton_pol_kcap \<and> 2 \<le> len \<and> len \<le> 1099511627777"

text \<open>The bridge that keeps the twin honest — it is what makes a drift between the abstract
  gate and its impl twin a FAST-LOOP failure rather than a silent divergence.\<close>
lemma newton_pol_gate_len_eq:
  assumes "0 < len"
  shows "newton_pol_gate_len len e dk s = newton_pol_gate (len - 1) e dk s"
  using assms
  by (auto simp: newton_pol_gate_len_def newton_pol_gate_def newton_pol_dcap_def
                 newton_pol_split_delay_def)

sepref_register "PR_CONST newton_pol_gate_len"
  :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"

sepref_definition newton_pol_gate_len_impl [llvm_inline] is
  "uncurry3 (RETURN oooo newton_pol_gate_len)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding newton_pol_gate_len_def newton_pol_emin_def newton_pol_ecap_def
    newton_pol_kcap_def newton_pol_sig_thresh_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  by sepref

lemma newton_pol_gate_len_impl_hnr[sepref_fr_rules]:
  "(uncurry3 newton_pol_gate_len_impl, uncurry3 (RETURN oooo PR_CONST newton_pol_gate_len)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using newton_pol_gate_len_impl.refine by (simp add: PR_CONST_def)


text \<open>The gate needs the node polynomial's DEGREE, which lives behind @{const poly_length_monadic}
  (an \<open>nres\<close> op — \<open>gmp_poly_assn\<close> is heap-owning, so \<open>length\<close> is not a pure term Sepref can read).
  Bundling the read and the test into one op keeps the after-pop body a flat cascade.\<close>
definition newton_pol_gate_mop :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
"newton_pol_gate_mop Q e dk s \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) Q;
  RETURN ((PR_CONST newton_pol_gate_len) len e dk s)
}"

lemma newton_pol_gate_mop_correct:
  assumes "0 < length Q" and "length Q < max_snat LENGTH(gmp_poly_len)"
  shows "newton_pol_gate_mop Q e dk s \<le> RETURN (newton_pol_gate (length Q - 1) e dk s)"
  using assms
  unfolding newton_pol_gate_mop_def poly_length_monadic_def PR_CONST_def
  apply (refine_vcg)
  by (auto simp: newton_pol_gate_len_eq)

sepref_register "PR_CONST newton_pol_gate_mop"
  :: "gmp_poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres"

sepref_definition newton_pol_gate_mop_impl [llvm_inline] is
  "uncurry3 newton_pol_gate_mop" ::
  "gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding newton_pol_gate_mop_def
  by sepref

lemma newton_pol_gate_mop_impl_hnr[sepref_fr_rules]:
  "(uncurry3 newton_pol_gate_mop_impl, uncurry3 (PR_CONST newton_pol_gate_mop)) \<in>
    gmp_poly_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using newton_pol_gate_mop_impl.refine by (simp add: PR_CONST_def)


(*FASTLOOP_FREEZE_ABOVE*)

definition newton_try_window_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres"
where
"newton_try_window_monadic v e m xs \<equiv> doN {
  ASSERT (0 < length xs);
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  ASSERT ((2 ^ e + 2) * (length xs - 1) < max_snat LENGTH(gmp_poly_len));
  \<comment> \<open>Window validity: instantiates \<open>carried_window_count_mono\<close> at \<open>j = 2^e+2\<close>. Specification-level (erased
     in generated code) and discharged at every call site: two here in the bail cascade (side0/side1) and
     four in \<open>Newton_Solver\<close>'s plain cascade. The probe sites supply \<open>m = kn-2\<close>; the block sites of the plain
     cascade supply \<open>m = 0\<close> and \<open>m = s-4\<close>.\<close>
  ASSERT (0 \<le> m \<and> m + 4 \<le> 2 ^ (2 ^ e + 2));
  \<comment> \<open>\<open>m+4\<close> as a fresh owned mpz (non-destructive add: \<open>m\<close> stays live for \<open>carried_init\<close>,
     which BORROWS both \<open>m\<close> and \<open>m+4\<close>); \<open>2^e\<close> as the snat SHIFT \<open>1<<e\<close> (\<open>e<LENGTH\<close> is an
     IMPL-only precondition, threaded on the HNR — the value \<open>(1<<e)+2 = 2^e+2\<close> holds for all \<open>e\<close>).
     \<open>m\<close> is OWNED: it is RETURNED inside the accepted \<open>(m, cand)\<close>, and FREED on reject.\<close>
  \<comment> \<open>\<open>m+4\<close> via the immediate @{const mpz_add_ui_snat_monadic} on a copy of the borrowed \<open>m\<close> (\<open>m\<close> stays owned:
     returned inside the accepted \<open>Some (m, cand)\<close>, freed on reject), with no materialised \<open>4\<close>.\<close>
  m4 \<leftarrow> RETURN (COPY m);
  m4 \<leftarrow> (PR_CONST mpz_add_ui_snat_monadic) m4 4;
  \<comment> \<open>\<^bold>\<open>Certify a rejection before paying for the exact build.\<close> The body below still runs on every probe
     the decide does not settle, so this can only remove work. The gate affects only performance
     (\<open>probe_reject_gate_mop\<close> returns \<open>0\<close> to decline; soundness holds for every exponent it could return), and
     \<open>nb\<close> is the \<open>O(deg)\<close> true maximum bit-length rather than the \<open>O(1)\<close> leading one, because at this site the
     leading coefficient is typically far smaller than the largest. \<open>kn\<close> is the dilation span
     \<open>(2\<^sup>e+2)(deg-1)\<close>, which the ASSERT above bounds. The \<open>None\<close> returned is the \<open>None\<close> the exact path would
     return: \<open>probe_reject_monadic_sound\<close> certifies \<open>count cand \<noteq> v\<close>, the branch condition of the capstone's
     specification, so the contract is unchanged.\<close>
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  ASSERT (len = length xs);
  \<comment> \<open>\<^bold>\<open>The \<open>m \<noteq> 0\<close> clause.\<close> At \<open>m = 0\<close> the build this decide speculates against has no \<open>O(deg\<^sup>2)\<close> stage:
     @{const carried_init_inplace_monadic} tests \<open>sgn m\<close> and returns the polynomial untouched, so the exact
     path is \<open>O(deg)\<close>, while \<open>probe_count_pipe\<close> runs \<open>taylor_shift_one\<close> twice. \<open>probe_reject_gate_mop\<close> prices
     the build as \<open>O(deg\<^sup>2)(nb+kn)\<close> with no term for this case, so the decide is declined there. Declining only
     affects speed: \<open>probe_reject_monadic_sound\<close> holds for every truncation exponent, and \<open>tg = 0\<close> reaches the
     \<open>rej = False\<close> branch the gate already has, so the capstone's statement is unchanged. The test comes first,
     so it also skips the \<open>O(deg)\<close> @{const poly_max_bitlen_monadic} scan. \<open>mpz_sgn_mop\<close> borrows \<open>m\<close>
     (\<open>mpzb_assn\<^sup>k\<close>, HNR \<open>mpzb_sgn_impl_mop_hnr\<close>), so \<open>m\<close> stays owned for the \<open>carried_init\<close> below and for the
     \<open>None\<close> arm's discard.\<close>
  sg \<leftarrow> (PR_CONST mpz_sgn_mop) m;
  tg \<leftarrow> (if sg \<noteq> 0
          then doN {
            nb \<leftarrow> (PR_CONST poly_max_bitlen_monadic) xs;
            (PR_CONST probe_reject_gate_mop) len ((((1::nat) << e) + 2) * (len - 1)) nb
          } else RETURN 0);
  rej \<leftarrow> (if 0 < tg
           then (PR_CONST probe_reject_monadic)
                  v (((1::nat) << e) + 2) m m4 tg xs
           else RETURN False);
  if rej then doN {
    (PR_CONST mpzb_discard_monadic) m4;
    (PR_CONST mpzb_discard_monadic) m;
    RETURN gmp_mpoly_opt.None
  } else doN {
    cand \<leftarrow> (PR_CONST carried_init_inplace_monadic)
              m (((1::nat) << e) + 2) m4 xs;
    (PR_CONST mpzb_discard_monadic) m4;
    ASSERT (length cand + 1 < max_snat LENGTH(gmp_poly_len));
    \<comment> \<open>The cheap truncated classification runs first. \<open>tc\<close> matches the exact count's classification, so
       \<open>tc \<in> {0,1}\<close> decides acceptance via \<open>tc = v\<close> with no exact count; an empty window (\<open>tc = 0\<close>) is rejected on
       operands truncated to about \<open>2*len\<close> bits. Only \<open>tc \<ge> 2\<close> pays for the exact count. The specification
       (\<open>Some \<Leftrightarrow> exact count = v\<close>) is unchanged.\<close>
    tc \<leftarrow> (PR_CONST carried_descartes_count_trunc_monadic) cand;
    match \<leftarrow> (if 2 \<le> tc
              then doN {
                \<comment> \<open>The capped kernel runs at \<open>cap = v\<close> and aborts at the \<open>v\<close>-th sign change. With the window-count
                   monotonicity bound \<open>count cand \<le> v\<close> (\<open>carried_window_count_mono\<close>, supplied by the
                   \<open>count xs \<le> v\<close> precondition), reaching \<open>v\<close> proves \<open>count cand = v\<close>, so the test is \<open>v \<le> r\<close> and
                   an accept exits early instead of running a full exact count; a cap above \<open>v\<close> would have
                   to scan past \<open>v\<close>. The two ASSERTs are specification-level (erased in generated code).\<close>
                ASSERT (2 \<le> v);
                ASSERT (carried_descartes_count xs \<le> v);
                r \<leftarrow> (PR_CONST carried_descartes_count_trunc_cap_monadic) v cand;
                RETURN (v \<le> r) }
              else RETURN (tc = v));
    if match then RETURN (gmp_mpoly_opt.Some (m, cand))
    else doN {
      (PR_CONST poly_free_monadic) cand;
      (PR_CONST mpzb_discard_monadic) m;
      RETURN gmp_mpoly_opt.None
    }
  }
}"

text \<open>Both branches speak: \<open>Some\<close> returns THE window child with count exactly
  \<open>v\<close>; \<open>None\<close> certifies the child's count differs — the impl's try order can
  then be matched attempt-for-attempt against @{const try_blocks_int_g}/
  @{const try_newton_int_g} in the loop bridge. The SPEC is stated over
  \<open>carried_init_same_den\<close> — the in-place op's proven refinement target
  (\<open>carried_init_inplace_monadic_correct\<close>, \<open>Carried_Kernel.thy\<close>: it returns
  \<open>carried_init_same_den l (2^k) r xs\<close>) — so the window-algebra spine composes without
  an extra bridge. Route: \<open>refine_vcg\<close> over that \<open>_correct\<close> + the exact-count
  \<open>_correct\<close> above; length side conditions from the init op's length lemma.

  \<^bold>\<open>The spine (\<open>Newton_Spec.thy\<close>).\<close>
  \<open>carried_repr_scalar P a b Q\<close> (a positive-rational-scalar relaxation of
  \<open>Bisection_Refine.thy\<close>'s exact \<open>carried_repr\<close> — chosen because
  \<open>carried_descartes_count\<close> only depends on sign, so exact equality is more
  than the algorithm needs, and the relaxation avoids re-deriving bisection-
  specific lcm/gcd bookkeeping for arbitrary windows) is preserved by the window
  transform: \<open>carried_window_repr_scalar\<close> shows \<open>window_child_formula m s (m+4)
  Q\<close> (\<open>= carried_init_same_den m s (m+4) Q\<close> by definition — one \<open>unfolding\<close>
  step bridges the two names) represents the global window
  \<open>[a+(m/s)(b-a), a+((m+4)/s)(b-a)]\<close> whenever \<open>Q\<close> represents \<open>[a,b]\<close>, and
  \<open>carried_repr_scalar_count\<close> transports this to \<open>descartes_list_int\<close> equality
  — exactly the fact this op's SPEC states. The loop invariant uses
  \<open>carried_repr_scalar\<close> throughout, not literally \<open>carried_repr\<close>.\<close>
lemma length_carried_init_same_den [simp]:
  "length (carried_init_same_den l d r xs) = length xs"
  unfolding carried_init_same_den_def by simp

text \<open>Sign variations of a list are bounded by its length (each fold step adds \<open>\<le> 1\<close>) —
  the soundness fact for the window-try length clamp: a window child whose length is below the
  target count \<open>v\<close> cannot have count \<open>= v\<close>. (Clone of the bail file's \<open>_bl\<close> triple.)\<close>
lemma sign_step_snd_le_cn: "snd (sign_step x (s, n)) \<le> Suc n"
  by (auto split: if_splits)

lemma fold_sign_step_snd_le_cn: "snd (fold sign_step xs (s, n)) \<le> n + length xs"
proof (induction xs arbitrary: s n)
  case (Cons x xs)
  obtain s' n' where sn': "sign_step x (s, n) = (s', n')" by (cases "sign_step x (s, n)")
  have "n' \<le> Suc n" using sign_step_snd_le_cn[of x s n] sn' by simp
  hence "snd (fold sign_step xs (s', n')) \<le> n' + length xs" using Cons.IH by (simp add: add.commute)
  thus ?case using \<open>n' \<le> Suc n\<close> sn' by simp
qed simp

lemma carried_descartes_count_le_length_cn: "carried_descartes_count Q \<le> length Q"
  using fold_sign_step_snd_le_cn[of "taylor_shift_list 1 (rev Q)" 0 0]
  by (simp add: carried_descartes_count_def sign_changes_fold_def)

text \<open>The gate is perf-only, so the abstract proof needs only its totality --- the value it
  returns is used solely through the branch condition \<open>0 < tg\<close>. Stated here rather than in
  \<open>Count.thy\<close> because it is about how THIS site consumes the gate.\<close>
lemma probe_reject_gate_mop_nofail: "probe_reject_gate_mop len kn nb \<le> SPEC (\<lambda>_. True)"
  unfolding probe_reject_gate_mop_def PR_CONST_def
  by (auto simp: pw_le_iff refine_pw_simps)

lemma carried_try_window_monadic_correct:
  assumes lxs: "0 < length xs"
      and lb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
      and gate: "(2 ^ e + 2) * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
      and m0: "0 \<le> m" and mj: "m + 4 \<le> 2 ^ (2 ^ e + 2)"
      and v2: "2 \<le> v" and cxv: "carried_descartes_count xs \<le> v"
  shows "newton_try_window_monadic v e m xs \<le> SPEC (\<lambda>res.
    (case res of
       Some (m', cand) \<Rightarrow>
         m' = m
         \<and> cand = carried_init_same_den (m) (2 ^ (2 ^ e + 2)) (m + 4) xs
         \<and> carried_descartes_count cand = v
     | None \<Rightarrow>
         carried_descartes_count
           (carried_init_same_den (m) (2 ^ (2 ^ e + 2)) (m + 4) xs) \<noteq> v))"
proof -
  have sh: "((1::nat) << e) = 2 ^ e" by (simp add: shiftl_def push_bit_eq_mult)
  have b4: "(4::nat) < max_snat LENGTH(gmp_long_len)" by (simp add: max_snat_def)
  \<comment> \<open>THE load-bearing bound: the window child's count never exceeds the node's, so the
     cap kernel's abort at \<open>v\<close> is conclusive.\<close>
  have candle: "carried_descartes_count (carried_init_same_den m (2 ^ (2 ^ e + 2)) (m + 4) xs)
      \<le> v"
    using carried_window_count_mono[OF lxs m0 mj] cxv by simp
  \<comment> \<open>The rejection branch. The decide returns \<open>True\<close> only on a certified rejection, and the fact it
     certifies, \<open>count (carried_init_same_den \<dots>) \<noteq> v\<close>, is the \<open>None\<close> case of this capstone's specification, so
     the branch discharges against the unchanged conclusion. The gate contributes only a value: soundness
     holds for every exponent, so only \<open>0 < tg\<close> (the branch condition) is used.\<close>
  have l2sound: "\<And>tg. 0 < tg \<Longrightarrow>
      probe_reject_monadic v (2 ^ e + 2) m (m + 4) tg xs
        \<le> SPEC (\<lambda>r. r \<longrightarrow>
            carried_descartes_count
              (carried_init_same_den m (2 ^ (2 ^ e + 2)) (m + 4) xs) \<noteq> v)"
    by (rule probe_reject_monadic_sound[OF m0 _ lxs lb gate]) simp_all
  show ?thesis
    using assms sh b4 candle l2sound
    unfolding newton_try_window_monadic_def PR_CONST_def
      mpzb_discard_monadic_def COPY_def poly_length_monadic_def
      mpz_sgn_mop_def
    apply (refine_vcg
        mpz_add_ui_snat_monadic_spec[THEN order_trans]
        poly_max_bitlen_monadic_nofail[THEN order_trans]
        probe_reject_gate_mop_nofail[THEN order_trans]
        probe_reject_monadic_sound[THEN order_trans]
        carried_init_inplace_monadic_correct[THEN order_trans]
        carried_descartes_count_trunc_monadic_classify[THEN order_trans]
        cap_count_match_mono_trunc[THEN order_trans])
    apply (auto simp: pw_le_iff refine_pw_simps slong_bounds_def max_sint_def min_sint_def
        sh algebra_simps)
    done
qed

sepref_register "PR_CONST newton_try_window_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres"

sepref_definition newton_try_window_impl [llvm_code] is
  "uncurry3 newton_try_window_monadic" ::
  "[\<lambda>(((v, e), m), xs). 0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length xs - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  unfolding newton_try_window_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)?
  supply [sepref_fr_rules] = mpzb_add_impl_hnr carried_descartes_count_cap_impl_hnr
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
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

lemma carried_try_window_impl_hnr[sepref_fr_rules]:
  "(uncurry3 newton_try_window_impl, uncurry3 (PR_CONST newton_try_window_monadic)) \<in>
    [\<lambda>(((v, e), m), xs). 0 < length xs \<and> length xs + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length xs - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        mpzb_assn\<^sup>d *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  using newton_try_window_impl.refine by (simp add: PR_CONST_def)

section \<open>Cascade bail\<close>

text \<open>\<^bold>\<open>The bail rule\<close>: once the Newton probe at location 0 has issued a try and it was rejected, skip the
  remaining try at this node and bisect. The fallback skipped is one further probe (location 1).

  \<^bold>\<open>Structure\<close>: a \<open>bail_\<close>-prefixed vertical (sides, window choice, after-pop, loop, main list, split
  pipeline). Everything semantically unchanged is reused: the loop state and assertion,
  \<open>newton_loop_cond\<close>/\<open>_safe_invar\<close>/\<open>_step_pre\<close>, all branch ops, the gate op, and
  @{const newton_try_window_monadic} (bail changes which windows are tried, not how a try validates).
  Only \<open>newton_window_side0_bail_monadic\<close> returns a \<open>tried\<close> flag, and the choice is an \<open>if\<close> on it.\<close>


definition newton_window_side0_bail_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> ((int \<times> gmp_poly) option \<times> bool) nres" where
"newton_window_side0_bail_monadic v e Q \<equiv> doN {
  (ok0, num0, den0) \<leftarrow> (PR_CONST newton_lambda_loc0_monadic) v Q;
  if ok0 then doN {
    kn0 \<leftarrow> (PR_CONST newton_snap_kn_monadic) e num0 den0;
    ASSERT (2 \<le> kn0);
    \<comment> \<open>\<open>kn0-2\<close> via the immediate @{const mpz_sub_ui_snat_monadic}.\<close>
    m \<leftarrow> (PR_CONST mpz_sub_ui_snat_monadic) kn0 2;
    res \<leftarrow> (PR_CONST newton_try_window_monadic) v e m Q;
    RETURN (res, True)
  } else doN {
    (PR_CONST mpzb_discard_monadic) num0;
    (PR_CONST mpzb_discard_monadic) den0;
    RETURN (gmp_mpoly_opt.None, False)
  }
}"

\<comment> \<open>side1 returns no \<open>tried\<close> flag: it is the last arm of the cascade, so nothing branches on whether it
   issued a try.\<close>
definition newton_window_side1_bail_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres" where
"newton_window_side1_bail_monadic v e Q \<equiv> doN {
  (ok1, num1, den1) \<leftarrow> (PR_CONST newton_lambda_loc1_monadic) v Q;
  if ok1 then doN {
    kn1 \<leftarrow> (PR_CONST newton_snap_kn_monadic) e num1 den1;
    ASSERT (2 \<le> kn1);
    \<comment> \<open>\<open>kn1-2\<close> via the immediate @{const mpz_sub_ui_snat_monadic}.\<close>
    m \<leftarrow> (PR_CONST mpz_sub_ui_snat_monadic) kn1 2;
    (PR_CONST newton_try_window_monadic) v e m Q
  } else doN {
    (PR_CONST mpzb_discard_monadic) num1;
    (PR_CONST mpzb_discard_monadic) den1;
    RETURN gmp_mpoly_opt.None
  }
}"

text \<open>The window choice with bail: the cascade is the two probes.

  \<^bold>\<open>No gate on cluster size.\<close> A gate \<open>v \<le> vcap\<close> on the variation count cannot separate the cases it would
  have to (a genuine cluster of 20 roots and a nested configuration can both have \<open>v = 20\<close>), so there is none.
  Blind end-blocks guarded by \<open>\<not> t0 \<and> \<not> t1\<close> would fire only on the nodes such a gate switched off, so without
  the gate they would be unreachable, and there are none.

  \<^bold>\<open>\<open>side1\<close> is kept.\<close> It is the fallback for \<open>ok0 = False\<close>, i.e. an algebraically zero shifted linear
  coefficient at the probe point, at the cost of one branch test.

  \<^bold>\<open>The cascade\<close>: try the location-0 Newton probe; if it produced a candidate its verdict is final (the
  bail); otherwise fall back to location 1. Two extensional identities give this form, and the refinement
  proofs use them:

  \<^item> \<^bold>\<open>The guard \<open>is_None res0 \<and> \<not> t0\<close> is just \<open>\<not> t0\<close>.\<close> @{const newton_window_side0_bail_monadic} returns
    \<open>(None, False)\<close> on its \<open>\<not> ok0\<close> branch, so \<open>\<not> t0 \<longrightarrow> is_None res0\<close>.
  \<^item> \<^bold>\<open>\<open>if \<not> is_None res0 then res0 else res1\<close> is just the branch value.\<close> When \<open>t0\<close>, side1 does not run, so
    \<open>res1 = None\<close> and both arms give \<open>res0\<close>; when \<open>\<not> t0\<close>, \<open>res0 = None\<close> by the identity above, so both arms give
    \<open>res1\<close>.

  So: probe accepted \<Rightarrow> \<open>Some\<close>, picked; probe rejected \<Rightarrow> \<open>t0 \<and> None\<close> \<Rightarrow> bail (bisect) without trying location 1,
  which is the difference from \<open>newton_window_choice_monadic\<close>; probe missed (\<open>\<not> ok0\<close>) \<Rightarrow> location 1 runs.
  An equivalent flat form, if needed for synthesis, is
  \<open>res1 \<leftarrow> (if \<not> t0 then side1 \<dots> else RETURN None); RETURN (if t0 then res0 else res1)\<close>.

  \<^bold>\<open>Correctness\<close>: \<open>newdsc_pol_bail\<close> is proved for every policy, and this is the policy with the Newton gate
  on of \<open>try_window_bail\<close> (\<open>Bail_Spec\<close>). \<open>try_blocks\<close> remains in \<open>NewDsc\<close>, and the plain
  \<open>newton_window_choice_monadic\<close> (\<open>Newton_Solver\<close>) keeps its blocks.\<close>
definition newton_window_choice_bail_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres" where
"newton_window_choice_bail_monadic v e Q \<equiv> doN {
  (res0, t0) \<leftarrow> (PR_CONST newton_window_side0_bail_monadic) v e Q;
  if t0 then RETURN res0
  else (PR_CONST newton_window_side1_bail_monadic) v e Q
}"

sepref_register "PR_CONST newton_window_side0_bail_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> ((int \<times> gmp_poly) option \<times> bool) nres"

sepref_definition newton_window_side0_bail_impl [llvm_code] is
  "uncurry2 newton_window_side0_bail_monadic" ::
  "[\<lambda>((v, e), Q). 0 < length Q \<and> 1 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn \<times>\<^sub>a bool1_assn"
  unfolding newton_window_side0_bail_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free gmp_poly_assn_free
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

lemma newton_window_side0_bail_impl_hnr[sepref_fr_rules]:
  "(uncurry2 newton_window_side0_bail_impl, uncurry2 (PR_CONST newton_window_side0_bail_monadic)) \<in>
    [\<lambda>((v, e), Q). 0 < length Q \<and> 1 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn \<times>\<^sub>a bool1_assn"
  using newton_window_side0_bail_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_window_side1_bail_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres"

sepref_definition newton_window_side1_bail_impl [llvm_code] is
  "uncurry2 newton_window_side1_bail_monadic" ::
  "[\<lambda>((v, e), Q). 0 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> length Q + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  unfolding newton_window_side1_bail_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free gmp_poly_assn_free
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

lemma newton_window_side1_bail_impl_hnr[sepref_fr_rules]:
  "(uncurry2 newton_window_side1_bail_impl, uncurry2 (PR_CONST newton_window_side1_bail_monadic)) \<in>
    [\<lambda>((v, e), Q). 0 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> length Q + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  using newton_window_side1_bail_impl.refine by (simp add: PR_CONST_def)

sepref_register "PR_CONST newton_window_choice_bail_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option nres"

sepref_definition newton_window_choice_bail_impl [llvm_code] is
  "uncurry2 newton_window_choice_bail_monadic" ::
  "[\<lambda>((v, e), Q). 0 < length Q \<and> 1 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> length Q + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  unfolding newton_window_choice_bail_monadic_def
  \<comment> \<open>No \<open>annot_snat_const\<close> here: this definition contains no numeric literal, and the method fails when
     there is nothing to annotate.\<close>
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free gmp_poly_assn_free
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

lemma newton_window_choice_bail_impl_hnr[sepref_fr_rules]:
  "(uncurry2 newton_window_choice_bail_impl,
      uncurry2 (PR_CONST newton_window_choice_bail_monadic)) \<in>
    [\<lambda>((v, e), Q). 0 < length Q \<and> 1 < length Q
      \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)
      \<and> length Q + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> (2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)
      \<and> e < LENGTH(gmp_poly_len) \<and> 2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)
      \<and> int v < max_sint LENGTH(gmp_long_len)]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
        gmp_poly_assn\<^sup>k \<rightarrow> gmp_mpoly_opt.option_assn"
  using newton_window_choice_bail_impl.refine by (simp add: PR_CONST_def)

end
