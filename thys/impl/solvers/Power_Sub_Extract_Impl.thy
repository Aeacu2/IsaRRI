theory Power_Sub_Extract_Impl
  imports Power_Sub_Detect_Impl
begin

text \<open>Extraction, the entry's second step (op \<open>pow_sub_extract_monadic\<close>).

  \<open>Q\<^sub>j = P\<^sub>j\<^sub>h\<close>: a strided copy at stride \<open>h\<close>, \<open>O(n/h)\<close> coefficients out of an \<open>O(n)\<close> input. The
  input polynomial stays borrowed; the output is a fresh owned buffer built by push, the same shape
  \<open>poly_scale_body_mop_monadic\<close> uses.

  \<^bold>\<open>The output length is \<open>Suc ((len - 1) div h)\<close>\<close>, as in \<open>pow_sub_extract\<close>. It is computed from the
  length once, outside the loop, for the same reason the detection loop takes its bound as a
  parameter.\<close>

section \<open>The strided copy\<close>

definition pow_sub_extract_len :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pow_sub_extract_len h len = Suc ((len - 1) div h)"

lemma pow_sub_extract_length:
  "length (pow_sub_extract h xs) = pow_sub_extract_len h (length xs)"
  by (simp add: pow_sub_extract_def pow_sub_extract_len_def)

definition pow_sub_extract_cond :: "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool" where
  "pow_sub_extract_cond outlen st \<longleftrightarrow> (let (j, dst) = st in j < outlen)"

sepref_register "PR_CONST pow_sub_extract_cond"
  :: "nat \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> bool"

abbreviation pow_sub_extract_state_assn where
  "pow_sub_extract_state_assn \<equiv> snat_assn' TYPE(gmp_poly_len) \<times>\<^sub>a gmp_poly_assn"

sepref_definition pow_sub_extract_cond_impl [llvm_inline] is
  "uncurry (RETURN oo pow_sub_extract_cond)" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_extract_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding pow_sub_extract_cond_def Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  by sepref

lemma pow_sub_extract_cond_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_extract_cond_impl,
    uncurry (RETURN oo (PR_CONST pow_sub_extract_cond))) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a pow_sub_extract_state_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  using pow_sub_extract_cond_impl.refine by (simp add: PR_CONST_def)

definition pow_sub_extract_body :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> (nat \<times> gmp_poly) nres"
  where
  "pow_sub_extract_body h xs st \<equiv> doN {
     let (j, dst) = st;
     ASSERT (j * h < length xs);
     ASSERT (j * h < max_snat LENGTH(gmp_poly_len));
     ASSERT (j + 1 < max_snat LENGTH(gmp_poly_len));
     ASSERT (length dst + 1 < max_snat LENGTH(gmp_poly_len));
     c \<leftarrow> (PR_CONST poly_copy_coeff_monadic) xs (j * h);
     dst \<leftarrow> (PR_CONST poly_push_coeff_monadic) dst c;
     RETURN (j + 1, dst)
   }"

sepref_register "PR_CONST pow_sub_extract_body"
  :: "nat \<Rightarrow> gmp_poly \<Rightarrow> nat \<times> gmp_poly \<Rightarrow> (nat \<times> gmp_poly) nres"

text \<open>\<^bold>\<open>The body's HNR has no precondition.\<close> Every state-dependent need
  (\<open>j * h < length xs\<close>, \<open>j * h < max_snat\<close>, \<open>j + 1 < max_snat\<close>, \<open>length dst + 1 < max_snat\<close>)
  is an ASSERT inside the op; @{thm hn_ASSERT_bind} turns those into assumptions that
  discharge @{const poly_copy_coeff_monadic}'s \<open>j * h < length xs\<close> and
  @{const poly_push_coeff_monadic}'s \<open>length dst + 1 < max_snat\<close>.

  \<^bold>\<open>A declared precondition mentioning the loop state (\<open>j\<close>, \<open>dst\<close>) could not be discharged\<close>:
  @{thm hn_monadic_WHILE_lin}'s \<open>f_ref\<close> premise translates the body under
  \<open>\<And>s' s. I s' \<Longrightarrow> \<dots>\<close>, so the only thing known about the state there is the invariant; the loop
  condition (\<open>j < outlen\<close>), which bounds \<open>j\<close>, is not in scope. An op whose side conditions do not
  all solve does not fire, so the loop would stay untranslated.\<close>

sepref_definition pow_sub_extract_body_impl [llvm_code] is
  "uncurry2 pow_sub_extract_body" ::
  "(snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      pow_sub_extract_state_assn\<^sup>d \<rightarrow>\<^sub>a pow_sub_extract_state_assn"
  unfolding pow_sub_extract_body_def
  unfolding Let_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
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

lemma pow_sub_extract_body_impl_hnr[sepref_fr_rules]:
  "(uncurry2 pow_sub_extract_body_impl, uncurry2 (PR_CONST pow_sub_extract_body)) \<in>
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k *\<^sub>a
      pow_sub_extract_state_assn\<^sup>d \<rightarrow>\<^sub>a pow_sub_extract_state_assn"
  using pow_sub_extract_body_impl.refine by (simp add: PR_CONST_def)

section \<open>The result projection (owned-poly state)\<close>

text \<open>\<^bold>\<open>The post-loop destructure of an owned-polynomial state needs its own op\<close>, as for
  \<open>carried_left_shift_result_impl\<close> and \<open>ethorner_count_trunc_result_impl\<close>: the state is taken
  destructively (\<open>\<^sup>d\<close>) and the projection is the loop's tail, so the WHILEIT's continuation is a
  registered op rather than an inline destructure. (A pure state, such as detection's \<open>(i, g)\<close>,
  can be destructured inline.)\<close>

definition pow_sub_extract_result_mop :: "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres" where
  "pow_sub_extract_result_mop st \<equiv> (let (j, dst) = st in RETURN dst)"

sepref_register "PR_CONST pow_sub_extract_result_mop"
  :: "nat \<times> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition pow_sub_extract_result_impl [llvm_inline] is
  "pow_sub_extract_result_mop" ::
  "pow_sub_extract_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  unfolding pow_sub_extract_result_mop_def
  unfolding Let_def
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma pow_sub_extract_result_impl_hnr[sepref_fr_rules]:
  "(pow_sub_extract_result_impl,
    PR_CONST pow_sub_extract_result_mop) \<in>
    pow_sub_extract_state_assn\<^sup>d \<rightarrow>\<^sub>a gmp_poly_assn"
  using pow_sub_extract_result_impl.refine
  by (simp add: PR_CONST_def)

section \<open>The loop\<close>

text \<open>The invariant is the prefix identity \<open>dst = map (\<lambda>j'. xs ! (j' * h)) [0..<j]\<close>, which at
  \<open>j = outlen\<close> IS @{const pow_sub_extract}.\<close>

definition pow_sub_extract_monadic :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres" where
  "pow_sub_extract_monadic h xs \<equiv> doN {
     ASSERT (0 < h \<and> 0 < length xs
             \<and> length xs < max_snat LENGTH(gmp_poly_len));
     len \<leftarrow> (PR_CONST poly_length_monadic) xs;
     ASSERT (len = length xs \<and> 0 < len
             \<and> len < max_snat LENGTH(gmp_poly_len));
     q \<leftarrow> RETURN ((len - 1) div h);
     ASSERT (q + 1 < max_snat LENGTH(gmp_poly_len));
     outlen \<leftarrow> RETURN (q + 1);
     dst \<leftarrow> (PR_CONST poly_empty_sz_monadic) outlen;
     st \<leftarrow> WHILEIT
        (\<lambda>(j, dst). j \<le> pow_sub_extract_len h (length xs)
                    \<and> dst = map (\<lambda>j'. xs ! (j' * h)) [0..<j])
        (\<lambda>st. (PR_CONST pow_sub_extract_cond) outlen st)
        (\<lambda>st. (PR_CONST pow_sub_extract_body) h xs st)
        (0, dst);
     (PR_CONST pow_sub_extract_result_mop) st
   }"

lemma extract_index_lt:
  assumes h: "0 < h" and j: "j < pow_sub_extract_len h (length xs)" and ne: "0 < length xs"
  shows "j * h < length xs"
proof -
  have "j \<le> (length xs - 1) div h" using j by (simp add: pow_sub_extract_len_def)
  then have "j * h \<le> ((length xs - 1) div h) * h" using h by simp
  also have "\<dots> \<le> length xs - 1" by (rule div_times_less_eq_dividend)
  finally have le: "j * h \<le> length xs - 1" .
  have "length xs - 1 < length xs" using ne by simp
  with le show ?thesis by (rule le_less_trans)
qed

lemma idx_le_prod: "0 < h \<Longrightarrow> j \<le> j * h" for j h :: nat
  by (cases h) auto

text \<open>The output length fits whenever the input length does: \<open>(n-1) div h \<le> n-1 < n\<close>, so
  \<open>outlen \<le> n\<close>. Needed as an ASSERT on the BOUND variable \<open>q\<close> — a machine-word add must be
  shown not to overflow, and the SEPREF layer can only use a fact stated on the variable
  the goal actually names (\<open>bind_ref_tag\<close> is a tag, not an equation).\<close>
lemma extract_outlen_bound:
  fixes n m h :: nat
  assumes ne: "0 < n" and lt: "n < m"
  shows "Suc ((n - Suc 0) div h) < m"
  using ne lt Euclidean_Rings.div_le_dividend[of "n - Suc 0" h] by linarith

lemma pow_sub_extract_monadic_correct:
  assumes h: "0 < h" and ne: "0 < length xs"
    and len: "length xs < max_snat LENGTH(gmp_poly_len)"
  shows "pow_sub_extract_monadic h xs \<le> RETURN (pow_sub_extract h xs)"
  unfolding pow_sub_extract_monadic_def pow_sub_extract_body_def pow_sub_extract_cond_def
    pow_sub_extract_result_mop_def
    PR_CONST_def poly_copy_coeff_monadic_def poly_push_coeff_monadic_def
    poly_length_monadic_def poly_empty_sz_monadic_def
  apply (refine_vcg
         WHILEIT_rule[where R = "measure (\<lambda>(j, dst). pow_sub_extract_len h (length xs) - j)"])
  apply (all \<open>(auto simp: Let_def extract_index_lt pow_sub_extract_len_def
                          pow_sub_extract_def)?\<close>)
  subgoal using h by simp
  subgoal using ne by simp
  subgoal using len by simp
  \<comment> \<open>the output-length bound \<open>Suc ((n-1) div h) \<le> n\<close>, i.e. the ASSERT that the machine-word
     \<open>q + 1\<close> does not overflow. Take the \<open>max_snat\<close> bound from \<open>prems\<close> rather than restating
     it from \<open>len\<close>: \<open>auto\<close> has already normalised this goal, and \<open>linarith\<close> matches atoms
     syntactically, so a re-stated bound need not connect.\<close>
  subgoal premises prems
  proof -
    have d: "(length xs - Suc 0) div h \<le> length xs - Suc 0"
      by (rule Euclidean_Rings.div_le_dividend)
    have ne': "0 < length xs" using prems by simp
    from d ne' prems show ?thesis by linarith
  qed
  done
  \<comment> \<open>The \<open>len = length xs\<close> ASSERT added for the SEPREF layer also hands \<open>auto\<close> the bound
     \<open>aa \<le> aa \<cdot> h < length xs < max_snat\<close>, so no separate subgoal remains at this call site.\<close>

section \<open>The loop assembly\<close>

text \<open>\<^bold>\<open>Assembly\<close>: a body without precondition plus a result op taking the state by \<open>\<^sup>d\<close>, so
  nothing state-dependent reaches the loop boundary, and the result op is a plain projection.

  \<^bold>\<open>\<open>outlen\<close> is computed rather than left as @{const pow_sub_extract_len}\<close>: that constant has no
  registered op, so it would reach translation as an opaque \<open>RETURN\<close>. It is the machine arithmetic
  it denotes, \<open>(len - 1) div h + 1\<close>, split across two binds so that the overflow ASSERT can name the
  bound variable \<open>q\<close>; an ASSERT stated on the expression would not connect, because all translation
  knows about a bind result is \<open>bind_ref_tag\<close>, a tag rather than an equation.\<close>

sepref_register "PR_CONST pow_sub_extract_monadic" :: "nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly nres"

sepref_definition pow_sub_extract_impl [llvm_code] is
  "uncurry pow_sub_extract_monadic" ::
  "[\<lambda>(h, xs). 0 < h \<and> 0 < length xs
              \<and> length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  unfolding pow_sub_extract_monadic_def
  unfolding Let_def
  supply [sepref_fr_rules] =
    pow_sub_extract_cond_impl_hnr
    pow_sub_extract_body_impl_hnr
    pow_sub_extract_result_impl_hnr
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

lemma pow_sub_extract_impl_hnr[sepref_fr_rules]:
  "(uncurry pow_sub_extract_impl, uncurry (PR_CONST pow_sub_extract_monadic)) \<in>
    [\<lambda>(h, xs). 0 < h \<and> 0 < length xs
                \<and> length xs < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow> gmp_poly_assn"
  using pow_sub_extract_impl.refine by (simp add: PR_CONST_def)

end
