theory Lowdeg_Split
  imports Lowdeg Split_Bisection
begin

text \<open>The low-degree dispatch: decide once whether the closed form of \<open>Lowdeg\<close> applies, and if
  it does emit both arms' windows directly; otherwise hand the whole input to the bisection solve
  unchanged.

  \<^bold>\<open>One classification serves both arms.\<close> Both discriminants are invariant under the reflection
  \<open>x \<mapsto> -x\<close>, so one computation decides both arms; only the per-arm root count differs, and it is
  read off the coefficient signs.

  \<^bold>\<open>The class code.\<close> \<open>0\<close> fall through · \<open>1\<close> no positive root on either arm · \<open>2\<close> one on the
  positive arm only · \<open>3\<close> one on the reflected arm only · \<open>4\<close> one on each.
  A \<open>bool \<times> bool\<close> would read better, but Sepref's \<open>trans\<close> phase does not handle its \<open>fst\<close>/\<open>snd\<close>
  projections.

  Degree 2, \<open>disc2 > 0\<close>: the roots straddle zero exactly when \<open>a\<^sub>2*a\<^sub>0 < 0\<close>, so that one test is both
  the condition under which the closed form applies and the count on each arm; the pipeline's
  split at zero separates them. When the roots share a sign, a separator is computed (below).
  Degree 3, \<open>disc3 < 0\<close>: exactly one real root, whose sign is \<open>- sign (a\<^sub>3*a\<^sub>0)\<close>, and \<open>a\<^sub>0 = 0\<close>
  puts it at the origin, where \<open>dsc_split_zero_check_monadic\<close> reports it.\<close>

definition lowdeg_class_monadic :: "gmp_poly \<Rightarrow> nat nres" where
"lowdeg_class_monadic xs \<equiv> doN {
  len \<leftarrow> (PR_CONST poly_length_monadic) xs;
  if len = 3 then doN {
    sD \<leftarrow> (PR_CONST lowdeg_disc2_sgn_monadic) xs 0 1 2;
    if sD < 0 then RETURN 1
    else if 0 < sD then doN {
      sp \<leftarrow> (PR_CONST lowdeg_sgn_prod_monadic) xs 2 0;
      if sp = 1 then RETURN 4
      else if sp = 2 then doN {
         \<comment> \<open>\<^bold>\<open>Both roots share a sign.\<close> \<open>sign (a\<^sub>2*a\<^sub>1)\<close> says which, since their sum is
            \<open>-a\<^sub>1/a\<^sub>2\<close>: a negative product means both are positive. \<open>sb = 0\<close> cannot occur here
            (\<open>a\<^sub>1 = 0\<close> with \<open>a\<^sub>2*a\<^sub>0 > 0\<close> forces \<open>disc2 < 0\<close>), and falling through on it is correct
            anyway. The separator is checked by the integer bridge @{const lowdeg_sep_ok_pure} /
            \<open>lowdeg_sep_bridge\<close>. \<^bold>\<open>The \<open>rf\<close> argument is the arm that will emit\<close>: on class 6 that is
            the reflection, whose \<open>a\<^sub>1\<close> is negated, and passing \<open>rf = True\<close> checks it without a clone.\<close>
         sb \<leftarrow> (PR_CONST lowdeg_sgn_prod_monadic) xs 2 1;
         if sb = 1 then doN {
           ok \<leftarrow> (PR_CONST lowdeg_sep_ok_monadic) False xs;
           if ok then RETURN 5 else RETURN 0
         } else if sb = 2 then doN {
           ok \<leftarrow> (PR_CONST lowdeg_sep_ok_monadic) True xs;
           if ok then RETURN 6 else RETURN 0
         } else RETURN 0
      } else RETURN 0
    } else RETURN 0
  } else if len = 4 then doN {
    sE \<leftarrow> (PR_CONST lowdeg_disc3_sgn_monadic) xs;
    if sE < 0 then doN {
      sp \<leftarrow> (PR_CONST lowdeg_sgn_prod_monadic) xs 3 0;
      if sp = 1 then RETURN 2 else if sp = 2 then RETURN 3 else RETURN 1
    } else RETURN 0
  } else RETURN 0
}"

sepref_register "PR_CONST lowdeg_class_monadic" :: "gmp_poly \<Rightarrow> nat nres"

sepref_definition lowdeg_class_impl [llvm_code] is
  "lowdeg_class_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  unfolding lowdeg_class_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  apply (annot_sint_const gmp_int_t)
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma lowdeg_class_impl_hnr[sepref_fr_rules]:
  "(lowdeg_class_impl, PR_CONST lowdeg_class_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE(gmp_poly_len)"
  using lowdeg_class_impl.refine by (simp add: PR_CONST_def)

text \<open>The reflected arm.  The clone and the reflection happen ONLY when this arm actually emits
  --- on the classes where it does not (\<open>1\<close> and \<open>2\<close>, which together are most of the degree-3
  workload) the whole \<open>poly_clone\<close> is skipped, which the per-arm version could not do because it
  had to reflect before it could classify.\<close>
definition lowdeg_emit_neg_monadic :: "bool \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"lowdeg_emit_neg_monadic one xs \<equiv>
  (if one then doN {
     ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
     Qb \<leftarrow> (PR_CONST poly_clone_monadic) xs;
     Qb \<leftarrow> (PR_CONST poly_reflect_in_place_monadic) Qb;
     accQ \<leftarrow> (PR_CONST lowdeg_emit_pos_monadic) True Qb;
     (PR_CONST poly_free_monadic) Qb;
     RETURN accQ
   } else (PR_CONST lowdeg_vec_empty_sz_monadic) 0)"

sepref_register "PR_CONST lowdeg_emit_neg_monadic"
  :: "bool \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition lowdeg_emit_neg_impl [llvm_code] is
  "uncurry lowdeg_emit_neg_monadic" ::
  "bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding lowdeg_emit_neg_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma lowdeg_emit_neg_impl_hnr[sepref_fr_rules]:
  "(uncurry lowdeg_emit_neg_impl, uncurry (PR_CONST lowdeg_emit_neg_monadic)) \<in>
    bool1_assn\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using lowdeg_emit_neg_impl.refine by (simp add: PR_CONST_def)

text \<open>Class 6: both roots negative, so the REFLECTED arm carries two windows.  The clone is
  reflected first and @{const lowdeg_emit_two_pos_monadic} then runs on it unchanged --- its \<open>q\<close>
  is recomputed from the clone, whose \<open>b\<close> is already negated, which is exactly the \<open>rf = True\<close>
  computation the classification checked on the original.\<close>
definition lowdeg_emit_two_neg_monadic :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"lowdeg_emit_two_neg_monadic xs \<equiv> doN {
  ASSERT (length xs + 1 < max_snat LENGTH(gmp_poly_len));
  Qb \<leftarrow> (PR_CONST poly_clone_monadic) xs;
  Qb \<leftarrow> (PR_CONST poly_reflect_in_place_monadic) Qb;
  accQ \<leftarrow> (PR_CONST lowdeg_emit_two_pos_monadic) Qb;
  (PR_CONST poly_free_monadic) Qb;
  RETURN accQ
}"

sepref_register "PR_CONST lowdeg_emit_two_neg_monadic"
  :: "gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres"

sepref_definition lowdeg_emit_two_neg_impl [llvm_code] is
  "lowdeg_emit_two_neg_monadic" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  unfolding lowdeg_emit_two_neg_monadic_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")?
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma lowdeg_emit_two_neg_impl_hnr[sepref_fr_rules]:
  "(lowdeg_emit_two_neg_impl, PR_CONST lowdeg_emit_two_neg_monadic) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a gmp_dyadic_interval_vec_assn"
  using lowdeg_emit_two_neg_impl.refine by (simp add: PR_CONST_def)

definition lowdeg_isolate_all_split_main ::
  "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres" where
"lowdeg_isolate_all_split_main xs \<equiv> doN {
  ASSERT (2 \<le> length xs);
  cl \<leftarrow> (PR_CONST lowdeg_class_monadic) xs;
  (if cl = 0 then (PR_CONST bisection_isolate_all_split_main) xs
   else doN {
     accP \<leftarrow> (if cl = 5 then (PR_CONST lowdeg_emit_two_pos_monadic) xs
                        else (PR_CONST lowdeg_emit_pos_monadic) (cl = 2 \<or> cl = 4) xs);
     accQ \<leftarrow> (if cl = 6 then (PR_CONST lowdeg_emit_two_neg_monadic) xs
                        else (PR_CONST lowdeg_emit_neg_monadic) (cl = 3 \<or> cl = 4) xs);
     xs0 \<leftarrow> (PR_CONST dsc_split_zero_check_monadic) xs;
     RETURN (accP, accQ, xs0)
   })
}"

sepref_register "PR_CONST lowdeg_isolate_all_split_main"
  :: "gmp_poly \<Rightarrow> (gmp_dyadic_interval_vec \<times> gmp_dyadic_interval_vec \<times> bool) nres"

sepref_definition lowdeg_isolate_all_split_main_impl [llvm_code] is
  "lowdeg_isolate_all_split_main" ::
  "gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
    gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  unfolding lowdeg_isolate_all_split_main_def
  apply (annot_snat_const "TYPE(gmp_poly_len)")
  supply [sepref_frame_free_rules] = mk_free_is_pure
  by sepref

lemma lowdeg_isolate_all_split_main_impl_hnr[sepref_fr_rules]:
  "(lowdeg_isolate_all_split_main_impl, PR_CONST lowdeg_isolate_all_split_main) \<in>
    gmp_poly_assn\<^sup>k \<rightarrow>\<^sub>a
      gmp_dyadic_interval_vec_assn \<times>\<^sub>a gmp_dyadic_interval_vec_assn \<times>\<^sub>a bool1_assn"
  using lowdeg_isolate_all_split_main_impl.refine by (simp add: PR_CONST_def)

end
