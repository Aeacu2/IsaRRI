theory Public_Export
imports
  "IsaRRI_LLVM.Power_Sub_Entry_Impl"
  "IsaRRI_LLVM.Lowdeg_Split"
begin

text \<open>The exported C interface: one entry and two GMP helpers.

  The entry dispatches on the coefficient count. Below degree 9 it runs the low-degree solve;
  otherwise it runs the power-substitution entry, and when no substitution applies it runs the
  deflating solve on the input. On the substituting path the reduced polynomial's windows are
  stored into both output triples (the negative half is kept in reflected coordinates), so the
  copy loop that does not free its vector is called twice and the vector is freed once.

  Caller obligations are not checked at run time; see \<open>Isarri_Correct\<close> for the theorem and
  its hypotheses.\<close>

definition [llvm_code]:
  "hybrid_store_interval_vec
    (out_count :: gmp_poly_len word ptr)
    (out_lna :: mpz_t ptr) (out_rnb :: mpz_t ptr)
    (out_k :: gmp_poly_len word ptr)
    (out_cap :: gmp_poly_len word)
    acc \<equiv>
    doM {
      let (lns, rns, ks) = acc;
      acc_len \<leftarrow> arl_len lns;
      ll_store acc_len out_count;
      llc_while
        (\<lambda>i. doM {
          in_acc \<leftarrow> ll_icmp_ult i acc_len;
          in_cap \<leftarrow> ll_icmp_ult i out_cap;
          ll_and in_acc in_cap
        })
        (\<lambda>i. doM {
          src_lna \<leftarrow> arl_nth lns i;
          src_rnb \<leftarrow> arl_nth rns i;
          src_k \<leftarrow> arl_nth ks i;
          p_lna \<leftarrow> ll_ofs_ptr out_lna i;
          dst_lna \<leftarrow> ll_load p_lna;
          dst_lna \<leftarrow> raw_mpz_set dst_lna src_lna;
          p_rnb \<leftarrow> ll_ofs_ptr out_rnb i;
          dst_rnb \<leftarrow> ll_load p_rnb;
          dst_rnb \<leftarrow> raw_mpz_set dst_rnb src_rnb;
          p_k \<leftarrow> ll_ofs_ptr out_k i;
          ll_store src_k p_k;
          i \<leftarrow> ll_add i (signed_nat 1);
          Mreturn i
        })
        (signed_nat 0 :: gmp_poly_len word);
      dyadic_interval_vec_free_impl acc
    }"

definition [llvm_code]:
  "store_interval_vec_keep
    (out_count :: gmp_poly_len word ptr)
    (out_lna :: mpz_t ptr) (out_rnb :: mpz_t ptr)
    (out_k :: gmp_poly_len word ptr)
    (out_cap :: gmp_poly_len word)
    acc \<equiv>
    doM {
      let (lns, rns, ks) = acc;
      acc_len \<leftarrow> arl_len lns;
      ll_store acc_len out_count;
      llc_while
        (\<lambda>i. doM {
          in_acc \<leftarrow> ll_icmp_ult i acc_len;
          in_cap \<leftarrow> ll_icmp_ult i out_cap;
          ll_and in_acc in_cap
        })
        (\<lambda>i. doM {
          src_lna \<leftarrow> arl_nth lns i;
          src_rnb \<leftarrow> arl_nth rns i;
          src_k \<leftarrow> arl_nth ks i;
          p_lna \<leftarrow> ll_ofs_ptr out_lna i;
          dst_lna \<leftarrow> ll_load p_lna;
          dst_lna \<leftarrow> raw_mpz_set dst_lna src_lna;
          p_rnb \<leftarrow> ll_ofs_ptr out_rnb i;
          dst_rnb \<leftarrow> ll_load p_rnb;
          dst_rnb \<leftarrow> raw_mpz_set dst_rnb src_rnb;
          p_k \<leftarrow> ll_ofs_ptr out_k i;
          ll_store src_k p_k;
          i \<leftarrow> ll_add i (signed_nat 1);
          Mreturn i
        })
        (signed_nat 0 :: gmp_poly_len word);
      Mreturn ()
    }"

definition [llvm_code]:
  "isarri_wrapper
    (out_pos_count :: gmp_poly_len word ptr)
    (out_pos_lna :: mpz_t ptr) (out_pos_rnb :: mpz_t ptr)
    (out_pos_k :: gmp_poly_len word ptr)
    (out_neg_count :: gmp_poly_len word ptr)
    (out_neg_lna :: mpz_t ptr) (out_neg_rnb :: mpz_t ptr)
    (out_neg_k :: gmp_poly_len word ptr)
    (out_xs0 :: gmp_poly_len word ptr)
    (out_ok :: gmp_poly_len word ptr)
    (out_cap :: gmp_poly_len word)
    (nfloor :: gmp_poly_len word)
    (hcap :: gmp_poly_len word)
    (dlt :: gmp_poly_len word)
    (len :: gmp_poly_len word) (coeff_ptrs :: mpz_t ptr) \<equiv>
    doM {
      small \<leftarrow> ll_icmp_ult len (signed_nat 10);
      llc_if small
        (doM {
          ll_store (signed_nat 0) out_ok;
          (accP, accQ, xs0b) \<leftarrow> lowdeg_isolate_all_split_main_impl (len, len, coeff_ptrs);
          hybrid_store_interval_vec
            out_pos_count out_pos_lna out_pos_rnb out_pos_k out_cap accP;
          hybrid_store_interval_vec
            out_neg_count out_neg_lna out_neg_rnb out_neg_k out_cap accQ;
          xs0_w \<leftarrow> (if to_bool xs0b then Mreturn (signed_nat 1) else Mreturn (signed_nat 0));
          ll_store xs0_w out_xs0
        })
        (doM {
      (out, xs0, ok) \<leftarrow> pow_sub_entry_impl nfloor hcap dlt (len, len, coeff_ptrs);
      ok_w \<leftarrow> (if to_bool ok then Mreturn (signed_nat 1) else Mreturn (signed_nat 0));
      ll_store ok_w out_ok;
      llc_if ok
        (doM {
          store_interval_vec_keep
            out_pos_count out_pos_lna out_pos_rnb out_pos_k out_cap out;
          store_interval_vec_keep
            out_neg_count out_neg_lna out_neg_rnb out_neg_k out_cap out;
          dyadic_interval_vec_free_impl out;
          xs0_w \<leftarrow> (if to_bool xs0 then Mreturn (signed_nat 1) else Mreturn (signed_nat 0));
          ll_store xs0_w out_xs0
        })
        (doM {
          dyadic_interval_vec_free_impl out;
          (accP, accQ, xs0f) \<leftarrow> defl_isolate_all_split_main_impl (len, len, coeff_ptrs);
          hybrid_store_interval_vec
            out_pos_count out_pos_lna out_pos_rnb out_pos_k out_cap accP;
          hybrid_store_interval_vec
            out_neg_count out_neg_lna out_neg_rnb out_neg_k out_cap accQ;
          xs0_w \<leftarrow> (if to_bool xs0f then Mreturn (signed_nat 1) else Mreturn (signed_nat 0));
          ll_store xs0_w out_xs0
        })
        })
    }"

export_llvm
  "isarri_wrapper ::
    gmp_poly_len word ptr \<Rightarrow>
      mpz_t ptr \<Rightarrow> mpz_t ptr \<Rightarrow>
      gmp_poly_len word ptr \<Rightarrow>
      gmp_poly_len word ptr \<Rightarrow>
      mpz_t ptr \<Rightarrow> mpz_t ptr \<Rightarrow>
      gmp_poly_len word ptr \<Rightarrow>
      gmp_poly_len word ptr \<Rightarrow>
      gmp_poly_len word ptr \<Rightarrow>
      gmp_poly_len word \<Rightarrow>
      gmp_poly_len word \<Rightarrow>
      gmp_poly_len word \<Rightarrow>
      gmp_poly_len word \<Rightarrow>
      gmp_poly_len word \<Rightarrow> mpz_t ptr \<Rightarrow> _"
    is "isarri"
  "mpzb_sgn_impl" is "int32_t isarri_mpz_sgn(gmp_mpz_struct*)"
  "mpzb_free" is "void isarri_mpz_free(gmp_mpz_struct*)"
  file "../../export/isarri.ll"

end
