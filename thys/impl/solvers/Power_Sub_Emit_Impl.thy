theory Power_Sub_Emit_Impl
  imports Power_Sub_Extract_Impl
begin

text \<open>Per-interval emission: the back-map of one reduced interval, with the high endpoint
  (op \<open>pow_sub_backmap_iv_monadic\<close>).

  \<^bold>\<open>Only the low endpoint needs a search.\<close> \<open>Power_Sub_Root_Impl\<close>'s \<open>root_floor_gmp2\<close> returns the
  numerator of @{const pow_sub_lo}, \<open>\<lfloor>a\<^sup>1\<^sup>/\<^sup>h \<cdot> 2\<^sup>m\<rfloor>\<close>. The high endpoint is \<open>\<lceil>\<cdot>\<rceil>\<close> at the same \<open>m\<close>,
  and by \<open>ceiling_altdef\<close> it differs from the floor only when the scaled root is exactly an integer,
  which one exact integer comparison decides (\<open>pow_sub_hi_of_num\<close>). So the pair costs one
  bisection plus one \<open>mpz\<close> comparison.

  \<^bold>\<open>Which endpoint goes where.\<close> The emitted window shrinks the image of the reduced interval, so a
  proper \<open>Q\<close>-interval \<open>(a,b)\<close> emits \<open>(pow_sub_hi h m a, pow_sub_lo h m b)\<close>: the ceiling on the left and
  the floor on the right.\<close>

section \<open>Exactness: the same integer identity, with \<open>\<le>\<close> tightened to \<open>=\<close>\<close>

text \<open>A near-twin of @{const root_test_monadic}, differing only in the final comparison
  (\<open>sg = 0\<close> rather than \<open>sg \<le> 0\<close>). Written out rather than shared: the two have different
  post-conditions and the tree's rule is one op per registered constant. Ownership is
  identical — \<open>rhs\<close> and \<open>n\<close> are both KEPT, and the three intermediates are consumed.\<close>

definition root_exact_monadic :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool nres" where
  "root_exact_monadic h k rhs n \<equiv> do {
     ASSERT (0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len));
     p \<leftarrow> (PR_CONST mpz_pow_nat_monadic) n h;
     l \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) p k;
     d \<leftarrow> (PR_CONST mpz_sub.amop_r1) l rhs;
     sg \<leftarrow> (PR_CONST mpz_sgn_mop) d;
     (PR_CONST mpzb_discard_monadic) d;
     RETURN (sg = 0)
   }"

lemma root_exact_monadic_correct:
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
  shows "root_exact_monadic h k rhs n \<le> RETURN (n ^ h * 2 ^ k = rhs)"
  unfolding root_exact_monadic_def PR_CONST_def mpz_sgn_mop_def
    mpz_sub.amop_r1_def mpz_sub.aop_r1_def mpzb_discard_monadic_def
  using h hb k
  apply (refine_vcg
         mpz_pow_nat_monadic_correct[OF h hb, THEN order_trans]
         mpz_shift_left_snat_monadic_spec_plain[OF k, THEN order_trans])
  apply (auto simp: sgn_if)
  done

sepref_register "PR_CONST root_exact_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool nres"

sepref_definition root_exact_impl [llvm_code] is
  "uncurry3 root_exact_monadic" ::
  "[\<lambda>(((h, k), rhs), n). 0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
                          \<and> k < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> bool1_assn"
  unfolding root_exact_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma root_exact_impl_hnr[sepref_fr_rules]:
  "(uncurry3 root_exact_impl, uncurry3 (PR_CONST root_exact_monadic)) \<in>
    [\<lambda>(((h, k), rhs), n). 0 < h \<and> h < max_snat LENGTH(gmp_poly_len)
                          \<and> k < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k \<rightarrow> bool1_assn"
  using root_exact_impl.refine
  by (simp add: PR_CONST_def)

section \<open>The CEILING numerator\<close>

text \<open>\<^bold>\<open>The \<open>n + 1\<close> branch needs an mpz \<open>1\<close>, and the tree can build one\<close> —
  \<open>mpz_from_int 1\<close> under \<open>annot_sint_const gmp_int_t\<close>. What has no folding method is the
  \<open>uint\<close> argument of \<open>mpz_add_ui\<close>.

  \<^bold>\<open>Ownership.\<close> \<open>A\<close> is KEPT (the caller's coefficient). \<open>root_floor_gmp2\<close> hands back an OWNED
  \<open>n\<close>; on the exact branch that IS the answer, and on the other branch it is consumed by the
  addition's second slot — which KEEPS it — so it is discarded explicitly there.\<close>

definition pow_sub_ceil_monadic :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int nres" where
  "pow_sub_ceil_monadic h m A k \<equiv> do {
     ASSERT (0 < h \<and> 0 \<le> A \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> h * m < max_snat LENGTH(gmp_poly_len));
     n \<leftarrow> (PR_CONST root_floor_gmp2) h m A k;
     rhs \<leftarrow> (PR_CONST mpz_shift_left_snat_monadic) (COPY A) (h * m);
     e \<leftarrow> (PR_CONST root_exact_monadic) h k rhs n;
     (PR_CONST mpzb_discard_monadic) rhs;
     if e then RETURN n
     else do {
       one \<leftarrow> RETURN (mpz_from_int 1);
       r \<leftarrow> (PR_CONST mpz_add.amop_r1) one n;
       (PR_CONST mpzb_discard_monadic) n;
       RETURN r
     }
   }"

text \<open>\<^bold>\<open>The two branches, split out.\<close> \<open>pow_sub_hi_of_num\<close> concludes with an \<open>if\<close>, whose \<open>n\<close>
  occurs only in the RIGHT-hand side — so it is unusable as a rewrite (extra variable) and
  cannot be handed to \<open>simp\<close>. Splitting on the test puts every variable in the premises, which
  is what lets \<open>blast\<close> instantiate \<open>n\<close> from the refinement goal's own hypotheses instead of the
  proof naming it positionally.\<close>

lemma pow_sub_hi_num_exact:
  fixes A :: int and n :: int
  assumes h: "0 < h" and A0: "0 \<le> A" and adef: "a = real_of_int A / 2 ^ k"
    and ndef: "pow_sub_lo h m a = real_of_int n / 2 ^ m"
    and ex: "n ^ h * 2 ^ k = A * 2 ^ (h * m)"
  shows "pow_sub_hi h m a = real_of_int n / 2 ^ m"
  using pow_sub_hi_of_num[OF h A0 adef ndef] ex by simp

lemma pow_sub_hi_num_strict:
  fixes A :: int and n :: int
  assumes h: "0 < h" and A0: "0 \<le> A" and adef: "a = real_of_int A / 2 ^ k"
    and ndef: "pow_sub_lo h m a = real_of_int n / 2 ^ m"
    and ne: "n ^ h * 2 ^ k \<noteq> A * 2 ^ (h * m)"
  shows "pow_sub_hi h m a = real_of_int (1 + n) / 2 ^ m"
  using pow_sub_hi_of_num[OF h A0 adef ndef] ne by simp

text \<open>\<^bold>\<open>The chain, end to end\<close>: the synthesised LLVM op returns the numerator of
  @{const pow_sub_hi} for any dyadic \<open>a = A / 2\<^sup>k\<close>, at the same shared exponent \<open>m\<close> the low
  endpoint uses — which is what makes the emitted triple \<open>(lna, rnb, m)\<close> well-formed.\<close>

lemma pow_sub_ceil_monadic_is_pow_sub_hi:
  fixes A :: int
  assumes h: "0 < h" and A0: "0 \<le> A"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and hm: "h * m < max_snat LENGTH(gmp_poly_len)"
    and adef: "a = real_of_int A / 2 ^ k"
  shows "pow_sub_ceil_monadic h m A k
           \<le> SPEC (\<lambda>n. pow_sub_hi h m a = real_of_int n / 2 ^ m)"
  unfolding pow_sub_ceil_monadic_def PR_CONST_def mpzb_discard_monadic_def
    mpz_add.amop_r1_def mpz_add.aop_r1_def mpz_from_int_def COPY_def
  using h A0 hb k hm
  apply (refine_vcg
         root_floor_gmp2_is_pow_sub_lo[OF h A0 hb k hm adef, THEN order_trans]
         mpz_shift_left_snat_monadic_spec_plain[OF hm, THEN order_trans]
         root_exact_monadic_correct[OF h hb k, THEN order_trans])
  \<comment> \<open>order-independent on purpose: the ASSERT goal and the two back-map branches come out of
     \<open>refine_vcg\<close> in an order the proof should not encode\<close>
  apply (all \<open>(simp add: top_fun_def; fail)
              | (blast intro: pow_sub_hi_num_exact[OF h A0 adef]; fail)
              | (blast intro: pow_sub_hi_num_strict[OF h A0 adef]; fail)\<close>)
  done

sepref_register "PR_CONST pow_sub_ceil_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int nres"

sepref_definition pow_sub_ceil_impl [llvm_code] is
  "uncurry3 pow_sub_ceil_monadic" ::
  "[\<lambda>(((h, m), A), k). 0 < h \<and> 0 \<le> A \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  unfolding pow_sub_ceil_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_sint_const gmp_int_t)
  by sepref

lemma pow_sub_ceil_impl_hnr[sepref_fr_rules]:
  "(uncurry3 pow_sub_ceil_impl, uncurry3 (PR_CONST pow_sub_ceil_monadic)) \<in>
    [\<lambda>(((h, m), A), k). 0 < h \<and> 0 \<le> A \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k \<rightarrow> mpzb_assn"
  using pow_sub_ceil_impl.refine
  by (simp add: PR_CONST_def)

section \<open>The per-interval emit\<close>

text \<open>\<^bold>\<open>One \<open>Q\<close>-interval in, one \<open>P\<close>-window out, at a shared exponent \<open>m\<close>.\<close> The pair is
  \<open>(pow_sub_hi h m a, pow_sub_lo h m b)\<close>, so the emitted window is a subinterval of
  \<open>(a\<^sup>1\<^sup>/\<^sup>h, b\<^sup>1\<^sup>/\<^sup>h)\<close> and soundness needs no endpoint hypothesis. Both inputs are kept: \<open>A\<close> and \<open>B\<close>
  are the caller's interval endpoints, and the entry re-emits them at higher precision if the
  certify step rejects.

  \<open>m\<close> is shared rather than per-endpoint because the interface carries one exponent per triple; the
  grid-monotonicity lemmas (\<open>pow_sub_lo_grid_mono\<close>, \<open>pow_sub_hi_grid_mono\<close>) let the two convergence
  witnesses be merged onto \<open>max m\<^sub>1 m\<^sub>2\<close>.\<close>

definition pow_sub_backmap_iv_monadic ::
  "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (int \<times> int) nres" where
  "pow_sub_backmap_iv_monadic h m A B k \<equiv> do {
     ASSERT (0 < h \<and> 0 \<le> A \<and> 0 \<le> B \<and> h < max_snat LENGTH(gmp_poly_len)
             \<and> k < max_snat LENGTH(gmp_poly_len)
             \<and> h * m < max_snat LENGTH(gmp_poly_len));
     lna \<leftarrow> (PR_CONST pow_sub_ceil_monadic) h m A k;
     rnb \<leftarrow> (PR_CONST root_floor_gmp2) h m B k;
     RETURN (lna, rnb)
   }"

lemma pow_sub_backmap_iv_monadic_correct:
  fixes A B :: int
  assumes h: "0 < h" and A0: "0 \<le> A" and B0: "0 \<le> B"
    and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and k: "k < max_snat LENGTH(gmp_poly_len)"
    and hm: "h * m < max_snat LENGTH(gmp_poly_len)"
    and adef: "a = real_of_int A / 2 ^ k" and bdef: "b = real_of_int B / 2 ^ k"
  shows "pow_sub_backmap_iv_monadic h m A B k
           \<le> SPEC (\<lambda>(l, r). pow_sub_hi h m a = real_of_int l / 2 ^ m
                             \<and> pow_sub_lo h m b = real_of_int r / 2 ^ m)"
  unfolding pow_sub_backmap_iv_monadic_def PR_CONST_def
  using h A0 B0 hb k hm
  apply (refine_vcg
         pow_sub_ceil_monadic_is_pow_sub_hi[OF h A0 hb k hm adef, THEN order_trans]
         root_floor_gmp2_is_pow_sub_lo[OF h B0 hb k hm bdef, THEN order_trans])
  apply (all \<open>(simp; fail) | blast\<close>)
  done

sepref_register "PR_CONST pow_sub_backmap_iv_monadic"
  :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (int \<times> int) nres"

sepref_definition pow_sub_backmap_iv_impl [llvm_code] is
  "uncurry4 pow_sub_backmap_iv_monadic" ::
  "[\<lambda>((((h, m), A), B), k). 0 < h \<and> 0 \<le> A \<and> 0 \<le> B
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k
    \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  unfolding pow_sub_backmap_iv_monadic_def
  supply [sepref_frame_free_rules] = mk_free_is_pure mpzb_assn_free
  apply (annot_sint_const gmp_int_t)?
  by sepref

lemma pow_sub_backmap_iv_impl_hnr[sepref_fr_rules]:
  "(uncurry4 pow_sub_backmap_iv_impl, uncurry4 (PR_CONST pow_sub_backmap_iv_monadic)) \<in>
    [\<lambda>((((h, m), A), B), k). 0 < h \<and> 0 \<le> A \<and> 0 \<le> B
       \<and> h < max_snat LENGTH(gmp_poly_len)
       \<and> k < max_snat LENGTH(gmp_poly_len)
       \<and> h * m < max_snat LENGTH(gmp_poly_len)]\<^sub>a
    (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k
    \<rightarrow> mpzb_assn \<times>\<^sub>a mpzb_assn"
  using pow_sub_backmap_iv_impl.refine
  by (simp add: PR_CONST_def)

end
