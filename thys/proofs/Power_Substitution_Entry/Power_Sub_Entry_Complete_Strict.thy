theory Power_Sub_Entry_Complete_Strict
  imports Power_Sub_Entry_Sound
begin

text \<open>\<^bold>\<open>Strict-or-degenerate completeness of the power-substitution entry.\<close>
  @{thm [source] pow_sub_entry_monadic_complete_of_pre} places every real root of the input in the
  CLOSED hull of an emitted window or of its reflection. That admits a root on a proper window's
  endpoint, which the window does not isolate. This theory proves the strong form: every real root
  lies strictly inside an emitted window or its reflection, or a window is exactly that root.

  The strict facts already existed and were weakened at the point of statement: the proper branch
  (@{thm [source] pow_sub_loop_tst_pair_ok_strong}) proves \<open>u\<^sup>h < y < v\<^sup>h\<close>, and the inexact
  degenerate branch is strict because the floor bound is an equality only in the exact case, which
  emits the point itself. The original statements are untouched; each lemma here is a strict twin.\<close>

lemma pow_sub_deg_exact_of_pow:
  fixes A L :: int
  assumes pw: "(real_of_int L / 2 ^ m) ^ h = real_of_int A / 2 ^ k"
  shows "L ^ h * 2 ^ k = A * 2 ^ (h * m)"
proof -
  have "(real_of_int L / 2 ^ m) ^ h = real_of_int (L ^ h) / 2 ^ (h * m)"
    by (rule real_div_pow_pow)
  with pw have "real_of_int (L ^ h) / 2 ^ (h * m) = real_of_int A / 2 ^ k" by simp
  then have "real_of_int (L ^ h) * 2 ^ k = real_of_int A * 2 ^ (h * m)"
    by (simp add: field_simps)
  then have "real_of_int (L ^ h * 2 ^ k) = real_of_int (A * 2 ^ (h * m))" by simp
  then show ?thesis by (simp only: of_int_eq_iff)
qed

lemma pow_sub_deg_tst_cover_strict:
  fixes A L R :: int
  assumes h: "0 < h" and A0: "0 \<le> A"
    and Ldef: "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
    and Rdef: "R = (if L ^ h * 2 ^ k = A * 2 ^ (h * m) then L else 1 + L)"
  shows "((real_of_int L / 2 ^ m) ^ h < real_of_int A / 2 ^ k
          \<and> real_of_int A / 2 ^ k < (real_of_int R / 2 ^ m) ^ h)
       \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ h = real_of_int A / 2 ^ k)"
proof (cases "L ^ h * 2 ^ k = A * 2 ^ (h * m)")
  case True
  then show ?thesis using Rdef pow_sub_deg_exact_pow[OF True] by simp
next
  case False
  define a where "a = real_of_int A / 2 ^ k"
  have a0: "0 \<le> a" unfolding a_def using A0 by simp
  have R: "R = 1 + L" using Rdef False by simp
  have uLo: "real_of_int L / 2 ^ m = pow_sub_lo h m a"
    unfolding Ldef a_def[symmetric] by (simp add: pow_sub_lo_num)
  have le: "(real_of_int L / 2 ^ m) ^ h \<le> a"
    unfolding uLo by (rule pow_sub_lo_pow_le[OF a0 h])
  have ne: "(real_of_int L / 2 ^ m) ^ h \<noteq> a"
    using pow_sub_deg_exact_of_pow False unfolding a_def by blast
  have bnd: "a powr (1 / real h) - 1 / 2 ^ m < pow_sub_lo h m a"
    using pow_sub_lo_bounds[OF a0] by blast
  have "a powr (1 / real h) < pow_sub_lo h m a + 1 / 2 ^ m" using bnd by linarith
  also have "\<dots> = real_of_int (1 + L) / 2 ^ m" unfolding uLo[symmetric] by (simp add: field_simps)
  finally have lt: "a powr (1 / real h) < real_of_int (1 + L) / 2 ^ m" .
  have "a = (a powr (1 / real h)) ^ h" using a0 h by (rule powr_root_pow[symmetric])
  also have "\<dots> < (real_of_int (1 + L) / 2 ^ m) ^ h"
    using lt h by (intro power_strict_mono) auto
  finally have hi: "a < (real_of_int R / 2 ^ m) ^ h" unfolding R .
  show ?thesis using le ne hi unfolding a_def by auto
qed

theorem pow_sub_emit_ok_pair_ok_strict:
  fixes Q0 :: "int poly" and A B :: int
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len: "0 < length q"
    and A0: "0 \<le> A" and B0: "0 \<le> B" and AB: "A \<le> B"
    and iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    and ok: "pow_sub_emit_ok h q ((A, B), k) ((L, R), m)"
  shows "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
    \<and> (\<forall>y. poly Q y = 0
        \<longrightarrow> (if A = B then y = real_of_int A / 2 ^ k
             else real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
        \<longrightarrow> ((real_of_int L / 2 ^ m) ^ h < y \<and> y < (real_of_int R / 2 ^ m) ^ h)
            \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ h = y))"
proof (cases "A = B")
  case True
  have tst: "pow_sub_deg_tst h A k q m"
    and Ld: "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
    and Rd: "R = (if L ^ h * 2 ^ k = A * 2 ^ (h * m) then L else 1 + L)"
    using ok True unfolding pow_sub_emit_ok_def by (simp_all add: Let_def)
  have iv': "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int A / 2 ^ k)"
    using iv True by simp
  have pk: "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
    by (rule pow_sub_deg_tst_pair_ok[OF h Pdef sf Qdef qdef len A0 iv' tst Ld Rd])
  have cov: "((real_of_int L / 2 ^ m) ^ h < real_of_int A / 2 ^ k
          \<and> real_of_int A / 2 ^ k < (real_of_int R / 2 ^ m) ^ h)
       \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ h = real_of_int A / 2 ^ k)"
    by (rule pow_sub_deg_tst_cover_strict[OF h A0 Ld Rd])
  show ?thesis using pk cov True by auto
next
  case False
  have ab: "real_of_int A / 2 ^ k < real_of_int B / 2 ^ k"
    using AB False by (simp add: divide_strict_right_mono)
  have tst: "pow_sub_loop_tst h A B k q m"
    and Ld: "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
    and Rd: "R = pow_sub_num_lo h m (real_of_int B / 2 ^ k)"
    using ok False unfolding pow_sub_emit_ok_def by (simp_all add: Let_def)
  show ?thesis
    using pow_sub_loop_tst_pair_ok_strong[OF h Pdef sf Qdef qdef len A0 B0 ab iv tst Ld Rd]
          False by auto
qed

lemma pow_sub_window_covers_lift_strict:
  fixes x u v :: real
  assumes d: "0 < d" and ev: "even d"
    and u0: "0 \<le> u" and v0: "0 \<le> v"
    and cov: "(u ^ d < x ^ d \<and> x ^ d < v ^ d) \<or> (u = v \<and> u ^ d = x ^ d)"
  shows "(u < x \<and> x < v \<or> u = x \<and> v = x)
       \<or> (- v < x \<and> x < - u \<or> - v = x \<and> - u = x)"
proof -
  have abs_pow: "\<bar>x\<bar> ^ d = x ^ d" using ev by (simp add: power_even_abs)
  have a0: "0 \<le> \<bar>x\<bar>" by simp
  obtain n where dn: "d = Suc n" using d by (cases d) auto
  have ax: "(u < \<bar>x\<bar> \<and> \<bar>x\<bar> < v) \<or> (u = v \<and> u = \<bar>x\<bar>)"
    using cov
  proof (elim disjE conjE)
    assume lo: "u ^ d < x ^ d" and hi: "x ^ d < v ^ d"
    have "u < \<bar>x\<bar>"
      using lo abs_pow by (metis a0 power_less_imp_less_base)
    moreover have "\<bar>x\<bar> < v"
      using hi abs_pow by (metis v0 power_less_imp_less_base)
    ultimately show ?thesis by simp
  next
    assume uv: "u = v" and eq: "u ^ d = x ^ d"
    have "u ^ Suc n = \<bar>x\<bar> ^ Suc n" using eq abs_pow dn by simp
    then have "u = \<bar>x\<bar>" using u0 a0 by (rule power_eq_imp_eq_base) simp
    with uv show ?thesis by simp
  qed
  show ?thesis
  proof (cases "0 \<le> x")
    case True
    then show ?thesis using ax by auto
  next
    case False
    then have "\<bar>x\<bar> = - x" by simp
    then show ?thesis using ax by auto
  qed
qed

lemma pow_sub_backmap_cover_of_post_strict:
  fixes Q0 :: "int poly" and y :: real
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len0: "0 < length q"
    and isoQ: "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
          (case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
    and covQ: "\<exists>j A B k. j < length (dyadic_interval_vec_triples accQ)
          \<and> dyadic_interval_vec_triples accQ ! j = ((A, B), k)
          \<and> ((real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
             \<or> (real_of_int A / 2 ^ k = y \<and> real_of_int B / 2 ^ k = y))"
    and pre: "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
          pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)"
    and lenEq: "length (dyadic_interval_vec_triples out)
                  = length (dyadic_interval_vec_triples accQ)"
    and emit: "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
          pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                              (dyadic_interval_vec_triples out ! j)"
    and ry: "poly Q y = 0"
  shows "\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
      \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
      \<and> 0 \<le> L \<and> L \<le> R
      \<and> (((real_of_int L / 2 ^ m) ^ h < y \<and> y < (real_of_int R / 2 ^ m) ^ h)
         \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ h = y))"
proof -
  from covQ obtain j A B k where jn: "j < length (dyadic_interval_vec_triples accQ)"
    and inj: "dyadic_interval_vec_triples accQ ! j = ((A, B), k)"
    and bnds: "(real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
                \<or> (real_of_int A / 2 ^ k = y \<and> real_of_int B / 2 ^ k = y)" by blast
  obtain L R m where outj: "dyadic_interval_vec_triples out ! j = ((L, R), m)"
    by (metis surj_pair)
  have A0: "0 \<le> A" and B0: "0 \<le> B"
    using pre[OF jn] unfolding inj pow_sub_iv_pre_def by (simp_all add: Let_def)
  have iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    using isoQ[OF jn] unfolding inj by simp
  have AB: "A \<le> B"
  proof -
    have "real_of_int A / 2 ^ k \<le> real_of_int B / 2 ^ k"
      using iv unfolding dsc_pair_ok_def by auto
    thus ?thesis by (simp add: divide_right_mono_neg field_simps)
  qed
  have branch: "if A = B then y = real_of_int A / 2 ^ k
                else real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k"
  proof (cases "A = B")
    case True
    then show ?thesis using bnds by auto
  next
    case False
    have "real_of_int A / 2 ^ k \<noteq> real_of_int B / 2 ^ k"
      using False by simp
    then show ?thesis using bnds False by auto
  qed
  have emitb: "dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
      \<and> (\<forall>y. poly Q y = 0
          \<longrightarrow> (if A = B then y = real_of_int A / 2 ^ k
               else real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
          \<longrightarrow> ((real_of_int L / 2 ^ m) ^ h < y \<and> y < (real_of_int R / 2 ^ m) ^ h)
              \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ h = y))"
    by (rule pow_sub_emit_ok_pair_ok_strict[OF h Pdef sf Qdef qdef len0 A0 B0 AB iv
              emit[OF jn, unfolded inj outj]])
  have cov: "((real_of_int L / 2 ^ m) ^ h < y \<and> y < (real_of_int R / 2 ^ m) ^ h)
              \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ h = y)"
    using emitb branch ry by blast
  have L0: "0 \<le> L"
  proof (cases "A = B")
    case True
    have "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
      using emit[OF jn, unfolded inj outj] True
      unfolding pow_sub_emit_ok_def by (simp add: Let_def)
    then show ?thesis using pow_sub_num_lo_nonneg[OF A0] by simp
  next
    case False
    have "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
      using emit[OF jn, unfolded inj outj] False
      unfolding pow_sub_emit_ok_def by (simp add: Let_def)
    then show ?thesis using pow_sub_num_hi_nonneg[OF A0] by simp
  qed
  have LR: "L \<le> R"
  proof -
    have "real_of_int L / 2 ^ m \<le> real_of_int R / 2 ^ m"
      using emitb unfolding dsc_pair_ok_def by auto
    thus ?thesis by (simp add: divide_right_mono_neg field_simps)
  qed
  show ?thesis
  proof (intro exI conjI)
    show "j < length (dyadic_interval_vec_triples out)" using jn lenEq by simp
    show "dyadic_interval_vec_triples out ! j = ((L, R), m)" by (rule outj)
    show "0 \<le> L" by (rule L0)
    show "L \<le> R" by (rule LR)
    show "((real_of_int L / 2 ^ m) ^ h < y \<and> y < (real_of_int R / 2 ^ m) ^ h)
              \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ h = y)" by (rule cov)
  qed
qed

theorem pow_sub_backmap_all_cover_strict:
  fixes Q0 :: "int poly" and accQ :: gmp_dyadic_interval_vec
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len0: "0 < length q" and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
    and ivQ: "dyadic_interval_vec_invar accQ"
    and n1: "length (dyadic_interval_vec_triples accQ) + 1
               < max_snat LENGTH(gmp_poly_len)"
    and isoQ: "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
          (case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
    and covQ: "\<And>y::real. 0 < y \<Longrightarrow> poly Q y = 0 \<Longrightarrow>
          (\<exists>j A B k. j < length (dyadic_interval_vec_triples accQ)
             \<and> dyadic_interval_vec_triples accQ ! j = ((A, B), k)
             \<and> ((real_of_int A / 2 ^ k < y \<and> y < real_of_int B / 2 ^ k)
                \<or> (real_of_int A / 2 ^ k = y \<and> real_of_int B / 2 ^ k = y)))"
  shows "pow_sub_backmap_all_monadic h q dlt accQ
           \<le> SPEC (\<lambda>(out, ok). ok \<longrightarrow>
                 (\<forall>y::real. 0 < y \<longrightarrow> poly Q y = 0 \<longrightarrow>
                   (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
                      \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
                      \<and> 0 \<le> L \<and> L \<le> R
                      \<and> (((real_of_int L / 2 ^ m) ^ h < y \<and> y < (real_of_int R / 2 ^ m) ^ h)
                         \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ h = y)))))"
proof -
  have main: "pow_sub_backmap_all_monadic h q dlt accQ
           \<le> SPEC (\<lambda>(out, ok).
                 dyadic_interval_vec_invar out
                 \<and> (ok \<longrightarrow> length (dyadic_interval_vec_triples out)
                             = length (dyadic_interval_vec_triples accQ)
                       \<and> (\<forall>j < length (dyadic_interval_vec_triples accQ).
                            pow_sub_iv_pre h q dlt
                              (dyadic_interval_vec_triples accQ ! j))
                       \<and> (\<forall>j < length (dyadic_interval_vec_triples accQ).
                            pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                                                (dyadic_interval_vec_triples out ! j))))"
    by (rule pow_sub_backmap_all_monadic_correct[OF h hb len0 len ivQ n1])
  show ?thesis
    apply (rule weaken_SPEC[OF main])
    apply clarsimp
    subgoal premises p for a aa b ba y
    proof -
      have pre': "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
            pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)"
        using p(6) by blast
      have emit': "\<And>j. j < length (dyadic_interval_vec_triples accQ) \<Longrightarrow>
            pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                                (dyadic_interval_vec_triples (a, aa, b) ! j)"
        using p(7) by blast
      have "\<exists>j L R m. j < length (dyadic_interval_vec_triples (a, aa, b))
          \<and> dyadic_interval_vec_triples (a, aa, b) ! j = ((L, R), m)
          \<and> 0 \<le> L \<and> L \<le> R
          \<and> (((real_of_int L / 2 ^ m) ^ h < y \<and> y < (real_of_int R / 2 ^ m) ^ h)
             \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ h = y))"
        by (rule pow_sub_backmap_cover_of_post_strict[OF h Pdef sf Qdef qdef len0 isoQ
                   covQ[OF p(3) p(4)] pre' p(5) emit' p(4)])
      thus ?thesis using p(5) by auto
    qed
    done
qed

lemma pow_sub_entry_sub_mop_complete_strict:
  fixes xs :: "int list" and d dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
    and "q \<equiv> pow_sub_extract d xs"
  assumes d2: "2 \<le> d" and par2: "2 \<le> gcd d 2" and db: "d < max_snat LENGTH(gmp_poly_len)"
    and ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and supp: "\<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> d dvd i"
    and qsolve: "defl_isolate_all_split_main q \<le> SPEC (\<lambda>(accP, accN, xs0).
          dyadic_interval_vec_invar accP
          \<and> length (dyadic_interval_vec_triples accP) + 1
              < max_snat LENGTH(gmp_poly_len)
          \<and> pow_sub_reduced_isolates (real_of_int_poly (Poly q)) accP
          \<and> pow_sub_reduced_covers (real_of_int_poly (Poly q)) accP)"
  shows "pow_sub_entry_sub_mop d dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>x::real. poly P x = 0 \<longrightarrow>
        (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
           \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
           \<and> ((real_of_int L / 2 ^ m < x \<and> x < real_of_int R / 2 ^ m
                \<or> real_of_int L / 2 ^ m = x \<and> real_of_int R / 2 ^ m = x)
              \<or> (- (real_of_int R / 2 ^ m) < x \<and> x < - (real_of_int L / 2 ^ m)
                \<or> - (real_of_int R / 2 ^ m) = x \<and> - (real_of_int L / 2 ^ m) = x)))))"
proof -
  have d0: "0 < d" using d2 by simp
  have ev: "even d" by (rule pow_sub_par_even[OF par2])
  have lenxs: "length xs < max_snat LENGTH(gmp_poly_len)" using len1 by simp
  have ne': "0 < length xs" using ne by simp
  have Pdef: "P = real_of_int_poly (Poly q) \<circ>\<^sub>p monom 1 d"
    unfolding P_def q_def by (rule pow_sub_reduced_algebra(1)[OF d0 ne nz supp])
  have canon: "coeffs (Poly q) = q"
    unfolding q_def by (rule pow_sub_reduced_algebra(2)[OF d0 ne nz supp])
  have qlen0: "0 < length q" unfolding q_def by simp
  have qlen: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "length q = Suc ((length xs - 1) div d)" unfolding q_def by simp
    also have "\<dots> \<le> Suc (length xs - 1)" by (simp add: Euclidean_Rings.div_le_dividend)
    finally show ?thesis using len1 ne' by linarith
  qed
  have Qorig: "poly (real_of_int_poly (Poly q)) 0 \<noteq> 0"
    by (rule pow_sub_squarefree_no_origin[OF d2 sfP[unfolded Pdef]])
  have xy: "0 < x ^ d \<and> poly (real_of_int_poly (Poly q)) (x ^ d) = 0"
    if rx: "poly P x = 0" for x :: real
  proof -
    have qroot: "poly (real_of_int_poly (Poly q)) (x ^ d) = 0"
      using rx unfolding Pdef by (simp add: poly_pcompose_monom)
    have xnz: "x \<noteq> 0"
    proof
      assume "x = 0"
      then have "x ^ d = 0" using d0 by (simp add: zero_power)
      with qroot Qorig show False by simp
    qed
    then have "0 < x ^ d" using ev by (simp add: zero_less_power_eq)
    with qroot show ?thesis by simp
  qed
  have bmc: "pow_sub_backmap_all_monadic d q dlt accP
        \<le> SPEC (\<lambda>(out, ok). ok \<longrightarrow>
             (\<forall>x::real. poly P x = 0 \<longrightarrow>
               (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
                  \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
                  \<and> ((real_of_int L / 2 ^ m < x \<and> x < real_of_int R / 2 ^ m
                       \<or> real_of_int L / 2 ^ m = x \<and> real_of_int R / 2 ^ m = x)
                     \<or> (- (real_of_int R / 2 ^ m) < x \<and> x < - (real_of_int L / 2 ^ m)
                       \<or> - (real_of_int R / 2 ^ m) = x \<and> - (real_of_int L / 2 ^ m) = x)))))"
    if ivQ: "dyadic_interval_vec_invar accP"
      and n1: "length (dyadic_interval_vec_triples accP) + 1
                 < max_snat LENGTH(gmp_poly_len)"
      and iso: "pow_sub_reduced_isolates (real_of_int_poly (Poly q)) accP"
      and cov: "pow_sub_reduced_covers (real_of_int_poly (Poly q)) accP"
    for accP
  proof -
    have base: "pow_sub_backmap_all_monadic d q dlt accP
          \<le> SPEC (\<lambda>(out, ok). ok \<longrightarrow>
               (\<forall>y::real. 0 < y \<longrightarrow> poly (real_of_int_poly (Poly q)) y = 0 \<longrightarrow>
                 (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
                    \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
                    \<and> 0 \<le> L \<and> L \<le> R
                    \<and> (((real_of_int L / 2 ^ m) ^ d < y \<and> y < (real_of_int R / 2 ^ m) ^ d)
                       \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ d = y)))))"
      by (rule pow_sub_backmap_all_cover_strict[OF d0 db Pdef sfP refl canon[symmetric]
                 qlen0 qlen ivQ n1])
         (use iso cov in \<open>auto simp: pow_sub_reduced_isolates_def
                pow_sub_reduced_covers_def\<close>)
    show ?thesis
      apply (rule weaken_SPEC[OF base])
      apply clarsimp
      subgoal premises p for a aa b ba x
      proof -
        have y1: "0 < x ^ d" and y2: "poly (real_of_int_poly (Poly q)) (x ^ d) = 0"
          using xy[OF p(2)] by auto
        obtain j L R m where jn: "j < length (dyadic_interval_vec_triples (a, aa, b))"
          and tj: "dyadic_interval_vec_triples (a, aa, b) ! j = ((L, R), m)"
          and L0: "0 \<le> L" and LR: "L \<le> R"
          and cv: "((real_of_int L / 2 ^ m) ^ d < x ^ d \<and> x ^ d < (real_of_int R / 2 ^ m) ^ d)
                   \<or> (L = R \<and> (real_of_int L / 2 ^ m) ^ d = x ^ d)"
          using p(3) y1 y2 by blast
        have u0: "0 \<le> real_of_int L / 2 ^ m" using L0 by simp
        have v0: "0 \<le> real_of_int R / 2 ^ m" using L0 LR by simp
        have cv': "((real_of_int L / 2 ^ m) ^ d < x ^ d \<and> x ^ d < (real_of_int R / 2 ^ m) ^ d)
                   \<or> (real_of_int L / 2 ^ m = real_of_int R / 2 ^ m
                      \<and> (real_of_int L / 2 ^ m) ^ d = x ^ d)"
          using cv by auto
        have "(real_of_int L / 2 ^ m < x \<and> x < real_of_int R / 2 ^ m
                \<or> real_of_int L / 2 ^ m = x \<and> real_of_int R / 2 ^ m = x)
              \<or> (- (real_of_int R / 2 ^ m) < x \<and> x < - (real_of_int L / 2 ^ m)
                \<or> - (real_of_int R / 2 ^ m) = x \<and> - (real_of_int L / 2 ^ m) = x)"
          by (rule pow_sub_window_covers_lift_strict[OF d0 ev u0 v0 cv'])
        thus ?thesis using jn tj by blast
      qed
      done
  qed
  show ?thesis
    unfolding pow_sub_entry_sub_mop_def PR_CONST_def
      dyadic_interval_vec_free_monadic_def mop_free_def
    apply (refine_vcg
           pow_sub_extract_monadic_correct[OF d0 ne' lenxs, folded q_def, THEN order_trans]
           qsolve[THEN order_trans]
           bmc[THEN order_trans])
    apply (all \<open>use d0 db qlen0 qlen ne' lenxs in \<open>auto simp: Let_def\<close>\<close>)
    done
qed

theorem pow_sub_entry_monadic_complete_strict:
  fixes xs :: "int list" and nfloor hcap dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and hcb: "hcap < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and qsolve: "\<And>d. 2 \<le> d \<Longrightarrow> even d \<Longrightarrow> d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
          defl_isolate_all_split_main (pow_sub_extract d xs)
            \<le> SPEC (\<lambda>(accP, accN, xs0).
                dyadic_interval_vec_invar accP
                \<and> length (dyadic_interval_vec_triples accP) + 1
                    < max_snat LENGTH(gmp_poly_len)
                \<and> pow_sub_reduced_isolates
                     (real_of_int_poly (Poly (pow_sub_extract d xs))) accP
                \<and> pow_sub_reduced_covers
                     (real_of_int_poly (Poly (pow_sub_extract d xs))) accP)"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>x::real. poly P x = 0 \<longrightarrow>
        (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
           \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
           \<and> ((real_of_int L / 2 ^ m < x \<and> x < real_of_int R / 2 ^ m
                \<or> real_of_int L / 2 ^ m = x \<and> real_of_int R / 2 ^ m = x)
              \<or> (- (real_of_int R / 2 ^ m) < x \<and> x < - (real_of_int L / 2 ^ m)
                \<or> - (real_of_int R / 2 ^ m) = x \<and> - (real_of_int L / 2 ^ m) = x)))))"
proof -
  have lenxs: "length xs < max_snat LENGTH(gmp_poly_len)" using len1 by simp
  have supp: "\<And>d. d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
        \<forall>i < length xs. xs ! i \<noteq> 0 \<longrightarrow> d dvd i"
    using pow_sub_exp_dvd_support by blast
  have hb: "pow_sub_h xs < max_snat LENGTH(gmp_poly_len)"
    using pow_sub_h_le_length[of xs] lenxs by simp
  have dbnd: "gcd (pow_sub_h xs) hcap < max_snat LENGTH(gmp_poly_len)"
    using pow_sub_gcd_le_max[of "pow_sub_h xs" hcap] hb hcb by simp
  have parbnd: "gcd d 2 < max_snat LENGTH(gmp_poly_len)" for d :: nat
  proof -
    have "gcd d 2 \<le> 2" by (rule pow_sub_gcd_two_le)
    thus ?thesis unfolding pow_sub_room_max_snat by linarith
  qed
  have sub: "pow_sub_entry_sub_mop d dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
        ok \<longrightarrow> (\<forall>x::real. poly P x = 0 \<longrightarrow>
          (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
             \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
             \<and> ((real_of_int L / 2 ^ m < x \<and> x < real_of_int R / 2 ^ m
                  \<or> real_of_int L / 2 ^ m = x \<and> real_of_int R / 2 ^ m = x)
                \<or> (- (real_of_int R / 2 ^ m) < x \<and> x < - (real_of_int L / 2 ^ m)
                  \<or> - (real_of_int R / 2 ^ m) = x \<and> - (real_of_int L / 2 ^ m) = x)))))"
    if d2: "2 \<le> d" and par2: "2 \<le> gcd d 2" and db: "d < max_snat LENGTH(gmp_poly_len)"
      and deq: "d = gcd (pow_sub_h xs) hcap"
    for d
  proof -
    have ev: "even d" by (rule pow_sub_par_even[OF par2])
    show ?thesis
      unfolding P_def
      by (rule pow_sub_entry_sub_mop_complete_strict[OF d2 par2 db ne len1 nz sfP[unfolded P_def]
                 supp[OF deq] qsolve[OF d2 ev deq]])
  qed
  show ?thesis
    unfolding pow_sub_entry_monadic_def PR_CONST_def
      pow_sub_entry_applicable_mop_def pow_sub_entry_exp_mop_def
      pow_sub_entry_bail_mop_def poly_length_monadic_def
    apply (refine_vcg
           pow_sub_h_monadic_correct[OF lenxs, THEN order_trans]
           snat_gcd_monadic_correct[THEN order_trans]
           sub[THEN order_trans]
           dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans])
    apply (all \<open>use ne lenxs len1 hb dbnd parbnd in \<open>auto simp: Let_def\<close>\<close>)
    done
qed

corollary pow_sub_entry_monadic_complete_strict_of_pre:
  fixes xs :: "int list" and nfloor hcap dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and hcb: "hcap < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and qpre: "\<And>d. 2 \<le> d \<Longrightarrow> even d \<Longrightarrow> d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
          dsc_isolate_all_split_defl_pre (pow_sub_extract d xs)"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> (\<forall>x::real. poly P x = 0 \<longrightarrow>
        (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
           \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
           \<and> ((real_of_int L / 2 ^ m < x \<and> x < real_of_int R / 2 ^ m
                \<or> real_of_int L / 2 ^ m = x \<and> real_of_int R / 2 ^ m = x)
              \<or> (- (real_of_int R / 2 ^ m) < x \<and> x < - (real_of_int L / 2 ^ m)
                \<or> - (real_of_int R / 2 ^ m) = x \<and> - (real_of_int L / 2 ^ m) = x)))))"
proof -
  have q4: "defl_isolate_all_split_main (pow_sub_extract d xs)
        \<le> SPEC (\<lambda>(accP, accN, xs0).
            dyadic_interval_vec_invar accP
            \<and> length (dyadic_interval_vec_triples accP) + 1
                < max_snat LENGTH(gmp_poly_len)
            \<and> pow_sub_reduced_isolates
                 (real_of_int_poly (Poly (pow_sub_extract d xs))) accP
            \<and> pow_sub_reduced_covers
                 (real_of_int_poly (Poly (pow_sub_extract d xs))) accP)"
    if d2: "2 \<le> d" and ev: "even d" and deq: "d = gcd (pow_sub_h xs) hcap" for d
    by (rule weaken_SPEC[OF defl_isolate_all_split_main_correct_qsolve[OF qpre[OF d2 ev deq]]])
       (auto intro: pow_sub_reduced_isolates_of_defl_acc pow_sub_reduced_covers_of_defl_acc)
  show ?thesis
    unfolding P_def
    by (rule pow_sub_entry_monadic_complete_strict[OF ne len1 hcb nz sfP[unfolded P_def] q4])
qed


end
