theory Power_Sub_Isolation_Strong
  imports
    IsaRRI_Refine.Isolation_Contract
    IsaRRI.Power_Sub_Entry_Complete_Strict
    IsaRRI.Deflation_Isolation_Strong
begin

text \<open>\<^bold>\<open>The power-substitution path: no root is reported twice.\<close>
  \<open>pow_sub_entry_monadic_correct_of_pre\<close> gives soundness per emitted window and
  \<open>pow_sub_entry_monadic_complete_strict_of_pre\<close> gives strict-or-degenerate completeness. This
  theory adds the remaining clause of the isolation contract, uniqueness: no root of \<open>P\<close> lies in
  two emitted windows.

  \<^bold>\<open>Why uniqueness on this path is about roots and not about the windows as sets.\<close> For a degenerate
  reduced window whose \<open>h\<close>-th root is not exactly representable, the back-map emits the dyadic
  window \<open>(L, L+1) / 2\<^sup>m\<close>. That window is certified to contain exactly one root of \<open>P\<close>, but nothing
  forces it to stop short of a neighbouring window's span in a root-free gap, so set-disjointness
  does not hold in general. (On the other two paths it does: the deflating loop's \<open>defl_geom\<close> and
  the low-degree windows are disjoint.)

  The clause the count needs does hold. Each emitted window's root maps under \<open>x \<mapsto> x\<^sup>h\<close> into its
  own reduced window; the reduced windows are pairwise disjoint
  (\<open>defl_isolate_all_split_main_correct_geom\<close>); and distinct reduced roots have distinct positive
  \<open>h\<close>-th roots. So the emitted windows are in bijection with the positive roots, which is what
  \<open>length ws = card {x. 0 < x \<and> poly P x = 0}\<close> requires.\<close>

section \<open>The contract clauses, as NAMED predicates\<close>

text \<open>\<^bold>\<open>The postcondition is a named constant.\<close> Stated inline, the four-clause postcondition is a
  nest of \<open>\<forall>\<close>/\<open>\<not>\<exists>\<close> over list indices that the automation closing the \<open>refine_vcg\<close> goals of
  @{thm [source] pow_sub_entry_sub_mop_complete_strict} unfolds and does not finish; as an atom
  the same goals close by \<open>assumption\<close>.\<close>

definition iv_root_unique :: "real poly \<Rightarrow> (real \<times> real) list \<Rightarrow> bool" where
  "iv_root_unique P ws \<longleftrightarrow> (\<forall>i j. i < length ws \<longrightarrow> j < length ws \<longrightarrow> i \<noteq> j \<longrightarrow>
      \<not> (\<exists>x. poly P x = 0 \<and> iv_in x (ws ! i) \<and> iv_in x (ws ! j)))"

definition iv_wins_pos :: "(real \<times> real) list \<Rightarrow> bool" where
  "iv_wins_pos ws \<longleftrightarrow> (\<forall>w \<in> set ws. \<forall>x. iv_in x w \<longrightarrow> 0 < x)"

definition iv_wins_neg :: "(real \<times> real) list \<Rightarrow> bool" where
  "iv_wins_neg ws \<longleftrightarrow> (\<forall>w \<in> set ws. \<forall>x. iv_in x w \<longrightarrow> x < 0)"

definition pow_sub_mirror :: "real \<times> real \<Rightarrow> real \<times> real" where
  "pow_sub_mirror w = (- snd w, - fst w)"

text \<open>\<^bold>\<open>The whole contract for the entry, both halves.\<close> The entry reports ONE vector and its
  reflection, so the negative half is \<open>map pow_sub_mirror\<close> of the positive one. The two \<open>Pos\<close>/\<open>Neg\<close>
  clauses also settle the cross-half case for free: no root can sit in a positive window and a
  reflected one at once.\<close>

definition pow_sub_entry_contract :: "real poly \<Rightarrow> (real \<times> real) list \<Rightarrow> bool" where
  "pow_sub_entry_contract P ws \<longleftrightarrow>
     iv_root_unique P ws \<and> iv_wins_pos ws
     \<and> iv_root_unique P (map pow_sub_mirror ws) \<and> iv_wins_neg (map pow_sub_mirror ws)"

section \<open>One emitted window: where its root goes, and that it is positive\<close>

text \<open>The proper branch's orientation fact, pulled out of
  \<open>pow_sub_loop_tst_pair_ok_strong\<close>'s proof so both lemmas below can use it without
  restructuring a certified proof.\<close>

lemma pow_sub_loop_tst_lt:
  fixes A B L R :: int
  assumes B0: "0 \<le> B"
    and tst: "pow_sub_loop_tst h A B k q m"
    and Ld: "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
    and Rd: "R = pow_sub_num_lo h m (real_of_int B / 2 ^ k)"
  shows "L < R"
proof -
  have lt: "L ^ h < R ^ h"
    using tst unfolding pow_sub_loop_tst_def pow_sub_sign_tst_def Ld[symmetric] Rd[symmetric]
    by auto
  have R0: "0 \<le> R" unfolding Rd by (rule pow_sub_num_lo_nonneg[OF B0])
  show ?thesis using lt R0 by (metis power_less_imp_less_base)
qed

text \<open>\<^bold>\<open>Where a root of an emitted window goes.\<close> If a root \<open>x\<close> of \<open>P\<close> lies in the window emitted
  for the reduced window \<open>(a, b)\<close>, then \<open>x\<^sup>h\<close> lies in \<open>(a, b)\<close>. The proper branch is containment
  (\<open>a \<le> u\<^sup>h\<close> and \<open>v\<^sup>h \<le> b\<close>, the shrink the soundness chain already proves); the inexact
  degenerate branch is the certified COUNT --- the window holds exactly one root of \<open>P\<close>, and
  \<open>a\<^sup>1\<^sup>/\<^sup>h\<close> is one of them, so \<open>x\<close> is it.\<close>

lemma pow_sub_emit_ok_root_image:
  fixes Q0 :: "int poly" and A B L R :: int and x :: real
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len: "0 < length q"
    and A0: "0 \<le> A" and B0: "0 \<le> B" and AB: "A \<le> B"
    and iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    and ok: "pow_sub_emit_ok h q ((A, B), k) ((L, R), m)"
    and rx: "poly P x = 0"
    and inx: "iv_in x (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
  shows "iv_in (x ^ h) (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
proof (cases "A = B")
  case True
  have tst: "pow_sub_deg_tst h A k q m"
    and Ld: "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
    and Rd: "R = (if L ^ h * 2 ^ k = A * 2 ^ (h * m) then L else 1 + L)"
    using ok True unfolding pow_sub_emit_ok_def by (simp_all add: Let_def)
  have iv': "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int A / 2 ^ k)"
    using iv True by simp
  define a where "a = real_of_int A / 2 ^ k"
  define u where "u = real_of_int L / 2 ^ m"
  define v where "v = real_of_int R / 2 ^ m"
  have a0: "0 \<le> a" unfolding a_def using A0 by simp
  have rootQ: "poly Q a = 0" using iv' unfolding dsc_pair_ok_def a_def by simp
  have L0: "0 \<le> L" unfolding Ld by (rule pow_sub_num_lo_nonneg[OF A0])
  show ?thesis
  proof (cases "L ^ h * 2 ^ k = A * 2 ^ (h * m)")
    case ex: True
    have "R = L" using Rd ex by simp
    then have "x = u" using inx unfolding iv_in_def u_def by auto
    moreover have "u ^ h = a" unfolding u_def a_def by (rule pow_sub_deg_exact_pow[OF ex])
    ultimately show ?thesis using True unfolding iv_in_def a_def by simp
  next
    case nex: False
    have R: "R = 1 + L" using Rd nex by simp
    have pk: "dsc_pair_ok P (u, v)"
      unfolding u_def v_def
      by (rule pow_sub_deg_tst_pair_ok[OF h Pdef sf Qdef qdef len A0 iv' tst Ld Rd])
    have cov: "u ^ h < a \<and> a < v ^ h"
      using pow_sub_deg_tst_cover_strict[OF h A0 Ld Rd] R unfolding u_def v_def a_def by auto
    have uv: "u < v" unfolding u_def v_def R by (simp add: divide_strict_right_mono)
    have u0: "0 \<le> u" unfolding u_def using L0 by simp
    define r where "r = a powr (1 / real h)"
    have r0: "0 \<le> r" unfolding r_def by simp
    have rh: "r ^ h = a" unfolding r_def using a0 h by (rule powr_root_pow)
    have ur: "u < r"
    proof -
      have "u ^ h < r ^ h" using cov rh by simp
      then show ?thesis using r0 by (rule power_less_imp_less_base)
    qed
    have rv: "r < v"
    proof -
      have "r ^ h < v ^ h" using cov rh by simp
      moreover have "0 \<le> v" using u0 uv by simp
      ultimately show ?thesis by (rule power_less_imp_less_base)
    qed
    have Pr: "poly P r = 0" unfolding Pdef using rh rootQ by (simp add: poly_pcompose_monom)
    have xuv: "u < x \<and> x < v" using inx uv unfolding iv_in_def u_def v_def by auto
    have one: "roots_in P u v = 1" using pk uv unfolding dsc_pair_ok_def by simp
    have card1: "card {y. u < y \<and> y < v \<and> poly P y = 0} = 1"
      using one roots_in_squarefree_card[OF sf] by simp
    then obtain w where W: "{y. u < y \<and> y < v \<and> poly P y = 0} = {w}"
      by (rule card_1_singletonE)
    have xin: "x \<in> {y. u < y \<and> y < v \<and> poly P y = 0}" using xuv rx by simp
    have rin: "r \<in> {y. u < y \<and> y < v \<and> poly P y = 0}" using ur rv Pr by simp
    have "x = r" using W xin rin by auto
    then have "x ^ h = a" using rh by simp
    then show ?thesis using True unfolding iv_in_def a_def by simp
  qed
next
  case False
  have tst: "pow_sub_loop_tst h A B k q m"
    and Ld: "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
    and Rd: "R = pow_sub_num_lo h m (real_of_int B / 2 ^ k)"
    using ok False unfolding pow_sub_emit_ok_def by (simp_all add: Let_def)
  have LR: "L < R" by (rule pow_sub_loop_tst_lt[OF B0 tst Ld Rd])
  define a where "a = real_of_int A / 2 ^ k"
  define b where "b = real_of_int B / 2 ^ k"
  define u where "u = real_of_int L / 2 ^ m"
  define v where "v = real_of_int R / 2 ^ m"
  have a0: "0 \<le> a" unfolding a_def using A0 by simp
  have b0: "0 \<le> b" unfolding b_def using B0 by simp
  have uhi: "u = pow_sub_hi h m a" unfolding u_def Ld a_def by (simp add: pow_sub_hi_num)
  have vlo: "v = pow_sub_lo h m b" unfolding v_def Rd b_def by (simp add: pow_sub_lo_num)
  have u0: "0 \<le> u" unfolding uhi by (rule pow_sub_hi_nonneg)
  have lo: "a \<le> u ^ h" unfolding uhi by (rule pow_sub_hi_pow_ge[OF a0 h])
  have hi: "v ^ h \<le> b" unfolding vlo by (rule pow_sub_lo_pow_le[OF b0 h])
  have uv: "u < v" unfolding u_def v_def using LR by (simp add: divide_strict_right_mono)
  have xuv: "u < x \<and> x < v" using inx uv unfolding iv_in_def u_def v_def by auto
  have x0: "0 \<le> x" using u0 xuv by simp
  have "u ^ h < x ^ h" using xuv u0 h by (simp add: power_strict_mono)
  moreover have "x ^ h < v ^ h" using xuv x0 h by (simp add: power_strict_mono)
  ultimately have "a < x ^ h \<and> x ^ h < b" using lo hi by linarith
  then show ?thesis unfolding iv_in_def a_def b_def by simp
qed

text \<open>\<^bold>\<open>Pos\<close>, per emitted window. The only way a window can touch the origin is the exact
  degenerate branch, and there the emitted point's \<open>h\<close>-th power IS a root of \<open>Q\<close> --- which cannot
  be \<open>0\<close>, because a squarefree \<open>Q \<circ>\<^sub>p x\<^sup>h\<close> forces \<open>poly Q 0 \<noteq> 0\<close>
  (\<open>pow_sub_squarefree_no_origin\<close>).\<close>

lemma pow_sub_emit_ok_window_pos:
  fixes A B L R :: int and x :: real
  assumes h: "0 < h" and A0: "0 \<le> A" and B0: "0 \<le> B"
    and iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    and Q0nz: "poly Q 0 \<noteq> 0"
    and ok: "pow_sub_emit_ok h q ((A, B), k) ((L, R), m)"
    and inx: "iv_in x (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
  shows "0 < x"
proof (cases "A = B")
  case True
  have Ld: "L = pow_sub_num_lo h m (real_of_int A / 2 ^ k)"
    and Rd: "R = (if L ^ h * 2 ^ k = A * 2 ^ (h * m) then L else 1 + L)"
    using ok True unfolding pow_sub_emit_ok_def by (simp_all add: Let_def)
  have L0: "0 \<le> L" unfolding Ld by (rule pow_sub_num_lo_nonneg[OF A0])
  show ?thesis
  proof (cases "L ^ h * 2 ^ k = A * 2 ^ (h * m)")
    case ex: True
    have "R = L" using Rd ex by simp
    then have xu: "x = real_of_int L / 2 ^ m" using inx unfolding iv_in_def by auto
    have pw: "(real_of_int L / 2 ^ m) ^ h = real_of_int A / 2 ^ k"
      by (rule pow_sub_deg_exact_pow[OF ex])
    have rootQ: "poly Q (real_of_int A / 2 ^ k) = 0"
      using iv True unfolding dsc_pair_ok_def by simp
    have "real_of_int A / 2 ^ k \<noteq> 0" using rootQ Q0nz by auto
    then have "x ^ h \<noteq> 0" using pw xu by simp
    then have "x \<noteq> 0" using h by auto
    moreover have "0 \<le> x" using xu L0 by simp
    ultimately show ?thesis by simp
  next
    case nex: False
    have R: "R = 1 + L" using Rd nex by simp
    have u0: "0 \<le> real_of_int L / 2 ^ m" using L0 by simp
    have "real_of_int L / 2 ^ m < real_of_int R / 2 ^ m"
      unfolding R using L0 by (simp add: divide_strict_right_mono)
    then show ?thesis using inx u0 unfolding iv_in_def by auto
  qed
next
  case False
  have tst: "pow_sub_loop_tst h A B k q m"
    and Ld: "L = pow_sub_num_hi h m (real_of_int A / 2 ^ k)"
    and Rd: "R = pow_sub_num_lo h m (real_of_int B / 2 ^ k)"
    using ok False unfolding pow_sub_emit_ok_def by (simp_all add: Let_def)
  have LR: "L < R" by (rule pow_sub_loop_tst_lt[OF B0 tst Ld Rd])
  have L0: "0 \<le> L" unfolding Ld by (rule pow_sub_num_hi_nonneg[OF A0])
  have u0: "0 \<le> real_of_int L / 2 ^ m" using L0 by simp
  have "real_of_int L / 2 ^ m < real_of_int R / 2 ^ m"
    using LR by (simp add: divide_strict_right_mono)
  then show ?thesis using inx u0 unfolding iv_in_def by auto
qed

section \<open>Lifting one window to the whole emitted vector\<close>

text \<open>The per-index hypotheses are stated as BOUNDED \<open>\<forall>\<close> rather than \<open>\<And>\<close>, which is also the
  shape @{thm [source] pow_sub_backmap_all_monadic_correct} delivers them in: a \<open>\<And>\<close>-quantified
  CONDITIONAL fact composes by its conclusion, so \<open>OF\<close> would re-add each one's own hypotheses as
  fresh goals (the trap recorded at \<open>defl_body_step\<close>'s \<open>kdepth\<close>). And each one is INSTANTIATED
  with \<open>rule_format\<close> rather than handed to \<open>simp\<close>: with the index still bound, \<open>simp\<close> cannot see
  past the \<open>case\<close> pattern and leaves the conjunct present-but-unusable.\<close>

lemma defl_wins_length: "length (defl_wins v) = length (dyadic_interval_vec_triples v)"
  unfolding defl_wins_def by simp

lemma defl_wins_nth:
  assumes "j < length (dyadic_interval_vec_triples v)"
    and "dyadic_interval_vec_triples v ! j = ((A, B), m)"
  shows "defl_wins v ! j = (real_of_int A / 2 ^ m, real_of_int B / 2 ^ m)"
  unfolding defl_wins_def using assms by simp

lemma pow_sub_backmap_window_root_image:
  fixes Q0 :: "int poly" and accQ out :: gmp_dyadic_interval_vec and x :: real
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0" and len0: "0 < length q"
    and isoQ: "\<forall>j < length (dyadic_interval_vec_triples accQ).
          (case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
    and preQ: "\<forall>j < length (dyadic_interval_vec_triples accQ).
          pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)"
    and lenEq: "length (dyadic_interval_vec_triples out)
                  = length (dyadic_interval_vec_triples accQ)"
    and emit: "\<forall>j < length (dyadic_interval_vec_triples accQ).
          pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                              (dyadic_interval_vec_triples out ! j)"
    and t: "t < length (defl_wins out)"
    and rx: "poly P x = 0" and inx: "iv_in x (defl_wins out ! t)"
  shows "iv_in (x ^ h) (defl_wins accQ ! t)"
proof -
  have tA: "t < length (dyadic_interval_vec_triples accQ)"
    using t lenEq by (simp add: defl_wins_length)
  have tO: "t < length (dyadic_interval_vec_triples out)" using tA lenEq by simp
  obtain A B k where at: "dyadic_interval_vec_triples accQ ! t = ((A, B), k)" by (metis surj_pair)
  obtain L R m where ot: "dyadic_interval_vec_triples out ! t = ((L, R), m)" by (metis surj_pair)
  have pre_t: "pow_sub_iv_pre h q dlt ((A, B), k)"
    using preQ[rule_format, OF tA] unfolding at .
  have A0: "0 \<le> A" and B0: "0 \<le> B"
    using pre_t unfolding pow_sub_iv_pre_def by (simp_all add: Let_def)
  have iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    using isoQ[rule_format, OF tA] unfolding at by simp
  have AB: "A \<le> B"
  proof -
    have "real_of_int A / 2 ^ k \<le> real_of_int B / 2 ^ k"
      using iv unfolding dsc_pair_ok_def by auto
    thus ?thesis by (simp add: divide_right_mono_neg field_simps)
  qed
  have wo: "defl_wins out ! t = (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
    by (rule defl_wins_nth[OF tO ot])
  have wa: "defl_wins accQ ! t = (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    by (rule defl_wins_nth[OF tA at])
  have ok: "pow_sub_emit_ok h q ((A, B), k) ((L, R), m)"
    using emit[rule_format, OF tA] unfolding at ot .
  show ?thesis
    unfolding wa
    by (rule pow_sub_emit_ok_root_image[OF h Pdef sf Qdef qdef len0 A0 B0 AB iv ok rx
              inx[unfolded wo]])
qed

lemma pow_sub_backmap_windows_unique:
  fixes Q0 :: "int poly" and accQ out :: gmp_dyadic_interval_vec
  assumes h: "0 < h" and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0" and len0: "0 < length q"
    and isoQ: "\<forall>j < length (dyadic_interval_vec_triples accQ).
          (case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
    and preQ: "\<forall>j < length (dyadic_interval_vec_triples accQ).
          pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)"
    and lenEq: "length (dyadic_interval_vec_triples out)
                  = length (dyadic_interval_vec_triples accQ)"
    and emit: "\<forall>j < length (dyadic_interval_vec_triples accQ).
          pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                              (dyadic_interval_vec_triples out ! j)"
    and disjQ: "iv_disj_mset (mset (defl_wins accQ))"
  shows "iv_root_unique P (defl_wins out)"
  unfolding iv_root_unique_def
proof (intro allI impI notI)
  fix i j
  assume i: "i < length (defl_wins out)" and j: "j < length (defl_wins out)" and ij: "i \<noteq> j"
    and ex: "\<exists>x. poly P x = 0 \<and> iv_in x (defl_wins out ! i) \<and> iv_in x (defl_wins out ! j)"
  from ex obtain x where rx: "poly P x = 0"
    and ini: "iv_in x (defl_wins out ! i)" and inj: "iv_in x (defl_wins out ! j)" by blast
  have iA: "i < length (defl_wins accQ)" and jA: "j < length (defl_wins accQ)"
    using i j lenEq by (simp_all add: defl_wins_length)
  have "iv_in (x ^ h) (defl_wins accQ ! i)"
    by (rule pow_sub_backmap_window_root_image[OF h Pdef sf Qdef qdef len0 isoQ preQ lenEq
              emit i rx ini])
  moreover have "iv_in (x ^ h) (defl_wins accQ ! j)"
    by (rule pow_sub_backmap_window_root_image[OF h Pdef sf Qdef qdef len0 isoQ preQ lenEq
              emit j rx inj])
  moreover have "iv_disj (defl_wins accQ ! i) (defl_wins accQ ! j)"
    by (rule iv_disj_mset_nth[OF disjQ iA jA ij])
  ultimately show False unfolding iv_disj_def by blast
qed

lemma pow_sub_backmap_windows_pos:
  fixes Q0 :: "int poly" and accQ out :: gmp_dyadic_interval_vec
  assumes h: "0 < h"
    and Q0nz: "poly Q 0 \<noteq> 0"
    and isoQ: "\<forall>j < length (dyadic_interval_vec_triples accQ).
          (case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
    and preQ: "\<forall>j < length (dyadic_interval_vec_triples accQ).
          pow_sub_iv_pre h q dlt (dyadic_interval_vec_triples accQ ! j)"
    and lenEq: "length (dyadic_interval_vec_triples out)
                  = length (dyadic_interval_vec_triples accQ)"
    and emit: "\<forall>j < length (dyadic_interval_vec_triples accQ).
          pow_sub_emit_ok h q (dyadic_interval_vec_triples accQ ! j)
                              (dyadic_interval_vec_triples out ! j)"
  shows "iv_wins_pos (defl_wins out)"
  unfolding iv_wins_pos_def
proof (intro ballI allI impI)
  fix w x assume w: "w \<in> set (defl_wins out)" and inx: "iv_in x w"
  from w obtain t where t: "t < length (defl_wins out)" and wt: "w = defl_wins out ! t"
    by (metis in_set_conv_nth)
  have tA: "t < length (dyadic_interval_vec_triples accQ)"
    using t lenEq by (simp add: defl_wins_length)
  have tO: "t < length (dyadic_interval_vec_triples out)" using tA lenEq by simp
  obtain A B k where at: "dyadic_interval_vec_triples accQ ! t = ((A, B), k)" by (metis surj_pair)
  obtain L R m where ot: "dyadic_interval_vec_triples out ! t = ((L, R), m)" by (metis surj_pair)
  have pre_t: "pow_sub_iv_pre h q dlt ((A, B), k)"
    using preQ[rule_format, OF tA] unfolding at .
  have A0: "0 \<le> A" and B0: "0 \<le> B"
    using pre_t unfolding pow_sub_iv_pre_def by (simp_all add: Let_def)
  have iv: "dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k)"
    using isoQ[rule_format, OF tA] unfolding at by simp
  have ok: "pow_sub_emit_ok h q ((A, B), k) ((L, R), m)"
    using emit[rule_format, OF tA] unfolding at ot .
  have wo: "defl_wins out ! t = (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)"
    by (rule defl_wins_nth[OF tO ot])
  show "0 < x"
    by (rule pow_sub_emit_ok_window_pos[OF h A0 B0 iv Q0nz ok inx[unfolded wt wo]])
qed

section \<open>The negative half is the reflection of the same vector\<close>

lemma iv_in_mirror: "iv_in x (pow_sub_mirror w) \<longleftrightarrow> iv_in (- x) w"
  unfolding pow_sub_mirror_def iv_in_def by (cases w) auto

lemma pow_sub_poly_even:
  fixes P Q :: "real poly" and x :: real
  assumes Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and ev: "even h"
  shows "poly P (- x) = poly P x"
  unfolding Pdef using ev by (simp add: poly_pcompose_monom power_minus_even)

lemma pow_sub_mirror_unique:
  fixes P Q :: "real poly"
  assumes Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and ev: "even h"
    and U: "iv_root_unique P ws"
  shows "iv_root_unique P (map pow_sub_mirror ws)"
  using U unfolding iv_root_unique_def
proof (intro allI impI notI)
  fix i j
  assume U': "\<forall>i j. i < length ws \<longrightarrow> j < length ws \<longrightarrow> i \<noteq> j \<longrightarrow>
                \<not> (\<exists>x. poly P x = 0 \<and> iv_in x (ws ! i) \<and> iv_in x (ws ! j))"
    and i: "i < length (map pow_sub_mirror ws)" and j: "j < length (map pow_sub_mirror ws)"
    and ij: "i \<noteq> j"
    and ex: "\<exists>x. poly P x = 0 \<and> iv_in x (map pow_sub_mirror ws ! i)
                \<and> iv_in x (map pow_sub_mirror ws ! j)"
  from ex obtain x where rx: "poly P x = 0"
    and ini: "iv_in x (map pow_sub_mirror ws ! i)"
    and inj: "iv_in x (map pow_sub_mirror ws ! j)" by blast
  have i': "i < length ws" and j': "j < length ws" using i j by simp_all
  have "poly P (- x) = 0" using rx pow_sub_poly_even[OF Pdef ev] by simp
  moreover have "iv_in (- x) (ws ! i)" using ini i' by (simp add: iv_in_mirror)
  moreover have "iv_in (- x) (ws ! j)" using inj j' by (simp add: iv_in_mirror)
  ultimately show False using U' i' j' ij by blast
qed

lemma pow_sub_mirror_neg:
  assumes "iv_wins_pos ws"
  shows "iv_wins_neg (map pow_sub_mirror ws)"
  using assms unfolding iv_wins_pos_def iv_wins_neg_def
proof (intro ballI allI impI)
  fix w x
  assume pos: "\<forall>w \<in> set ws. \<forall>x. iv_in x w \<longrightarrow> 0 < x"
    and w: "w \<in> set (map pow_sub_mirror ws)" and inx: "iv_in x w"
  from w obtain w0 where w0: "w0 \<in> set ws" and wm: "w = pow_sub_mirror w0" by auto
  have "iv_in (- x) w0" using inx unfolding wm by (simp add: iv_in_mirror)
  then have "0 < - x" using pos w0 by blast
  then show "x < 0" by simp
qed

section \<open>The back-map loop\<close>

theorem pow_sub_backmap_all_unique:
  fixes Q0 :: "int poly" and accQ :: gmp_dyadic_interval_vec
  assumes h: "0 < h" and hb: "h < max_snat LENGTH(gmp_poly_len)"
    and Pdef: "P = Q \<circ>\<^sub>p monom 1 h" and sf: "squarefree P"
    and Qdef: "Q = map_poly real_of_int Q0" and qdef: "q = coeffs Q0"
    and len0: "0 < length q" and len: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
    and ivQ: "dyadic_interval_vec_invar accQ"
    and n1: "length (dyadic_interval_vec_triples accQ) + 1 < max_snat LENGTH(gmp_poly_len)"
    and isoQ: "\<forall>j < length (dyadic_interval_vec_triples accQ).
          (case dyadic_interval_vec_triples accQ ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok Q (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
    and disjQ: "iv_disj_mset (mset (defl_wins accQ))"
    and Q0nz: "poly Q 0 \<noteq> 0"
  shows "pow_sub_backmap_all_monadic h q dlt accQ
           \<le> SPEC (\<lambda>(out, ok). ok \<longrightarrow>
                 iv_root_unique P (defl_wins out) \<and> iv_wins_pos (defl_wins out))"
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
    \<comment> \<open>\<open>split_paired_all\<close> turns the \<open>\<And>x. case x of (out, ok) \<Rightarrow> \<dots>\<close> into named components (the
       vector splits into its three columns too, which the lemmas below unify with).\<close>
    apply (simp only: split_paired_all prod.case)
    apply (rule impI)
    apply (elim conjE)
    apply (drule (1) mp)
    apply (elim conjE)
    apply (rule conjI)
     apply (rule pow_sub_backmap_windows_unique[OF h Pdef sf Qdef qdef len0 isoQ _ _ _ disjQ];
            assumption)
    apply (rule pow_sub_backmap_windows_pos[OF h Q0nz isoQ]; assumption)
    done
qed

section \<open>The entry op: both halves\<close>

text \<open>Structurally @{thm [source] pow_sub_entry_sub_mop_complete_strict}, with the reduced solve's
  DISJOINTNESS (\<open>iv_disj_mset\<close>, from the deflating capstone's geometry) in place of its coverage,
  and the negative half derived from the positive one by \<open>pow_sub_mirror_unique\<close> --- the entry
  reports one vector and its reflection, so there is no second solve to reason about.\<close>

lemma pow_sub_entry_sub_mop_unique:
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
          \<and> iv_disj_mset (mset (defl_wins accP)))"
  shows "pow_sub_entry_sub_mop d dlt xs
           \<le> SPEC (\<lambda>(out, xs0, ok). ok \<longrightarrow> pow_sub_entry_contract P (defl_wins out))"
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
  have bmc: "pow_sub_backmap_all_monadic d q dlt accP
        \<le> SPEC (\<lambda>(out, ok). ok \<longrightarrow> pow_sub_entry_contract P (defl_wins out))"
    if ivQ: "dyadic_interval_vec_invar accP"
      and n1: "length (dyadic_interval_vec_triples accP) + 1
                 < max_snat LENGTH(gmp_poly_len)"
      and iso: "pow_sub_reduced_isolates (real_of_int_poly (Poly q)) accP"
      and disj: "iv_disj_mset (mset (defl_wins accP))"
    for accP
  proof -
    have isoQ: "\<forall>j < length (dyadic_interval_vec_triples accP).
          (case dyadic_interval_vec_triples accP ! j of ((A, B), k) \<Rightarrow>
             dsc_pair_ok (real_of_int_poly (Poly q))
               (real_of_int A / 2 ^ k, real_of_int B / 2 ^ k))"
      using iso by (auto simp: pow_sub_reduced_isolates_def)
    have base: "pow_sub_backmap_all_monadic d q dlt accP
          \<le> SPEC (\<lambda>(out, ok). ok \<longrightarrow>
               iv_root_unique P (defl_wins out) \<and> iv_wins_pos (defl_wins out))"
      by (rule pow_sub_backmap_all_unique[OF d0 db Pdef sfP refl canon[symmetric]
                 qlen0 qlen ivQ n1 isoQ disj Qorig])
    show ?thesis
      apply (rule weaken_SPEC[OF base])
      apply (simp only: split_paired_all prod.case)
      apply (rule impI)
      apply (drule (1) mp)
      apply (elim conjE)
      apply (simp only: pow_sub_entry_contract_def)
      \<comment> \<open>\<open>simp only\<close> uses the ASSUMPTIONS, so the two positive clauses may already be \<open>True\<close> by
         the time the conjunction is split --- take either shape rather than assuming one.\<close>
      apply (intro conjI)
         apply (all \<open>(assumption | rule TrueI
                      | erule pow_sub_mirror_unique[OF Pdef ev]
                      | erule pow_sub_mirror_neg)\<close>)
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

section \<open>THE PATH-B CAPSTONE\<close>

text \<open>Structurally @{thm [source] pow_sub_entry_monadic_complete_strict} and its \<open>_of_pre\<close>
  corollary. The \<open>qsolve\<close> hypothesis carries the reduced solve's DISJOINTNESS, which
  \<open>defl_isolate_all_split_main_correct_geom\<close> supplies --- so the path-B contract rests on the
  path-C geometry, exactly as the header's argument says.\<close>

theorem pow_sub_entry_monadic_unique:
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
                \<and> iv_disj_mset (mset (defl_wins accP)))"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs
           \<le> SPEC (\<lambda>(out, xs0, ok). ok \<longrightarrow> pow_sub_entry_contract P (defl_wins out))"
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
  have sub: "pow_sub_entry_sub_mop d dlt xs
        \<le> SPEC (\<lambda>(out, xs0, ok). ok \<longrightarrow> pow_sub_entry_contract P (defl_wins out))"
    if d2: "2 \<le> d" and par2: "2 \<le> gcd d 2" and db: "d < max_snat LENGTH(gmp_poly_len)"
      and deq: "d = gcd (pow_sub_h xs) hcap"
    for d
  proof -
    have ev: "even d" by (rule pow_sub_par_even[OF par2])
    show ?thesis
      unfolding P_def
      by (rule pow_sub_entry_sub_mop_unique[OF d2 par2 db ne len1 nz sfP[unfolded P_def]
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

corollary pow_sub_entry_monadic_unique_of_pre:
  fixes xs :: "int list" and nfloor hcap dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and hcb: "hcap < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and qpre: "\<And>d. 2 \<le> d \<Longrightarrow> even d \<Longrightarrow> d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
          dsc_isolate_all_split_defl_pre (pow_sub_extract d xs)"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs
           \<le> SPEC (\<lambda>(out, xs0, ok). ok \<longrightarrow> pow_sub_entry_contract P (defl_wins out))"
proof -
  have q4: "defl_isolate_all_split_main (pow_sub_extract d xs)
        \<le> SPEC (\<lambda>(accP, accN, xs0).
            dyadic_interval_vec_invar accP
            \<and> length (dyadic_interval_vec_triples accP) + 1
                < max_snat LENGTH(gmp_poly_len)
            \<and> pow_sub_reduced_isolates
                 (real_of_int_poly (Poly (pow_sub_extract d xs))) accP
            \<and> iv_disj_mset (mset (defl_wins accP)))"
    if d2: "2 \<le> d" and ev: "even d" and deq: "d = gcd (pow_sub_h xs) hcap" for d
    by (rule weaken_SPEC[OF defl_isolate_all_split_main_correct_geom[OF qpre[OF d2 ev deq]]])
       (auto intro: pow_sub_reduced_isolates_of_defl_acc)
  show ?thesis
    unfolding P_def
    by (rule pow_sub_entry_monadic_unique[OF ne len1 hcb nz sfP[unfolded P_def] q4])
qed


end
