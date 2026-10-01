theory Count_Spec
  imports "IsaRRI_Spec.Dsc_Taylor"
begin

text \<open>Abstract layer of coefficient truncation in the carried Descartes count: the truncation,
  error and threshold mathematics, with no GMP or Sepref content.

  Main results (consumed by \<open>Count\<close>'s kernel classification proof): \<open>trunc_list\<close> (floor-truncate
  all coefficients by \<open>2^t\<close>), \<open>trunc_thresh\<close> (the per-position bit-length trust threshold),
  \<open>trusted_sgn\<close>/\<open>trunc_changes\<close> (the threshold-guarded sign-variation fold), and the two main
  theorems \<open>trunc_changes_ge2_sound\<close> (a guarded count \<open>\<ge> 2\<close> lower-bounds the exact count) and
  \<open>trunc_changes_decisive_exact\<close> (no ambiguity \<Longrightarrow> guarded count = exact count).\<close>

section \<open>Coefficient truncation and its one-sided residue\<close>

text \<open>Floor-truncation of every coefficient by \<open>2^t\<close>. HOL's integer \<open>div\<close> IS floor
  division, matching GMP's \<open>mpz_fdiv_q_2exp\<close> binding (\<open>fdiv_q_2exp a n \<equiv> a div 2^n\<close>)
  exactly. Floor (not truncate-toward-zero, msolve's choice) is deliberate: the residue is
  one-sided, so positive shifted coefficients need no trust threshold at all.\<close>
definition trunc_list :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
  "trunc_list t ys = map (\<lambda>x. x div 2 ^ t) ys"

definition trunc_resid_list :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
  "trunc_resid_list t ys = map (\<lambda>x. x mod 2 ^ t) ys"

lemma length_trunc_list[simp]: "length (trunc_list t ys) = length ys"
  by (simp add: trunc_list_def)

lemma length_trunc_resid_list[simp]: "length (trunc_resid_list t ys) = length ys"
  by (simp add: trunc_resid_list_def)

text \<open>Pointwise decomposition \<open>ys!i = 2^t * trunc + resid\<close> with the one-sided residue
  \<open>0 \<le> resid < 2^t\<close>. Route: \<open>div_mult_mod_eq\<close>, \<open>pos_mod_sign\<close>/\<open>pos_mod_bound\<close>
  (find-thms for the exact current names).\<close>
lemma trunc_decomp_nth:
  assumes "i < length ys"
  shows "ys ! i = 2 ^ t * (trunc_list t ys ! i) + trunc_resid_list t ys ! i"
  using assms
  by (simp add: trunc_list_def trunc_resid_list_def div_mult_mod_eq mult.commute)

lemma trunc_resid_nth_lb:
  assumes "i < length ys"
  shows "0 \<le> trunc_resid_list t ys ! i"
  using assms
  by (simp add: trunc_resid_list_def pos_mod_sign)

lemma trunc_resid_nth_ub:
  assumes "i < length ys"
  shows "trunc_resid_list t ys ! i < 2 ^ t"
  using assms
  by (simp add: trunc_resid_list_def pos_mod_bound)

section \<open>Taylor-shift linearity and the per-position error bound\<close>

text \<open>Worst-case growth of the one-sided residue through the shift-by-1: position \<open>i\<close>
  of the shifted length-\<open>len\<close> list accumulates \<open>\<Sum>_{j\<ge>i} C(j,i) = C(len, i+1)\<close>
  (hockey-stick) units of residue.\<close>
definition shift1_err_bound :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "shift1_err_bound len i = int (len choose Suc i)"

text \<open>Additivity of one \<open>ruffini_step\<close>, generalized over both seed coefficients so
  the induction's recursive calls (which reseed with the head of the tail lists) go
  through unchanged.\<close>
lemma ruffini_step_add:
  assumes "length qs1 = length qs2"
  shows "ruffini_step c (a1 + a2) (map2 (+) qs1 qs2)
       = map2 (+) (ruffini_step c a1 qs1) (ruffini_step c a2 qs2)"
  using assms
proof (induction qs1 qs2 arbitrary: a1 a2 rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons q1 qs1' q2 qs2')
  then show ?case by (simp add: algebra_simps)
qed

text \<open>Linearity of the shift (a fold of \<open>ruffini_step\<close>; each step is linear).
  Route: induction on the lists (equal length), unfolding \<open>ruffini_step\<close>.\<close>
lemma taylor_shift_list_map2_add:
  assumes "length xs = length ys"
  shows "taylor_shift_list c (map2 (+) xs ys)
       = map2 (+) (taylor_shift_list c xs) (taylor_shift_list c ys)"
  using assms
proof (induction xs ys rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case by (simp add: ruffini_step_add)
qed

text \<open>Scalar-multiplicativity of one \<open>ruffini_step\<close>, generalized over the seed
  coefficient for the same reason as above.\<close>
lemma ruffini_step_map_smult:
  "ruffini_step c (a * x) (map ((*) a) qs) = map ((*) a) (ruffini_step c x qs)"
proof (induction qs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons q qs')
  have IH: "ruffini_step c (a * q) (map ((*) a) qs') = map ((*) a) (ruffini_step c q qs')"
    using Cons.IH by blast
  show ?case
    by (simp only: ruffini_step.simps list.map IH) (simp add: algebra_simps)
qed

lemma taylor_shift_list_map_smult:
  "taylor_shift_list c (map ((*) a) ys) = map ((*) a) (taylor_shift_list c ys)"
proof (induction ys)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case by (simp add: ruffini_step_map_smult)
qed

text \<open>Pointwise monotonicity of one \<open>ruffini_step\<close> (\<open>c=1\<close>): nonneg seeds and a
  nonneg pointwise-\<open>\<le>\<close> tail give a nonneg pointwise-\<open>\<le>\<close> result at every position.
  Stated with object-level \<open>\<forall>/\<longrightarrow>\<close> over the seeds/index so the induction's recursive
  call (which reseeds with the head elements) carries the right generality without
  \<open>arbitrary\<close> bookkeeping.\<close>
lemma ruffini_step_mono_all:
  assumes "length qs1 = length qs2"
  shows "\<forall>a1 a2 k. 0 \<le> a1 \<longrightarrow> a1 \<le> a2 \<longrightarrow>
         (\<forall>j<length qs1. 0 \<le> qs1 ! j \<and> qs1 ! j \<le> qs2 ! j) \<longrightarrow>
         k < Suc (length qs1) \<longrightarrow>
         0 \<le> ruffini_step (1::int) a1 qs1 ! k
         \<and> ruffini_step 1 a1 qs1 ! k \<le> ruffini_step 1 a2 qs2 ! k"
  using assms
proof (induction qs1 qs2 rule: list_induct2)
  case Nil
  then show ?case by (auto simp: less_Suc0)
next
  case (Cons q1 qs1' q2 qs2')
  show ?case
  proof (intro allI impI)
    fix a1 a2 :: int and k :: nat
    assume a1: "0 \<le> a1" and a12: "a1 \<le> a2"
      and pw: "\<forall>j<length (q1 # qs1'). 0 \<le> (q1 # qs1') ! j \<and> (q1 # qs1') ! j \<le> (q2 # qs2') ! j"
      and kb: "k < Suc (length (q1 # qs1'))"
    have q12: "0 \<le> q1" "q1 \<le> q2" using pw by auto
    have pw': "\<forall>j<length qs1'. 0 \<le> qs1' ! j \<and> qs1' ! j \<le> qs2' ! j"
      using pw by auto
    show "0 \<le> ruffini_step 1 a1 (q1 # qs1') ! k
        \<and> ruffini_step 1 a1 (q1 # qs1') ! k \<le> ruffini_step 1 a2 (q2 # qs2') ! k"
    proof (cases k)
      case 0
      then show ?thesis using a1 a12 q12 by simp
    next
      case (Suc k')
      then have "0 \<le> ruffini_step 1 q1 qs1' ! k' \<and> ruffini_step 1 q1 qs1' ! k' \<le> ruffini_step 1 q2 qs2' ! k'"
        using Cons.IH q12 pw' kb Suc by auto
      then show ?thesis using Suc by simp
    qed
  qed
qed

text \<open>Convenience \<open>\<Longrightarrow>\<close>-form corollary of the above, for readable call sites.\<close>
lemma ruffini_step_mono:
  assumes "length qs1 = length qs2"
    and "0 \<le> a1" and "a1 \<le> a2"
    and "\<forall>j<length qs1. 0 \<le> qs1 ! j \<and> qs1 ! j \<le> qs2 ! j"
    and "k < Suc (length qs1)"
  shows "0 \<le> ruffini_step (1::int) a1 qs1 ! k
       \<and> ruffini_step 1 a1 qs1 ! k \<le> ruffini_step 1 a2 qs2 ! k"
  using ruffini_step_mono_all[OF assms(1)] assms(2-5) by blast

text \<open>The shift-by-1 matrix is nonnegative: monotone on nonneg inputs, all positions.\<close>
lemma taylor_shift_list_one_mono_all:
  fixes xs ys :: "int list"
  assumes "length xs = length ys"
    and "\<forall>j<length xs. 0 \<le> xs ! j \<and> xs ! j \<le> ys ! j"
  shows "\<forall>i<length xs. 0 \<le> taylor_shift_list 1 xs ! i
       \<and> taylor_shift_list 1 xs ! i \<le> taylor_shift_list 1 ys ! i"
  using assms
proof (induction xs ys rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs' y ys')
  have pw': "\<forall>j<length xs'. 0 \<le> xs' ! j \<and> xs' ! j \<le> ys' ! j"
    using Cons.prems by auto
  have IH': "\<forall>i<length xs'. 0 \<le> taylor_shift_list 1 xs' ! i
       \<and> taylor_shift_list 1 xs' ! i \<le> taylor_shift_list 1 ys' ! i"
    using Cons.IH pw' by blast
  have xy: "0 \<le> x" "x \<le> y" using Cons.prems by auto
  have tlen: "length (taylor_shift_list 1 xs') = length (taylor_shift_list 1 ys')"
    using Cons.hyps(1) by simp
  have pw_shift: "\<forall>k<length (taylor_shift_list 1 xs').
      0 \<le> taylor_shift_list 1 xs' ! k \<and> taylor_shift_list 1 xs' ! k \<le> taylor_shift_list 1 ys' ! k"
    using IH' by simp
  have "\<forall>k<Suc (length (taylor_shift_list 1 xs')).
      0 \<le> ruffini_step 1 x (taylor_shift_list 1 xs') ! k
      \<and> ruffini_step 1 x (taylor_shift_list 1 xs') ! k \<le> ruffini_step 1 y (taylor_shift_list 1 ys') ! k"
    using ruffini_step_mono[OF tlen] xy pw_shift by blast
  then show ?case by simp
qed

text \<open>The shift-by-1 matrix is nonnegative: monotone on nonneg inputs. Pinned to
  \<open>int list\<close>: every other definition in this file (\<open>trunc_list\<close>, \<open>shift_trunc_resid\<close>, ...) is
  already \<open>int\<close>-specific, matching the GMP coefficient domain.\<close>
lemma taylor_shift_list_one_mono:
  fixes xs ys :: "int list"
  assumes "length xs = length ys"
    and "\<And>j. j < length xs \<Longrightarrow> 0 \<le> xs ! j \<and> xs ! j \<le> ys ! j"
    and "i < length xs"
  shows "0 \<le> taylor_shift_list 1 xs ! i
       \<and> taylor_shift_list 1 xs ! i \<le> taylor_shift_list 1 ys ! i"
  using taylor_shift_list_one_mono_all[of xs ys] assms by blast

text \<open>Closed form for one \<open>ruffini_step\<close> at \<open>c=1\<close>: position \<open>k\<close> of the result is
  the adjacent-pair sum \<open>(a#qs)!k + (a#qs)!(k+1)\<close> (the last position has no
  successor to add). Generalized over the seed and index for the same reseeding
  reason as the other \<open>ruffini_step\<close> helpers.\<close>
lemma ruffini_step_one_nth:
  assumes "k \<le> length qs"
  shows "ruffini_step 1 a qs ! k
       = (a # qs) ! k + (if k < length qs then (a # qs) ! Suc k else 0)"
  using assms
proof (induction qs arbitrary: a k)
  case Nil
  then show ?case by simp
next
  case (Cons q qs')
  show ?case
  proof (cases k)
    case 0
    then show ?thesis by simp
  next
    case (Suc k')
    then have "k' \<le> length qs'" using Cons.prems by simp
    then have "ruffini_step 1 q qs' ! k'
        = (q # qs') ! k' + (if k' < length qs' then (q # qs') ! Suc k' else 0)"
      using Cons.IH by blast
    then show ?thesis using Suc by simp
  qed
qed

text \<open>Evaluating the bound: the all-ones input shifts to exactly the hockey-stick
  binomial per position. Route: induction on \<open>len\<close> (all-\<open>i\<close> form), each step an
  adjacent-pair sum via @{thm [source] ruffini_step_one_nth} collapsing to Pascal's
  rule (\<open>binomial_Suc_Suc\<close>); the out-of-range branch matches \<open>binomial_eq_0\<close>
  automatically (no extra case split needed).\<close>
lemma taylor_shift_list_one_replicate_ones_all:
  "\<forall>i<len. taylor_shift_list 1 (replicate len (1::int)) ! i = shift1_err_bound len i"
proof (induction len)
  case 0
  then show ?case by simp
next
  case (Suc n)
  define Tn where "Tn = taylor_shift_list 1 (replicate n (1::int))"
  have Tn_len: "length Tn = n" by (simp add: Tn_def)
  have step: "taylor_shift_list 1 (replicate (Suc n) (1::int)) = ruffini_step 1 1 Tn"
    by (simp add: Tn_def)
  show ?case
  proof (intro allI impI)
    fix i assume i: "i < Suc n"
    have nth: "ruffini_step 1 (1::int) Tn ! i
        = (1 # Tn) ! i + (if i < n then (1 # Tn) ! Suc i else 0)"
      using ruffini_step_one_nth[of i Tn "1::int"] i Tn_len by simp
    show "taylor_shift_list 1 (replicate (Suc n) (1::int)) ! i = shift1_err_bound (Suc n) i"
    proof (cases i)
      case 0
      show ?thesis
      proof (cases "n = 0")
        case True
        with 0 show ?thesis
          by (simp add: shift1_err_bound_def)
      next
        case False
        then have n0: "0 < n" by simp
        then have Tn0: "Tn ! 0 = shift1_err_bound n 0"
          using Suc.IH by (simp add: Tn_def)
        have nth0: "ruffini_step 1 (1::int) Tn ! 0 = 1 + Tn ! 0"
          using nth n0 0 by simp
        show ?thesis
          using step nth0 Tn0 0
          by (simp add: shift1_err_bound_def binomial_Suc_Suc)
      qed
    next
      case (Suc i')
      then have i'n: "i' < n" using i by simp
      then have Tni': "Tn ! i' = shift1_err_bound n i'"
        using Suc.IH by (simp add: Tn_def)
      show ?thesis
      proof (cases "Suc i' < n")
        case True
        then have Tnsi': "Tn ! Suc i' = shift1_err_bound n (Suc i')"
          using Suc.IH by (simp add: Tn_def)
        show ?thesis
          using nth step Tni' Tnsi' True Suc
          by (simp add: shift1_err_bound_def binomial_Suc_Suc)
      next
        case False
        then have "n \<le> Suc i'" by simp
        with i'n have "n = Suc i'" by simp
        then show ?thesis
          using nth step Tni' False Suc
          by (simp add: shift1_err_bound_def binomial_Suc_Suc binomial_eq_0)
      qed
    qed
  qed
qed

lemma taylor_shift_list_one_replicate_ones:
  assumes "i < len"
  shows "taylor_shift_list 1 (replicate len 1) ! i = shift1_err_bound len i"
  using taylor_shift_list_one_replicate_ones_all assms by blast

text \<open>The master error decomposition: the exact shifted coefficient is \<open>2^t\<close> times the
  truncated-then-shifted coefficient plus a one-sided error \<open>< C(len,i+1) * 2^t\<close>.\<close>
definition shift_trunc_resid :: "nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int" where
  "shift_trunc_resid t ys i =
     taylor_shift_list 1 ys ! i - 2 ^ t * (taylor_shift_list 1 (trunc_list t ys) ! i)"

text \<open>List-level form of @{thm [source] trunc_decomp_nth}, needed to invoke the
  shift's linearity.\<close>
lemma trunc_decomp_list:
  "ys = map2 (+) (map ((*) (2 ^ t)) (trunc_list t ys)) (trunc_resid_list t ys)"
  by (rule nth_equalityI) (simp_all add: trunc_decomp_nth)

lemma map_mult_zero_eq_replicate:
  "map ((*) (0::int)) xs = replicate (length xs) 0"
  by (induction xs) simp_all

text \<open>The shift of the all-zero list is all-zero: a free corollary of scalar-\<open>0\<close>
  multiplicativity (\<open>map ((*) 0) qs = replicate (length qs) 0\<close> for any \<open>qs\<close>).\<close>
lemma taylor_shift_list_replicate_zero:
  "taylor_shift_list c (replicate len (0::int)) = replicate len 0"
proof -
  have "replicate len (0::int) = map ((*) 0) (replicate len 1)"
    by (simp add: map_replicate)
  also have "taylor_shift_list c \<dots> = map ((*) 0) (taylor_shift_list c (replicate len (1::int)))"
    by (rule taylor_shift_list_map_smult)
  also have "\<dots> = replicate len 0"
    by (simp add: map_mult_zero_eq_replicate)
  finally show ?thesis by simp
qed

text \<open>The exact residue identity: the shift's error against the truncated-then-shifted
  poly is exactly the shift of the truncation residues (the \<open>2^t\<close>-scaled term cancels
  via linearity). This is the crux that lets the LB/UB fall out of the already-proven
  monotonicity and hockey-stick lemmas.\<close>
lemma shift_trunc_resid_eq:
  assumes "i < length ys"
  shows "shift_trunc_resid t ys i = taylor_shift_list 1 (trunc_resid_list t ys) ! i"
proof -
  have len_eq: "length (map ((*) (2 ^ t)) (trunc_list t ys)) = length (trunc_resid_list t ys)"
    by simp
  have "taylor_shift_list 1 ys
      = taylor_shift_list 1 (map2 (+) (map ((*) (2 ^ t)) (trunc_list t ys)) (trunc_resid_list t ys))"
    using trunc_decomp_list by metis
  also have "\<dots> = map2 (+) (taylor_shift_list 1 (map ((*) (2 ^ t)) (trunc_list t ys)))
                            (taylor_shift_list 1 (trunc_resid_list t ys))"
    by (rule taylor_shift_list_map2_add[OF len_eq])
  also have "taylor_shift_list 1 (map ((*) (2 ^ t)) (trunc_list t ys))
           = map ((*) (2 ^ t)) (taylor_shift_list 1 (trunc_list t ys))"
    by (rule taylor_shift_list_map_smult)
  finally have eq: "taylor_shift_list 1 ys
      = map2 (+) (map ((*) (2 ^ t)) (taylor_shift_list 1 (trunc_list t ys)))
                  (taylor_shift_list 1 (trunc_resid_list t ys))" .
  have ilen: "i < length (taylor_shift_list 1 (trunc_list t ys))"
    using assms by simp
  have "taylor_shift_list 1 ys ! i
      = 2 ^ t * (taylor_shift_list 1 (trunc_list t ys) ! i)
        + taylor_shift_list 1 (trunc_resid_list t ys) ! i"
    using eq ilen by simp
  then show ?thesis
    unfolding shift_trunc_resid_def by simp
qed

lemma shift_trunc_resid_lb:
  assumes "i < length ys"
  shows "0 \<le> shift_trunc_resid t ys i"
proof -
  let ?len = "length ys"
  have len_eq: "length (replicate ?len (0::int)) = length (trunc_resid_list t ys)"
    by simp
  have pw: "\<forall>j<length (replicate ?len (0::int)).
      0 \<le> replicate ?len (0::int) ! j \<and> replicate ?len (0::int) ! j \<le> trunc_resid_list t ys ! j"
    by (auto simp: trunc_resid_nth_lb)
  have "0 \<le> taylor_shift_list 1 (replicate ?len (0::int)) ! i
      \<and> taylor_shift_list 1 (replicate ?len (0::int)) ! i
        \<le> taylor_shift_list 1 (trunc_resid_list t ys) ! i"
    using taylor_shift_list_one_mono[OF len_eq pw[rule_format]] assms by simp
  then show ?thesis
    using shift_trunc_resid_eq[OF assms] by (simp add: taylor_shift_list_replicate_zero)
qed

lemma shift_trunc_resid_ub:
  assumes "i < length ys"
  shows "shift_trunc_resid t ys i < shift1_err_bound (length ys) i * 2 ^ t"
proof -
  let ?len = "length ys"
  have len_eq: "length (trunc_resid_list t ys) = length (replicate ?len (2 ^ t - 1 :: int))"
    by simp
  have pw: "\<forall>j<length (trunc_resid_list t ys).
      0 \<le> trunc_resid_list t ys ! j \<and> trunc_resid_list t ys ! j \<le> replicate ?len (2 ^ t - 1 :: int) ! j"
    by (auto simp: trunc_resid_nth_lb) (metis diff_less_mono2 nth_replicate trunc_resid_nth_ub zless_add1_eq)
  have mono: "taylor_shift_list 1 (trunc_resid_list t ys) ! i
      \<le> taylor_shift_list 1 (replicate ?len (2 ^ t - 1 :: int)) ! i"
    using taylor_shift_list_one_mono[OF len_eq pw[rule_format]] assms by simp
  have const_shift: "taylor_shift_list 1 (replicate ?len (2 ^ t - 1 :: int)) ! i
      = (2 ^ t - 1) * shift1_err_bound ?len i"
  proof -
    have "replicate ?len (2 ^ t - 1 :: int) = map ((*) (2 ^ t - 1)) (replicate ?len 1)"
      by (simp add: map_replicate)
    also have "taylor_shift_list 1 \<dots>
        = map ((*) (2 ^ t - 1)) (taylor_shift_list 1 (replicate ?len (1::int)))"
      by (rule taylor_shift_list_map_smult)
    finally show ?thesis
      using taylor_shift_list_one_replicate_ones[OF assms] assms
      by (simp add: nth_map)
  qed
  have bge1: "1 \<le> shift1_err_bound ?len i"
    unfolding shift1_err_bound_def using assms
    by (simp add: Suc_leI zero_less_binomial)
  have lt: "(2 ^ t - 1) * shift1_err_bound ?len i < shift1_err_bound ?len i * 2 ^ t"
    using bge1 by (simp add: mult_strict_right_mono mult.commute)
  have "taylor_shift_list 1 (trunc_resid_list t ys) ! i < shift1_err_bound ?len i * 2 ^ t"
    using mono const_shift lt by simp
  then show ?thesis
    using shift_trunc_resid_eq[OF assms] by simp
qed

section \<open>The bit-length trust threshold\<close>

text \<open>Minimal \<open>b\<close> with \<open>m < 2^b\<close> (so \<open>nat_bitlen 0 = 0\<close>). Matches the impl-side word
  bit-length loop; \<open>mpz_bitlen2_monadic\<close>'s spec is stated against \<open>2^r\<close> bounds and
  connects directly.\<close>
definition nat_bitlen :: "nat \<Rightarrow> nat" where
  "nat_bitlen m = (LEAST b. m < 2 ^ b)"

lemma nat_bitlen_lt: "m < 2 ^ nat_bitlen m"
  unfolding nat_bitlen_def
  by (rule LeastI_ex) (rule exI[of _ m], rule less_exp)

text \<open>The per-position threshold exponent, capped at \<open>len\<close>. The uncapped bound
  \<open>min (i+1) (len-1-i) * nat_bitlen len\<close> is far too conservative in the middle of the polynomial
  (at degree 96 the middle demands 336 bits of trust margin, where the row-sum bound below gives
  96), which would send every \<open>cnt\<in>{0,1}\<close> node to the exact count. Capping at \<open>len\<close> is sound
  (\<open>shift1_err_bound_le_len\<close> below, the binomial row-sum bound) and matches msolve's own trust test
  (the explicit \<open>min(deg, ...)\<close> in its \<open>utils.c\<close>). At the leading position \<open>i = len-1\<close> the
  threshold is 0: trusted iff nonzero, with no special case.\<close>
definition trunc_thresh :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "trunc_thresh len i = min (min (Suc i) (len - Suc i) * nat_bitlen len) len"

text \<open>Row-sum bound: \<open>C(n,k) \<le> 2^n\<close> for ANY \<open>k\<close> (find-thms \<open>binomial_le_pow2\<close>) —
  the cap's soundness witness, position-independent.\<close>
lemma shift1_err_bound_le_len: "shift1_err_bound len i \<le> 2 ^ len"
  unfolding shift1_err_bound_def by (simp add: binomial_le_pow2)

text \<open>Route: \<open>C(n,k) \<le> n^k\<close> (find-thms \<open>binomial_le_pow\<close>-family) + symmetry
  \<open>C(n,k) = C(n,n-k)\<close> + \<open>len < 2^(nat_bitlen len)\<close> monotone through \<open>^m\<close>; combined
  with the row-sum bound (\<open>shift1_err_bound_le_len\<close>) to land under the CAPPED
  threshold (\<open>min _ len\<close>) via \<open>2^(min a b) = min (2^a) (2^b)\<close>.\<close>
lemma shift1_err_bound_le_thresh:
  assumes "Suc i \<le> len"
  shows "shift1_err_bound len i \<le> 2 ^ trunc_thresh len i"
proof -
  define k where "k = Suc i"
  define m where "m = min k (len - k)"
  have kle: "k \<le> len" using assms k_def by simp
  have step1: "len choose k \<le> len ^ m"
  proof (cases "k \<le> len - k")
    case True
    then have "m = k" by (simp add: m_def)
    then show ?thesis using binomial_le_pow[OF kle] by simp
  next
    case False
    then have meq: "m = len - k" by (simp add: m_def)
    have "len choose k = len choose (len - k)"
      using binomial_symmetric[OF kle] by simp
    also have "\<dots> \<le> len ^ (len - k)"
      using binomial_le_pow[of "len - k" len] by simp
    finally show ?thesis using meq by simp
  qed
  have step2: "len \<le> 2 ^ nat_bitlen len"
    using nat_bitlen_lt[of len] by simp
  have step3: "len ^ m \<le> (2 ^ nat_bitlen len) ^ m"
    by (rule power_mono[OF step2]) simp
  have step4: "(2 ^ nat_bitlen len) ^ m = (2::nat) ^ (m * nat_bitlen len)"
  proof -
    have "(2 ^ nat_bitlen len) ^ m = (2::nat) ^ (nat_bitlen len * m)"
      by (simp add: power_mult)
    then show ?thesis by (simp add: mult.commute)
  qed
  have uncapped: "len choose k \<le> 2 ^ (m * nat_bitlen len)"
    using step1 step3 step4 by simp
  have capped: "shift1_err_bound len i \<le> 2 ^ (m * nat_bitlen len)"
    unfolding shift1_err_bound_def using uncapped by (simp add: k_def of_nat_mono)
  have rowsum: "shift1_err_bound len i \<le> 2 ^ len"
    using shift1_err_bound_le_len .
  show ?thesis
    unfolding trunc_thresh_def
  proof (cases "min (Suc i) (len - Suc i) * nat_bitlen len \<le> len")
    case True
    then show "shift1_err_bound len i
        \<le> 2 ^ min (min (Suc i) (len - Suc i) * nat_bitlen len) len"
      using capped by (simp add: k_def m_def)
  next
    case False
    then show "shift1_err_bound len i
        \<le> 2 ^ min (min (Suc i) (len - Suc i) * nat_bitlen len) len"
      using rowsum by simp
  qed
qed

section \<open>Subsequence monotonicity of \<open>changes\<close> (Sturm\_Tarski's clean 2-lookahead
  recursive sign-variation count) -- the bridge that makes the trusted-subsequence
  argument tractable\<close>

text \<open>Bridged to our \<open>sign_changes_fold\<close> via the two EXISTING lemmas
  @{thm [source] changes_eq_sign_changes} (\<open>List_Changes.thy\<close>) and
  @{thm [source] sign_changes_eq_fold} (\<open>Dsc_Taylor.thy\<close>): \<open>changes xs = int
  (sign_changes_fold xs)\<close>. \<open>changes\<close>'s definition already treats a literal \<open>0\<close>
  entry as transparent (skip, keep prior reference) -- exactly
  @{thm [source] changes_filter_zeros} -- which makes masking arguments direct
  structural inductions instead of fold-state bookkeeping.\<close>
lemma changes_eq_sign_changes_fold:
  fixes xs :: "int list"
  shows "changes xs = int (sign_changes_fold xs)"
  using changes_eq_sign_changes[of xs] sign_changes_eq_fold[of xs] by simp

text \<open>A literal \<open>0\<close> entry contributes nothing (transparent to \<open>changes\<close>), regardless
  of position.\<close>
lemma changes_zero_skip:
  "changes (us @ (0::int) # vs) = changes (us @ vs)"
proof -
  have "changes (us @ 0 # vs) = changes (filter (\<lambda>x. x \<noteq> 0) (us @ 0 # vs))"
    by (rule changes_filter_zeros)
  also have "\<dots> = changes (filter (\<lambda>x. x \<noteq> 0) (us @ vs))"
    by simp
  also have "\<dots> = changes (us @ vs)"
    using changes_filter_zeros[of "us @ vs"] by simp
  finally show ?thesis .
qed

text \<open>Inserting ONE element anywhere never decreases \<open>changes\<close> -- the \<open>int\<close>
  instance of the AFP's \<open>sign_changes_remove_general\<close> (there fixed at \<open>real\<close>;
  the underlying machinery, \<open>length_remdups_adj_insert_le\<close>, is fully polymorphic,
  so the proof carries over verbatim).\<close>
lemma changes_insert_general:
  fixes x :: int
  shows "changes (us @ vs) \<le> changes (us @ [x] @ vs)"
proof (cases "x = 0")
  case True
  then show ?thesis using changes_zero_skip[of us vs] by simp
next
  case False
  let ?signs_U = "filter (\<lambda>z. z \<noteq> 0) (map sgn us)"
  let ?signs_V = "filter (\<lambda>z. z \<noteq> 0) (map sgn vs)"
  have LHS: "sign_changes_fold (us @ vs) = length (remdups_adj (?signs_U @ ?signs_V)) - 1"
    unfolding sign_changes_eq_fold[symmetric] Descartes_Sign_Rule.sign_changes_def
    by (simp add: filter_map o_def)
  have RHS: "sign_changes_fold (us @ [x] @ vs)
      = length (remdups_adj (?signs_U @ [sgn x] @ ?signs_V)) - 1"
    using False
    unfolding sign_changes_eq_fold[symmetric] Descartes_Sign_Rule.sign_changes_def
    by (simp add: sgn_eq_0_iff)
  have mono: "length (remdups_adj (?signs_U @ ?signs_V)) - 1
            \<le> length (remdups_adj (?signs_U @ sgn x # ?signs_V)) - 1"
    using length_remdups_adj_insert_le[of ?signs_U ?signs_V "sgn x"] diff_le_mono by blast
  have "sign_changes_fold (us @ vs) \<le> sign_changes_fold (us @ x # vs)"
    using LHS RHS mono by simp
  then have "int (sign_changes_fold (us @ vs)) \<le> int (sign_changes_fold (us @ x # vs))"
    by (rule of_nat_mono)
  then show ?thesis
    unfolding changes_eq_sign_changes_fold by simp
qed

text \<open>The masking-monotonicity workhorse, generalized over a COMMON PREFIX \<open>us\<close> that
  grows by one matched element per induction step (case \<open>z=t\<close>) or stays put while
  the mismatched \<open>0\<close> is skipped and the true element inserted back (case \<open>z=0\<close>).\<close>
lemma changes_mask_le_prefix:
  fixes us :: "int list"
  assumes "length zs = length ts"
    and "\<forall>j<length zs. zs ! j = 0 \<or> zs ! j = ts ! j"
  shows "changes (us @ zs) \<le> changes (us @ ts)"
  using assms
proof (induction zs ts arbitrary: us rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons z zs' t ts')
  have z_case: "z = 0 \<or> z = t" using Cons.prems by (metis length_greater_0_conv list.discI nth_Cons_0)
  have pw': "\<forall>j<length zs'. zs' ! j = 0 \<or> zs' ! j = ts' ! j"
    using Cons.prems by fastforce
  from z_case show ?case
  proof
    assume zt: "z = t"
    have "us @ z # zs' = (us @ [t]) @ zs'" using zt by simp
    also have "changes \<dots> \<le> changes ((us @ [t]) @ ts')"
      using Cons.IH[of "us @ [t]"] pw' by simp
    also have "(us @ [t]) @ ts' = us @ t # ts'" by simp
    finally show ?thesis by simp
  next
    assume z0: "z = 0"
    have "changes (us @ z # zs') = changes (us @ zs')"
      unfolding z0 by (rule changes_zero_skip)
    also have "\<dots> \<le> changes (us @ ts')"
      using Cons.IH[of us] pw' by simp
    also have "\<dots> \<le> changes (us @ [t] @ ts')"
      using changes_insert_general by simp
    also have "us @ [t] @ ts' = us @ t # ts'" by simp
    finally show ?thesis by simp
  qed
qed

lemma changes_mask_le:
  fixes zs ts :: "int list"
  assumes "length zs = length ts"
    and "\<forall>j<length zs. zs ! j = 0 \<or> zs ! j = ts ! j"
  shows "changes zs \<le> changes ts"
  using changes_mask_le_prefix[of zs ts "[]"] assms by simp

section \<open>Trusted signs and the guarded sign-variation fold\<close>

text \<open>Trust classification of ONE truncated-shifted coefficient at position \<open>i\<close>:
  positive \<Rightarrow> trusted \<open>+\<close> (free, one-sided residue); \<open>\<le> -2^thresh\<close> \<Rightarrow> trusted \<open>-\<close>;
  the window \<open>(-2^thresh, 0]\<close> is ambiguous (\<open>None\<close>). The impl tests the negative
  branch as \<open>sgn < 0 \<and> thresh < bitlen\<close> — equivalent via the \<open>mpz_bitlen2\<close> spec.\<close>
definition trusted_sgn :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int option" where
  "trusted_sgn len i x =
     (if 0 < x then Some 1
      else if x \<le> - (2 ^ trunc_thresh len i) then Some (-1)
      else None)"

text \<open>A trusted sign IS the exact sign of the corresponding full-precision shifted
  coefficient (in particular that coefficient is nonzero). Assembles the error
  decomposition with the threshold obligation.\<close>
lemma trusted_sgn_sound:
  assumes "i < length ys"
    and "trusted_sgn (length ys) i (taylor_shift_list 1 (trunc_list t ys) ! i) = Some s"
  shows "sgn (taylor_shift_list 1 ys ! i) = s"
proof -
  let ?len = "length ys"
  define Tp where "Tp = taylor_shift_list 1 (trunc_list t ys) ! i"
  define T where "T = taylor_shift_list 1 ys ! i"
  have decomp: "T = 2 ^ t * Tp + shift_trunc_resid t ys i"
    unfolding T_def Tp_def shift_trunc_resid_def by simp
  have lb: "0 \<le> shift_trunc_resid t ys i" using shift_trunc_resid_lb[OF assms(1)] .
  have ub: "shift_trunc_resid t ys i < shift1_err_bound ?len i * 2 ^ t"
    using shift_trunc_resid_ub[OF assms(1)] .
  have thresh: "shift1_err_bound ?len i \<le> 2 ^ trunc_thresh ?len i"
    using shift1_err_bound_le_thresh[of i ?len] assms(1) by simp
  have cases_s: "(0 < Tp \<and> s = 1) \<or> (Tp \<le> -(2 ^ trunc_thresh ?len i) \<and> s = -1)"
    using assms(2) unfolding trusted_sgn_def Tp_def
    by (auto split: if_splits)
  from cases_s show ?thesis
  proof
    assume "0 < Tp \<and> s = 1"
    then have Tp_pos: "0 < Tp" and s1: "s = 1" by auto
    have "0 < 2 ^ t * Tp" using Tp_pos by simp
    then have "0 < T" using decomp lb by linarith
    then show ?thesis unfolding T_def s1 by simp
  next
    assume "Tp \<le> -(2 ^ trunc_thresh ?len i) \<and> s = -1"
    then have Tp_neg: "Tp \<le> -(2 ^ trunc_thresh ?len i)" and sm1: "s = -1" by auto
    have h1: "2 ^ t * Tp \<le> 2 ^ t * (- (2 ^ trunc_thresh ?len i))"
      by (intro mult_left_mono Tp_neg) simp
    have h2: "shift_trunc_resid t ys i \<le> shift1_err_bound ?len i * 2 ^ t - 1"
      using ub by simp
    have "T \<le> 2 ^ t * (- (2 ^ trunc_thresh ?len i)) + (shift1_err_bound ?len i * 2 ^ t - 1)"
      unfolding decomp using h1 h2 by (rule add_mono)
    also have "\<dots> = 2 ^ t * (shift1_err_bound ?len i - 2 ^ trunc_thresh ?len i) - 1"
      by (simp add: algebra_simps)
    also have "\<dots> \<le> 2 ^ t * 0 - 1"
      using thresh by (intro diff_mono mult_left_mono) auto
    finally have "T < 0" by simp
    then show ?thesis unfolding T_def sm1 by simp
  qed
qed

text \<open>The guarded fold state: (last trusted sign, count of trusted sign changes,
  ambiguity seen). \<open>cnt\<close>/\<open>amb\<close> naming — \<open>changes\<close> is a \<open>List_Changes\<close> constant
  (CONVENTIONS section 3).\<close>
fun tsign_step :: "int option \<Rightarrow> int \<times> nat \<times> bool \<Rightarrow> int \<times> nat \<times> bool" where
  "tsign_step None (last_s, cnt, amb) = (last_s, cnt, True)"
| "tsign_step (Some s) (last_s, cnt, amb) =
     (s, (if last_s \<noteq> 0 \<and> s \<noteq> last_s then cnt + 1 else cnt), amb)"

definition trunc_changes :: "nat \<Rightarrow> int list \<Rightarrow> nat \<times> bool" where
  "trunc_changes len ys =
     (case fold (\<lambda>(i, x). tsign_step (trusted_sgn len i x))
            (zip [0..<length ys] ys) (0, 0, False)
      of (_, cnt, amb) \<Rightarrow> (cnt, amb))"

text \<open>The representative value used to reduce \<open>tsign_step\<close> to plain \<open>sign_step\<close>:
  the trusted sign itself (always nonzero, \<open>\<in>{1,-1}\<close>) when trusted, \<open>0\<close> (transparent
  to \<open>sign_step\<close>, exactly like \<open>tsign_step\<close>'s \<open>None\<close> branch) when not.\<close>
definition tsign_repr :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "tsign_repr len i x = (case trusted_sgn len i x of Some s \<Rightarrow> s | None \<Rightarrow> 0)"

text \<open>One \<open>tsign_step\<close> matches one \<open>sign_step\<close> on the representative value, EXACTLY
  (dropping the ambiguity component) -- given the invariant \<open>last_s = 0 \<longrightarrow> cnt = 0\<close>
  (always true from a \<open>(0,0,...)\<close> start, since \<open>cnt\<close> only ever changes together with
  \<open>last_s\<close> becoming/staying nonzero).\<close>
lemma tsign_step_eq_sign_step:
  assumes "last_s = 0 \<longrightarrow> cnt = 0"
  shows "(\<lambda>(a,b,c). (a,b)) (tsign_step (trusted_sgn len i x) (last_s, cnt, amb))
       = sign_step (tsign_repr len i x) (last_s, cnt)"
  using assms
  unfolding tsign_repr_def trusted_sgn_def
  by (cases "0 < x"; cases "x \<le> - (2 ^ trunc_thresh len i)") auto

text \<open>The invariant is preserved by one step (needed to chain the correspondence
  through a whole fold).\<close>
lemma tsign_step_invar:
  assumes "last_s = 0 \<longrightarrow> cnt = 0"
    and "tsign_step (trusted_sgn len i x) (last_s, cnt, amb) = (last_s', cnt', amb')"
  shows "last_s' = 0 \<longrightarrow> cnt' = 0"
  using assms
  unfolding trusted_sgn_def
  by (cases "0 < x"; cases "x \<le> - (2 ^ trunc_thresh len i)") auto

text \<open>Recursive index-tracked reformulation of \<open>trunc_changes\<close>'s fold -- a helper
  \<open>fun\<close> (proof-only, does not touch \<open>trunc_changes\<close>'s own definition) that makes
  the correspondence proof a plain structural induction instead of \<open>zip\<close>/\<open>upt\<close>
  bookkeeping.\<close>
fun tsign_fold_idx :: "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int \<times> nat \<times> bool \<Rightarrow> int \<times> nat \<times> bool" where
  "tsign_fold_idx len i0 [] st = st"
| "tsign_fold_idx len i0 (x # xs) st =
     tsign_fold_idx len (Suc i0) xs (tsign_step (trusted_sgn len i0 x) st)"

lemma fold_tsign_eq_idx:
  "fold (\<lambda>(i, x). tsign_step (trusted_sgn len i x)) (zip [i0..<i0 + length xs] xs) st
     = tsign_fold_idx len i0 xs st"
proof (induction xs arbitrary: i0 st)
  case Nil
  then show ?case by simp
next
  case (Cons x xs')
  have "[i0..<i0 + length (x # xs')] = i0 # [Suc i0..<i0 + length (x # xs')]"
    by (rule upt_conv_Cons) simp
  then have "[i0..<i0 + length (x # xs')] = i0 # [Suc i0..<Suc i0 + length xs']"
    by simp
  then show ?case
    using Cons.IH[of "Suc i0" "tsign_step (trusted_sgn len i0 x) st"]
    by simp
qed

text \<open>The masked representative list, matching \<open>tsign_fold_idx\<close>'s consumption
  order (position \<open>i0+j\<close> for the \<open>j\<close>-th element of \<open>xs\<close>).\<close>
definition tsign_Z :: "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list" where
  "tsign_Z len i0 xs = map (\<lambda>j. tsign_repr len (i0 + j) (xs ! j)) [0..<length xs]"

lemma length_tsign_Z[simp]: "length (tsign_Z len i0 xs) = length xs"
  by (simp add: tsign_Z_def)

text \<open>The core correspondence: \<open>tsign_fold_idx\<close>'s \<open>(last\_s,cnt)\<close> components equal
  plain \<open>sign_step\<close> folded over the masked representative list, EXACTLY (given the
  invariant on the initial state). Proof by induction on \<open>xs\<close>, arbitrary \<open>i0\<close> and
  state -- each step reduces via @{thm [source] tsign_step_eq_sign_step}.\<close>
lemma tsign_fold_idx_eq_sign_step:
  assumes "last_s = 0 \<longrightarrow> cnt = 0"
  shows "(\<lambda>(a,b,c). (a,b)) (tsign_fold_idx len i0 xs (last_s, cnt, amb))
       = fold sign_step (tsign_Z len i0 xs) (last_s, cnt)"
  using assms
proof (induction xs arbitrary: i0 last_s cnt amb)
  case Nil
  then show ?case by (simp add: tsign_Z_def)
next
  case (Cons x xs')
  obtain ls1 cnt1 amb1 where step1:
    "tsign_step (trusted_sgn len i0 x) (last_s, cnt, amb) = (ls1, cnt1, amb1)"
    by (cases "tsign_step (trusted_sgn len i0 x) (last_s, cnt, amb)")
  have eq1: "(ls1, cnt1) = sign_step (tsign_repr len i0 x) (last_s, cnt)"
    using tsign_step_eq_sign_step[OF Cons.prems, of len i0 x amb] step1 by simp
  have invar1: "ls1 = 0 \<longrightarrow> cnt1 = 0"
    using tsign_step_invar[OF Cons.prems step1] .
  have "(\<lambda>(a,b,c). (a,b)) (tsign_fold_idx len i0 (x # xs') (last_s, cnt, amb))
      = (\<lambda>(a,b,c). (a,b)) (tsign_fold_idx len (Suc i0) xs' (ls1, cnt1, amb1))"
    using step1 by simp
  also have "\<dots> = fold sign_step (tsign_Z len (Suc i0) xs') (ls1, cnt1)"
    using Cons.IH[OF invar1] by simp
  also have "\<dots> = fold sign_step (tsign_Z len (Suc i0) xs') (sign_step (tsign_repr len i0 x) (last_s, cnt))"
    using eq1 by simp
  also have "\<dots> = fold sign_step (tsign_repr len i0 x # tsign_Z len (Suc i0) xs') (last_s, cnt)"
    by simp
  also have "tsign_repr len i0 x # tsign_Z len (Suc i0) xs' = tsign_Z len i0 (x # xs')"
    unfolding tsign_Z_def
    by (simp add: map_upt_Suc del: upt_Suc)
  finally show ?case .
qed

text \<open>Direction 1 (usable even WITH ambiguity — powers the early-abort-at-2 branch):
  trusted signs are exact signs of a SUBSEQUENCE of the full shifted list, and a
  subsequence never has more sign changes than the full sequence. Route: find-thms
  \<open>List_Changes\<close>/\<open>Descartes_Sign_Rule\<close> for an existing sublist-monotonicity of
  \<open>changes\<close> first; else induction on the fold with the prefix invariant.\<close>
text \<open>\<^bold>\<open>The general form.\<close> The masking argument below never mentions the threshold: it proves
  that the trusted count is a lower bound on the exact count outright, via
  @{thm [source] changes_mask_le} on a subsequence. The version at \<open>2\<close> and the version at an
  arbitrary \<open>cap\<close> (an early abort at that cap) are both one-line corollaries below.\<close>
lemma trunc_changes_le_sound:
  shows "fst (trunc_changes (length ys) (taylor_shift_list 1 (trunc_list t ys)))
           \<le> sign_changes_fold (taylor_shift_list 1 ys)"
proof -
  let ?len = "length ys"
  let ?xs = "taylor_shift_list 1 (trunc_list t ys)"
  let ?T = "taylor_shift_list 1 ys"
  have len_xs: "length ?xs = ?len" by simp
  have tc_eq: "trunc_changes ?len ?xs
      = (case tsign_fold_idx ?len 0 ?xs (0, 0, False) of (_, cnt, amb) \<Rightarrow> (cnt, amb))"
    unfolding trunc_changes_def
    using fold_tsign_eq_idx[of ?len 0 ?xs "(0, 0, False)"] len_xs
    by (simp add: id_def cong: prod.case_cong)
  obtain ls1 cnt1 amb1 where st1: "tsign_fold_idx ?len 0 ?xs (0, 0, False) = (ls1, cnt1, amb1)"
    by (cases "tsign_fold_idx ?len 0 ?xs (0, 0, False)") auto
  have cnt_eq: "fst (trunc_changes ?len ?xs) = cnt1"
    using tc_eq st1 by simp
  have corr: "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx ?len 0 ?xs (0, 0, False))
      = fold sign_step (tsign_Z ?len 0 ?xs) (0, 0)"
    using tsign_fold_idx_eq_sign_step[of 0 0 ?len 0 ?xs False] by simp
  have cnt1_eq: "cnt1 = sign_changes_fold (tsign_Z ?len 0 ?xs)"
    using corr st1 unfolding sign_changes_fold_def by (metis snd_conv split_conv)
  have pw: "\<forall>j < length (tsign_Z ?len 0 ?xs).
      tsign_Z ?len 0 ?xs ! j = 0 \<or> tsign_Z ?len 0 ?xs ! j = (map sgn ?T) ! j"
  proof (intro allI impI)
    fix j assume j: "j < length (tsign_Z ?len 0 ?xs)"
    then have jlen: "j < ?len" by simp
    then have jxlen: "j < length ?xs" using len_xs by simp
    show "tsign_Z ?len 0 ?xs ! j = 0 \<or> tsign_Z ?len 0 ?xs ! j = (map sgn ?T) ! j"
    proof (cases "trusted_sgn ?len j (?xs ! j)")
      case None
      then have "tsign_Z ?len 0 ?xs ! j = 0"
        unfolding tsign_Z_def tsign_repr_def using jxlen by simp
      then show ?thesis by simp
    next
      case (Some s)
      then have z_eq: "tsign_Z ?len 0 ?xs ! j = s"
        unfolding tsign_Z_def tsign_repr_def using jxlen by simp
      have "sgn (?T ! j) = s"
        using trusted_sgn_sound[of j ys t s] jlen Some by simp
      then show ?thesis using z_eq jlen by simp
    qed
  qed
  have lens: "length (tsign_Z ?len 0 ?xs) = length (map sgn ?T)"
    using len_xs by simp
  have mask_le: "changes (tsign_Z ?len 0 ?xs) \<le> changes (map sgn ?T)"
    using changes_mask_le[OF lens] pw by simp
  have lhs_eq: "changes (tsign_Z ?len 0 ?xs) = int cnt1"
    using changes_eq_sign_changes_fold[of "tsign_Z ?len 0 ?xs"] cnt1_eq by simp
  have rhs_eq: "changes (map sgn ?T) = int (sign_changes_fold ?T)"
    using changes_map_sgn_eq[of ?T] changes_eq_sign_changes_fold[of ?T] by simp
  have "cnt1 \<le> sign_changes_fold ?T"
    using mask_le lhs_eq rhs_eq by simp
  then show ?thesis
    using cnt_eq by simp
qed

text \<open>The specialisation the solvers use, a corollary of the general bound above.\<close>
lemma trunc_changes_ge2_sound:
  assumes "2 \<le> fst (trunc_changes (length ys) (taylor_shift_list 1 (trunc_list t ys)))"
  shows "2 \<le> sign_changes_fold (taylor_shift_list 1 ys)"
  using assms trunc_changes_le_sound[of ys t] by simp

text \<open>The early abort at an arbitrary cap is sound by the same bound.\<close>
lemma trunc_changes_ge_cap_sound:
  assumes "cap \<le> fst (trunc_changes (length ys) (taylor_shift_list 1 (trunc_list t ys)))"
  shows "cap \<le> sign_changes_fold (taylor_shift_list 1 ys)"
  using assms trunc_changes_le_sound[of ys t] by simp

text \<open>The ambiguity flag is exactly "some position hit \<open>None\<close>" (it starts at the
  given seed and only ever gets OR-ed with a fresh \<open>None\<close> hit, per \<open>tsign_step\<close>'s
  own definition -- monotone, never reset).\<close>
lemma tsign_fold_idx_amb_iff:
  "(\<lambda>(a, b, c). c) (tsign_fold_idx len i0 xs (last_s, cnt, amb0))
     \<longleftrightarrow> (amb0 \<or> (\<exists>j < length xs. trusted_sgn len (i0 + j) (xs ! j) = None))"
proof (induction xs arbitrary: i0 last_s cnt amb0)
  case Nil
  then show ?case by simp
next
  case (Cons x xs')
  obtain ls1 cnt1 amb1 where step1:
    "tsign_step (trusted_sgn len i0 x) (last_s, cnt, amb0) = (ls1, cnt1, amb1)"
    by (cases "tsign_step (trusted_sgn len i0 x) (last_s, cnt, amb0)")
  have amb1_eq: "amb1 = (amb0 \<or> trusted_sgn len i0 x = None)"
    using step1 by (cases "trusted_sgn len i0 x") auto
  have "(\<lambda>(a, b, c). c) (tsign_fold_idx len i0 (x # xs') (last_s, cnt, amb0))
      = (\<lambda>(a, b, c). c) (tsign_fold_idx len (Suc i0) xs' (ls1, cnt1, amb1))"
    using step1 by simp
  also have "\<dots> \<longleftrightarrow> (amb1 \<or> (\<exists>j < length xs'. trusted_sgn len (Suc i0 + j) (xs' ! j) = None))"
    using Cons.IH by simp
  also have "\<dots> \<longleftrightarrow>
      (amb0 \<or> trusted_sgn len i0 x = None
       \<or> (\<exists>j < length xs'. trusted_sgn len (Suc i0 + j) (xs' ! j) = None))"
    using amb1_eq by simp
  also have "\<dots> \<longleftrightarrow> (amb0 \<or> (\<exists>j < length (x # xs'). trusted_sgn len (i0 + j) ((x # xs') ! j) = None))"
    by (auto simp: less_Suc_eq_0_disj)
  finally show ?case .
qed

text \<open>Direction 2 (the decisive case): NO ambiguity anywhere \<Longrightarrow> every full-precision
  shifted coefficient is nonzero with sign equal to its trusted sign, so the trusted
  sign sequence equals the filtered nonzero sign sequence of the exact shift and the
  counts agree EXACTLY. Route: \<open>trusted_sgn_sound\<close> + @{thm [source]
  fold_sign_step_map_filter}.\<close>
lemma trunc_changes_decisive_exact:
  assumes "\<not> snd (trunc_changes (length ys) (taylor_shift_list 1 (trunc_list t ys)))"
  shows "fst (trunc_changes (length ys) (taylor_shift_list 1 (trunc_list t ys)))
       = sign_changes_fold (taylor_shift_list 1 ys)"
proof -
  let ?len = "length ys"
  let ?xs = "taylor_shift_list 1 (trunc_list t ys)"
  let ?T = "taylor_shift_list 1 ys"
  have len_xs: "length ?xs = ?len" by simp
  have tc_eq: "trunc_changes ?len ?xs
      = (case tsign_fold_idx ?len 0 ?xs (0, 0, False) of (_, cnt, amb) \<Rightarrow> (cnt, amb))"
    unfolding trunc_changes_def
    using fold_tsign_eq_idx[of ?len 0 ?xs "(0, 0, False)"] len_xs
    by (simp add: id_def cong: prod.case_cong)
  obtain ls1 cnt1 amb1 where st1: "tsign_fold_idx ?len 0 ?xs (0, 0, False) = (ls1, cnt1, amb1)"
    by (cases "tsign_fold_idx ?len 0 ?xs (0, 0, False)") auto
  have cnt_eq: "fst (trunc_changes ?len ?xs) = cnt1"
    using tc_eq st1 by simp
  have amb_eq: "snd (trunc_changes ?len ?xs) = amb1"
    using tc_eq st1 by simp
  have no_none: "\<forall>j < length ?xs. trusted_sgn ?len j (?xs ! j) \<noteq> None"
    using tsign_fold_idx_amb_iff[of ?len 0 ?xs 0 0 False] st1 amb_eq assms by auto
  have corr: "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx ?len 0 ?xs (0, 0, False))
      = fold sign_step (tsign_Z ?len 0 ?xs) (0, 0)"
    using tsign_fold_idx_eq_sign_step[of 0 0 ?len 0 ?xs False] by simp
  have cnt1_eq: "cnt1 = sign_changes_fold (tsign_Z ?len 0 ?xs)"
    using corr st1 unfolding sign_changes_fold_def by (metis snd_conv split_conv)
  have exact: "tsign_Z ?len 0 ?xs = map sgn ?T"
  proof (rule nth_equalityI)
    show "length (tsign_Z ?len 0 ?xs) = length (map sgn ?T)" using len_xs by simp
    fix j assume "j < length (tsign_Z ?len 0 ?xs)"
    then have jlen: "j < ?len" by simp
    then have jxlen: "j < length ?xs" using len_xs by simp
    obtain s where some_s: "trusted_sgn ?len j (?xs ! j) = Some s"
      using no_none jxlen by (cases "trusted_sgn ?len j (?xs ! j)") auto
    have z_eq: "tsign_Z ?len 0 ?xs ! j = s"
      unfolding tsign_Z_def tsign_repr_def using jxlen some_s by simp
    have "sgn (?T ! j) = s"
      using trusted_sgn_sound[of j ys t s] jlen some_s by simp
    then show "tsign_Z ?len 0 ?xs ! j = map sgn ?T ! j"
      using z_eq jxlen by simp
  qed
  have lhs_eq: "changes (tsign_Z ?len 0 ?xs) = int cnt1"
    using changes_eq_sign_changes_fold[of "tsign_Z ?len 0 ?xs"] cnt1_eq by simp
  have rhs_eq: "changes (map sgn ?T) = int (sign_changes_fold ?T)"
    using changes_map_sgn_eq[of ?T] changes_eq_sign_changes_fold[of ?T] by simp
  have "cnt1 = sign_changes_fold ?T"
    using exact lhs_eq rhs_eq by simp
  then show ?thesis
    using cnt_eq by simp
qed

section \<open>Kernel-bridging helpers (consumed by \<open>Count.thy\<close>'s classify proof)\<close>

text \<open>Splitting the indexed fold across an append -- the workhorse for both the
  per-step invariant unfold (\<open>take (Suc i) = take i @ [nth i]\<close>) and the early-abort
  prefix bound (\<open>xs = take i xs @ drop i xs\<close>).\<close>
lemma tsign_fold_idx_append:
  "tsign_fold_idx len i0 (xs @ ys) st
     = tsign_fold_idx len (i0 + length xs) ys (tsign_fold_idx len i0 xs st)"
  by (induction xs arbitrary: i0 st) simp_all

lemma tsign_fold_idx_take_Suc:
  assumes "i < length xs"
  shows "tsign_fold_idx len i0 (take (Suc i) xs) st
       = tsign_step (trusted_sgn len (i0 + i) (xs ! i)) (tsign_fold_idx len i0 (take i xs) st)"
proof -
  have "take (Suc i) xs = take i xs @ [xs ! i]"
    using assms by (rule take_Suc_conv_app_nth)
  then have "tsign_fold_idx len i0 (take (Suc i) xs) st
      = tsign_fold_idx len (i0 + length (take i xs)) [xs ! i] (tsign_fold_idx len i0 (take i xs) st)"
    by (simp add: tsign_fold_idx_append)
  also have "length (take i xs) = i" using assms by simp
  finally show ?thesis by simp
qed

text \<open>The \<open>(last_s, cnt)\<close> components never look at the ambiguity bit -- congruence
  over folds whose start states agree on \<open>(last_s, cnt)\<close>.\<close>
lemma tsign_step_fst_snd_cong:
  assumes "(\<lambda>(a, b, c). (a, b)) st = (\<lambda>(a, b, c). (a, b)) st'"
  shows "(\<lambda>(a, b, c). (a, b)) (tsign_step os st) = (\<lambda>(a, b, c). (a, b)) (tsign_step os st')"
  using assms by (cases os; cases st; cases st') auto

lemma tsign_fold_idx_fst_snd_cong:
  assumes "(\<lambda>(a, b, c). (a, b)) st = (\<lambda>(a, b, c). (a, b)) st'"
  shows "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx len i0 xs st)
       = (\<lambda>(a, b, c). (a, b)) (tsign_fold_idx len i0 xs st')"
  using assms
proof (induction xs arbitrary: i0 st st')
  case Nil
  then show ?case by simp
next
  case (Cons x xs')
  show ?case
    using Cons.IH[OF tsign_step_fst_snd_cong[OF Cons.prems]] by simp
qed

text \<open>The ambiguity bit is a monotone OR of the seed with the \<open>None\<close>-hits -- so a
  non-\<open>False\<close> seed just ORs in (a direct corollary of @{thm [source]
  tsign_fold_idx_amb_iff}).\<close>
lemma tsign_fold_idx_amb_or:
  "(\<lambda>(a, b, c). c) (tsign_fold_idx len i0 xs (ls, cnt, amb0))
     = (amb0 \<or> (\<lambda>(a, b, c). c) (tsign_fold_idx len i0 xs (ls, cnt, False)))"
  using tsign_fold_idx_amb_iff[of len i0 xs ls cnt amb0]
        tsign_fold_idx_amb_iff[of len i0 xs ls cnt False]
  by simp

text \<open>The count component never decreases along the fold (each step adds 0 or 1).\<close>
lemma tsign_step_cnt_mono:
  "(\<lambda>(a, b, c). b) st \<le> (\<lambda>(a, b, c). b) (tsign_step os st)"
  by (cases os; cases st) auto

lemma tsign_fold_idx_cnt_mono:
  "(\<lambda>(a, b, c). b) st \<le> (\<lambda>(a, b, c). b) (tsign_fold_idx len i0 xs st)"
proof (induction xs arbitrary: i0 st)
  case Nil
  then show ?case by simp
next
  case (Cons x xs')
  have "(\<lambda>(a, b, c). b) st \<le> (\<lambda>(a, b, c). b) (tsign_step (trusted_sgn len i0 x) st)"
    by (rule tsign_step_cnt_mono)
  also have "\<dots> \<le> (\<lambda>(a, b, c). b) (tsign_fold_idx len (Suc i0) xs' (tsign_step (trusted_sgn len i0 x) st))"
    by (rule Cons.IH)
  finally show ?case by simp
qed

text \<open>\<open>trunc_changes\<close> in terms of the recursive indexed fold (the reusable form of
  the conversion used inline by the two main theorems above).\<close>
lemma trunc_changes_conv_fold_idx:
  "trunc_changes len xs
     = (case tsign_fold_idx len 0 xs (0, 0, False) of (_, cnt, amb) \<Rightarrow> (cnt, amb))"
  unfolding trunc_changes_def
  using fold_tsign_eq_idx[of len 0 xs "(0, 0, False)"]
  by (simp add: id_def cong: prod.case_cong)

text \<open>Boundary split: \<open>trunc_changes\<close> = the fold over \<open>butlast\<close> plus ONE final step at
  position \<open>length xs - 1\<close> -- the shape of the kernel's loop-plus-\<open>extra_f\<close> structure.\<close>
lemma trunc_changes_split_last:
  assumes "xs \<noteq> []"
  shows "trunc_changes len xs
    = (case tsign_step (trusted_sgn len (length xs - 1) (last xs))
             (tsign_fold_idx len 0 (butlast xs) (0, 0, False))
       of (_, cnt, amb) \<Rightarrow> (cnt, amb))"
proof -
  have split: "xs = butlast xs @ [last xs]"
    using assms by simp
  have "tsign_fold_idx len 0 xs (0, 0, False)
      = tsign_fold_idx len (0 + length (butlast xs)) [last xs]
          (tsign_fold_idx len 0 (butlast xs) (0, 0, False))"
    by (subst split) (rule tsign_fold_idx_append)
  also have "length (butlast xs) = length xs - 1" by simp
  finally have "tsign_fold_idx len 0 xs (0, 0, False)
      = tsign_step (trusted_sgn len (length xs - 1) (last xs))
          (tsign_fold_idx len 0 (butlast xs) (0, 0, False))"
    by simp
  then show ?thesis
    unfolding trunc_changes_conv_fold_idx
    by (simp add: id_def cong: prod.case_cong)
qed

text \<open>Early-abort lower bound: the count of any \<open>take\<close>-prefix fold (from the zero
  start) bounds the full \<open>trunc_changes\<close> count from below.\<close>
lemma trunc_changes_cnt_ge_prefix:
  assumes "tsign_fold_idx len 0 (take i xs) (0, 0, False) = (ls, cnt, amb)"
  shows "cnt \<le> fst (trunc_changes len xs)"
proof -
  have "tsign_fold_idx len 0 xs (0, 0, False)
      = tsign_fold_idx len 0 (take i xs @ drop i xs) (0, 0, False)" by simp
  also have "\<dots> = tsign_fold_idx len (0 + length (take i xs)) (drop i xs)
                    (tsign_fold_idx len 0 (take i xs) (0, 0, False))"
    by (rule tsign_fold_idx_append)
  also have "\<dots> = tsign_fold_idx len (0 + length (take i xs)) (drop i xs) (ls, cnt, amb)"
    by (simp add: assms)
  finally have full: "tsign_fold_idx len 0 xs (0, 0, False)
      = tsign_fold_idx len (0 + length (take i xs)) (drop i xs) (ls, cnt, amb)" .
  have "cnt \<le> (\<lambda>(a, b, c). b) (tsign_fold_idx len (0 + length (take i xs)) (drop i xs) (ls, cnt, amb))"
    using tsign_fold_idx_cnt_mono[of "(ls, cnt, amb)"] by simp
  then have "cnt \<le> (\<lambda>(a, b, c). b) (tsign_fold_idx len 0 xs (0, 0, False))"
    using full by simp
  then show ?thesis
    unfolding trunc_changes_conv_fold_idx
    by (cases "tsign_fold_idx len 0 xs (0, 0, False)") auto
qed

text \<open>The kernel's per-coefficient trust TEST (sign + bit-length comparison) computes
  exactly @{const trusted_sgn}, given any \<open>bl\<close> satisfying \<open>mpz_bitlen2_monadic\<close>'s
  spec conjuncts for the coefficient value.\<close>
lemma trusted_sgn_bitlen_test:
  fixes x :: int
  assumes ub: "\<bar>x\<bar> < 2 ^ bl"
    and lb: "x \<noteq> 0 \<Longrightarrow> 2 ^ (bl - 1) \<le> \<bar>x\<bar>"
  shows "trusted_sgn len i x
       = (if 0 < sgn x then Some 1
          else if sgn x < 0 \<and> trunc_thresh len i < bl then Some (-1)
          else None)"
proof (cases x "0::int" rule: linorder_cases)
  case less
  have xne: "x \<noteq> 0" using less by simp
  have blpos: "0 < bl"
  proof (rule ccontr)
    assume "\<not> 0 < bl"
    then have "bl = 0" by simp
    then have "\<bar>x\<bar> < 1" using ub by simp
    then show False using xne by simp
  qed
  have iff: "x \<le> - (2 ^ trunc_thresh len i) \<longleftrightarrow> trunc_thresh len i < bl"
  proof
    assume "trunc_thresh len i < bl"
    then have "trunc_thresh len i \<le> bl - 1" by simp
    then have "(2::int) ^ trunc_thresh len i \<le> 2 ^ (bl - 1)"
      by (simp add: power_increasing)
    also have "\<dots> \<le> \<bar>x\<bar>" using lb xne by simp
    finally show "x \<le> - (2 ^ trunc_thresh len i)" using less by simp
  next
    assume "x \<le> - (2 ^ trunc_thresh len i)"
    then have "(2::int) ^ trunc_thresh len i \<le> \<bar>x\<bar>" using less by simp
    also have "\<dots> < 2 ^ bl" using ub .
    finally show "trunc_thresh len i < bl"
      using power_less_imp_less_exp[of "2::int" "trunc_thresh len i" bl] by simp
  qed
  show ?thesis
    unfolding trusted_sgn_def using less iff by auto
next
  case equal
  then show ?thesis
    unfolding trusted_sgn_def by auto
next
  case greater
  then show ?thesis
    unfolding trusted_sgn_def by auto
qed

subsection \<open>The masked-coefficient device (guarded-bitlen repair)\<close>

text \<open>\<^bold>\<open>Masked coefficients.\<close> @{thm [source] trusted_sgn_bitlen_test} needs the upper bound
  \<open>\<bar>x\<bar> < 2 ^ bl\<close>, which the specification of \<open>mpz_bitlen2_monadic\<close> supplies only under a
  \<open>size_t\<close>-representability guard on \<open>\<bar>x\<bar>\<close>. For an arbitrary internal coefficient that guard is not
  dischargeable, so the kernel's per-coefficient decision cannot be proved equal to
  @{const trusted_sgn} on the true coefficient: an out-of-range coefficient may be distrusted by the
  kernel where @{const trusted_sgn} trusts it.

  The same fold still works: the kernel's decision is exactly @{const trusted_sgn} applied to the
  coefficient \<^emph>\<open>masked to \<open>0\<close>\<close> when the kernel distrusts it (@{const trusted_sgn} maps \<open>0\<close> to
  \<open>None\<close>, which is the distrust step). So the loop invariant carries \<open>\<exists>zs.\<close> a mask of the
  shifted-truncated prefix instead of the prefix itself, and the two facts the exit lemma needs both
  hold:
    \<^item> soundness of the count (\<open>\<le>\<close> the true count) holds for every mask, by the masking
      monotonicity of @{const changes} (\<open>tsign_mask_cnt_le_prefix\<close> below);
    \<^item> in the decisive case \<open>\<not>amb\<close> the mask is trivial (a masked position hits \<open>None\<close>, which sets
      \<open>amb\<close>; \<open>tsign_fold_idx_mask_not_amb\<close> below), so the exact transfer is unchanged.
  Only the unconditional lower bound is used, so nothing depends on the guard.\<close>

text \<open>The kernel's trust TEST computes @{const trusted_sgn} of the MASKED coefficient,
  using ONLY the (unconditional) lower bound: kernel-trust implies real trust, because
  \<open>thresh < bl\<close> with \<open>2 ^ (bl - 1) \<le> \<bar>x\<bar>\<close> gives \<open>x \<le> - (2 ^ thresh)\<close>. The masked-\<open>0\<close>
  branch is @{const trusted_sgn}'s own \<open>None\<close>.\<close>
lemma trusted_sgn_bitlen_test_masked:
  fixes x :: int
  assumes lb: "x \<noteq> 0 \<Longrightarrow> 2 ^ (bl - 1) \<le> \<bar>x\<bar>"
  shows "trusted_sgn len i
           (if 0 < sgn x \<or> sgn x < 0 \<and> trunc_thresh len i < bl then x else 0)
       = (if 0 < sgn x \<or> sgn x < 0 \<and> trunc_thresh len i < bl then Some (sgn x) else None)"
proof (cases x "0::int" rule: linorder_cases)
  case less
  show ?thesis
  proof (cases "trunc_thresh len i < bl")
    case True
    have "trunc_thresh len i \<le> bl - 1" using True by simp
    then have "(2::int) ^ trunc_thresh len i \<le> 2 ^ (bl - 1)"
      by (simp add: power_increasing)
    also have "\<dots> \<le> \<bar>x\<bar>" using lb less by simp
    finally have "(2::int) ^ trunc_thresh len i \<le> \<bar>x\<bar>" .
    then have le: "x \<le> - (2 ^ trunc_thresh len i)" using less by simp
    show ?thesis unfolding trusted_sgn_def using less True le by auto
  next
    case False
    have pos: "(0::int) < 2 ^ trunc_thresh len i" by simp
    show ?thesis unfolding trusted_sgn_def using less False pos by auto
  qed
next
  case equal
  then show ?thesis unfolding trusted_sgn_def by auto
next
  case greater
  then show ?thesis unfolding trusted_sgn_def by auto
qed

text \<open>A masked position hits @{const trusted_sgn}'s \<open>None\<close> branch, which raises \<open>amb\<close>
  for the rest of the fold. So a fold that ends with \<open>\<not>amb\<close> saw NO effective mask.\<close>
lemma tsign_fold_idx_mask_not_amb:
  assumes len_eq: "length zs = length ts"
    and mask: "\<forall>j<length zs. zs ! j = 0 \<or> zs ! j = ts ! j"
    and noamb: "\<not> (\<lambda>(a, b, c). c) (tsign_fold_idx len i0 zs st)"
  shows "zs = ts"
  using assms
proof (induction zs ts arbitrary: i0 st rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons z zs' t ts')
  obtain ls cnt amb where stq: "st = (ls, cnt, amb)" by (cases st)
  have z_case: "z = 0 \<or> z = t"
    using Cons.prems(1) by (metis length_greater_0_conv list.discI nth_Cons_0)
  have pw': "\<forall>j<length zs'. zs' ! j = 0 \<or> zs' ! j = ts' ! j"
    using Cons.prems(1) by fastforce
  show ?case
  proof (cases "z = t")
    case True
    have tail: "\<not> (\<lambda>(a, b, c). c)
        (tsign_fold_idx len (Suc i0) zs' (tsign_step (trusted_sgn len i0 z) st))"
      using Cons.prems(2) by simp
    show ?thesis using Cons.IH[OF pw' tail] True by simp
  next
    case False
    then have z0: "z = 0" using z_case by simp
    have none: "trusted_sgn len i0 z = None"
      unfolding z0 trusted_sgn_def using zero_less_power[of "2::int" "trunc_thresh len i0"]
      by simp
    have "tsign_step (trusted_sgn len i0 z) st = (ls, cnt, True)"
      unfolding none stq by simp
    then have "(\<lambda>(a, b, c). c) (tsign_fold_idx len i0 (z # zs') st)
        = (\<lambda>(a, b, c). c) (tsign_fold_idx len (Suc i0) zs' (ls, cnt, True))"
      by simp
    also have "\<dots> = True" using tsign_fold_idx_amb_or[of len "Suc i0" zs' ls cnt True] by simp
    finally show ?thesis using Cons.prems(2) by simp
  qed
qed

text \<open>Count soundness for a FULL-length mask: the trusted-sign count of any mask of the
  shifted-truncated coefficient list is at most the true sign-variation count. Same
  route as @{thm [source] trunc_changes_ge2_sound}, with the extra masking layer folded
  into the same pointwise \<open>0\<close>-or-equal side condition.\<close>
lemma tsign_mask_cnt_le_full:
  assumes lenws: "length ws = length ys"
    and mask: "\<forall>j<length ws. ws ! j = 0 \<or> ws ! j = taylor_shift_list 1 (trunc_list t ys) ! j"
  shows "(\<lambda>(a, b, c). b) (tsign_fold_idx (length ys) 0 ws (0, 0, b0))
       \<le> sign_changes_fold (taylor_shift_list 1 ys)"
proof -
  let ?len = "length ys"
  let ?xs = "taylor_shift_list 1 (trunc_list t ys)"
  let ?T = "taylor_shift_list 1 ys"
  obtain ls1 cnt1 amb1 where st1: "tsign_fold_idx ?len 0 ws (0, 0, b0) = (ls1, cnt1, amb1)"
    by (cases "tsign_fold_idx ?len 0 ws (0, 0, b0)") auto
  have corr: "(\<lambda>(a, b, c). (a, b)) (tsign_fold_idx ?len 0 ws (0, 0, b0))
      = fold sign_step (tsign_Z ?len 0 ws) (0, 0)"
    using tsign_fold_idx_eq_sign_step[of 0 0 ?len 0 ws b0] by simp
  have cnt1_eq: "cnt1 = sign_changes_fold (tsign_Z ?len 0 ws)"
    using corr st1 unfolding sign_changes_fold_def by (metis snd_conv split_conv)
  have pw: "\<forall>j < length (tsign_Z ?len 0 ws).
      tsign_Z ?len 0 ws ! j = 0 \<or> tsign_Z ?len 0 ws ! j = (map sgn ?T) ! j"
  proof (intro allI impI)
    fix j assume j: "j < length (tsign_Z ?len 0 ws)"
    then have jws: "j < length ws" by simp
    then have jlen: "j < ?len" using lenws by simp
    show "tsign_Z ?len 0 ws ! j = 0 \<or> tsign_Z ?len 0 ws ! j = (map sgn ?T) ! j"
    proof (cases "trusted_sgn ?len j (ws ! j)")
      case None
      then have "tsign_Z ?len 0 ws ! j = 0"
        unfolding tsign_Z_def tsign_repr_def using jws by simp
      then show ?thesis by simp
    next
      case (Some s)
      then have z_eq: "tsign_Z ?len 0 ws ! j = s"
        unfolding tsign_Z_def tsign_repr_def using jws by simp
      have wsj: "ws ! j = ?xs ! j"
      proof (rule ccontr)
        assume "ws ! j \<noteq> ?xs ! j"
        then have "ws ! j = 0" using mask jws by blast
        then show False using Some
          unfolding trusted_sgn_def
          using zero_less_power[of "2::int" "trunc_thresh ?len j"] by simp
      qed
      have "sgn (?T ! j) = s"
        using trusted_sgn_sound[of j ys t s] jlen Some wsj by simp
      then show ?thesis using z_eq jlen by simp
    qed
  qed
  have lens: "length (tsign_Z ?len 0 ws) = length (map sgn ?T)"
    using lenws by simp
  have mask_le: "changes (tsign_Z ?len 0 ws) \<le> changes (map sgn ?T)"
    using changes_mask_le[OF lens] pw by simp
  have lhs_eq: "changes (tsign_Z ?len 0 ws) = int cnt1"
    using changes_eq_sign_changes_fold[of "tsign_Z ?len 0 ws"] cnt1_eq by simp
  have rhs_eq: "changes (map sgn ?T) = int (sign_changes_fold ?T)"
    using changes_map_sgn_eq[of ?T] changes_eq_sign_changes_fold[of ?T] by simp
  have "cnt1 \<le> sign_changes_fold ?T"
    using mask_le lhs_eq rhs_eq by simp
  then show ?thesis using st1 by simp
qed

text \<open>Count soundness for a PREFIX mask (the loop invariant's form): extend the mask by
  the untouched tail of the shifted-truncated list and use count-monotonicity of the
  fold (@{thm [source] tsign_fold_idx_cnt_mono}).\<close>
lemma tsign_mask_cnt_le_prefix:
  assumes lenzs: "length zs \<le> length ys"
    and mask: "\<forall>j<length zs. zs ! j = 0 \<or> zs ! j = taylor_shift_list 1 (trunc_list t ys) ! j"
  shows "(\<lambda>(a, b, c). b) (tsign_fold_idx (length ys) 0 zs (0, 0, b0))
       \<le> sign_changes_fold (taylor_shift_list 1 ys)"
proof -
  let ?len = "length ys"
  let ?xs = "taylor_shift_list 1 (trunc_list t ys)"
  define ws where "ws = zs @ drop (length zs) ?xs"
  have lenxs: "length ?xs = ?len" by simp
  have lenws: "length ws = ?len" unfolding ws_def using lenzs lenxs by simp
  have maskws: "\<forall>j<length ws. ws ! j = 0 \<or> ws ! j = ?xs ! j"
  proof (intro allI impI)
    fix j assume j: "j < length ws"
    show "ws ! j = 0 \<or> ws ! j = ?xs ! j"
    proof (cases "j < length zs")
      case True
      then have "ws ! j = zs ! j" unfolding ws_def by (simp add: nth_append)
      then show ?thesis using mask True by simp
    next
      case False
      then have "ws ! j = drop (length zs) ?xs ! (j - length zs)"
        unfolding ws_def by (simp add: nth_append)
      also have "\<dots> = ?xs ! j" using False j lenws lenxs by simp
      finally show ?thesis by simp
    qed
  qed
  have split: "tsign_fold_idx ?len 0 ws (0, 0, b0)
      = tsign_fold_idx ?len (0 + length zs) (drop (length zs) ?xs)
          (tsign_fold_idx ?len 0 zs (0, 0, b0))"
    unfolding ws_def by (rule tsign_fold_idx_append)
  have "(\<lambda>(a, b, c). b) (tsign_fold_idx ?len 0 zs (0, 0, b0))
      \<le> (\<lambda>(a, b, c). b) (tsign_fold_idx ?len 0 ws (0, 0, b0))"
    unfolding split by (rule tsign_fold_idx_cnt_mono)
  also have "\<dots> \<le> sign_changes_fold (taylor_shift_list 1 ys)"
    using tsign_mask_cnt_le_full[OF lenws maskws] .
  finally show ?thesis .
qed

text \<open>The kernel loop's sign-accounting invariant, packaged as ONE predicate: the fold
  state is the guarded fold over SOME mask \<open>zs\<close> of the length-\<open>i\<close> prefix of the
  shifted-truncated coefficients. Packaged (rather than inlined \<open>\<exists>zs\<close>) so the WHILET
  invariant stays opaque to the simplifier at every extraction site.\<close>
definition tmask_state :: "int list \<Rightarrow> bool \<Rightarrow> int \<times> nat \<times> bool \<Rightarrow> nat \<Rightarrow> bool" where
  "tmask_state ys' amb0 st i \<equiv>
     (\<exists>zs. length zs = i
           \<and> (\<forall>j<i. zs ! j = 0 \<or> zs ! j = taylor_shift_list 1 ys' ! j)
           \<and> st = tsign_fold_idx (length ys') 0 zs (0, 0, amb0))"

lemma tmask_state_init: "tmask_state ys' amb0 (0, 0, amb0) 0"
  unfolding tmask_state_def by (rule exI[where x="[]"]) simp

text \<open>Count soundness of the invariant: whatever the kernel distrusted, its running
  count never exceeds the true sign-variation count of the FULL-precision shift.\<close>
lemma tmask_state_cnt_le:
  assumes st: "tmask_state ys' amb0 (ls, cnt, amb) i"
    and ys'eq: "ys' = trunc_list t ys"
    and ile: "i \<le> length ys"
  shows "cnt \<le> sign_changes_fold (taylor_shift_list 1 ys)"
proof -
  from st obtain zs where zs: "length zs = i"
    "\<forall>j<i. zs ! j = 0 \<or> zs ! j = taylor_shift_list 1 ys' ! j"
    "(ls, cnt, amb) = tsign_fold_idx (length ys') 0 zs (0, 0, amb0)"
    unfolding tmask_state_def by blast
  have lenys': "length ys' = length ys" using ys'eq by simp
  have bnd: "(\<lambda>(a, b, c). b) (tsign_fold_idx (length ys) 0 zs (0, 0, amb0))
      \<le> sign_changes_fold (taylor_shift_list 1 ys)"
    using tsign_mask_cnt_le_prefix[of zs ys t amb0] zs(1,2) ile ys'eq by simp
  have z3: "tsign_fold_idx (length ys) 0 zs (0, 0, amb0) = (ls, cnt, amb)"
    using zs(3) lenys' by simp
  show ?thesis using bnd unfolding z3 by simp
qed

text \<open>Decisiveness of the invariant: with no ambiguity the mask was TRIVIAL, so the
  state is the ORIGINAL (unmasked) prefix fold and the exact transfer applies.\<close>
lemma tmask_state_not_amb:
  assumes st: "tmask_state ys' amb0 (ls, cnt, amb) i"
    and noamb: "\<not> amb"
    and ile: "i \<le> length ys'"
  shows "(ls, cnt, amb) = tsign_fold_idx (length ys') 0
           (take i (taylor_shift_list 1 ys')) (0, 0, amb0)"
proof -
  from st obtain zs where zs: "length zs = i"
    "\<forall>j<i. zs ! j = 0 \<or> zs ! j = taylor_shift_list 1 ys' ! j"
    "(ls, cnt, amb) = tsign_fold_idx (length ys') 0 zs (0, 0, amb0)"
    unfolding tmask_state_def by blast
  let ?T = "taylor_shift_list 1 ys'"
  have lenT: "length ?T = length ys'" by simp
  have len_eq: "length zs = length (take i ?T)" using zs(1) ile lenT by simp
  have mask: "\<forall>j<length zs. zs ! j = 0 \<or> zs ! j = take i ?T ! j"
    using zs(1,2) ile lenT by simp
  have z3: "tsign_fold_idx (length ys') 0 zs (0, 0, amb0) = (ls, cnt, amb)"
    using zs(3) by simp
  have "\<not> (\<lambda>(a, b, c). c) (tsign_fold_idx (length ys') 0 zs (0, 0, amb0))"
    unfolding z3 using noamb by simp
  from tsign_fold_idx_mask_not_amb[OF len_eq mask this] have "zs = take i ?T" .
  then show ?thesis using zs(3) by simp
qed

text \<open>At the LEADING position the threshold exponent is 0, so trust degenerates to
  plain nonzero-ness -- the kernel's boundary \<open>extra_f\<close>/\<open>s_last\<close> handling implements
  exactly this step.\<close>
lemma trusted_sgn_last:
  fixes x :: int
  shows "trusted_sgn len (len - 1) x = (if x = 0 then None else Some (sgn x))"
proof -
  have "trunc_thresh len (len - 1) = 0"
    unfolding trunc_thresh_def by (cases len) auto
  then show ?thesis
    unfolding trusted_sgn_def by auto
qed

end
