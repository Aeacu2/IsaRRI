theory Window_Mono
  imports "IsaRRI_LLVM.Carried_Kernel" Newton_Spec "IsaRRI_Spec.Dsc_Bern" "IsaRRI_Spec.Bernstein_Split" "IsaRRI_Spec.Dsc_Rat"
begin

text \<open>Monotonicity of the window count, as pure \<open>real poly\<close> / Bernstein mathematics over the carried
  frame (no monad, no Sepref, no heap).
  Main results: \<open>carried_window_count_mono\<close> and the Bernstein and reciprocal transport lemmas it
  rests on. The monotone bound is what makes it sound for the capped count kernel to abort early
  once the cap \<open>v\<close> is reached.\<close>

text \<open>Clone of @{thm [source] changes_Bernstein_coeffs_eq_changes_coeffs}
  (\<open>Dsc_Bern.thy\<close>) with \<open>defines "p \<equiv> degree P"\<close> relaxed to \<open>assumes "degree P \<le> p"\<close>.
  The original proof consumes \<open>p = degree P\<close> ONLY through \<open>degR_le : degree R \<le> p\<close>;
  everything else is \<open>p\<close>-parametric. This is what makes the padded-degree transport work.\<close>

lemma changes_Bernstein_coeffs_eq_changes_coeffs_elev:
  fixes P :: "real poly" and a b :: real
  assumes degP: "degree P \<le> p"
  defines "R \<equiv> P \<circ>\<^sub>p [:a,1:] \<circ>\<^sub>p [:0, b-a:]"
  shows "changes (Bernstein_coeffs p a b P)
       = changes (coeffs ((reciprocal_poly p R) \<circ>\<^sub>p [:1,1:]))"
proof -
  have coeffs_id:
    "Bernstein_coeffs p a b P = Bernstein_coeffs_01 p R"
    unfolding Bernstein_coeffs_def Bernstein_coeffs_01_def R_def
    by (simp add: pcompose_assoc)

  have degRP: "degree R \<le> degree P"
    unfolding R_def
    by (metis (no_types, lifting) One_nat_def degree_pCons_eq_if degree_pcompose
        le_eq_less_or_eq mult.right_neutral mult_zero_right zero_le)
  with degP have degR_le: "degree R \<le> p" by simp

  have B01_is_changes:
    "Bernstein_changes_01 p R = changes (Bernstein_coeffs_01 p R)"
    unfolding Bernstein_changes_01_def
    using changes_nonneg[of "Bernstein_coeffs_01 p R"] by simp

  have "changes (Bernstein_coeffs_01 p R)
      = changes (coeffs ((reciprocal_poly p R) \<circ>\<^sub>p [:1,1:]))"
    using Bernstein_changes_01_eq_changes[OF degR_le]
    unfolding B01_is_changes
    by simp

  thus ?thesis
    using coeffs_id by simp
qed

text \<open>Helper: a list equals its trailing-zero-stripped form re-padded with exactly the
  stripped zeros. Pure @{const strip_while} bookkeeping (no polynomial content).\<close>
lemma strip_while_0_append_replicate:
  fixes ys :: "'a::zero list"
  shows "strip_while ((=) 0) ys @ replicate (length ys - length (strip_while ((=) 0) ys)) 0 = ys"
proof -
  let ?zs = "takeWhile ((=) 0) (rev ys)"
  have zs0: "?zs = replicate (length ?zs) 0"
  proof (rule nth_equalityI)
    show "length ?zs = length (replicate (length ?zs) 0)" by simp
    fix i assume i: "i < length ?zs"
    then have "?zs ! i \<in> set ?zs" by simp
    then have "?zs ! i = 0" using set_takeWhileD by fastforce
    then show "?zs ! i = replicate (length ?zs) 0 ! i" using i by simp
  qed
  have split: "rev ys = ?zs @ dropWhile ((=) 0) (rev ys)" by simp
  have "ys = rev (rev ys)" by simp
  also have "\<dots> = rev (dropWhile ((=) 0) (rev ys)) @ rev ?zs"
    using split by (metis rev_append)
  also have "rev (dropWhile ((=) 0) (rev ys)) = strip_while ((=) 0) ys"
    by (simp add: strip_while_def)
  finally have ys_eq: "ys = strip_while ((=) 0) ys @ rev ?zs" .
  have lenz: "length ?zs = length ys - length (strip_while ((=) 0) ys)"
    by (metis ys_eq length_append length_rev add_diff_cancel_left')
  have "rev ?zs = replicate (length ?zs) 0" using zs0 by (metis rev_replicate)
  then show ?thesis using ys_eq lenz by simp
qed

text \<open>Helper: reversing a length-\<open>n\<close> coefficient list is exactly the reciprocal at the
  PADDED degree \<open>n-1\<close> — the list-level counterpart of @{const reciprocal_poly}'s definitional
  \<open>Poly (rev (coeffs P @ replicate (p - degree P) 0))\<close> form, specialised to \<open>p = length ys - 1\<close>
  where the padding restores exactly the stripped trailing zeros.\<close>
lemma reciprocal_poly_Poly_rev:
  fixes ys :: "'a::comm_ring_1 list"
  shows "reciprocal_poly (length ys - 1) (Poly ys) = Poly (rev ys)"
proof (cases "Poly ys = 0")
  case True
  then obtain m where "ys = replicate m 0" using Poly_eq_0 by blast
  then have "Poly (rev ys) = 0" by (simp add: Poly_replicate_0)
  with True show ?thesis by (simp add: reciprocal_0)
next
  case False
  have deg: "degree (Poly ys) = length (coeffs (Poly ys)) - 1"
    using False by (simp add: degree_eq_length_coeffs)
  have strip: "coeffs (Poly ys) @ replicate (length ys - length (coeffs (Poly ys))) 0 = ys"
    by (metis coeffs_Poly strip_while_0_append_replicate)
  have lc: "length (coeffs (Poly ys)) = degree (Poly ys) + 1"
    by (rule length_coeffs[OF False])
  have arith: "(length ys - 1) - degree (Poly ys) = length ys - length (coeffs (Poly ys))"
    unfolding lc by simp
  have rec: "reciprocal_poly (length ys - 1) (Poly ys)
      = Poly (rev (coeffs (Poly ys) @ replicate ((length ys - 1) - degree (Poly ys)) 0))"
    by (simp add: reciprocal_poly_def)
  show ?thesis unfolding rec arith using strip by simp
qed

text \<open>Helper: @{const changes} of a coefficient list is invariant under the
  order-embedding \<open>of_rat\<close> (the \<open>Dsc_Rat\<close> transfer ingredient, lifted to \<open>changes\<close>/\<open>coeffs\<close>).\<close>
lemma changes_coeffs_of_rat:
  fixes P :: "rat poly"
  shows "changes (coeffs (map_poly (of_rat::rat \<Rightarrow> real) P)) = changes (coeffs P)"
proof -
  have "coeffs (map_poly (of_rat::rat \<Rightarrow> real) P) = map of_rat (coeffs P)"
    by (simp add: coeffs_map_poly of_rat_eq_0_iff)
  thus ?thesis
    by (metis changes_eq_sign_changes sign_changes_map_of_rat)
qed

text \<open>The rational list @{const local_poly_rat} is the coefficient list of the local transform
  \<open>P \<circ>\<^sub>p [:a, b-a:]\<close>, and mapping it to \<open>real\<close> gives exactly the validator's \<open>R\<close>.\<close>
lemma Poly_local_poly_rat_rat:
  "Poly (local_poly_rat a b xs)
     = pcompose (map_poly rat_of_int (Poly xs)) [:a, b - a:]"
proof -
  have "Poly (local_poly_rat a b xs)
      = pcompose (pcompose (map_poly rat_of_int (Poly xs)) [:a, 1:]) [:0, b - a:]"
    unfolding local_poly_rat_def
    by (simp add: Poly_scale_poly_list Poly_taylor_shift_list Poly_map_rat_of_int)
  also have "\<dots> = pcompose (map_poly rat_of_int (Poly xs)) (pcompose [:a, 1:] [:0, b - a:])"
    by (rule pcompose_assoc[symmetric])
  also have "pcompose ([:a, 1:] :: rat poly) [:0, b - a:] = [:a, b - a:]"
    by (simp add: pcompose_pCons)
  finally show ?thesis .
qed

lemma map_poly_of_rat_local_poly_rat:
  "map_poly (of_rat :: rat \<Rightarrow> real) (Poly (local_poly_rat a b xs))
     = pcompose (map_poly of_int (Poly xs)) [:of_rat a, of_rat b - of_rat a:]"
proof -
  have "map_poly (of_rat :: rat \<Rightarrow> real) (Poly (local_poly_rat a b xs))
      = map_poly of_rat (pcompose (map_poly rat_of_int (Poly xs)) [:a, b - a:])"
    by (simp add: Poly_local_poly_rat_rat)
  also have "\<dots> = pcompose (map_poly of_rat (map_poly rat_of_int (Poly xs)))
                    (map_poly of_rat [:a, b - a:])"
    by (rule of_rat_hom.map_poly_pcompose)
  also have "map_poly of_rat (map_poly rat_of_int (Poly xs)) = map_poly of_int (Poly xs)"
    by (simp add: map_poly_map_poly o_def of_rat_of_int_eq)
  also have "map_poly (of_rat::rat\<Rightarrow>real) [:a, b - a:] = [:of_rat a, of_rat b - of_rat a:]"
    by (simp add: of_rat_hom.map_poly_pCons_hom of_rat_diff)
  finally show ?thesis .
qed

section \<open>Sub-interval monotonicity of \<open>Bernstein_changes\<close>\<close>

text \<open>Two applications of @{thm [source] Bernstein_changes_split} (case-splitting the
  endpoint equalities), plus nonnegativity of the discarded summands
  (@{const Bernstein_changes} is \<open>int (nat \<dots>)\<close> by definition). Holds for any
  \<open>p \<ge> degree P\<close> — the instance used by the transport below is \<open>p = length xs - 1\<close>.\<close>

corollary Bernstein_changes_subinterval_mono:
  fixes P :: "real poly" and a a' b' b :: real
  assumes "a \<le> a'" and "a' < b'" and "b' \<le> b" and degP: "degree P \<le> p"
  shows "Bernstein_changes p a' b' P \<le> Bernstein_changes p a b P"
proof -
  have nn: "\<And>u w. (0::int) \<le> Bernstein_changes p u w P"
    by (simp add: Bernstein_changes_def)
  have left: "Bernstein_changes p a' b P \<le> Bernstein_changes p a b P"
  proof (cases "a = a'")
    case True then show ?thesis by simp
  next
    case False
    then have aa: "a < a'" using assms(1) by simp
    have a'b: "a' < b" using assms(2,3) by simp
    from Bernstein_changes_split[OF aa a'b degP] nn[of a a'] show ?thesis by linarith
  qed
  have right: "Bernstein_changes p a' b' P \<le> Bernstein_changes p a' b P"
  proof (cases "b' = b")
    case True then show ?thesis by simp
  next
    case False
    then have bb: "b' < b" using assms(3) by simp
    from Bernstein_changes_split[OF assms(2) bb degP] nn[of b' b] show ?thesis by linarith
  qed
  from left right show ?thesis by linarith
qed

lemma Poly_map_of_rat:
  "Poly (map (of_rat :: rat \<Rightarrow> real) xs) = map_poly of_rat (Poly xs)"
  by (rule poly_eqI) (simp add: coeff_Poly coeff_map_poly nth_default_map_eq)

lemma len_local_poly_rat [simp]:
  "length (local_poly_rat a b xs) = length xs"
  by (simp add: local_poly_rat_def length_scale_poly_list length_taylor_shift_list)

section \<open>The transport: \<open>descartes_list_int\<close> at elevated degree\<close>

text \<open>\<^bold>\<open>Proof route\<close> (each step against a named lemma):
  \<^enum> @{thm [source] descartes_list_int_via_local} (\<open>Newton_Spec.thy\<close>) reduces the
    LHS to \<open>sign_changes_fold (taylor_shift_list 1 (rev (local_poly_rat a b xs)))\<close>
    (needs \<open>length xs > 0\<close>, \<open>a \<noteq> b\<close> — both hypotheses here).
  \<^enum> Poly-side repackaging at FIXED length \<open>n = length xs\<close>: with
    \<open>Rq = Poly (map rat_of_int xs) \<circ>\<^sub>p [:a,1:] \<circ>\<^sub>p [:0, b-a:] :: rat poly\<close>,
    \<open>Poly (rev (local_poly_rat a b xs)) = reciprocal_poly (n-1) Rq\<close> — the list pipeline
    computes \<open>map (coeff Rq) [0..<n]\<close> (via @{thm [source] Poly_taylor_shift_list} /
    \<open>Poly_scale_poly_list\<close>, both length-preserving), and reversing THAT length-\<open>n\<close> list
    is exactly \<open>coeff (reciprocal_poly (n-1) Rq) i = coeff Rq (n-1-i)\<close>
    (\<open>reciprocal_poly_coeff\<close>, AFP \<open>RRI_Misc\<close>). Then \<open>taylor_shift_list 1 \<dots>\<close> is
    \<open>\<circ>\<^sub>p [:1,1:]\<close> and \<open>sign_changes_fold = changes \<circ> coeffs \<circ> Poly\<close> up to
    @{thm [source] sign_changes_fold_Poly} + \<open>changes_eq_sign_changes\<close> (final stripping
    is harmless — \<open>sign_changes_fold\<close> ignores zeros; ONLY the reversal step is
    length-sensitive).
  \<^enum> rat \<rightarrow> real transfer: \<open>changes\<close> commutes with the injective order-embedding
    \<open>real_of_rat\<close> on coefficient lists (\<open>changes_coeffs_of_rat\<close> above);
    \<open>map_poly\<close> composition gives
    \<open>map_poly of_rat Rq = map_poly of_int (Poly xs) \<circ>\<^sub>p [:of_rat a,1:] \<circ>\<^sub>p [:0, of_rat (b-a):]\<close>.
  \<^enum> Close with @{thm [source] changes_Bernstein_coeffs_eq_changes_coeffs_elev} at
    \<open>p = n-1\<close> (its precondition \<open>degree (map_poly of_int (Poly xs)) \<le> n-1\<close> is free) +
    \<open>Bernstein_changes_def\<close>.\<close>

lemma descartes_list_int_eq_Bernstein_changes:
  fixes a b :: rat
  assumes len: "0 < length xs" and ab: "a < b"
  shows "int (descartes_list_int a b xs)
       = Bernstein_changes (length xs - 1) (of_rat a) (of_rat b)
           (map_poly of_int (Poly xs) :: real poly)"
proof -
  have abne: "a \<noteq> b" using ab by simp
  have step1: "int (descartes_list_int a b xs)
      = int (sign_changes_fold (taylor_shift_list (1::rat) (rev (local_poly_rat a b xs))))"
    using descartes_list_int_via_local[OF len abne] by simp
  define n where "n = length xs"
  define P where "P = (map_poly of_int (Poly xs) :: real poly)"
  define R where "R = P \<circ>\<^sub>p [:real_of_rat a, 1:] \<circ>\<^sub>p [:0, real_of_rat b - real_of_rat a:]"
  have degP: "degree P \<le> n - 1"
  proof -
    have "degree P \<le> degree (Poly xs)" unfolding P_def by (rule degree_map_poly_le)
    also have "\<dots> \<le> length xs - 1"
      using len by (simp add: degree_le coeff_Poly nth_default_beyond)
    finally show ?thesis unfolding n_def .
  qed
  \<comment> \<open>RHS reduction via the elevated Bernstein-coeff validator (already proven).\<close>
  have rhs: "Bernstein_changes (n - 1) (real_of_rat a) (real_of_rat b) P
      = changes (coeffs (reciprocal_poly (n - 1) R \<circ>\<^sub>p [:1,1:]))"
    unfolding Bernstein_changes_def
    using changes_Bernstein_coeffs_eq_changes_coeffs_elev[OF degP]
    by (simp add: R_def changes_nonneg)
  \<comment> \<open>The rat window poly maps to the elev validator's \<open>R\<close> (single-composition form).\<close>
  have mLq_R: "map_poly of_rat (Poly (local_poly_rat a b xs)) = R"
    unfolding R_def P_def
    by (simp add: map_poly_of_rat_local_poly_rat pcompose_assoc[symmetric] pcompose_pCons)
  \<comment> \<open>LHS list\<rightarrow>reciprocal reduction, transferred to \<open>real\<close> via \<open>H0\<close> on the mapped list.\<close>
  have claim: "map_poly of_rat (Poly (taylor_shift_list (1::rat) (rev (local_poly_rat a b xs))))
             = reciprocal_poly (n - 1) R \<circ>\<^sub>p [:1, 1:]"
  proof -
    have lenm: "length (map (of_rat::rat \<Rightarrow> real) (local_poly_rat a b xs)) = n"
      by (simp add: n_def)
    have "map_poly (of_rat::rat \<Rightarrow> real) (Poly (rev (local_poly_rat a b xs)))
        = Poly (rev (map of_rat (local_poly_rat a b xs)))"
      by (simp add: Poly_map_of_rat[symmetric] rev_map)
    also have "\<dots> = reciprocal_poly (n - 1) (Poly (map of_rat (local_poly_rat a b xs)))"
      using reciprocal_poly_Poly_rev[symmetric, of "map of_rat (local_poly_rat a b xs)"] lenm
      by simp
    also have "Poly (map (of_rat::rat \<Rightarrow> real) (local_poly_rat a b xs))
        = map_poly of_rat (Poly (local_poly_rat a b xs))"
      by (rule Poly_map_of_rat)
    finally have "map_poly (of_rat::rat \<Rightarrow> real) (Poly (rev (local_poly_rat a b xs)))
        = reciprocal_poly (n - 1) R"
      using mLq_R by simp
    thus ?thesis
      by (simp add: Poly_taylor_shift_list of_rat_hom.map_poly_pcompose
                    of_rat_hom.map_poly_pCons_hom)
  qed
  have "int (descartes_list_int a b xs)
      = changes (coeffs (Poly (taylor_shift_list (1::rat) (rev (local_poly_rat a b xs)))))"
    using step1 by (simp add: sign_changes_fold_Poly changes_eq_sign_changes)
  also have "\<dots> = changes (coeffs (map_poly (of_rat::rat \<Rightarrow> real)
                    (Poly (taylor_shift_list (1::rat) (rev (local_poly_rat a b xs))))))"
    by (rule changes_coeffs_of_rat[symmetric])
  also have "\<dots> = changes (coeffs (reciprocal_poly (n - 1) R \<circ>\<^sub>p [:1, 1:]))"
    by (simp add: claim)
  also have "\<dots> = Bernstein_changes (n - 1) (real_of_rat a) (real_of_rat b) P"
    using rhs by simp
  finally show ?thesis by (simp add: n_def P_def)
qed

section \<open>Window-child count monotonicity\<close>

text \<open>\<^bold>\<open>Proof route:\<close>
  \<^enum> Child side: \<open>carried_init_same_den m (2^j) (m+4) xs = window_child_formula m (2^j) (m+4) xs\<close>
    (one \<open>unfolding\<close> — the two definitions are identical, \<open>Carried_Kernel.thy\<close> vs
    \<open>Newton_Spec.thy\<close>); @{thm [source] window_child_formula_repr_scalar} (\<open>d = 2^j > 0\<close>)
    gives \<open>carried_repr_scalar xs (m/2^j) ((m+4)/2^j) child\<close>; then
    @{thm [source] carried_repr_scalar_count} (needs \<open>length xs > 0\<close> and distinct endpoints —
    they differ by \<open>4/2^j > 0\<close>) turns @{const carried_descartes_count} of the child into
    \<open>descartes_list_int (m/2^j) ((m+4)/2^j) xs\<close>.
  \<^enum> Node side: \<open>carried_repr_scalar xs 0 1 xs\<close> holds with witness scalar \<open>1\<close>
    (\<open>local_poly_rat 0 1 xs = map rat_of_int xs\<close>: \<open>taylor_shift_list 0 = id\<close> and
    \<open>scale_poly_list 1 = id\<close>, both one-liners via \<open>poly_eq_same_length\<close> +
    @{thm [source] Poly_taylor_shift_list} with \<open>pcompose _ [:0,1:] = id\<close>), so
    \<open>carried_descartes_count xs = descartes_list_int 0 1 xs\<close> by the same count lemma.
  \<^enum> Both sides through @{thm [source] descartes_list_int_eq_Bernstein_changes} at the SAME
    \<open>p = length xs - 1\<close> (the child inherits it via the SAME list \<open>xs\<close> — note both
    \<open>descartes_list_int\<close> facts are about \<open>xs\<close>, only the intervals differ), then
    @{thm [source] Bernstein_changes_subinterval_mono} with
    \<open>0 \<le> m/2^j < (m+4)/2^j \<le> 1\<close> from \<open>0 \<le> m \<and> m + 4 \<le> 2^j\<close> (via \<open>of_rat\<close> monotonicity).

  \<^bold>\<open>Why this statement is exactly what the window try consumes.\<close> In
  \<open>carried_try_window_monadic_correct\<close>, the accept branch runs the cap kernel at
  \<open>cap = v\<close>: abort (\<open>v \<le> r\<close>) gives \<open>v \<le> t\<close> (\<open>t\<close> = exact count of the candidate); this
  lemma bounds \<open>t \<le> carried_descartes_count xs\<close>; the spec-level precondition
  \<open>carried_descartes_count xs \<le> v\<close> closes \<open>t = v\<close>. The reject
  branch (\<open>r < v\<close>) needs only the cap contract's exactness half — no monotonicity.\<close>

lemma carried_window_count_mono:
  fixes m :: int and j :: nat
  assumes len: "0 < length xs" and m0: "0 \<le> m" and mj: "m + 4 \<le> 2 ^ j"
  shows "carried_descartes_count (carried_init_same_den m (2 ^ j) (m + 4) xs)
       \<le> carried_descartes_count xs"
proof -
  define A where "A = (of_int m / of_int (2 ^ j) :: rat)"
  define B where "B = (of_int (m + 4) / of_int (2 ^ j) :: rat)"
  define P where "P = (map_poly of_int (Poly xs) :: real poly)"
  have jpos: "(0::int) < 2 ^ j" by simp
  have AB: "A < B" unfolding A_def B_def using jpos by (simp add: divide_strict_right_mono)
  \<comment> \<open>child count = \<open>descartes_list_int A B xs\<close>\<close>
  have child_eq: "carried_init_same_den m (2 ^ j) (m + 4) xs = window_child_formula m (2 ^ j) (m + 4) xs"
    by (simp add: carried_init_same_den_def window_child_formula_def)
  have repr_child: "carried_repr_scalar xs A B (carried_init_same_den m (2 ^ j) (m + 4) xs)"
    unfolding child_eq A_def B_def by (rule window_child_formula_repr_scalar[OF jpos])
  have cnt_child: "carried_descartes_count (carried_init_same_den m (2 ^ j) (m + 4) xs)
      = descartes_list_int A B xs"
    unfolding carried_descartes_count_def
    using carried_repr_scalar_count[OF repr_child len] AB by simp
  \<comment> \<open>node count = \<open>descartes_list_int 0 1 xs\<close> (witness scalar 1)\<close>
  have lpr01: "local_poly_rat 0 1 xs = map rat_of_int xs"
  proof (rule poly_eq_same_length)
    show "length (local_poly_rat 0 1 xs) = length (map rat_of_int xs)" by simp
    show "Poly (local_poly_rat 0 1 xs) = Poly (map rat_of_int xs)"
      by (simp add: Poly_local_poly_rat_rat Poly_map_rat_of_int pcompose_pCons)
  qed
  have repr_node: "carried_repr_scalar xs 0 1 xs"
    unfolding carried_repr_scalar_def
    by (rule exI[of _ 1]) (simp add: lpr01 smult_list_def rev_map)
  have cnt_node: "carried_descartes_count xs = descartes_list_int 0 1 xs"
    unfolding carried_descartes_count_def
    using carried_repr_scalar_count[OF repr_node len] by simp
  \<comment> \<open>real-interval bounds \<open>0 \<le> A < B \<le> 1\<close>\<close>
  have jr: "(0::rat) < of_int (2 ^ j)" using jpos by simp
  have A0: "(0::rat) \<le> A" unfolding A_def using m0 jr by simp
  have B1: "B \<le> 1"
  proof -
    have "of_int (m + 4) \<le> (of_int (2 ^ j) :: rat)" by (metis mj of_int_le_iff)
    thus ?thesis unfolding B_def using jr by simp
  qed
  have b0: "(0::real) \<le> real_of_rat A" using A0 by (metis of_rat_0 of_rat_less_eq)
  have bAB: "real_of_rat A < real_of_rat B" using AB by (simp add: of_rat_less)
  have b1: "real_of_rat B \<le> 1" using B1 by (metis of_rat_1 of_rat_less_eq)
  have degP: "degree P \<le> length xs - 1"
  proof -
    have "degree P \<le> degree (Poly xs)" unfolding P_def by (rule degree_map_poly_le)
    also have "\<dots> \<le> length xs - 1"
      using len by (simp add: degree_le coeff_Poly nth_default_beyond)
    finally show ?thesis .
  qed
  \<comment> \<open>transfer both counts to Bernstein via the elevated-degree transport, apply sub-interval monotonicity\<close>
  have "int (descartes_list_int A B xs)
      = Bernstein_changes (length xs - 1) (real_of_rat A) (real_of_rat B) P"
    unfolding P_def using descartes_list_int_eq_Bernstein_changes[OF len AB] by simp
  also have "\<dots> \<le> Bernstein_changes (length xs - 1) 0 1 P"
    using Bernstein_changes_subinterval_mono[OF b0 bAB b1 degP] .
  also have "\<dots> = int (descartes_list_int 0 1 xs)"
    unfolding P_def using descartes_list_int_eq_Bernstein_changes[OF len, of 0 1] by simp
  finally have "descartes_list_int A B xs \<le> descartes_list_int 0 1 xs" by simp
  thus ?thesis using cnt_child cnt_node by simp
qed

end
