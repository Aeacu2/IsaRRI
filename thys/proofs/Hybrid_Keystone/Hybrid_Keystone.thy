theory Hybrid_Keystone
  imports IsaRRI_Refine.Hybrid_Loop_Refine
begin

text \<open>\<^bold>\<open>The \<open>\<exists>pol\<close> keystone for the lazy hybrid solver\<close>, together with the chain of lemmas that builds
  up to it: the midpoint bridge and the split arm's child build and decision, the window arm, the truncation coupling and
  the \<open>\<alpha>\<close>-projection, the full invariant steps of each arm, the concrete pop, the termination measure, and the
  assembly at loop exit.\<close>

section \<open>The midpoint bridge: the \<open>O(1)\<close> read is the half-evaluation\<close>

text \<open>\<^bold>\<open>The identity the fused midpoint read rests on.\<close> The split arm does not run the \<open>O(len)\<close> half-evaluation
  loop \<open>poly_hom_eval_trust_half_monadic\<close>; it reads the right child's constant coefficient in \<open>O(1)\<close>. This theory is the
  machine-checked statement that the two agree.

  The chain: @{const carried_right}\<open> = taylor_shift_list 1 \<circ> \<close>@{const carried_left}, so by
  @{thm [source] Poly_taylor_shift_list} its polynomial is @{const carried_left}'s composed with
  \<open>[:1, 1:]\<close>; evaluating at \<open>0\<close> reads coefficient \<open>0\<close> on the left and gives
  \<open>poly (Poly (carried_left xs)) 1\<close> on the right. @{thm [source] carried_left_eq_dilate} then
  turns that into the dilated \<Sum>, which @{thm [source] cdlr_eval_half_scaled} already knows is
  \<open>2\<^sup>n\<^sup>-\<^sup>1\<close> times the rational midpoint value.\<close>

lemma carried_left_length[simp]: "length (carried_left xs) = length xs"
  by (simp add: carried_left_eq_dilate)

lemma carried_right_length[simp]: "length (carried_right xs) = length xs"
  by (simp add: carried_right_def carried_left_eq_dilate)

lemma carried_right_nth0_poly:
  assumes ne: "0 < length xs"
  shows "carried_right xs ! 0 = poly (Poly (carried_left xs)) 1"
proof -
  have ne': "carried_right xs \<noteq> []"
    using ne carried_right_length[of xs] by fastforce
  have "carried_right xs ! 0 = poly.coeff (Poly (carried_right xs)) 0"
    using ne ne' by (simp add: nth_default_def)
  also have "\<dots> = poly (Poly (carried_right xs)) 0"
    by (simp add: poly_0_coeff_0)
  also have "\<dots> = poly (pcompose (Poly (carried_left xs)) [:1, 1:]) 0"
    by (simp add: carried_right_def Poly_taylor_shift_list)
  also have "\<dots> = poly (Poly (carried_left xs)) 1"
    by (simp add: poly_pcompose)
  finally show ?thesis .
qed

lemma carried_right_nth0_sum:
  assumes ne: "0 < length xs"
  shows "carried_right xs ! 0 = (\<Sum>i<length xs. xs ! i * 2 ^ (length xs - Suc i))"
proof -
  have "poly (Poly (carried_left xs)) 1
      = (\<Sum>i<length (carried_left xs). carried_left xs ! i * 1 ^ i)"
    by (rule poly_Poly_nth_sum)
  also have "\<dots> = (\<Sum>i<length xs. xs ! i * 2 ^ (length xs - Suc i))"
    by (simp add: carried_left_eq_dilate dilate_list_nth)
  finally show ?thesis using carried_right_nth0_poly[OF ne] by simp
qed

text \<open>\<^bold>\<open>The bridge in the form the mid decision needs\<close>: the sign of the \<open>O(1)\<close> read decides
  exactly the midpoint-root question that @{thm [source] truncate_mid_test_agrees} states for the
  pruned half-eval op. \<open>2\<^sup>n\<^sup>-\<^sup>1 \<noteq> 0\<close> makes the scaling harmless.\<close>
lemma carried_right_nth0_zero_iff:
  assumes ne: "0 < length xs"
  shows "(carried_right xs ! 0 = 0)
       = (poly (map_poly rat_of_int (Poly xs)) (1 / 2) = 0)"
proof -
  have xsne: "xs \<noteq> []" using ne by auto
  have scaled: "rat_of_int (\<Sum>i<length xs. xs ! i * 2 ^ (length xs - Suc i))
      = 2 ^ (length xs - 1) * poly (map_poly rat_of_int (Poly xs)) (rat_of_int 1 / rat_of_int 2)"
    by (rule cdlr_eval_half_scaled[OF xsne])
  \<comment> \<open>go through the rat IMAGE of the read in one step: chaining \<open>=\<close>-rewrites instead fights
     simp, which pushes \<open>rat_of_int\<close> inside the \<Sum> on one side only.\<close>
  have key: "rat_of_int (carried_right xs ! 0)
      = 2 ^ (length xs - 1) * poly (map_poly rat_of_int (Poly xs)) (1 / 2)"
    using carried_right_nth0_sum[OF ne] scaled by simp
  have "(carried_right xs ! 0 = 0) = (rat_of_int (carried_right xs ! 0) = 0)" by simp
  also have "\<dots> = (2 ^ (length xs - 1)
                    * poly (map_poly rat_of_int (Poly xs)) (1 / 2) = (0::rat))"
    by (simp only: key)
  also have "\<dots> = (poly (map_poly rat_of_int (Poly xs)) (1 / 2) = 0)" by simp
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>The LOCK-case retrunc, proven LOCALLY -- this is the key that avoids editing the
  truncation base.\<close> \<open>carried_retrunc_mop_def\<close>'s first two branches are
  \<open>if len \<le> 1 then RETURN (xs, g) else if 4398046511104 \<le> g then RETURN (xs, g)\<close>, so under a
  LOCK guard the op is the identity on BOTH -- no truncation, guard passed through, whatever
  its value. That is exactly the fact @{thm [source] cdlr_retrunc_child} cannot supply at
  \<open>gin = 2\<^sup>4\<^sup>2 + v\<close>, because its conclusion asserts \<open>g' \<le> 2\<^sup>4\<^sup>2\<close>. Stated here with NO upper cap,
  it lets the payload-carrying lock guard through and unblocks the gate-OPEN reject arm without
  touching \<open>Truncate_Loop_Refine\<close>.\<close>
lemma cdlr_retrunc_child_lock:
  assumes lock: "4398046511104 \<le> gin"
    and ne: "0 < length child"
    and lb: "length child + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_retrunc_mop child gin \<le> SPEC (\<lambda>(ys, g'). ys = child \<and> g' = gin)"
  unfolding carried_retrunc_mop_def poly_length_monadic_def PR_CONST_def
  using ne lb
  by (simp add: lock)

text \<open>\<^bold>\<open>Drop-in shape\<close>: the same conclusion FORM as @{thm [source] cdlr_retrunc_child} (a
  \<open>node_frame\<close> plus the lock implication) but with the \<open>g' \<le> 2\<^sup>4\<^sup>2\<close> conjunct replaced by
  \<open>2\<^sup>4\<^sup>2 \<le> g'\<close>, so it can be substituted for that lemma inside the LOCK branch of
  \<open>truncate_children_mid_agrees\<close> and carries a payload guard through unchanged.\<close>
lemma cdlr_retrunc_child_lock_frame:
  assumes lock: "4398046511104 \<le> gin"
    and eq: "child = XL"
    and ne: "0 < length child"
    and lb: "length child + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_retrunc_mop child gin
       \<le> SPEC (\<lambda>(ys, g'). node_frame XL ys g' \<and> 4398046511104 \<le> g' \<and> g' = gin \<and> ys = XL)"
  apply (rule order_trans[OF cdlr_retrunc_child_lock[OF lock ne lb]])
  using lock eq by (simp add: node_frame_exact_any_g)

section \<open>The fused children-and-midpoint op's two extra outputs\<close>

text \<open>@{const truncate_children_mid_monadic} is @{const truncate_children_monadic} with two
  borrowed reads of \<open>qr ! 0\<close> spliced in before the retruncation, so that the read sees
  @{const carried_right}\<open> Q\<close> exactly (retruncating first would add slack and break the
  \<open>g + len\<close> bound @{const mid_guard_mop} certifies). This lemma states what those two reads
  return; the children-frame conjuncts are @{thm [source] truncate_children_agrees}'s and are
  picked up separately at the push site, the only consumer that needs them.

  \<open>mag\<close> is \<open>hybrid_bitlen2_full\<close>'s magnitude hypothesis: the bit-length spec's upper bound
  is guarded by \<open>size_t\<close> representability, so it is a genuine precondition.

  The structure is @{thm [source] truncate_children_agrees}'s, with the two pure reads spliced
  between the \<open>lr_step\<close> collapse and the first \<open>cdlr_retrunc_child\<close>. The frame premises are
  needed even though the conclusion's new conjuncts do not mention them: the two
  retruncations must still be shown non-failing, and that is what \<open>cdlr_retrunc_child\<close> needs.\<close>

text \<open>The bit-length bundle, re-derived here rather than imported: the identical fact
  \<open>mpz_bitlen2_monadic_full\<close> lives in \<open>Kiou_Bound_Refine.thy\<close>, whose session is NOT an
  ancestor of this one, and the two chains both own \<open>impl/solvers\<close> so they can never co-build
  (\<open>new-check-session\<close> trap 5 — copy pure lemmas, do not import). Same three base facts, same
  proof; \<open>hybrid_\<close> prefix keeps the C9 duplicate-fact lint clean.

  \<^bold>\<open>Why one bundled fact and not three:\<close> \<open>refine_vcg\<close> applies only ONE \<open>\<le> SPEC\<close> fact per
  producer call, so supplying the bounds separately leaves whichever one it picks as the only
  hypothesis downstream.\<close>
lemma hybrid_bitlen2_full:
  assumes "\<bar>m\<bar> < 2 ^ (max_snat LENGTH(gmp_poly_len) - 1)"
  shows "mpz_bitlen2_monadic m \<le> SPEC (\<lambda>r.
      \<bar>m\<bar> < 2 ^ r \<and> (m \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>m\<bar>) \<and> r < max_snat LENGTH(gmp_poly_len))"
  using mpz_bitlen2_monadic_pow2_bound[OF bitlen2_snat_guard[OF assms]]
    mpz_bitlen2_monadic_lower[of m] mpz_bitlen2_monadic_snat_bound[OF assms]
  by (auto simp: pw_le_iff refine_pw_simps)

text \<open>\<^bold>\<open>The same bundle without the magnitude precondition.\<close>
  @{thm [source] hybrid_bitlen2_full}'s upper conjuncts (\<open>\<bar>m\<bar> < 2 ^ r\<close> and
  \<open>r < max_snat\<close>) are the only reason \<open>mag\<close> exists, and \<open>mag\<close> is not provable: unfolding
  @{const carried_right} makes it a bound on a power-of-two-weighted combination of the node
  polynomial's own coefficients, and @{const carried_init_same_den}'s Taylor shift by \<open>l ~ 2 ^ k\<close>
  grows those like \<open>2 ^ (k * deg)\<close>. It therefore cannot be a caller premise.

  \<^bold>\<open>It is also not needed\<close>: the sole consumer of the bit length is
  \<open>truncate_mid_decide_agrees\<close> (below), whose only bit-length premise is \<open>midbl_lb\<close>, the lower bound, which
  @{thm [source] mpz_bitlen2_monadic_lower} gives unconditionally. The impl side does not need it either:
  @{thm [source] hybrid_loop_step_args_impl_hnr} is precondition-free, and the sepref synthesis runs off
  @{const hybrid_loop_step_pre}, which has no magnitude conjunct.\<close>
lemma hybrid_bitlen2_lower:
  "mpz_bitlen2_monadic m \<le> SPEC (\<lambda>r. m \<noteq> 0 \<longrightarrow> 2 ^ (r - 1) \<le> \<bar>m\<bar>)"
  using mpz_bitlen2_monadic_lower[of m]
  by (auto simp: pw_le_iff refine_pw_simps)

lemma truncate_children_mid_agrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
  shows "truncate_children_mid_monadic g Q \<le> SPEC (\<lambda>(ql, gl, qr, gr, mids, midbl).
           node_frame (carried_left X) ql gl \<and> node_frame (carried_right X) qr gr \<and>
           gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
           (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
           (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X) \<and>
           mids = sgn (carried_right Q ! 0) \<and>
           (carried_right Q ! 0 \<noteq> 0 \<longrightarrow> 2 ^ (midbl - 1) \<le> \<bar>carried_right Q ! 0\<bar>))"
proof -
  have lr_step: "carried_left_right_monadic Q \<bind> f
      \<le> f (carried_left Q, carried_right Q)" for f
  proof -
    have "carried_left_right_monadic Q \<bind> f
        \<le> RETURN (carried_left Q, carried_right Q) \<bind> f"
      by (rule bind_mono(1)[OF carried_left_right_monadic_correct[OF Qne Qbound]]) simp
    also have "\<dots> = f (carried_left Q, carried_right Q)" by simp
    finally show ?thesis .
  qed
  have lb_l: "length (carried_left Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lb_r: "length (carried_right Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qbound by simp_all
  have rne: "0 < length (carried_right Q)" using Qne by simp
  \<comment> \<open>the fused op's extra \<open>ASSERT (0 < length qr)\<close> surfaces as \<open>carried_right Q = [] \<Longrightarrow> False\<close>,
     which needs the LIST form, not the length form.\<close>
  \<comment> \<open>\<^bold>\<open>Explicit instantiation, NOT simp.\<close> \<open>simp add: length_greater_0_conv[symmetric]\<close> LOOPS
     here: the reversed rule rewrites \<open>xs \<noteq> [] \<longrightarrow> 0 < length xs\<close> while the DEFAULT
     @{thm [source] length_greater_0_conv} rewrites straight back. And a plain \<open>simp\<close> cannot do
     it either — @{thm [source] carried_right_length} normalizes \<open>rne\<close> to \<open>0 < length Q\<close>, losing
     the \<open>carried_right Q\<close> the goal is about.\<close>
  have rneL: "carried_right Q \<noteq> []"
    using rne length_greater_0_conv[of "carried_right Q"] by blast
  show ?thesis
  proof (cases "g = 0")
    case True
    hence XQ: "X = Q" using frame unfolding node_frame_def by simp
    have fl: "node_frame (carried_left X) (carried_left Q) 0"
      and fr: "node_frame (carried_right X) (carried_right Q) 0"
      unfolding XQ by (rule node_frame_exact)+
    show ?thesis
      unfolding truncate_children_mid_monadic_def truncate_child_guards_mop_def
        poly_length_monadic_def poly_coeff_sgn_monadic_def
        poly_coeff_bitlen2_monadic_def PR_CONST_def
      using Qne Qbound
      apply (simp add: True)
      apply (rule order_trans[OF lr_step])
      apply (simp add: lb_l rne)
      apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
          cdlr_retrunc_child[OF fl lb_l, THEN order_trans])
      apply (all \<open>(simp add: rneL; fail)?\<close>)
      apply (clarsimp simp: lb_r)
      apply (refine_vcg cdlr_retrunc_child[OF fr lb_r, THEN order_trans])
      apply (all \<open>(simp; fail)?\<close>)
      done
  next
    case g_ne0: False
    show ?thesis
    proof (cases "4398046511104 \<le> g")
      case glock: True
      hence QX: "Q = X" using lock by simp
      \<comment> \<open>stated at \<open>g\<close>, not at the literal \<open>2\<^sup>4\<^sup>2\<close>: \<open>truncate_child_guards_mop\<close>'s LOCK branch
         returns \<open>(g, g)\<close> UNCHANGED, so a payload guard \<open>2\<^sup>4\<^sup>2 + v\<close> propagates to the children
         by design. Pinning \<open>g\<close> to the literal here is what forced the old \<open>g_le\<close> premise and
         made the gate-OPEN reject arm (which calls in at \<open>glock = 2\<^sup>4\<^sup>2 + v\<close>) unreachable.\<close>
      have eq_l: "carried_left Q = carried_left X"
        and eq_r: "carried_right Q = carried_right X" unfolding QX by simp_all
      have fl: "node_frame (carried_left X) (carried_left Q) g"
        and fr: "node_frame (carried_right X) (carried_right Q) g"
        unfolding QX by (rule node_frame_exact_any_g)+
      have lock_l: "4398046511104 \<le> g \<longrightarrow> carried_left Q = carried_left X"
        and lock_r: "4398046511104 \<le> g \<longrightarrow> carried_right Q = carried_right X"
        unfolding QX by simp_all
      show ?thesis
        unfolding truncate_children_mid_monadic_def truncate_child_guards_mop_def
          poly_length_monadic_def poly_coeff_sgn_monadic_def
          poly_coeff_bitlen2_monadic_def PR_CONST_def
        using Qne Qbound
        apply (simp add: g_ne0 glock)
        apply (rule order_trans[OF lr_step])
        apply (simp add: lb_l rne)
        apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
            cdlr_retrunc_child_lock_frame[OF glock eq_l _ lb_l, THEN order_trans])
        apply (all \<open>(simp add: rneL; fail)?\<close>)
        apply (clarsimp simp: lb_r)
        apply (refine_vcg cdlr_retrunc_child_lock_frame[OF glock eq_r _ lb_r, THEN order_trans])
        apply (all \<open>(simp; fail)?\<close>)
        done
    next
      case gsmall: False
      have g_win: "g < 1099511627776" using g_tri gsmall by simp
      have not_g40: "\<not> 1099511627776 \<le> g" using g_win by simp
      have not_len40: "\<not> 1099511627776 \<le> length Q" using Q_small by simp
      have QneL: "Q \<noteq> []" using Qne by simp
      have gplen: "g + length Q < max_snat LENGTH(gmp_poly_len)"
        using g_win Q_small unfolding max_snat_def by simp
      have fl: "node_frame (carried_left X) (carried_left Q) (g + length Q - Suc 0)"
        using node_frame_child_left_impl[OF frame g_ne0] Qne
        by (simp add: Nat.add_diff_assoc Suc_le_eq)
      have fr: "node_frame (carried_right X) (carried_right Q) (g + length Q)"
        using node_frame_child_right_tight[OF frame] .
      have gle_l: "g + length Q - Suc 0 \<le> 4398046511104"
        using g_win Q_small by linarith
      have gle_r: "g + length Q \<le> 4398046511104"
        using g_win Q_small by linarith
      have lock_l: "4398046511104 \<le> g + length Q - Suc 0 \<longrightarrow> carried_left Q = carried_left X"
        using g_win Q_small by (intro impI) linarith
      have lock_r: "4398046511104 \<le> g + length Q \<longrightarrow> carried_right Q = carried_right X"
        using g_win Q_small by (intro impI) linarith
      show ?thesis
        unfolding truncate_children_mid_monadic_def truncate_child_guards_mop_def
          poly_length_monadic_def poly_coeff_sgn_monadic_def
          poly_coeff_bitlen2_monadic_def PR_CONST_def
        apply (simp add: g_ne0 gsmall not_g40 not_len40 QneL g_win Q_small gplen)
        apply (rule ASSERT_leI)
        subgoal using gplen by simp
        apply (rule order_trans[OF lr_step])
        apply (simp add: lb_l rne)
        apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
            cdlr_retrunc_child[OF fl lb_l gle_l lock_l, THEN order_trans])
        apply (all \<open>(simp add: rneL Qbound; fail)?\<close>)
        apply clarsimp
        \<comment> \<open>\<open>clarsimp\<close> splits out a leftover \<open>Suc (length Q) < max_snat\<close> as goal 1, so the
           \<open>refine_vcg\<close> below would otherwise fire on the wrong goal. It must be inserted
           (\<open>subgoal using\<close>), not passed as a simp rule: a word bound used as a rewrite does not
           close a goal that is that bound.\<close>
        subgoal using Qbound by simp
        apply (refine_vcg cdlr_retrunc_child[OF fr lb_r gle_r lock_r, THEN order_trans])
        \<comment> \<open>the conclusion now says \<open>\<le> max g 2\<^sup>4\<^sup>2\<close> (so a payload lock guard fits); in THIS
           branch the child guards are \<open>\<le> 2\<^sup>4\<^sup>2\<close>, which entails it via \<open>le_max_iff_disj\<close>.\<close>
        apply (all \<open>(simp add: le_max_iff_disj; fail)?\<close>)
        done
    qed
  qed
qed

section \<open>The midpoint decision agrees with the true midpoint fact\<close>

text \<open>\<^bold>\<open>The midpoint decision is sound.\<close> @{const truncate_mid_decide_monadic} returns \<open>0\<close> = not a root,
  \<open>1\<close> = the midpoint is an exact root, \<open>2\<close> = ambiguous (the caller escalates). This is the
  \<open>mid_decide\<close> analogue of @{thm [source] truncate_mid_test_agrees}, which states the same fact
  for the pruned half-evaluation op.

  Both decisive branches reduce to the midpoint bridge: on an exact (\<open>g = 0\<close>) or locked (\<open>2\<^sup>4\<^sup>2 \<le> g\<close>) node the
  stored polynomial is \<open>X\<close>, so the \<open>O(1)\<close> read is the exact midpoint value and
  @{thm [source] carried_right_nth0_zero_iff} decides the root question outright. The guarded
  branch is the interesting one: there the read is truncated, and soundness of \<open>code = 0\<close> is
  exactly @{thm [source] cdlr_trust_arith}, whose \<open>acc\<close> is, by
  @{thm [source] carried_right_nth0_sum}, precisely the \<open>qr ! 0\<close> the impl reads, and whose \<open>tr\<close>
  hypothesis is literally @{const lead_trust_mop}'s formula at guard \<open>g + len\<close>. \<open>code = 2\<close>
  asserts nothing, so the clamp branch (\<open>2\<^sup>4\<^sup>0 \<le> g < 2\<^sup>4\<^sup>2\<close>, where @{const mid_guard_mop} genuinely
  under-approximates) is vacuously fine; that is why the clamp is conservative.\<close>
lemma truncate_mid_decide_agrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and len_eq: "len = length Q"
    and Qne: "0 < length Q"
    and Q_small: "length Q < 1099511627776"
    and mids_eq: "mids = sgn (carried_right Q ! 0)"
    and midbl_lb: "carried_right Q ! 0 \<noteq> 0 \<longrightarrow> 2 ^ (midbl - 1) \<le> \<bar>carried_right Q ! 0\<bar>"
  shows "truncate_mid_decide_monadic g len mids midbl \<le> SPEC (\<lambda>code.
      (code = 1 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0) \<and>
      (code = 0 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0) \<and>
      (g = 0 \<or> 4398046511104 \<le> g \<longrightarrow> code \<noteq> 2) \<and>
      (code = 0 \<or> code = 1 \<or> code = 2))"
proof -
  have QneL: "Q \<noteq> []" using Qne by simp
  have acc_eq: "carried_right Q ! 0 = (\<Sum>i<length Q. Q ! i * 2 ^ (length Q - Suc i))"
    by (rule carried_right_nth0_sum[OF Qne])
  \<comment> \<open>the two EXACT branches: the stored poly is \<open>X\<close> itself, so the read decides outright.\<close>
  have exact: "Q = X \<Longrightarrow>
      (mids = 0) = (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)"
    using mids_eq carried_right_nth0_zero_iff[OF Qne] by (simp add: sgn_if split: if_splits)
  show ?thesis
  proof (cases "g = 0")
    case True
    hence XQ: "Q = X" using frame unfolding node_frame_def by simp
    show ?thesis unfolding truncate_mid_decide_monadic_def
      using exact[OF XQ] by (auto simp: True)
  next
    case g_ne0: False
    show ?thesis
    proof (cases "4398046511104 \<le> g")
      case glock: True
      show ?thesis unfolding truncate_mid_decide_monadic_def
        using exact[OF lock[rule_format, OF glock]] by (auto simp: g_ne0 glock)
    next
      case gsmall: False
      show ?thesis
      proof (cases "1099511627776 \<le> g")
        case clamp: True
        \<comment> \<open>out-of-trust-window: the op returns the ambiguous sentinel, which asserts nothing.\<close>
        show ?thesis unfolding truncate_mid_decide_monadic_def
          by (simp add: g_ne0 gsmall clamp)
      next
        case g_win: False
        obtain s0 where frame0: "gframe s0 g X Q" using frame node_frameE by blast
        have gplen: "g + length Q < max_snat LENGTH(gmp_poly_len)"
          using g_win Q_small unfolding max_snat_def by simp
        \<comment> \<open>keep @{const mid_guard_mop} FOLDED and feed its value as a \<open>\<le> SPEC\<close> fact: unfolding
           it inline lets \<open>simp\<close> distribute its ASSERT cascade through the implications and the
           goal stops matching @{thm [source] cdlr_trust_arith}.\<close>
        have gm: "mid_guard_mop g len \<le> SPEC (\<lambda>r. r = g + length Q)"
          unfolding mid_guard_mop_def
          using g_win Q_small gplen by (simp add: len_eq)
        show ?thesis
          unfolding truncate_mid_decide_monadic_def lead_trust_mop_def
            op_snat_unat_conv_def PR_CONST_def
          apply (simp add: g_ne0 gsmall g_win)
          apply (refine_vcg gm[THEN order_trans])
          \<comment> \<open>\<open>code = 1\<close> is unreachable on this branch (it returns \<open>0\<close> or \<open>2\<close>), so that
             implication is vacuous; \<open>code = 0\<close> gives \<open>tr\<close>, which is literally
             @{thm [source] cdlr_trust_arith}'s hypothesis once \<open>sgn\<close> is unfolded.\<close>
          \<comment> \<open>\<open>midbl_lb\<close> is an OBJECT implication; \<open>cdlr_trust_arith\<close>'s \<open>bl_lb\<close> is a META one,
             hence \<open>[rule_format]\<close>. Used as a FACT, not via \<open>rule\<close>, so simp can bridge its
             \<open>rat_of_int 1 / rat_of_int 2\<close> to the goal's \<open>1 / 2\<close>. The goal ORDER is not pinned
             (the code-trichotomy conjunct was added later), so close them by \<open>all\<close>.\<close>
          apply (all \<open>(simp split: if_splits; fail)?\<close>)
          apply (all \<open>(insert cdlr_trust_arith[OF frame0 QneL acc_eq midbl_lb[rule_format]]
                              mids_eq,
                       auto simp: sgn_if split: if_splits)?\<close>)
          done
      qed
    qed
  qed
qed

section \<open>The split arm's push-time classify\<close>

text \<open>\<^bold>\<open>Both pushed children get an @{const hybrid_cs_ok} cache entry\<close> against their own exact
  counts. The children are already built (the caller hoisted the build out), so this op only g-classifies and pushes
  them. The two classifies are independent instances of
  @{thm [source] carried_descartes_count_g_hybrid_cs_ok}.

  \<open>qtodo\<close>/\<open>gs\<close> grow by the two children in order (left, right); @{const hybrid_pcc_result_monadic}
  is a bare \<open>RETURN\<close>, and the pushes go through the truncating keystone's
  @{thm [source] cdlr_push2_eq} / @{thm [source] cdlr_append_eq}.\<close>
lemma hybrid_classify_prebuilt_correct:
  assumes frameL: "node_frame XL ql gl" and frameR: "node_frame XR qr gr"
    and lockL: "4398046511104 \<le> gl \<longrightarrow> XL = ql"
    and lockR: "4398046511104 \<le> gr \<longrightarrow> XR = qr"
    and lbL: "length XL + 1 < max_snat LENGTH(gmp_poly_len)"
    and lbR: "length XR + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbL: "length XL * nat_bitlen (length XL) < max_snat LENGTH(gmp_poly_len)"
    and pbR: "length XR * nat_bitlen (length XR) < max_snat LENGTH(gmp_poly_len)"
    and gbL: "gl + length XL < max_snat LENGTH(gmp_poly_len)"
    and gbR: "gr + length XR < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_classify_prebuilt_monadic qtodo gs ql gl qr gr
       \<le> SPEC (\<lambda>(qtodo', gs', cl, cr).
           qtodo' = qtodo @ [ql, qr] \<and> gs' = gs @ [gl, gr] \<and>
           hybrid_cs_ok gl cl (carried_descartes_count XL) \<and>
           hybrid_cs_ok gr cr (carried_descartes_count XR))"
proof -
  \<comment> \<open>state the word bounds on the FRAME TARGETS, not on the children: a caller sees
     \<open>carried_left/right X\<close>, never the retruncated child, so child-form premises are
     undischargeable at the call site. @{thm [source] cdlr_node_frame_len} bridges them.\<close>
  have lL: "length ql = length XL" using cdlr_node_frame_len[OF frameL] by simp
  have lR: "length qr = length XR" using cdlr_node_frame_len[OF frameR] by simp
  have lbL': "length ql + 1 < max_snat LENGTH(gmp_poly_len)" using lbL lL by simp
  have lbR': "length qr + 1 < max_snat LENGTH(gmp_poly_len)" using lbR lR by simp
  have pbL': "length ql * nat_bitlen (length ql) < max_snat LENGTH(gmp_poly_len)"
    using pbL lL by simp
  have pbR': "length qr * nat_bitlen (length qr) < max_snat LENGTH(gmp_poly_len)"
    using pbR lR by simp
  have gbL': "gl + length ql < max_snat LENGTH(gmp_poly_len)" using gbL lL by simp
  have gbR': "gr + length qr < max_snat LENGTH(gmp_poly_len)" using gbR lR by simp
  show ?thesis
  unfolding hybrid_classify_prebuilt_monadic_def hybrid_pcc_result_monadic_def
    PR_CONST_def Let_def
  apply (refine_vcg
      carried_descartes_count_g_hybrid_cs_ok[OF frameL lbL' pbL' gbL' lockL, THEN order_trans]
      carried_descartes_count_g_hybrid_cs_ok[OF frameR lbR' pbR' gbR' lockR, THEN order_trans])
  \<comment> \<open>the three leading ASSERTs are the literal premises, so they must be inserted, not
     passed as simp rules.\<close>
  subgoal using qcap by simp
  subgoal using lbL' by simp
  subgoal using lbR' by simp
  apply (simp add: cdlr_push2_eq[OF qcap] cdlr_append_eq)
  \<comment> \<open>the two \<open>gs\<close>-capacity ASSERTs plus the final \<open>RETURN \<le> RES\<close> product match; \<open>gcap\<close> must be
     INSERTED for the same reason as above.\<close>
  apply (insert gcap, auto simp: pw_le_iff refine_pw_simps)
  done
qed

text \<open>\<^bold>\<open>The full split-arm state push.\<close> Bisection geometry on \<open>todo\<close> (children \<open>(2l, l+r)\<close> and
  \<open>(l+r, 2r)\<close> at depth \<open>k+1\<close> — @{thm [source] cdlr_push_children_eq}), the two classified
  children on \<open>qtodo\<close>/\<open>gs\<close>/\<open>cs\<close>, and the child exponent / \<sigma> successor duplicated on \<open>es\<close>/\<open>ss\<close>.
  \<open>rp\<close> passes through untouched — the root-immutability conjunct in miniature.

  \<sigma> enters ONLY through @{const hybrid_split_run_len}, whose value is left symbolic here: the
  \<open>\<exists>pol\<close> keystone absorbs \<sigma>-divergence, so no lemma on this path may constrain it.\<close>
lemma hybrid_split_pair_state_correct:
  assumes frameL: "node_frame XL ql gl" and frameR: "node_frame XR qr gr"
    and lockL: "4398046511104 \<le> gl \<longrightarrow> XL = ql"
    and lockR: "4398046511104 \<le> gr \<longrightarrow> XR = qr"
    and lbL: "length XL + 1 < max_snat LENGTH(gmp_poly_len)"
    and lbR: "length XR + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbL: "length XL * nat_bitlen (length XL) < max_snat LENGTH(gmp_poly_len)"
    and pbR: "length XR * nat_bitlen (length XR) < max_snat LENGTH(gmp_poly_len)"
    and gbL: "gl + length XL < max_snat LENGTH(gmp_poly_len)"
    and gbR: "gr + length XR < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and scap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_pair_state_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s mid ql gl qr gr
       \<le> SPEC (\<lambda>(todo', qtodo', es', ss', cs', gs', rp').
           todo' = (lns @ [2 * l_num, l_num + r_num], rns @ [l_num + r_num, 2 * r_num],
                    ks @ [k + 1, k + 1]) \<and>
           qtodo' = qtodo @ [ql, qr] \<and> gs' = gs @ [gl, gr] \<and>
           es' = es @ [newton_child_exp e, newton_child_exp e] \<and>
           rp' = rp \<and>
           (\<exists>cl cr. cs' = cs @ [cl, cr] \<and>
                    ss' = ss @ [hybrid_split_run_len mid cl cr s,
                                hybrid_split_run_len mid cl cr s] \<and>
                    hybrid_cs_ok gl cl (carried_descartes_count XL) \<and>
                    hybrid_cs_ok gr cr (carried_descartes_count XR)))"
proof -
  \<comment> \<open>\<open>gl\<close>/\<open>gr\<close> are OUTPUTS of the caller's \<open>children_mid\<close>, so a premise mentioning them
     cannot be discharged eagerly at the call site. Take a \<open>gl\<close>-FREE capacity bound plus the
     guard cap (which \<open>children_mid\<close>'s own postcondition supplies) and derive the product.\<close>
  \<comment> \<open>every producer must reach \<open>refine_vcg\<close> as a \<open>\<le> SPEC\<close> fact; an equation supplied as a simp
     rule rewrites the head but then leaves a \<open>RETURN \<dots> \<le> SPEC \<dots>\<close> the chain cannot continue
     from.\<close>
  have pc: "dyadic_interval_vec_push_children_monadic (lns, rns, ks) l_num r_num k
      \<le> SPEC (\<lambda>todo'. todo' = (lns @ [2 * l_num, l_num + r_num],
                                rns @ [l_num + r_num, 2 * r_num], ks @ [k + 1, k + 1]))"
    by (simp add: cdlr_push_children_eq[OF push kcap])
  show ?thesis
    unfolding hybrid_split_pair_state_monadic_def PR_CONST_def Let_def
    \<comment> \<open>INSERT the capacity facts up front so \<open>refine_vcg\<close> discharges the six leading ASSERTs
       itself and reaches the body in ONE pass.\<close>
    using qcap ecap scap ccap gcap push scap1
    apply (refine_vcg pc[THEN order_trans]
        hybrid_classify_prebuilt_correct[OF frameL frameR lockL lockR lbL lbR
          pbL pbR gbL gbR qcap gcap, THEN order_trans]
        dyadic_exp_push2_monadic_spec[THEN order_trans])
    apply (all \<open>(simp add: cdlr_append_eq; fail)?\<close>)
    done
qed

text \<open>\<^bold>\<open>Productivity of the split arm on an exact or locked node\<close> (\<open>\<le> SPEC (\<lambda>_. True)\<close>, i.e.
  the arm never fails). \<open>code \<noteq> 2\<close> (carried by
  @{thm [source] truncate_mid_decide_agrees}) makes the ambiguous rebuild branch unreachable, so
  this case has two terminal arms, not five. Productivity is what the \<open>\<Down>\<close>-refinement of the loop step needs;
  \<open>Truncate_Loop_Refine\<close> has the analogous productivity lemmas for its plain leaves.

  \<^bold>\<open>Why the postcondition is \<open>True\<close> and not the state result.\<close> Strengthening it to the real result
  (\<open>todo'\<close>/\<open>es'\<close>/\<open>rp'\<close> plus the dichotomy "the midpoint leaf is pushed iff the midpoint is a root") requires
  composing @{thm [source] truncate_children_mid_agrees} with
  @{thm [source] truncate_mid_decide_agrees} across the op's own bind. \<open>children_mid\<close>'s
  postcondition is a 6-tuple case-lambda; a \<open>clarsimp\<close> between the two \<open>refine_vcg\<close> stages
  destructures it far enough to discharge \<open>mids_eq\<close>, but \<open>midbl_lb\<close> (an object implication
  whose antecedent \<open>clarsimp\<close> has already stripped) then no longer matches. A fused
  two-op lemma does not help either: its trailing \<open>RETURN\<close> does not match the op's continuation
  \<open>if code = 2 \<dots>\<close>.

  The workable route is that of @{thm [source] truncate_branch_split_agrees}, which \<open>define\<close>s the expected final
  value and proves the abstract side equals \<open>RETURN pfin\<close>, collapsing the comparison instead of threading a large
  SPEC through \<open>refine_vcg\<close>.\<close>
(*FASTLOOP_FREEZE_ABOVE*)

text \<open>\<^bold>\<open>Transport for the factored child build.\<close> @{const hybrid_branch_split_monadic} delegates to
  @{const hybrid_split_children_classic_monadic} instead of inlining \<open>children_mid + decide\<close>, so both exact-branch
  proofs below consume this contract instead of the two-op composition: the same node_frame/guard conclusions, with
  the op's internal rebuild arm absorbed and \<open>code = 1\<close> replaced by the returned Boolean.\<close>

text \<open>The skip-right children step as a bind rule: the continuation is proved for every \<open>(r, rz)\<close>
  the full contract (@{thm [source] carried_left_right_skip_right_correct}) allows. The template's
  deterministic \<open>lr_step\<close> cannot be used: the op's result is specified, not computed.\<close>
lemma carried_left_right_skip_right_bind:
  assumes ne: "0 < length xs"
    and cap: "length xs + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
    and kb: "g + length xs < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>r rz. \<lbrakk> \<not> rz \<longrightarrow> r = carried_right xs;
        rz \<longrightarrow> r = [carried_right xs ! 0] \<and> carried_right xs ! 0 \<noteq> 0 \<and>
               carried_descartes_count (carried_right xs) = 0 \<and> right_empty_certified g xs \<rbrakk>
        \<Longrightarrow> f (carried_left xs, r, rz) \<le> SPEC \<Phi>"
  shows "carried_left_right_skip_right_monadic g xs \<bind> f \<le> SPEC \<Phi>"
  \<comment> \<open>the FULL contract, not \<open>_nth0\<close>: on \<open>rz\<close> the stub is exactly the singleton.\<close>
  apply (refine_vcg carried_left_right_skip_right_correct[OF ne cap dep kb, THEN order_trans])
  by (auto intro!: cont split: prod.splits)

text \<open>\<^bold>\<open>The contract of the skip-right children build.\<close> The template is
  @{thm [source] truncate_children_mid_agrees}, and the op differs from it in one step:
  the children come from @{const carried_left_right_skip_right_monadic}, which may prove the right child
  empty (\<open>rz\<close>) and then returns the singleton stub \<open>[carried_right Q ! 0]\<close> instead of the child.
  So the right child's frame is claimed only on \<open>\<not> rz\<close>, and on \<open>rz\<close> the exact right child's
  count is \<open>0\<close> (@{thm [source] right_empty_certified_count_zero}), which is what lets the caller skip
  the push. Both \<open>qr!0\<close> reads are unchanged on both branches.\<close>
lemma truncate_children_mid_skip_right_agrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_children_mid_skip_right_monadic g Q \<le> SPEC (\<lambda>(ql, gl, qr, gr, mids, midbl, rz).
           node_frame (carried_left X) ql gl \<and>
           gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
           (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
           (\<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                     (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X)) \<and>
           (rz \<longrightarrow> carried_descartes_count (carried_right X) = 0 \<and>
                   carried_right Q ! 0 \<noteq> 0) \<and>
           mids = sgn (carried_right Q ! 0) \<and>
           (carried_right Q ! 0 \<noteq> 0 \<longrightarrow> 2 ^ (midbl - 1) \<le> \<bar>carried_right Q ! 0\<bar>))"
proof -
  have lb_l: "length (carried_left Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lb_r: "length (carried_right Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qbound by simp_all
  have rne: "0 < length (carried_right Q)" using Qne by simp
  have rneL: "carried_right Q \<noteq> []"
    using rne length_greater_0_conv[of "carried_right Q"] by blast
  \<comment> \<open>the stub is never retruncated: \<open>carried_retrunc_mop\<close> returns any list of length \<open>\<le> 1\<close>.\<close>
  have stub_rt: "carried_retrunc_mop [s] h \<le> SPEC (\<lambda>(ys, h'). ys = [s] \<and> h' = h)" for s h
    unfolding carried_retrunc_mop_def poly_length_monadic_def PR_CONST_def by simp
  show ?thesis
  proof (cases "g = 0")
    case True
    hence XQ: "X = Q" using frame unfolding node_frame_def by simp
    have fl: "node_frame (carried_left X) (carried_left Q) 0"
      and fr: "node_frame (carried_right X) (carried_right Q) 0"
      unfolding XQ by (rule node_frame_exact)+
    show ?thesis
      unfolding truncate_children_mid_skip_right_monadic_def truncate_child_guards_mop_def
        poly_length_monadic_def poly_coeff_sgn_monadic_def
        poly_coeff_bitlen2_monadic_def PR_CONST_def
      using Qne Qbound Qbound2 dep
      apply (simp add: True)
      apply (rule carried_left_right_skip_right_bind[where g = 0, OF Qne Qbound2 dep])
      subgoal using Qbound by simp
      subgoal for r rz
        apply (cases rz)
        subgoal
          apply (simp add: lb_l)
          apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
              cdlr_retrunc_child[OF fl lb_l, THEN order_trans] stub_rt[THEN order_trans])
          apply (auto simp: XQ)
          done
        subgoal
          apply (simp add: lb_l rne)
          apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
              cdlr_retrunc_child[OF fl lb_l, THEN order_trans])
          apply (all \<open>(simp add: rneL; fail)?\<close>)
          apply (clarsimp simp: lb_r)
          apply (refine_vcg cdlr_retrunc_child[OF fr lb_r, THEN order_trans])
          apply (all \<open>(simp; fail)?\<close>)
          done
        done
      done
  next
    case g_ne0: False
    show ?thesis
    proof (cases "4398046511104 \<le> g")
      case glock: True
      hence QX: "Q = X" using lock by simp
      have eq_l: "carried_left Q = carried_left X"
        and eq_r: "carried_right Q = carried_right X" unfolding QX by simp_all
      show ?thesis
        unfolding truncate_children_mid_skip_right_monadic_def truncate_child_guards_mop_def
          poly_length_monadic_def poly_coeff_sgn_monadic_def
          poly_coeff_bitlen2_monadic_def PR_CONST_def
        using Qne Qbound Qbound2 dep
        apply (simp add: g_ne0 glock)
        apply (rule carried_left_right_skip_right_bind[OF Qne Qbound2 dep kb])
        subgoal for r rz
          apply (cases rz)
          subgoal
            apply (simp add: lb_l)
            apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
                cdlr_retrunc_child_lock_frame[OF glock eq_l _ lb_l, THEN order_trans]
                stub_rt[THEN order_trans])
            apply (auto simp: QX)
            done
          subgoal
            apply (simp add: lb_l rne)
            apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
                cdlr_retrunc_child_lock_frame[OF glock eq_l _ lb_l, THEN order_trans])
            apply (all \<open>(simp add: rneL; fail)?\<close>)
            apply (clarsimp simp: lb_r)
            apply (refine_vcg
                cdlr_retrunc_child_lock_frame[OF glock eq_r _ lb_r, THEN order_trans])
            apply (all \<open>(simp; fail)?\<close>)
            done
          done
        done
    next
      case gsmall: False
      have g_win: "g < 1099511627776" using g_tri gsmall by simp
      have not_g40: "\<not> 1099511627776 \<le> g" using g_win by simp
      have not_len40: "\<not> 1099511627776 \<le> length Q" using Q_small by simp
      have QneL: "Q \<noteq> []" using Qne by simp
      have gplen: "g + length Q < max_snat LENGTH(gmp_poly_len)"
        using g_win Q_small unfolding max_snat_def by simp
      have fl: "node_frame (carried_left X) (carried_left Q) (g + length Q - Suc 0)"
        using node_frame_child_left_impl[OF frame g_ne0] Qne
        by (simp add: Nat.add_diff_assoc Suc_le_eq)
      have fr: "node_frame (carried_right X) (carried_right Q) (g + length Q)"
        using node_frame_child_right_tight[OF frame] .
      have gle_l: "g + length Q - Suc 0 \<le> 4398046511104"
        using g_win Q_small by linarith
      have gle_r: "g + length Q \<le> 4398046511104"
        using g_win Q_small by linarith
      have lock_l: "4398046511104 \<le> g + length Q - Suc 0 \<longrightarrow> carried_left Q = carried_left X"
        using g_win Q_small by (intro impI) linarith
      have lock_r: "4398046511104 \<le> g + length Q \<longrightarrow> carried_right Q = carried_right X"
        using g_win Q_small by (intro impI) linarith
      \<comment> \<open>\<^bold>\<open>THE one place the frame transfer is needed\<close>: at a truncated guard the certificate is
         about the STORED node, and @{thm [source] right_empty_certified_count_zero} carries it to \<open>X\<close>.\<close>
      have cnt0: "right_empty_certified g Q \<Longrightarrow> carried_descartes_count (carried_right X) = 0"
        by (rule right_empty_certified_count_zero[OF frame]) (use gsmall in simp_all)
      show ?thesis
        unfolding truncate_children_mid_skip_right_monadic_def truncate_child_guards_mop_def
          poly_length_monadic_def poly_coeff_sgn_monadic_def
          poly_coeff_bitlen2_monadic_def PR_CONST_def
        using Qne Qbound Qbound2 dep
        apply (simp add: g_ne0 gsmall not_g40 not_len40 QneL g_win Q_small gplen)
        apply (rule ASSERT_leI)
        subgoal using gplen by simp
        apply (rule carried_left_right_skip_right_bind[OF Qne Qbound2 dep kb])
        subgoal for r rz
          apply (cases rz)
          subgoal
            apply (simp add: lb_l)
            apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
                cdlr_retrunc_child[OF fl lb_l gle_l lock_l, THEN order_trans]
                stub_rt[THEN order_trans])
            apply (auto intro: cnt0 simp: le_max_iff_disj gle_r)
            done
          subgoal
            apply (simp add: lb_l rne)
            apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
                cdlr_retrunc_child[OF fl lb_l gle_l lock_l, THEN order_trans])
            apply (all \<open>(simp add: rneL Qbound; fail)?\<close>)
            apply clarsimp
            apply (refine_vcg cdlr_retrunc_child[OF fr lb_r gle_r lock_r, THEN order_trans])
            apply (all \<open>(simp add: le_max_iff_disj; fail)?\<close>)
            done
          done
        done
    qed
  qed
qed

lemma hybrid_split_children_classic_agrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_children_classic_monadic l_num r_num k rp g len Q
      \<le> SPEC (\<lambda>(ql, gl, qr, gr, mid, rz).
          node_frame (carried_left X) ql gl \<and>
          gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
          (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
          (\<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X)) \<and>
          (rz \<longrightarrow> carried_descartes_count (carried_right X) = 0) \<and>
          (mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0) \<and>
          (\<not> mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0))"proof -
  \<comment> \<open>\<^bold>\<open>The op's \<open>code = 2\<close> rebuild arm is dead here, and that is the content of this lemma.\<close> Under \<open>gex\<close> the
     stored polynomial is the exact node on both branches (at \<open>g = 0\<close> by @{thm [source] node_frame_def}, at a lock guard
     by \<open>lock\<close>), and on both of those @{const truncate_mid_decide_monadic} is a bare
     \<open>RETURN (if 0 < mids \<or> mids < 0 then 0 else 1)\<close>: it returns \<open>0\<close> or \<open>1\<close>, never
     the escalate sentinel, and never reads \<open>len\<close>. Two consequences: this contract needs no
     \<open>len = length Q\<close> premise (unlike the two-op composition, whose
     @{thm [source] truncate_mid_decide_agrees} step does), and the rebuild arm's
     \<open>carried_init_inplace\<close> chain never has to be reasoned about, so no
     \<open>recompute\<close>/\<open>kcap\<close> premise either.\<close>
  have QX: "Q = X"
  proof (cases "g = 0")
    case True
    have "X = Q" using frame True unfolding node_frame_def by simp
    thus ?thesis by (rule sym)
  next
    case False
    thus ?thesis using gex lock by simp
  qed

  have dec: "truncate_mid_decide_monadic g len' mids midbl
      \<le> SPEC (\<lambda>code. code \<noteq> 2
          \<and> ((code = 1) = (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)))"
    if mids_eq: "mids = sgn (carried_right Q ! 0)" for len' mids midbl
  proof -
    have "(mids = 0) = (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)"
      using mids_eq carried_right_nth0_zero_iff[OF Qne] QX
      by (simp add: sgn_if split: if_splits)
    thus ?thesis
      unfolding truncate_mid_decide_monadic_def using gex by auto
  qed

  show ?thesis
    unfolding hybrid_split_children_classic_monadic_def PR_CONST_def
    using Qne Qbound Qbound2 dep rpne rpb krp
    apply (refine_vcg
        truncate_children_mid_skip_right_agrees[OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb,
          THEN order_trans]
        dec[THEN order_trans])
    apply (all \<open>(clarsimp; fail)?\<close>)
    done
qed

text \<open>\<^bold>\<open>The two TWINS of the contract above\<close> -- the bind form and the DECOMPOSED form,
  for exactly the reason \<open>truncate_children_mid_decide_bind_decomp\<close> records:
  \<open>refine_vcg\<close> produces the decomposed shape whenever the prefix sits under an outer bind
  (it has already split \<open>m \<bind> rest \<le> SPEC \<Phi>\<close> into
  \<open>m \<le> SPEC (\<lambda>x. rest x \<le> SPEC \<Phi>)\<close>), and the bind form then has no
  match. \<^bold>\<open>Supply BOTH to \<open>refine_vcg\<close>\<close>; do not try to convert one into the other
  (three routes were tried on the classic twin and all three diverge or fail to unify under the
  \<open>case_prod\<close> binder).\<close>

lemma hybrid_split_children_classic_gbind:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>ql gl qr gr mid rz.
        \<lbrakk>node_frame (carried_left X) ql gl;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          \<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0;
          mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          \<not> mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0\<rbrakk>
        \<Longrightarrow> f ql gl qr gr mid rz \<le> SPEC \<Phi>"
  shows "(doN { (ql, gl, qr, gr, mid, rz) \<leftarrow>
                 hybrid_split_children_classic_monadic l_num r_num k rp g len Q;
               f ql gl qr gr mid rz })
       \<le> SPEC \<Phi>"
  apply (refine_vcg hybrid_split_children_classic_agrees[
        OF frame lock gex g_tri Qne Qbound Qbound2 dep Q_small kb rpne rpb krp,
        THEN order_trans])
  apply clarsimp
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

lemma hybrid_split_children_classic_gbind_decomp:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>ql gl qr gr mid rz.
        \<lbrakk>node_frame (carried_left X) ql gl;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          \<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0;
          mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          \<not> mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0\<rbrakk>
        \<Longrightarrow> f ql gl qr gr mid rz \<le> SPEC \<Phi>"
  \<comment> \<open>\<^bold>\<open>Note where the \<open>\<le> SPEC \<Phi>\<close> sits.\<close> \<open>bind_rule\<close> turns
     \<open>m \<bind> case_prod h \<le> SPEC \<Phi>\<close> into
     \<open>m \<le> SPEC (\<lambda>x. (case x of \<dots> \<Rightarrow> h \<dots>) \<le> SPEC \<Phi>)\<close> --
     the comparison is OUTSIDE the case-lambda. Writing the pattern-matching abbreviation
     \<open>SPEC (\<lambda>(ql, \<dots>, rz). f \<dots> \<le> SPEC \<Phi>)\<close> instead puts it INSIDE, giving
     \<open>case_prod (\<lambda>\<dots>. f \<dots> \<le> SPEC \<Phi>)\<close> -- extensionally the same predicate but a
     DIFFERENT term, which higher-order unification will not match. That mismatch is silent:
     the rule simply never fires and \<open>refine_vcg\<close> leaves the untouched goal to whatever
     tactic follows.\<close>
  shows "hybrid_split_children_classic_monadic l_num r_num k rp g len Q
       \<le> SPEC (\<lambda>x. (case x of (ql, gl, qr, gr, mid, rz) \<Rightarrow> f ql gl qr gr mid rz)
             \<le> SPEC \<Phi>)"
  apply (refine_vcg hybrid_split_children_classic_agrees[
        OF frame lock gex g_tri Qne Qbound Qbound2 dep Q_small kb rpne rpb krp,
        THEN order_trans])
  apply clarsimp
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

section \<open>The left-only push\<close>

text \<open>\<^bold>\<open>The left child's interval push, in the explicit-triple form\<close> the arm closers consume
  (the one-child twin of @{thm [source] cdlr_push_children_eq}). A \<open>\<le> SPEC\<close> rather than an
  equation: the op is built from spec'd GMP primitives, not \<open>RETURN\<close>s.\<close>
lemma dyadic_iv_push_left_child_eq:
  assumes push: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
  shows "dyadic_iv_push_left_child_monadic (lns, rns, ks) l_num r_num k
      \<le> SPEC (\<lambda>todo'. todo' = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [k + 1]))"
  unfolding dyadic_iv_push_left_child_monadic_def dyadic_interval_vec_push_monadic_def
    PR_CONST_def
  apply (refine_vcg mpz_double_shift_monadic_spec_plain[THEN order_trans])
  using push kcap
  by (auto simp: mpzb_discard_monadic_def mpz_add.aop_r1_def top_fun_def top_bool_def
                 poly_push_coeff_monadic_def dyadic_interval_vec_pushable_def)

text \<open>\<^bold>\<open>The left-only classify.\<close> The cut-down of @{thm [source] hybrid_classify_prebuilt_correct}:
  one classify, one push each on \<open>qtodo\<close>/\<open>gs\<close>, and \<open>cr = 0\<close> as a LITERAL. Capacity premises
  are the two-child lemma's \<open>+2\<close> forms, so an arm can hand both lemmas the same facts.\<close>
lemma hybrid_classify_prebuilt_left_correct:
  assumes frameL: "node_frame XL ql gl"
    and lockL: "4398046511104 \<le> gl \<longrightarrow> XL = ql"
    and lbL: "length XL + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbL: "length XL * nat_bitlen (length XL) < max_snat LENGTH(gmp_poly_len)"
    and gbL: "gl + length XL < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_classify_prebuilt_left_monadic qtodo gs ql gl
       \<le> SPEC (\<lambda>(qtodo', gs', cl, cr).
           qtodo' = qtodo @ [ql] \<and> gs' = gs @ [gl] \<and> cr = 0 \<and>
           hybrid_cs_ok gl cl (carried_descartes_count XL))"
proof -
  have lL: "length ql = length XL" using cdlr_node_frame_len[OF frameL] by simp
  have lbL': "length ql + 1 < max_snat LENGTH(gmp_poly_len)" using lbL lL by simp
  have pbL': "length ql * nat_bitlen (length ql) < max_snat LENGTH(gmp_poly_len)"
    using pbL lL by simp
  have gbL': "gl + length ql < max_snat LENGTH(gmp_poly_len)" using gbL lL by simp
  have qcap1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have gcap1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  show ?thesis
    unfolding hybrid_classify_prebuilt_left_monadic_def hybrid_pcc_result_monadic_def
      poly_vec_push_monadic_def PR_CONST_def Let_def
    apply (refine_vcg
        carried_descartes_count_g_hybrid_cs_ok[OF frameL lbL' pbL' gbL' lockL, THEN order_trans])
    subgoal using qcap1 by simp
    subgoal using lbL' by simp
    apply (insert qcap1 gcap1, auto simp: cdlr_append_eq pw_le_iff refine_pw_simps)
    done
qed

text \<open>\<^bold>\<open>The left-only pair-state step.\<close> The one-child twin of
  @{thm [source] hybrid_split_pair_state_correct}: every column gains ONE entry, and the
  run-length update reads \<open>cr = 0\<close>. Same premises as the two-child lemma minus the right child's.\<close>
lemma hybrid_split_pair_state_left_correct:
  assumes frameL: "node_frame XL ql gl"
    and lockL: "4398046511104 \<le> gl \<longrightarrow> XL = ql"
    and lbL: "length XL + 1 < max_snat LENGTH(gmp_poly_len)"
    and pbL: "length XL * nat_bitlen (length XL) < max_snat LENGTH(gmp_poly_len)"
    and gbL: "gl + length XL < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and scap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kcap: "Suc k < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_pair_state_left_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s mid ql gl
       \<le> SPEC (\<lambda>(todo', qtodo', es', ss', cs', gs', rp').
           todo' = (lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [k + 1]) \<and>
           qtodo' = qtodo @ [ql] \<and> gs' = gs @ [gl] \<and>
           es' = es @ [newton_child_exp e] \<and>
           rp' = rp \<and>
           (\<exists>cl. cs' = cs @ [cl] \<and>
                 ss' = ss @ [hybrid_split_run_len mid cl 0 s] \<and>
                 hybrid_cs_ok gl cl (carried_descartes_count XL)))"
proof -
  have push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    using push unfolding dyadic_interval_vec_pushable2_def dyadic_interval_vec_pushable_def
    by simp
  have qcap1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have gcap1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  have ecap1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecap by simp
  have scap1': "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using scap by simp
  have ccap1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  show ?thesis
    unfolding hybrid_split_pair_state_left_monadic_def PR_CONST_def Let_def
    using qcap1 ecap1 scap1' ccap1 gcap1 push1 scap1
    apply (refine_vcg dyadic_iv_push_left_child_eq[OF push1 kcap, THEN order_trans]
        hybrid_classify_prebuilt_left_correct[OF frameL lockL lbL pbL gbL qcap gcap,
          THEN order_trans])
    apply (all \<open>(simp add: cdlr_append_eq; fail)?\<close>)
    done
qed
lemma hybrid_branch_split_exact_productive:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and g_le: "g \<le> 4398046511104"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and Qpb: "length Q * nat_bitlen (length Q) < max_snat LENGTH(gmp_poly_len)"
    and recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rp_small: "length rp < 1099511627776"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (\<lambda>_. True)"
proof -
  have g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g" using gex by auto
  have lenXQ: "length X = length Q" by (rule cdlr_node_frame_len[OF frame])
  \<comment> \<open>\<^bold>\<open>Root-anchored bounds\<close> — the technique @{thm [source] truncate_branch_split_agrees} uses:
     every child of an exact node is itself a @{const carried_init_same_den} of the SAME
     retained root at depth \<open>k+1\<close> (@{thm [source] carried_left_right_reconstruct}), so ALL
     child-side word bounds reduce to bounds on \<open>rp\<close>, which the caller has. Carrying
     child-SHAPED premises instead is undischargeable at the call site, because the children
     are outputs of \<open>children_mid\<close>.\<close>
  have lenXrp: "length X = length rp"
    by (simp add: recompute truncate_length_carried_init_same_den)
  \<comment> \<open>\<^bold>\<open>ROOT-ANCHORED bounds\<close> — the technique @{thm [source] truncate_branch_split_agrees}
     uses, and the reason child-SHAPED premises are the wrong design: each child of an exact
     node is itself a @{const carried_init_same_den} of the SAME retained root at depth
     \<open>k+1\<close> (@{thm [source] carried_left_right_reconstruct}), so every child-side word bound
     reduces to a bound on \<open>rp\<close> — which the caller has, whereas the children are OUTPUTS of
     \<open>children_mid\<close> and so can never be constrained by a premise.\<close>
  have lenXrp: "length X = length rp"
    by (simp add: recompute truncate_length_carried_init_same_den)
  have lenL: "length (carried_left X) = length rp"
    and lenR: "length (carried_right X) = length rp"
    using lenXrp by simp_all
  have lbLX: "length (carried_left X) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lbRX: "length (carried_right X) + 1 < max_snat LENGTH(gmp_poly_len)"
    using rpb lenL lenR by simp_all
  have pbLX: "length (carried_left X) * nat_bitlen (length (carried_left X))
                < max_snat LENGTH(gmp_poly_len)"
    and pbRX: "length (carried_right X) * nat_bitlen (length (carried_right X))
                < max_snat LENGTH(gmp_poly_len)"
    using rp_pb lenL lenR by simp_all
  have gcXL: "4398046511104 + length (carried_left X) < max_snat LENGTH(gmp_poly_len)"
    and gcXR: "4398046511104 + length (carried_right X) < max_snat LENGTH(gmp_poly_len)"
    using rp_small lenL lenR unfolding max_snat_def by simp_all
  have pm: "carried_push_mid_monadic (al, ar, ak) l_num r_num k
      \<le> SPEC (\<lambda>a. a = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1]))"
    by (simp add: cdlr_push_mid_eq[OF accpush])
  \<comment> \<open>\<^bold>\<open>The three extra premises cost the caller nothing\<close>: \<open>Q_small\<close> puts \<open>length Q\<close> under
     \<open>2\<^sup>4\<^sup>0\<close> and \<open>g_le\<close> puts \<open>g\<close> at most \<open>2\<^sup>4\<^sup>2\<close>, so both sums sit far below \<open>max_snat 64\<close>.\<close>
  have Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    using Q_small unfolding max_snat_def by simp
  have dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)" using Qbound by simp
  have kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    using g_le Q_small unfolding max_snat_def by simp
  show ?thesis
    unfolding hybrid_branch_split_monadic_def poly_length_monadic_def PR_CONST_def
      poly_free_monadic_def
    using gex Qne Qbound Qbound2 dep kcap rpne rpb krp qcap gcap ecap sscap ccap push accpush scap1
    \<comment> \<open>TWO STAGES with a \<open>clarsimp\<close> between: \<open>children_mid\<close>'s postcondition is a 6-tuple
       case-lambda, and until it is DESTRUCTURED the follow-on rule's \<open>mids_eq\<close>/\<open>midbl_lb\<close>
       premises cannot be matched against it and surface as goals instead.\<close>
    apply (refine_vcg
        hybrid_split_children_classic_gbind[
          OF frame lock gex g_tri Qne Qbound Qbound2 dep Q_small kb rpne rpb krp]
        hybrid_split_children_classic_gbind_decomp[
          OF frame lock gex g_tri Qne Qbound Qbound2 dep Q_small kb rpne rpb krp])
    apply clarsimp
    \<comment> \<open>the \<open>rz\<close> arm pushes the left child only (@{thm [source]
       hybrid_split_pair_state_left_correct}); for a productivity statement that is all it needs.\<close>
    \<comment> \<open>\<^bold>\<open>On every goal, not the first.\<close> \<open>clarsimp\<close> splits the \<open>if rz\<close>/\<open>if mid\<close> cascade into four
       goals, and a bare \<open>apply (refine_vcg \<dots>)\<close> touches only the first.\<close>
    apply (all \<open>(refine_vcg
        hybrid_split_pair_state_correct[where XL = "carried_left X" and XR = "carried_right X",
          OF _ _ _ _ lbLX lbRX pbLX pbRX _ _, THEN order_trans]
        hybrid_split_pair_state_left_correct[where XL = "carried_left X",
          OF _ _ lbLX pbLX _, THEN order_trans]
        pm[THEN order_trans])?\<close>)
    \<comment> \<open>the frame references \<open>XL\<close>/\<open>XR\<close> in @{thm [source] hybrid_split_pair_state_correct} are
       GHOSTS — they do not occur in the program text, so \<open>refine_vcg\<close> instantiates them by
       unification with the children themselves. For a PRODUCTIVITY statement any instantiation
       serves, and @{thm [source] node_frame_exact_any_g} discharges the reflexive one.\<close>
    apply (all \<open>((rule node_frame_exact_any_g | assumption); fail)?\<close>)
    apply (all \<open>((insert gex g_le gcXL gcXR, auto simp: max_def); fail)?\<close>)
    apply (all \<open>(simp; fail)?\<close>)    \<comment> \<open>the prefix now yields \<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close>; under \<open>gex\<close> and \<open>g_le\<close> that collapses back to
       \<open>\<le> 2\<^sup>4\<^sup>2\<close> (either \<open>g = 0\<close> or \<open>g = 2\<^sup>4\<^sup>2\<close>), so \<open>max_def\<close> plus those two closes it.\<close>
    apply (all \<open>((insert gex g_le gcXL gcXR, auto simp: max_def); fail)?\<close>)
    \<comment> \<open>residual child-length bounds: pull \<open>length child = length (carried_left/right X)\<close> off the
       frame premise with \<open>frule\<close>, then \<open>lenXQ\<close> closes against \<open>Qbound\<close>. \<open>auto\<close> with
       \<open>dest!: cdlr_node_frame_len\<close> loops here.\<close>
    apply (all \<open>(rule hybrid_split_pair_state_left_correct
          [where XL = "carried_left X", OF _ _ lbLX pbLX _, THEN order_trans]
        ; insert ccap gex g_le gcXL gcXR lenXQ
        ; (auto simp: pm max_def); fail)?\<close>)
    apply (all \<open>(rule hybrid_split_pair_state_correct
          [where XL = "carried_left X" and XR = "carried_right X",
            OF _ _ _ _ lbLX lbRX pbLX pbRX _ _, THEN order_trans])
        ; insert ccap gex g_le gcXL gcXR lenXQ
        ; (auto simp: pm max_def)\<close>)
    done
qed

section \<open>The gate-open window arm\<close>

text \<open>\<^bold>\<open>Bail's window correspondence applies verbatim.\<close> It need not be re-derived with free gate Booleans:
  @{thm [source] newton_window_pick_bail_abs} is \<^bold>\<open>pol-free\<close>, concluding against \<open>try_window_bail_int True\<close>. Since
  @{thm [source] hybrid_tree1_unfold} feeds \<open>try_window_bail_int (snd dec)\<close>, recording
  \<open>dec = (True, True)\<close> at a gate-open pop makes it apply as stated, for the
  \<open>Some\<close> (accept) and \<open>None\<close> (reject) outcomes alike. That recorded value is also exactly
  \<open>pol_final\<close>'s own shape at \<open>gate = True\<close> (\<open>pol_final \<dots> = (gate, gate)\<close>), so the \<open>\<exists>pol\<close> witness stays
  consistent with bail's fixed policy. \<open>try_window_bail_int\<close> reads only the \<open>snd\<close> component.\<close>

lemma hybrid_window_pick_at_recorded_dec:
  assumes repr: "carried_repr_scalar P a b Q" and len2: "Suc 0 < length P"
    and ab: "a < b" and l0r0: "l0 < r0" and canon: "coeffs (Poly P) = P"
    and abdef: "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)"
               "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
    and dec: "pol (degree (Poly P)) a b e dk (s, descartes_list_int a b (coeffs (Poly P)))
              = (True, True)"
  shows "map_option (\<lambda>(m, _). dyadic_iv_node_iv l0 r0 k0
                        (fst (newton_window_child l r k e m))
                        (fst (snd (newton_window_child l r k e m)))
                        (snd (snd (newton_window_child l r k e m))))
                    (newton_window_pick_bail v e Q)
       = try_window_bail_int
           (snd (pol (degree (Poly P)) a b e dk (s, descartes_list_int a b (coeffs (Poly P)))))
           a b (N_of e) (Poly P) v"
  using newton_window_pick_bail_abs[OF repr len2 ab l0r0 canon abdef] dec by simp

section \<open>Building block: the truncation coupling\<close>

text \<open>\<^bold>\<open>The hybrid analogue of @{term truncate_state_rel}, as a PREDICATE not a relation.\<close>
  The dense keystone can state its coupling as a relation onto a plain-bisection twin state
  because that twin exists; the hybrid solver has no twin — absorbing that divergence is
  precisely what the \<open>\<exists>pol\<close> keystone is for. So the same content is carried
  as a predicate over the hybrid state alone: every stored node is \<open>node_frame\<close>d against the
  EXACT polynomial its own \<open>(l, r, k)\<close> triple recomputes from the retained root \<open>rp\<close>, guards
  stay under the EXACT-LOCK cap, and a LOCKed node's stored poly IS that exact polynomial.

  \<open>rp\<close>-immutability is structural here: \<open>rp\<close> is a parameter of the predicate, so a step that
  changed it could not re-establish the predicate at the same \<open>rp\<close>.\<close>
definition hybrid_trunc_coupling ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow> bool" where
  "hybrid_trunc_coupling todo qtodo gs rp \<longleftrightarrow>
     (case todo of (lns, rns, ks) \<Rightarrow>
        length lns = length qtodo \<and> length rns = length qtodo \<and>
        length ks = length qtodo \<and> length gs = length qtodo \<and>
        (\<forall>i < length qtodo.
           node_frame (carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp)
                      (qtodo ! i) (gs ! i) \<and>
           (gs ! i \<le> (ks ! i + 1) * length rp \<or> 4398046511104 \<le> gs ! i) \<and>
           (4398046511104 \<le> gs ! i \<longrightarrow>
              qtodo ! i = carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp)))"

text \<open>\<^bold>\<open>Seed\<close>: the initial state — one root node at \<open>(l_num, r_num, k)\<close> carrying the exact
  poly \<open>P\<close> with guard \<open>0\<close> — satisfies the coupling, because \<open>P\<close> IS the carried init of \<open>rp\<close>
  (the keystone's \<open>P_eq\<close> premise) and a poly is its own frame at guard \<open>0\<close>.\<close>
lemma hybrid_trunc_coupling_init:
  assumes P_eq: "P = carried_init_same_den l_num (2 ^ k) r_num rp"
  shows "hybrid_trunc_coupling ([l_num], [r_num], [k]) [P] [0] rp"
  unfolding hybrid_trunc_coupling_def
  using P_eq by (simp add: node_frame_exact)

text \<open>\<^bold>\<open>The cache coupling\<close>, factored out so its preservation lemmas mirror the
  truncation coupling's exactly (pop / push). Every worklist slot's cached class is
  @{const hybrid_cs_ok} against the EXACT count of the polynomial that slot's own
  \<open>(l, r, k)\<close> recomputes from \<open>rp\<close> — the property @{thm [source] hybrid_resolve_count_monadic_classify}
  consumes at pop to hand the dispatch a bail-trustworthy class.\<close>
definition hybrid_cs_coupling ::
  "gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow> bool" where
  "hybrid_cs_coupling todo qtodo cs gs rp \<longleftrightarrow>
     length cs = length qtodo \<and>
     (case todo of (lns, rns, ks) \<Rightarrow>
        (\<forall>i < length qtodo.
           hybrid_cs_ok (gs ! i) (cs ! i)
             (carried_descartes_count
                (carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp))))"

lemma hybrid_cs_coupling_pop:
  assumes c: "hybrid_cs_coupling (lns, rns, ks) qtodo cs gs rp"
    and lg: "length gs = length qtodo"
    and ll: "length lns = length qtodo" and lr': "length rns = length qtodo"
    and lk: "length ks = length qtodo"
  shows "hybrid_cs_coupling (butlast lns, butlast rns, butlast ks)
           (butlast qtodo) (butlast cs) (butlast gs) rp"
  using c lg ll lr' lk unfolding hybrid_cs_coupling_def by (auto simp: nth_butlast)

lemma hybrid_cs_coupling_push:
  assumes c: "hybrid_cs_coupling (lns, rns, ks) qtodo cs gs rp"
    and lg: "length gs = length qtodo"
    and ll: "length lns = length qtodo" and lr': "length rns = length qtodo"
    and lk: "length ks = length qtodo"
    and ok1: "hybrid_cs_ok g1 c1
                (carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp))"
    and ok2: "hybrid_cs_ok g2 c2
                (carried_descartes_count (carried_init_same_den l2 (2 ^ k2) r2 rp))"
  shows "hybrid_cs_coupling (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
           (qtodo @ [q1, q2]) (cs @ [c1, c2]) (gs @ [g1, g2]) rp"
  using c lg ll lr' lk ok1 ok2 unfolding hybrid_cs_coupling_def
  by (auto simp: nth_append less_Suc_eq)


section \<open>\<open>\<sigma>\<close> is a GHOST column -- the accounting runs on abstract run lengths\<close>

text \<open>\<^bold>\<open>Why the abstract node list cannot be \<open>\<alpha>\<close> of the concrete columns.\<close> The split
  arm pushes children whose run length is @{const hybrid_split_run_len}, computed from the
  cached classes; the abstract driver's is @{const split_run_len_int}, computed from the exact
  counts. They genuinely differ: an ambiguous child caches the sentinel \<open>4\<close>, which carries no
  count information at all (see \<open>Hybrid_Solver_Dispatch\<close>). So no lemma can identify
  the two, and a split step that pinned the pushed \<open>\<sigma>\<close> to \<open>split_run_len_int\<close> would be unsatisfiable
  (\<open>hybrid_npush_forall_sv_is_vacuous\<close>).

  \<^bold>\<open>So \<open>\<sigma>\<close> is not projected at all.\<close> The accounting runs over its own node list,
  which carries the abstract run lengths and is advanced only by the abstract step rules; the
  concrete columns are tied to it by \<open>hybrid_nodes_sigma_variant\<close>, which compares the
  first four components and ignores \<open>\<sigma>\<close> entirely.

  \<^bold>\<open>Why this needs no \<open>\<sigma>\<close>-independence theorem.\<close> @{const hybrid_acc_invar} is \<open>\<sigma>\<close>-sensitive:
  its \<open>\<forall>pol\<close> ranges over policies that may read \<open>\<sigma>\<close> at any node whose view is not yet
  recorded, so it cannot be transported across a \<open>\<sigma>\<close>-change. It never has to be. A node's view
  enters \<open>D\<close> exactly when its subtree is expanded (@{thm [source] hybrid_acc_invar_step}), and
  \<open>D\<close>'s own constraint quantifies over \<open>\<forall>e2 dk2 s2 w2\<close>, so the recorded decision holds at the
  ghost \<open>\<sigma>\<close>, which is the only \<open>\<sigma>\<close> the accounting ever sees. Blindness is already in the
  invariant, per recorded view; it does not have to be imposed globally on \<open>pol\<close>, and the
  abstract tree never has to be proved \<open>\<sigma>\<close>-independent by induction over
  \<open>newdsc_pol_bail\<close>. A design that projects \<open>\<sigma>\<close> from \<open>ss\<close> does need that induction.\<close>
definition hybrid_nodes_sigma_variant ::
  "(rat \<times> rat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> bool" where
  "hybrid_nodes_sigma_variant ns ms \<longleftrightarrow>
     map (\<lambda>(a, b, e, dk, s). (a, b, e, dk)) ns = map (\<lambda>(a, b, e, dk, s). (a, b, e, dk)) ms"

lemma hybrid_nodes_sigma_variant_refl: "hybrid_nodes_sigma_variant ns ns"
  by (simp add: hybrid_nodes_sigma_variant_def)

lemma hybrid_nodes_sigma_variant_NilD:
  "hybrid_nodes_sigma_variant ns [] \<Longrightarrow> ns = []"
  by (simp add: hybrid_nodes_sigma_variant_def)

lemma hybrid_nodes_sigma_variant_snocI:
  "hybrid_nodes_sigma_variant ns ms
     \<Longrightarrow> hybrid_nodes_sigma_variant (ns @ [(a, b, e, dk, s1)]) (ms @ [(a, b, e, dk, s2)])"
  by (simp add: hybrid_nodes_sigma_variant_def)

lemma hybrid_nodes_sigma_variant_snoc2I:
  "hybrid_nodes_sigma_variant ns ms
     \<Longrightarrow> hybrid_nodes_sigma_variant
           (ns @ [(a1, b1, e1, dk1, s1), (a2, b2, e2, dk2, s2)])
           (ms @ [(a1, b1, e1, dk1, t1), (a2, b2, e2, dk2, t2)])"
  by (simp add: hybrid_nodes_sigma_variant_def)

text \<open>The pop direction: a \<open>\<sigma>\<close>-variant of a snoc-decomposed node list is itself snoc-decomposed,
  at the SAME first four components and some ghost run length.\<close>
lemma hybrid_nodes_sigma_variant_snocE:
  assumes sv: "hybrid_nodes_sigma_variant ns (ms @ [(a, b, e, dk, s)])"
  obtains ns' sg where "ns = ns' @ [(a, b, e, dk, sg)]"
    and "hybrid_nodes_sigma_variant ns' ms"
proof -
  let ?f = "\<lambda>(a, b, e, dk, s). (a, b, e, dk)"
  from sv have m: "map ?f ns = map ?f ms @ [(a, b, e, dk)]"
    by (simp add: hybrid_nodes_sigma_variant_def)
  hence ne: "ns \<noteq> []" by auto
  obtain ns' nd where nsd: "ns = ns' @ [nd]"
    using ne by (cases ns rule: rev_cases) auto
  obtain a' b' e' dk' sg where ndd: "nd = (a', b', e', dk', sg)" by (cases nd) auto
  from m nsd ndd have hd: "map ?f ns' = map ?f ms"
    and tl: "(a', b', e', dk') = (a, b, e, dk)"
    by (simp_all add: append1_eq_conv)
  have L: "ns = ns' @ [(a, b, e, dk, sg)]" using nsd ndd tl by simp
  have R: "hybrid_nodes_sigma_variant ns' ms"
    using hd by (simp add: hybrid_nodes_sigma_variant_def)
  from L R show thesis by (rule that)
qed

text \<open>\<^bold>\<open>The abstract invariant, ghost-\<open>\<sigma>\<close> form.\<close> Identical to @{const hybrid_abs_invar} except
  that the accounting's node list is existential and only \<open>\<sigma>\<close>-variant to the projection.\<close>
definition hybrid_abs_invar_g ::
  "int poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat)
     \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "hybrid_abs_invar_g P l0 r0 k0 seed todo es ss acc \<longleftrightarrow>
     (\<exists>D ns. hybrid_nodes_sigma_variant ns (hybrid_alpha_nodes l0 r0 k0 todo es ss) \<and>
             alr_ivl_run_invar (map fst D) (hybrid_alpha_views l0 r0 k0 todo) \<and>
             hybrid_acc_invar P seed D
               (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)) ns)"

text \<open>The base's invariant is the special case \<open>ns = \<alpha>\<close>, so its \<open>init\<close> transfers verbatim.\<close>
lemma hybrid_abs_invar_gI:
  "hybrid_abs_invar P l0 r0 k0 seed todo es ss acc
     \<Longrightarrow> hybrid_abs_invar_g P l0 r0 k0 seed todo es ss acc"
  unfolding hybrid_abs_invar_g_def hybrid_abs_invar_def
  using hybrid_nodes_sigma_variant_refl by blast

lemma hybrid_abs_invar_g_init:
  assumes triples: "dyadic_interval_vec_triples todo = [((l0, r0), k0)]"
    and lr: "l0 < r0"
    and es: "es = [e0]" and ss: "ss = [0]"
    and acc_empty: "dyadic_interval_vec_triples acc = []"
  shows "hybrid_abs_invar_g P l0 r0 k0 (0, 1, e0, k0, 0) todo es ss acc"
  by (rule hybrid_abs_invar_gI[OF hybrid_abs_invar_init[OF triples lr es ss acc_empty]])

text \<open>\<^bold>\<open>Exit\<close>: an empty worklist forces the ghost list empty too, so the accounting collapses
  exactly as it does in the base.\<close>
lemma hybrid_abs_invar_g_exit:
  assumes inv: "hybrid_abs_invar_g P l0 r0 k0 (a, b, e0, dk0, 0) todo es ss acc"
    and empty: "dyadic_interval_vec_triples todo = []"
  shows "\<exists>pol. mset (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc))
              = mset (newdsc_pol_bail_int pol a b e0 dk0 P)"
proof -
  from inv obtain D ns
    where sv: "hybrid_nodes_sigma_variant ns (hybrid_alpha_nodes l0 r0 k0 todo es ss)"
      and run: "alr_ivl_run_invar (map fst D) (hybrid_alpha_views l0 r0 k0 todo)"
      and acc: "hybrid_acc_invar P (a, b, e0, dk0, 0) D
                  (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)) ns"
    by (auto simp: hybrid_abs_invar_g_def)
  have nodes_empty: "hybrid_alpha_nodes l0 r0 k0 todo es ss = []"
    using empty by (simp add: hybrid_alpha_nodes_def)
  have ns_empty: "ns = []"
    using sv nodes_empty by (simp add: hybrid_nodes_sigma_variant_def)
  have dist: "distinct (map fst D)" using run by (rule alr_ivl_run_invar_D_distinct)
  have acc0: "hybrid_acc_invar P (a, b, e0, dk0, 0) D
                (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)) []"
    using acc by (simp add: ns_empty)
  show ?thesis by (rule hybrid_acc_invar_exit[OF acc0 dist])
qed

text \<open>\<^bold>\<open>The full WHILEIT refinement invariant\<close> = the abstract
  \<open>\<exists>D\<close> accounting @{const hybrid_abs_invar_g}, \<oplus> the truncation coupling, \<oplus> the
  cache coupling: every worklist slot's cached class is @{const hybrid_cs_ok} against the
  EXACT count of the polynomial that slot's own \<open>(l, r, k)\<close> recomputes from \<open>rp\<close>. Bail's word
  bounds are deliberately NOT folded in here — they are s-value-agnostic and live in
  \<open>hybrid_loop_safe_invar\<close>, so \<open>\<sigma>\<close> never leaks into these conjuncts.\<close>
definition hybrid_refine_invar ::
  "int poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat)
     \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list
     \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "hybrid_refine_invar P l0 r0 k0 seed todo qtodo es ss cs gs rp acc \<longleftrightarrow>
     hybrid_abs_invar_g P l0 r0 k0 seed todo es ss acc \<and>
     hybrid_trunc_coupling todo qtodo gs rp \<and>
     hybrid_cs_coupling todo qtodo cs gs rp"

text \<open>\<^bold>\<open>Seed\<close>: the three components' own init lemmas, combined. The seed cache class \<open>c0\<close> is a
  HYPOTHESIS, exactly as bail's keystone parameterizes over its seed classify \<open>cc\<close>
  (\<open>bail_main_list_correct\<close>'s \<open>cs_wit\<close>/\<open>seed_safe\<close>) — the impl computes it with
  @{const carried_descartes_count_trunc_monadic}, so it is discharged at the assembly, not here.\<close>
lemma hybrid_refine_invar_init:
  assumes lr: "l0 < r0"
    and P_eq: "P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and cs_seed: "hybrid_cs_ok 0 c0 (carried_descartes_count P)"
    and acc_empty: "dyadic_interval_vec_triples acc = []"
    and triples: "dyadic_interval_vec_triples ([l0], [r0], [k0]) = [((l0, r0), k0)]"
  shows "hybrid_refine_invar (Poly P') l0 r0 k0 (0, 1, e0, k0, 0)
           ([l0], [r0], [k0]) [P] [e0] [0] [c0] [0] rp acc"
  unfolding hybrid_refine_invar_def
  using hybrid_abs_invar_g_init[OF triples lr refl refl acc_empty]
        hybrid_trunc_coupling_init[OF P_eq] cs_seed P_eq
  by (simp add: hybrid_cs_coupling_def)

text \<open>\<^bold>\<open>Exit\<close>: at an empty worklist the invariant yields the keystone's \<open>\<exists>pol\<close> conclusion —
  the coupling and cache conjuncts are not needed here, only the abstract accounting.\<close>
lemma hybrid_refine_invar_exit:
  assumes inv: "hybrid_refine_invar P l0 r0 k0 (a, b, e0, dk0, 0) todo qtodo es ss cs gs rp acc"
    and empty: "dyadic_interval_vec_triples todo = []"
  shows "\<exists>pol. mset (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc))
              = mset (newdsc_pol_bail_int pol a b e0 dk0 P)"
proof -
  have "hybrid_abs_invar_g P l0 r0 k0 (a, b, e0, dk0, 0) todo es ss acc"
    using inv unfolding hybrid_refine_invar_def by simp
  from hybrid_abs_invar_g_exit[OF this empty] show ?thesis .
qed

text \<open>\<^bold>\<open>Pop preservation\<close>: dropping the LIFO-last slot from every column preserves the
  coupling — the surviving slots keep their own \<open>(l, r, k)\<close> triples, hence their own
  recompute-from-\<open>rp\<close> frames. This is the \<open>v = 0\<close> discard arm's whole coupling obligation, and
  the prefix half of every other arm's.\<close>
lemma hybrid_trunc_coupling_pop:
  assumes c: "hybrid_trunc_coupling (lns, rns, ks) qtodo gs rp"
  shows "hybrid_trunc_coupling (butlast lns, butlast rns, butlast ks)
           (butlast qtodo) (butlast gs) rp"
proof -
  have L: "length lns = length qtodo" "length rns = length qtodo"
     and K: "length ks = length qtodo" "length gs = length qtodo"
    using c unfolding hybrid_trunc_coupling_def by simp_all
  have body: "\<And>i. i < length qtodo \<Longrightarrow>
      node_frame (carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp)
                 (qtodo ! i) (gs ! i) \<and>
      (gs ! i \<le> (ks ! i + 1) * length rp \<or> 4398046511104 \<le> gs ! i) \<and>
      (4398046511104 \<le> gs ! i \<longrightarrow>
         qtodo ! i = carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp)"
    using c unfolding hybrid_trunc_coupling_def by simp
  show ?thesis
    unfolding hybrid_trunc_coupling_def
    using L K body by (auto simp: nth_butlast)
qed

text \<open>\<^bold>\<open>Push preservation\<close>: appending two children — each already framed against its OWN
  recompute-from-\<open>rp\<close> — preserves the coupling. Together with
  @{thm [source] hybrid_trunc_coupling_pop} this is the coupling half of every split/window
  arm: pop the parent, push the pair.\<close>
lemma hybrid_trunc_coupling_push:
  assumes c: "hybrid_trunc_coupling (lns, rns, ks) qtodo gs rp"
    and f1: "node_frame (carried_init_same_den l1 (2 ^ k1) r1 rp) q1 g1"
    and f2: "node_frame (carried_init_same_den l2 (2 ^ k2) r2 rp) q2 g2"
    and g1le: "g1 \<le> (k1 + 1) * length rp \<or> 4398046511104 \<le> g1"
    and g2le: "g2 \<le> (k2 + 1) * length rp \<or> 4398046511104 \<le> g2"
    and lk1: "4398046511104 \<le> g1 \<longrightarrow> q1 = carried_init_same_den l1 (2 ^ k1) r1 rp"
    and lk2: "4398046511104 \<le> g2 \<longrightarrow> q2 = carried_init_same_den l2 (2 ^ k2) r2 rp"
  shows "hybrid_trunc_coupling (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
           (qtodo @ [q1, q2]) (gs @ [g1, g2]) rp"
proof -
  have L: "length lns = length qtodo" "length rns = length qtodo"
     and K: "length ks = length qtodo" "length gs = length qtodo"
    using c unfolding hybrid_trunc_coupling_def by simp_all
  have body: "\<And>i. i < length qtodo \<Longrightarrow>
      node_frame (carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp)
                 (qtodo ! i) (gs ! i) \<and>
      (gs ! i \<le> (ks ! i + 1) * length rp \<or> 4398046511104 \<le> gs ! i) \<and>
      (4398046511104 \<le> gs ! i \<longrightarrow>
         qtodo ! i = carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp)"
    using c unfolding hybrid_trunc_coupling_def by simp
  show ?thesis
    unfolding hybrid_trunc_coupling_def
    using L K body f1 f2 g1le g2le lk1 lk2
    by (auto simp: nth_append less_Suc_eq)
qed

text \<open>\<^bold>\<open>The discard arm's ENTIRE coupling obligation\<close>: popping the LIFO-last slot preserves both
  couplings. The \<open>v = 0\<close> branch pushes nothing (@{thm [source] hybrid_tree1_discard}: the node's
  subtree is empty), so this IS its step; every other arm uses it as the prefix half before
  pushing with the \<open>_push\<close> lemmas.\<close>
lemma hybrid_refine_invar_pop_couplings:
  assumes inv: "hybrid_refine_invar P l0 r0 k0 seed (lns, rns, ks) qtodo es ss cs gs rp acc"
  shows "hybrid_trunc_coupling (butlast lns, butlast rns, butlast ks)
           (butlast qtodo) (butlast gs) rp \<and>
         hybrid_cs_coupling (butlast lns, butlast rns, butlast ks)
           (butlast qtodo) (butlast cs) (butlast gs) rp"
proof -
  have tc: "hybrid_trunc_coupling (lns, rns, ks) qtodo gs rp"
    and cc: "hybrid_cs_coupling (lns, rns, ks) qtodo cs gs rp"
    using inv unfolding hybrid_refine_invar_def by simp_all
  have L: "length lns = length qtodo" "length rns = length qtodo"
     and K: "length ks = length qtodo" "length gs = length qtodo"
    using tc unfolding hybrid_trunc_coupling_def by simp_all
  show ?thesis
    using hybrid_trunc_coupling_pop[OF tc]
          hybrid_cs_coupling_pop[OF cc K(2) L(1) L(2) K(1)] by simp
qed

section \<open>Building block: the \<open>\<alpha>\<close>-projection under a two-child push\<close>

text \<open>The base proves the POP side (@{thm [source] hybrid_alpha_nodes_butlast},
  @{thm [source] hybrid_alpha_views_butlast}); the step lemmas need the PUSH side too. Since
  @{const dyadic_interval_vec_triples} is \<open>zip (zip lns rns) ks\<close>, appending one entry to each
  column appends one triple — provided the columns were equal-length to start with, which the
  coupling guarantees.\<close>
lemma dyadic_interval_vec_triples_append2:
  assumes "length lns = length rns" and "length rns = length ks"
  shows "dyadic_interval_vec_triples (lns @ [a, b], rns @ [c, d], ks @ [p, q])
       = dyadic_interval_vec_triples (lns, rns, ks) @ [((a, c), p), ((b, d), q)]"
  using assms unfolding dyadic_interval_vec_triples_def by simp

lemma hybrid_alpha_nodes_append2:
  assumes lr: "length lns = length rns" and rk: "length rns = length ks"
    and le: "length es = length ks" and ls: "length ss = length ks"
  shows "hybrid_alpha_nodes l0 r0 k0 (lns @ [a, b], rns @ [c, d], ks @ [p, q])
             (es @ [e1, e2]) (ss @ [s1, s2])
       = hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
         @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((a, c), p)),
             snd (dyadic_iv_node_iv_of l0 r0 k0 ((a, c), p)), e1, p, s1),
            (fst (dyadic_iv_node_iv_of l0 r0 k0 ((b, d), q)),
             snd (dyadic_iv_node_iv_of l0 r0 k0 ((b, d), q)), e2, q, s2)]"
  using assms
  unfolding hybrid_alpha_nodes_def dyadic_interval_vec_triples_append2[OF lr rk]
  by (simp add: dyadic_interval_vec_triples_def)

lemma hybrid_alpha_views_append2:
  assumes lr: "length lns = length rns" and rk: "length rns = length ks"
  shows "hybrid_alpha_views l0 r0 k0 (lns @ [a, b], rns @ [c, d], ks @ [p, q])
       = hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
         @ [dyadic_iv_node_iv_of l0 r0 k0 ((a, c), p),
            dyadic_iv_node_iv_of l0 r0 k0 ((b, d), q)]"
  unfolding hybrid_alpha_views_def dyadic_interval_vec_triples_append2[OF lr rk] by simp

section \<open>The rational-to-real policy partner (kills the \<open>\<And>pol2\<close> \<open>polrel\<close> premise)\<close>

text \<open>\<^bold>\<open>Why this exists.\<close> @{thm [source] hybrid_acc_invar_step}'s \<open>branch\<close> obligation is
  \<open>\<And>pol\<close>-quantified, and the abstract branch equations
  (@{thm [source] hybrid_tree1_split}, @{thm [source] hybrid_tree1_window}) each need a REAL
  policy \<open>polr\<close> related to that \<open>pol\<close> by \<open>polrel\<close>. A \<open>polr\<close> fixed OUTSIDE the binder cannot
  serve every \<open>pol\<close> inside it, and stating the premise as \<open>\<And>pol2. polr \<dots> = pol2 \<dots>\<close> to paper
  over that is \<^bold>\<open>unsatisfiable\<close> -- see \<open>hybrid_polrel_forall_pol_is_vacuous\<close>.

  \<^bold>\<open>The fix is constructive\<close>: \<open>of_rat\<close> is injective, so it has a left inverse, and the real
  partner can simply be BUILT from the rational policy at each \<open>pol\<close>. That turns \<open>polrel\<close>
  into a proved fact instead of a hypothesis, and every lemma downstream sheds both the premise and its
  \<open>polr\<close> parameter. The \<open>norel\<close> variants below are the two branch equations with \<open>polr\<close> already
  discharged; they are conditional rewrites with a SCHEMATIC policy, so \<open>simp\<close> instantiates them
  at whatever \<open>pol\<close> the enclosing binder supplies.

  This also discharges, generically, the \<open>polrel\<close> packaging duty that the int/real bridge
  @{thm [source] hybrid_pol_int_sound_real_image'} imposes on the keystone's witness.\<close>
definition hybrid_polr_of_pol :: "newton_pol \<Rightarrow> newton_pol_real" where
  "hybrid_polr_of_pol pol =
     (\<lambda>p x y e dk sv. pol p (inv of_rat x) (inv of_rat y) e dk (fst sv, nat (snd sv)))"

lemma hybrid_polr_of_pol_rel:
  "hybrid_polr_of_pol pol p (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
     = pol p a2 b2 e2 dk2 (s2, v)"
proof -
  have inj: "inj (of_rat :: rat \<Rightarrow> real)" by (simp add: inj_def)
  show ?thesis by (simp add: hybrid_polr_of_pol_def inv_f_f[OF inj])
qed

text \<open>The two branch equations, \<open>polr\<close>-free.\<close>
lemma hybrid_tree1_split_norel:
  fixes pol :: newton_pol
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and ab: "a < b"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and dec: "pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P)) = (False, False)"
  shows "mset (hybrid_tree1 pol P a b e dk s) =
      (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
       then {#((a + b) / 2, (a + b) / 2)#} else {#})
      + mset (hybrid_tree1 pol P a ((a + b) / 2) (max 1 (e - 1)) (dk + 1)
                (split_run_len_int P a b s))
      + mset (hybrid_tree1 pol P ((a + b) / 2) b (max 1 (e - 1)) (dk + 1)
                (split_run_len_int P a b s))"
  \<comment> \<open>pin EVERY variable with \<open>where\<close> before \<open>OF\<close> -- the idiom
     @{thm [source] hybrid_tree1_split} itself carries: against schematic \<open>?P\<close>/\<open>?a\<close>/\<open>?b\<close>
     the higher-order \<open>polrel\<close> argument raises \<open>OF: multiple unifiers\<close>.\<close>
  by (rule hybrid_tree1_split[where P = P and pol = pol
        and polr = "hybrid_polr_of_pol pol"
        and a = a and b = b and e = e and dk = dk and s = s,
        OF P0 p0 sf ab hybrid_polr_of_pol_rel v2 dec])

lemma hybrid_tree1_window_norel:
  fixes pol :: newton_pol
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and ab: "a < b"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and win: "try_window_bail_int
                (snd (pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P))))
                a b (N_of e) P (descartes_list_int a b (coeffs P)) = Some I"
  shows "mset (hybrid_tree1 pol P a b e dk s)
       = mset (hybrid_tree1 pol P (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s)"
  by (rule hybrid_tree1_window[where P = P and pol = pol
        and polr = "hybrid_polr_of_pol pol"
        and a = a and b = b and e = e and dk = dk and s = s and I = I,
        OF P0 p0 sf ab hybrid_polr_of_pol_rel v2 win])

section \<open>The discard arm's full abstract step\<close>

text \<open>\<^bold>\<open>The \<open>v = 0\<close> arm re-establishes @{const hybrid_abs_invar_g}.\<close> This is the first fully
  assembled step of the WHILEIT: the popped node's exact count is \<open>0\<close>, so
  @{thm [source] hybrid_tree1_discard} makes its subtree EMPTY — nothing is appended to acc and
  no children are pushed. The decision recorded for the node is irrelevant to the accounting
  (the branch equation holds for every \<open>pol\<close>), so any \<open>dec\<close> works; freshness comes from
  @{thm [source] alr_ivl_run_invar_leaf}, which needs only that the popped view is non-degenerate.

  Stated over the ALREADY-PROJECTED node list so it is independent of the concrete columns;
  the concrete arm supplies the projection via @{thm [source] hybrid_alpha_nodes_butlast} /
  @{thm [source] hybrid_alpha_views_butlast}.\<close>
lemma hybrid_acc_invar_discard_step:
  assumes inv: "hybrid_acc_invar P seed D ACC (rest @ [(a, b, e, dk, s)])"
    and zero: "descartes_list_int a b (coeffs P) = 0"
  shows "hybrid_acc_invar P seed (D @ [((a, b), dec)]) ACC rest"
proof -
  have branch: "\<And>pol. pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P)) = dec
      \<Longrightarrow> mset (hybrid_tree1 pol P a b e dk s)
          = mset [] + hybrid_tree_mset pol P []"
    by (simp add: hybrid_tree1_discard[OF zero])
  from hybrid_acc_invar_step[OF inv branch]
  show ?thesis by simp
qed

text \<open>\<^bold>\<open>The \<open>v = 1\<close> accept arm\<close>, the direct analogue: the popped node's subtree is the
  SINGLETON \<open>[(a, b)]\<close> (@{thm [source] hybrid_tree1_accept}), so that interval is appended to
  acc and again no children are pushed. Its \<open>alr_ivl_run_invar\<close> half is the same
  @{thm [source] alr_ivl_run_invar_leaf} step as the discard arm's.\<close>
lemma hybrid_acc_invar_accept_step:
  assumes inv: "hybrid_acc_invar P seed D ACC (rest @ [(a, b, e, dk, s)])"
    and one: "descartes_list_int a b (coeffs P) = 1"
  shows "hybrid_acc_invar P seed (D @ [((a, b), dec)]) (ACC @ [(a, b)]) rest"
proof -
  have branch: "\<And>pol. pol (degree P) a b e dk (s, descartes_list_int a b (coeffs P)) = dec
      \<Longrightarrow> mset (hybrid_tree1 pol P a b e dk s)
          = mset [(a, b)] + hybrid_tree_mset pol P []"
    by (simp add: hybrid_tree1_accept[OF one])
  from hybrid_acc_invar_step[OF inv branch]
  show ?thesis by simp
qed

text \<open>\<^bold>\<open>The gate-CLOSED split arm\<close>: the popped node contributes the mid-root leaf (present iff
  the midpoint really is a root) and pushes the two bisection children, at the SAME split points
  the impl uses — truncation degrades coefficients, never geometry. The recorded decision is
  \<open>(False, False)\<close>, i.e. no window try fires (@{thm [source] hybrid_tree1_split}).\<close>
lemma hybrid_acc_invar_split_step:
  assumes inv: "hybrid_acc_invar P seed D ACC (rest @ [(a, b, e, dk, s)])"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and ab: "a < b"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
  shows "hybrid_acc_invar P seed (D @ [((a, b), (False, False))])
           (ACC @ (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                   then [((a + b) / 2, (a + b) / 2)] else []))
           (rest @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, split_run_len_int P a b s),
                    ((a + b) / 2, b, max 1 (e - 1), dk + 1, split_run_len_int P a b s)])"
proof -
  have branch: "\<And>pol2. pol2 (degree P) a b e dk (s, descartes_list_int a b (coeffs P))
                        = (False, False)
      \<Longrightarrow> mset (hybrid_tree1 pol2 P a b e dk s)
          = mset (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                  then [((a + b) / 2, (a + b) / 2)] else [])
            + hybrid_tree_mset pol2 P
                [(a, (a + b) / 2, max 1 (e - 1), dk + 1, split_run_len_int P a b s),
                 ((a + b) / 2, b, max 1 (e - 1), dk + 1, split_run_len_int P a b s)]"
    by (simp add: hybrid_tree1_split_norel[OF P0 p0 sf ab v2]
                  hybrid_tree_mset_Cons add.assoc)
  from hybrid_acc_invar_step[OF inv branch] show ?thesis by simp
qed

text \<open>\<^bold>\<open>The gate-open window arm\<close>: when the recorded decision makes a window try fire, the
  node's subtree is exactly its single window child's; nothing reaches acc and one node is
  pushed (@{thm [source] hybrid_tree1_window}). With the recorded value \<open>dec = (True, True)\<close>, \<open>win\<close> is supplied
  by the pol-free @{thm [source] hybrid_window_pick_at_recorded_dec}, which is why no re-derivation of bail's
  window math is needed here.\<close>
lemma hybrid_acc_invar_window_step:
  assumes inv: "hybrid_acc_invar P seed D ACC (rest @ [(a, b, e, dk, s)])"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and ab: "a < b"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and win: "try_window_bail_int (snd (dec :: bool \<times> bool)) a b (N_of e) P
                (descartes_list_int a b (coeffs P)) = Some I"
  shows "hybrid_acc_invar P seed (D @ [((a, b), dec)]) ACC
           (rest @ [(fst I, snd I, e + 1, dk + (2 ^ e + 2), s)])"
proof -
  have branch: "\<And>pol2. pol2 (degree P) a b e dk (s, descartes_list_int a b (coeffs P)) = dec
      \<Longrightarrow> mset (hybrid_tree1 pol2 P a b e dk s)
          = mset [] + hybrid_tree_mset pol2 P
                        [(fst I, snd I, e + 1, dk + (2 ^ e + 2), s)]"
    using win
    by (simp add: hybrid_tree1_window_norel[OF P0 p0 sf ab v2]
                  hybrid_tree_mset_Cons)
  from hybrid_acc_invar_step[OF inv branch] show ?thesis by simp
qed

text \<open>Its @{const alr_ivl_run_invar} half: the popped view moves from the live worklist into the
  recorded map, which is exactly @{thm [source] alr_ivl_run_invar_leaf}.\<close>
lemma hybrid_run_invar_discard_step:
  assumes inv: "alr_ivl_run_invar (map fst D) (views @ [(a, b)])" and ab: "a < b"
  shows "alr_ivl_run_invar (map fst (D @ [((a, b), dec)])) views"
  using alr_ivl_run_invar_leaf[OF inv] ab by simp

section \<open>The first full invariant step (the \<open>v = 0\<close> arm)\<close>

text \<open>\<^bold>\<open>@{const hybrid_abs_invar_g} is re-established by the discard arm.\<close> Stated over the
  \<open>\<alpha>\<close>-PROJECTIONS rather than the concrete columns, so the \<open>butlast\<close> plumbing
  (@{thm [source] hybrid_alpha_nodes_butlast} / @{thm [source] hybrid_alpha_views_butlast})
  is supplied by the caller and this lemma carries only the accounting content. The recorded
  decision is arbitrary — the discard branch equation holds for EVERY policy, which is why the
  \<open>\<exists>pol\<close> device costs nothing on this arm.\<close>
lemma hybrid_abs_invar_discard_step:
  assumes inv: "hybrid_abs_invar_g P l0 r0 k0 seed todo es ss acc"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 todo es ss
                 = hybrid_alpha_nodes l0 r0 k0 todo' es' ss' @ [(a, b, e, dk, s)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 todo
                 = hybrid_alpha_views l0 r0 k0 todo' @ [(a, b)]"
    and ab: "a < b"
    and zero: "descartes_list_int a b (coeffs P) = 0"
  shows "hybrid_abs_invar_g P l0 r0 k0 seed todo' es' ss' acc"
proof -
  from inv obtain D ns
    where sv: "hybrid_nodes_sigma_variant ns (hybrid_alpha_nodes l0 r0 k0 todo es ss)"
      and run: "alr_ivl_run_invar (map fst D) (hybrid_alpha_views l0 r0 k0 todo)"
      and acc: "hybrid_acc_invar P seed D
                  (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)) ns"
    by (auto simp: hybrid_abs_invar_g_def)
  obtain ns' sg where nsd: "ns = ns' @ [(a, b, e, dk, sg)]"
    and sv': "hybrid_nodes_sigma_variant ns' (hybrid_alpha_nodes l0 r0 k0 todo' es' ss')"
    by (rule hybrid_nodes_sigma_variant_snocE[OF sv[unfolded nsplit]])
  have run': "alr_ivl_run_invar (map fst (D @ [((a, b), (False, False))]))
                (hybrid_alpha_views l0 r0 k0 todo')"
    using hybrid_run_invar_discard_step[OF run[unfolded vsplit] ab] .
  have acc': "hybrid_acc_invar P seed (D @ [((a, b), (False, False))])
                (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)) ns'"
    using hybrid_acc_invar_discard_step[OF acc[unfolded nsd] zero] .
  show ?thesis
    unfolding hybrid_abs_invar_g_def using sv' run' acc' by blast
qed

text \<open>\<^bold>\<open>The \<open>v = 1\<close> accept arm's full step\<close>, same template: the popped view leaves the worklist
  and its interval is appended to acc, whose \<open>\<alpha>\<close>-projection therefore grows by exactly that
  pair (\<open>accgrow\<close>, supplied by the concrete push lemma
  @{thm [source] hybrid_acc_push_iv_correct}).\<close>
lemma hybrid_abs_invar_accept_step:
  assumes inv: "hybrid_abs_invar_g P l0 r0 k0 seed todo es ss acc"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 todo es ss
                 = hybrid_alpha_nodes l0 r0 k0 todo' es' ss' @ [(a, b, e, dk, s)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 todo
                 = hybrid_alpha_views l0 r0 k0 todo' @ [(a, b)]"
    and ab: "a < b"
    and one: "descartes_list_int a b (coeffs P) = 1"
    and accgrow: "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc')
                  = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc) @ [(a, b)]"
  shows "hybrid_abs_invar_g P l0 r0 k0 seed todo' es' ss' acc'"
proof -
  from inv obtain D ns
    where sv: "hybrid_nodes_sigma_variant ns (hybrid_alpha_nodes l0 r0 k0 todo es ss)"
      and run: "alr_ivl_run_invar (map fst D) (hybrid_alpha_views l0 r0 k0 todo)"
      and acc: "hybrid_acc_invar P seed D
                  (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)) ns"
    by (auto simp: hybrid_abs_invar_g_def)
  obtain ns' sg where nsd: "ns = ns' @ [(a, b, e, dk, sg)]"
    and sv': "hybrid_nodes_sigma_variant ns' (hybrid_alpha_nodes l0 r0 k0 todo' es' ss')"
    by (rule hybrid_nodes_sigma_variant_snocE[OF sv[unfolded nsplit]])
  have run': "alr_ivl_run_invar (map fst (D @ [((a, b), (False, False))]))
                (hybrid_alpha_views l0 r0 k0 todo')"
    using hybrid_run_invar_discard_step[OF run[unfolded vsplit] ab] .
  have acc': "hybrid_acc_invar P seed (D @ [((a, b), (False, False))])
                (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc')) ns'"
    using hybrid_acc_invar_accept_step[OF acc[unfolded nsd] one]
    by (simp add: accgrow)
  show ?thesis
    unfolding hybrid_abs_invar_g_def using sv' run' acc' by blast
qed

text \<open>\<^bold>\<open>The gate-CLOSED split arm's full step\<close>: the popped view moves into the recorded map and
  its two children join the worklist. Freshness is @{thm [source] alr_ivl_run_invar_split}, whose
  geometric side conditions (children strictly inside the parent, disjoint from each other) are
  @{thm [source] alr_ivl_split_children_geometry}'s — already proven in the base.\<close>
lemma hybrid_abs_invar_split_step:
  assumes inv: "hybrid_abs_invar_g P l0 r0 k0 seed todo es ss acc"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 todo es ss
                 = hybrid_alpha_nodes l0 r0 k0 todo'' es'' ss'' @ [(a, b, e, dk, s)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 todo
                 = hybrid_alpha_views l0 r0 k0 todo'' @ [(a, b)]"
    and npush: "hybrid_alpha_nodes l0 r0 k0 todo' es' ss'
                 = hybrid_alpha_nodes l0 r0 k0 todo'' es'' ss''
                   @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, t1),
                      ((a + b) / 2, b, max 1 (e - 1), dk + 1, t2)]"
    and vpush: "hybrid_alpha_views l0 r0 k0 todo'
                 = hybrid_alpha_views l0 r0 k0 todo'' @ [(a, (a + b) / 2), ((a + b) / 2, b)]"
    and accgrow: "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc')
                  = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)
                    @ (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                       then [((a + b) / 2, (a + b) / 2)] else [])"
    and ab: "a < b"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
  shows "hybrid_abs_invar_g P l0 r0 k0 seed todo' es' ss' acc'"
proof -
  from inv obtain D ns
    where sv: "hybrid_nodes_sigma_variant ns (hybrid_alpha_nodes l0 r0 k0 todo es ss)"
      and run: "alr_ivl_run_invar (map fst D) (hybrid_alpha_views l0 r0 k0 todo)"
      and acc: "hybrid_acc_invar P seed D
                  (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)) ns"
    by (auto simp: hybrid_abs_invar_g_def)
  obtain ns2 sg where nsd: "ns = ns2 @ [(a, b, e, dk, sg)]"
    and sv2: "hybrid_nodes_sigma_variant ns2 (hybrid_alpha_nodes l0 r0 k0 todo'' es'' ss'')"
    by (rule hybrid_nodes_sigma_variant_snocE[OF sv[unfolded nsplit]])
  have geo: "alr_ivl_pss (a, (a + b) / 2) (a, b)" "alr_ivl_pss ((a + b) / 2, b) (a, b)"
       "alr_ivl_disjoint (a, (a + b) / 2) ((a + b) / 2, b)"
       "fst (a, (a + b) / 2) < snd (a, (a + b) / 2)"
       "fst ((a + b) / 2, b) < snd ((a + b) / 2, b)"
    using alr_ivl_split_children_geometry[OF ab] by auto
  have abv: "fst (a, b) < snd (a, b)" using ab by simp
  have run': "alr_ivl_run_invar (map fst (D @ [((a, b), (False, False))]))
                (hybrid_alpha_views l0 r0 k0 todo')"
    unfolding vpush
    using alr_ivl_run_invar_split[OF run[unfolded vsplit] geo(1) geo(2) geo(3) abv geo(4) geo(5)]
    by simp
  \<comment> \<open>the ghost children carry the ABSTRACT run length at the GHOST \<open>\<sigma>\<close>; what the program
     pushed onto \<open>ss\<close> never enters the accounting at all.\<close>
  have accg: "hybrid_acc_invar P seed (D @ [((a, b), (False, False))])
                (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc'))
                (ns2 @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, split_run_len_int P a b sg),
                        ((a + b) / 2, b, max 1 (e - 1), dk + 1, split_run_len_int P a b sg)])"
    unfolding accgrow
    by (rule hybrid_acc_invar_split_step[OF acc[unfolded nsd] P0 p0 sf ab v2])
  have svg: "hybrid_nodes_sigma_variant
               (ns2 @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, split_run_len_int P a b sg),
                       ((a + b) / 2, b, max 1 (e - 1), dk + 1, split_run_len_int P a b sg)])
               (hybrid_alpha_nodes l0 r0 k0 todo' es' ss')"
    unfolding npush by (rule hybrid_nodes_sigma_variant_snoc2I[OF sv2])
  show ?thesis
    unfolding hybrid_abs_invar_g_def using svg run' accg by blast
qed

text \<open>\<^bold>\<open>The gate-OPEN window arm's full step\<close>, completing the four. One child is pushed, so
  freshness is @{thm [source] alr_ivl_run_invar_window}; its \<open>alr_ivl_pss\<close> side condition (the window
  child is strictly inside the parent) is the base's
  @{thm [source] try_window_bail_Some_width_lt} territory and is taken as \<open>wsub\<close> here, since
  the concrete arm establishes it from the probe's own output.\<close>
lemma hybrid_abs_invar_window_step:
  assumes inv: "hybrid_abs_invar_g P l0 r0 k0 seed todo es ss acc"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 todo es ss
                 = hybrid_alpha_nodes l0 r0 k0 todo'' es'' ss'' @ [(a, b, e, dk, s)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 todo
                 = hybrid_alpha_views l0 r0 k0 todo'' @ [(a, b)]"
    and npush: "hybrid_alpha_nodes l0 r0 k0 todo' es' ss'
                 = hybrid_alpha_nodes l0 r0 k0 todo'' es'' ss''
                   @ [(fst I, snd I, e + 1, dk + (2 ^ e + 2), sw)]"
    and vpush: "hybrid_alpha_views l0 r0 k0 todo'
                 = hybrid_alpha_views l0 r0 k0 todo'' @ [(fst I, snd I)]"
    and ab: "a < b"
    and wsub: "alr_ivl_pss (fst I, snd I) (a, b)" and wprop: "fst I < snd I"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and win: "try_window_bail_int (snd (dec :: bool \<times> bool)) a b (N_of e) P
                (descartes_list_int a b (coeffs P)) = Some I"
  shows "hybrid_abs_invar_g P l0 r0 k0 seed todo' es' ss' acc"
proof -
  from inv obtain D ns
    where sv: "hybrid_nodes_sigma_variant ns (hybrid_alpha_nodes l0 r0 k0 todo es ss)"
      and run: "alr_ivl_run_invar (map fst D) (hybrid_alpha_views l0 r0 k0 todo)"
      and acc: "hybrid_acc_invar P seed D
                  (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)) ns"
    by (auto simp: hybrid_abs_invar_g_def)
  obtain ns2 sg where nsd: "ns = ns2 @ [(a, b, e, dk, sg)]"
    and sv2: "hybrid_nodes_sigma_variant ns2 (hybrid_alpha_nodes l0 r0 k0 todo'' es'' ss'')"
    by (rule hybrid_nodes_sigma_variant_snocE[OF sv[unfolded nsplit]])
  have abv: "fst (a, b) < snd (a, b)" using ab by simp
  have wv: "fst (fst I, snd I) < snd (fst I, snd I)" using wprop by simp
  have run': "alr_ivl_run_invar (map fst (D @ [((a, b), dec)]))
                (hybrid_alpha_views l0 r0 k0 todo')"
    unfolding vpush
    using alr_ivl_run_invar_window[OF run[unfolded vsplit] wsub abv wv] by simp
  have accg: "hybrid_acc_invar P seed (D @ [((a, b), dec)])
                (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc))
                (ns2 @ [(fst I, snd I, e + 1, dk + (2 ^ e + 2), sg)])"
    by (rule hybrid_acc_invar_window_step[OF acc[unfolded nsd] P0 p0 sf ab v2 win])
  have svg: "hybrid_nodes_sigma_variant (ns2 @ [(fst I, snd I, e + 1, dk + (2 ^ e + 2), sg)])
               (hybrid_alpha_nodes l0 r0 k0 todo' es' ss')"
    unfolding npush by (rule hybrid_nodes_sigma_variant_snocI[OF sv2])
  show ?thesis
    unfolding hybrid_abs_invar_g_def using svg run' accg by blast
qed

text \<open>\<^bold>\<open>The COMPLETE \<open>v = 0\<close> invariant step\<close>: abstract accounting (\<open>\<exists>D\<close> + freshness) and BOTH
  couplings, re-established together across one discard pop. This is the first arm proven at the
  full @{const hybrid_refine_invar} level — the shape the remaining three arms and then the
  WHILEIT assembly consume.\<close>
lemma hybrid_refine_invar_discard_step:
  assumes inv: "hybrid_refine_invar P l0 r0 k0 seed (lns, rns, ks) qtodo es ss cs gs rp acc"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, b, e, dk, s)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and ab: "a < b"
    and zero: "descartes_list_int a b (coeffs P) = 0"
  shows "hybrid_refine_invar P l0 r0 k0 seed
           (butlast lns, butlast rns, butlast ks) (butlast qtodo)
           (butlast es) (butlast ss) (butlast cs) (butlast gs) rp acc"
proof -
  have absI: "hybrid_abs_invar_g P l0 r0 k0 seed (lns, rns, ks) es ss acc"
    using inv unfolding hybrid_refine_invar_def by simp
  have abs': "hybrid_abs_invar_g P l0 r0 k0 seed
                (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss) acc"
    by (rule hybrid_abs_invar_discard_step[OF absI nsplit vsplit ab zero])
  show ?thesis
    unfolding hybrid_refine_invar_def
    using abs' hybrid_refine_invar_pop_couplings[OF inv] by simp
qed

text \<open>\<^bold>\<open>The COMPLETE \<open>v = 1\<close> invariant step\<close>: same pop, but the accepted interval joins acc.
  The couplings are indifferent to acc (they constrain the WORKLIST), so the coupling half is
  the identical pop.\<close>
lemma hybrid_refine_invar_accept_step:
  assumes inv: "hybrid_refine_invar P l0 r0 k0 seed (lns, rns, ks) qtodo es ss cs gs rp acc"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, b, e, dk, s)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and ab: "a < b"
    and one: "descartes_list_int a b (coeffs P) = 1"
    and accgrow: "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc')
                  = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc) @ [(a, b)]"
  shows "hybrid_refine_invar P l0 r0 k0 seed
           (butlast lns, butlast rns, butlast ks) (butlast qtodo)
           (butlast es) (butlast ss) (butlast cs) (butlast gs) rp acc'"
proof -
  have absI: "hybrid_abs_invar_g P l0 r0 k0 seed (lns, rns, ks) es ss acc"
    using inv unfolding hybrid_refine_invar_def by simp
  have abs': "hybrid_abs_invar_g P l0 r0 k0 seed
                (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss) acc'"
    by (rule hybrid_abs_invar_accept_step[OF absI nsplit vsplit ab one accgrow])
  show ?thesis
    unfolding hybrid_refine_invar_def
    using abs' hybrid_refine_invar_pop_couplings[OF inv] by simp
qed

text \<open>\<^bold>\<open>The COMPLETE split / window invariant steps\<close>: these PUSH, so the coupling half needs
  @{thm [source] hybrid_trunc_coupling_push} / @{thm [source] hybrid_cs_coupling_push} on top
  of the pop — i.e. the caller must supply each pushed child's frame, guard cap, lock condition
  and cache class. Those are exactly what @{thm [source] hybrid_classify_prebuilt_correct}
  returns, so the concrete arm feeds them straight in.\<close>
lemma hybrid_refine_invar_push_couplings:
  assumes inv: "hybrid_refine_invar P l0 r0 k0 seed (lns, rns, ks) qtodo es ss cs gs rp acc"
    and f1: "node_frame (carried_init_same_den l1 (2 ^ k1) r1 rp) q1 g1"
    and f2: "node_frame (carried_init_same_den l2 (2 ^ k2) r2 rp) q2 g2"
    and g1le: "g1 \<le> (k1 + 1) * length rp \<or> 4398046511104 \<le> g1"
    and g2le: "g2 \<le> (k2 + 1) * length rp \<or> 4398046511104 \<le> g2"
    and lk1: "4398046511104 \<le> g1 \<longrightarrow> q1 = carried_init_same_den l1 (2 ^ k1) r1 rp"
    and lk2: "4398046511104 \<le> g2 \<longrightarrow> q2 = carried_init_same_den l2 (2 ^ k2) r2 rp"
    and ok1: "hybrid_cs_ok g1 c1
                (carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp))"
    and ok2: "hybrid_cs_ok g2 c2
                (carried_descartes_count (carried_init_same_den l2 (2 ^ k2) r2 rp))"
  shows "hybrid_trunc_coupling
           (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
           (butlast qtodo @ [q1, q2]) (butlast gs @ [g1, g2]) rp \<and>
         hybrid_cs_coupling
           (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
           (butlast qtodo @ [q1, q2]) (butlast cs @ [c1, c2]) (butlast gs @ [g1, g2]) rp"
proof -
  have tcp: "hybrid_trunc_coupling (butlast lns, butlast rns, butlast ks)
               (butlast qtodo) (butlast gs) rp"
    and ccp: "hybrid_cs_coupling (butlast lns, butlast rns, butlast ks)
               (butlast qtodo) (butlast cs) (butlast gs) rp"
    using hybrid_refine_invar_pop_couplings[OF inv] by simp_all
  have L: "length (butlast lns) = length (butlast qtodo)"
     "length (butlast rns) = length (butlast qtodo)"
     "length (butlast ks) = length (butlast qtodo)"
     "length (butlast gs) = length (butlast qtodo)"
    using tcp unfolding hybrid_trunc_coupling_def by simp_all
  show ?thesis
    using hybrid_trunc_coupling_push[OF tcp f1 f2 g1le g2le lk1 lk2]
          hybrid_cs_coupling_push[OF ccp L(4) L(1) L(2) L(3) ok1 ok2]
    by simp
qed

text \<open>\<^bold>\<open>The COMPLETE split-arm invariant step\<close>: abstract accounting plus BOTH couplings across a
  pop-then-push-pair. Every premise here is produced by the concrete arm —
  @{thm [source] hybrid_split_pair_state_correct} returns the pushed columns and the two
  children's frames/guards/classes, and @{thm [source] hybrid_alpha_nodes_append2} /
  @{thm [source] hybrid_alpha_views_append2} turn those columns into the \<open>\<alpha>\<close>-projections the
  abstract step consumes.\<close>
lemma hybrid_refine_invar_split_step:
  assumes inv: "hybrid_refine_invar P l0 r0 k0 seed (lns, rns, ks) qtodo es ss cs gs rp acc"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, b, e, dk, s)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and npush: "hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
                   (butlast es @ [e1, e2]) (butlast ss @ [s1, s2])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, t1),
                      ((a + b) / 2, b, max 1 (e - 1), dk + 1, t2)]"
    and vpush: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, (a + b) / 2), ((a + b) / 2, b)]"
    and accgrow: "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc')
                  = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)
                    @ (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                       then [((a + b) / 2, (a + b) / 2)] else [])"
    and ab: "a < b"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and f1: "node_frame (carried_init_same_den l1 (2 ^ k1) r1 rp) q1 g1"
    and f2: "node_frame (carried_init_same_den l2 (2 ^ k2) r2 rp) q2 g2"
    and g1le: "g1 \<le> (k1 + 1) * length rp \<or> 4398046511104 \<le> g1"
    and g2le: "g2 \<le> (k2 + 1) * length rp \<or> 4398046511104 \<le> g2"
    and lk1: "4398046511104 \<le> g1 \<longrightarrow> q1 = carried_init_same_den l1 (2 ^ k1) r1 rp"
    and lk2: "4398046511104 \<le> g2 \<longrightarrow> q2 = carried_init_same_den l2 (2 ^ k2) r2 rp"
    and ok1: "hybrid_cs_ok g1 c1
                (carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp))"
    and ok2: "hybrid_cs_ok g2 c2
                (carried_descartes_count (carried_init_same_den l2 (2 ^ k2) r2 rp))"
  shows "hybrid_refine_invar P l0 r0 k0 seed
           (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
           (butlast qtodo @ [q1, q2]) (butlast es @ [e1, e2]) (butlast ss @ [s1, s2])
           (butlast cs @ [c1, c2]) (butlast gs @ [g1, g2]) rp acc'"
proof -
  have absI: "hybrid_abs_invar_g P l0 r0 k0 seed (lns, rns, ks) es ss acc"
    using inv unfolding hybrid_refine_invar_def by simp
  have abs': "hybrid_abs_invar_g P l0 r0 k0 seed
                (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
                (butlast es @ [e1, e2]) (butlast ss @ [s1, s2]) acc'"
    \<comment> \<open>\<open>rule\<close> + explicit \<open>show\<close>s, not \<open>OF\<close>: \<open>polrel\<close> is higher-order and \<open>OF\<close> gives
       \<open>multiple unifiers\<close>.\<close>
  proof (rule hybrid_abs_invar_split_step)
    show "hybrid_abs_invar_g P l0 r0 k0 seed (lns, rns, ks) es ss acc" by (rule absI)
    show "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
          = hybrid_alpha_nodes l0 r0 k0
              (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
            @ [(a, b, e, dk, s)]" by (rule nsplit)
    show "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
          = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks) @ [(a, b)]"
      by (rule vsplit)
    show "hybrid_alpha_nodes l0 r0 k0
            (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
            (butlast es @ [e1, e2]) (butlast ss @ [s1, s2])
          = hybrid_alpha_nodes l0 r0 k0
              (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
            @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, t1),
               ((a + b) / 2, b, max 1 (e - 1), dk + 1, t2)]"
      by (rule npush)
    show "hybrid_alpha_views l0 r0 k0
            (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
          = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
            @ [(a, (a + b) / 2), ((a + b) / 2, b)]" by (rule vpush)
    show "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc')
          = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)
            @ (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
               then [((a + b) / 2, (a + b) / 2)] else [])" by (rule accgrow)
    show "a < b" by (rule ab)
    show "P \<noteq> 0" by (rule P0)
    show "degree P \<noteq> 0" by (rule p0)
    show "square_free (map_poly of_int P :: real poly)" by (rule sf)
    show "2 \<le> descartes_list_int a b (coeffs P)" by (rule v2)
  qed
  show ?thesis
    unfolding hybrid_refine_invar_def
    using abs' hybrid_refine_invar_push_couplings[OF inv f1 f2 g1le g2le lk1 lk2 ok1 ok2]
    by simp
qed

text \<open>\<^bold>\<open>Single-child push\<close>: the gate-OPEN window arm pushes ONE node (the accepted window
  child), not a pair, so it needs these one-sided counterparts of the \<open>_push\<close> lemmas.\<close>
lemma hybrid_trunc_coupling_push1:
  assumes c: "hybrid_trunc_coupling (lns, rns, ks) qtodo gs rp"
    and f1: "node_frame (carried_init_same_den l1 (2 ^ k1) r1 rp) q1 g1"
    and g1le: "g1 \<le> (k1 + 1) * length rp \<or> 4398046511104 \<le> g1"
    and lk1: "4398046511104 \<le> g1 \<longrightarrow> q1 = carried_init_same_den l1 (2 ^ k1) r1 rp"
  shows "hybrid_trunc_coupling (lns @ [l1], rns @ [r1], ks @ [k1])
           (qtodo @ [q1]) (gs @ [g1]) rp"
proof -
  have L: "length lns = length qtodo" "length rns = length qtodo"
     and K: "length ks = length qtodo" "length gs = length qtodo"
    using c unfolding hybrid_trunc_coupling_def by simp_all
  have body: "\<And>i. i < length qtodo \<Longrightarrow>
      node_frame (carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp)
                 (qtodo ! i) (gs ! i) \<and>
      (gs ! i \<le> (ks ! i + 1) * length rp \<or> 4398046511104 \<le> gs ! i) \<and>
      (4398046511104 \<le> gs ! i \<longrightarrow>
         qtodo ! i = carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp)"
    using c unfolding hybrid_trunc_coupling_def by simp
  show ?thesis
    unfolding hybrid_trunc_coupling_def
    using L K body f1 g1le lk1 by (auto simp: nth_append less_Suc_eq)
qed

lemma hybrid_cs_coupling_push1:
  assumes c: "hybrid_cs_coupling (lns, rns, ks) qtodo cs gs rp"
    and lg: "length gs = length qtodo"
    and ll: "length lns = length qtodo" and lr': "length rns = length qtodo"
    and lk: "length ks = length qtodo"
    and ok1: "hybrid_cs_ok g1 c1
                (carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp))"
  shows "hybrid_cs_coupling (lns @ [l1], rns @ [r1], ks @ [k1])
           (qtodo @ [q1]) (cs @ [c1]) (gs @ [g1]) rp"
  using c lg ll lr' lk ok1 unfolding hybrid_cs_coupling_def
  by (auto simp: nth_append less_Suc_eq)

text \<open>\<^bold>\<open>The COMPLETE gate-OPEN window invariant step\<close> — the fourth and last arm at full
  @{const hybrid_refine_invar} level.\<close>
lemma hybrid_refine_invar_window_step:
  assumes inv: "hybrid_refine_invar P l0 r0 k0 seed (lns, rns, ks) qtodo es ss cs gs rp acc"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, b, e, dk, s)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and npush: "hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [k1])
                   (butlast es @ [e1]) (butlast ss @ [s1])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(fst I, snd I, e + 1, dk + (2 ^ e + 2), sw)]"
    and vpush: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [k1])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(fst I, snd I)]"
    and ab: "a < b"
    and wsub: "alr_ivl_pss (fst I, snd I) (a, b)" and wprop: "fst I < snd I"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and win: "try_window_bail_int (snd (dec :: bool \<times> bool)) a b (N_of e) P
                (descartes_list_int a b (coeffs P)) = Some I"
    and f1: "node_frame (carried_init_same_den l1 (2 ^ k1) r1 rp) q1 g1"
    and g1le: "g1 \<le> (k1 + 1) * length rp \<or> 4398046511104 \<le> g1"
    and lk1: "4398046511104 \<le> g1 \<longrightarrow> q1 = carried_init_same_den l1 (2 ^ k1) r1 rp"
    and ok1: "hybrid_cs_ok g1 c1
                (carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp))"
  shows "hybrid_refine_invar P l0 r0 k0 seed
           (butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [k1])
           (butlast qtodo @ [q1]) (butlast es @ [e1]) (butlast ss @ [s1])
           (butlast cs @ [c1]) (butlast gs @ [g1]) rp acc"
proof -
  have absI: "hybrid_abs_invar_g P l0 r0 k0 seed (lns, rns, ks) es ss acc"
    using inv unfolding hybrid_refine_invar_def by simp
  have abs': "hybrid_abs_invar_g P l0 r0 k0 seed
                (butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [k1])
                (butlast es @ [e1]) (butlast ss @ [s1]) acc"
  proof (rule hybrid_abs_invar_window_step[where dec = dec])
    show "hybrid_abs_invar_g P l0 r0 k0 seed (lns, rns, ks) es ss acc" by (rule absI)
    show "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
          = hybrid_alpha_nodes l0 r0 k0
              (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
            @ [(a, b, e, dk, s)]" by (rule nsplit)
    show "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
          = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks) @ [(a, b)]"
      by (rule vsplit)
    show "hybrid_alpha_nodes l0 r0 k0
            (butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [k1])
            (butlast es @ [e1]) (butlast ss @ [s1])
          = hybrid_alpha_nodes l0 r0 k0
              (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
            @ [(fst I, snd I, e + 1, dk + (2 ^ e + 2), sw)]" by (rule npush)
    show "hybrid_alpha_views l0 r0 k0
            (butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [k1])
          = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
            @ [(fst I, snd I)]" by (rule vpush)
    show "a < b" by (rule ab)
    show "alr_ivl_pss (fst I, snd I) (a, b)" by (rule wsub)
    show "fst I < snd I" by (rule wprop)
    show "P \<noteq> 0" by (rule P0)
    show "degree P \<noteq> 0" by (rule p0)
    show "square_free (map_poly of_int P :: real poly)" by (rule sf)
    show "2 \<le> descartes_list_int a b (coeffs P)" by (rule v2)
    show "try_window_bail_int (snd (dec :: bool \<times> bool)) a b (N_of e) P
            (descartes_list_int a b (coeffs P)) = Some I" by (rule win)
  qed
  have tcp: "hybrid_trunc_coupling (butlast lns, butlast rns, butlast ks)
               (butlast qtodo) (butlast gs) rp"
    and ccp: "hybrid_cs_coupling (butlast lns, butlast rns, butlast ks)
               (butlast qtodo) (butlast cs) (butlast gs) rp"
    using hybrid_refine_invar_pop_couplings[OF inv] by simp_all
  have L: "length (butlast lns) = length (butlast qtodo)"
     "length (butlast rns) = length (butlast qtodo)"
     "length (butlast ks) = length (butlast qtodo)"
     "length (butlast gs) = length (butlast qtodo)"
    using tcp unfolding hybrid_trunc_coupling_def by simp_all
  show ?thesis
    unfolding hybrid_refine_invar_def
    using abs' hybrid_trunc_coupling_push1[OF tcp f1 g1le lk1]
          hybrid_cs_coupling_push1[OF ccp L(4) L(1) L(2) L(3) ok1]
    by simp
qed

section \<open>The concrete pop\<close>

text \<open>\<^bold>\<open>The loop step's pop prefix collapses to a literal.\<close> Six \<open>pop_last\<close> ops in a row, each
  with a proven \<open>_eq\<close> in the Truncate keystone (@{thm [source] cdlr_todo_pop_eq},
  @{thm [source] cdlr_poly_vec_pop_eq}, @{thm [source] cdlr_exp_pop_eq}), so the whole prefix
  reduces to \<open>last\<close>/\<open>butlast\<close> on every column — which is EXACTLY the shape the four
  \<open>hybrid_refine_invar_*_step\<close> lemmas take. This is the bridge from the concrete loop body to
  the abstract steps.\<close>
lemma hybrid_loop_step_args_pop:
  assumes tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lne: "lns \<noteq> []" and lr: "length rns = length lns" and lk: "length ks = length lns"
    and qne: "qtodo \<noteq> []" and ene: "es \<noteq> []" and sne: "ss \<noteq> []"
    and cne: "cs \<noteq> []" and gne: "gs \<noteq> []"
  shows "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs acc rp
       \<le> doN {
            ASSERT (0 < length (last qtodo));
            ASSERT (length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len));
            ASSERT (length (last qtodo) + 2 < max_snat LENGTH(gmp_poly_len));
            ASSERT (1 * (length (last qtodo) - 1) < max_snat LENGTH(gmp_poly_len));
            ASSERT (last ks + 1 < max_snat LENGTH(gmp_poly_len));
            ASSERT (last ss + 1 < max_snat LENGTH(gmp_poly_len));
            ASSERT (0 < length rp);
            ASSERT (length rp + 1 < max_snat LENGTH(gmp_poly_len));
            ASSERT (last ks * (length rp - 1) < max_snat LENGTH(gmp_poly_len));
            ASSERT (dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks));
            ASSERT (dyadic_interval_vec_pushable acc);
            ASSERT (length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len));
            ASSERT (length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len));
            ASSERT (length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len));
            ASSERT (length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len));
            ASSERT (length (butlast gs) + 2 < max_snat LENGTH(gmp_poly_len));
            hybrid_after_pop_monadic
              (butlast lns, butlast rns, butlast ks) (butlast qtodo)
              (butlast es) (butlast ss) (butlast cs) (butlast gs) acc rp
              (last lns) (last rns) (last ks) (last es) (last ss) (last cs) (last gs)
              (last qtodo)
          }"
  unfolding hybrid_loop_step_args_monadic_def PR_CONST_def
  using tinv lne qne ene sne cne gne
  by (simp add: cdlr_todo_pop_eq[OF lne lr lk] cdlr_poly_vec_pop_eq[OF qne]
                cdlr_exp_pop_eq[OF ene] cdlr_exp_pop_eq[OF sne]
                cdlr_exp_pop_eq[OF cne] cdlr_exp_pop_eq[OF gne])

section \<open>Building block: the loop exit condition\<close>

text \<open>\<^bold>\<open>Negated loop condition \<Rightarrow> empty worklist\<close>, in the exact form
  @{thm [source] hybrid_refine_invar_exit} needs. @{const hybrid_loop_cond} tests only the
  \<open>lns\<close> column; @{const dyadic_interval_vec_triples} is \<open>zip (zip lns rns) ks\<close>, so an empty
  \<open>lns\<close> already forces the triple list empty regardless of the other columns — no length
  side-conditions needed.\<close>
lemma hybrid_loop_cond_exit_triples:
  assumes "\<not> hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
  shows "dyadic_interval_vec_triples (lns, rns, ks) = []"
  using assms
  unfolding hybrid_loop_cond_def dyadic_interval_vec_triples_def Let_def by simp

text \<open>\<^bold>\<open>Hence the keystone conclusion at loop exit\<close>: combining the exit condition with the
  invariant gives the \<open>\<exists>pol\<close> multiset equality directly.\<close>
lemma hybrid_refine_invar_exit_cond:
  assumes inv: "hybrid_refine_invar P l0 r0 k0 (a, b, e0, dk0, 0)
                  (lns, rns, ks) qtodo es ss cs gs rp acc"
    and nc: "\<not> hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
  shows "\<exists>pol. mset (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc))
              = mset (newdsc_pol_bail_int pol a b e0 dk0 P)"
  by (rule hybrid_refine_invar_exit[OF inv hybrid_loop_cond_exit_triples[OF nc]])

lemma dyadic_interval_vec_triples_single[simp]:
  "dyadic_interval_vec_triples ([l], [r], [k]) = [((l, r), k)]"
  by (simp add: dyadic_interval_vec_triples_def)

text \<open>\<^bold>\<open>The seed, with no residual side condition\<close> — the shape
  @{const hybrid_main_list_monadic} actually builds: one root node \<open>(l_num, r_num, k)\<close>
  carrying the exact \<open>P\<close> at guard \<open>0\<close>, empty acc. Pairs with
  @{thm [source] hybrid_refine_invar_exit_cond} to bracket the WHILEIT.\<close>
lemma hybrid_refine_invar_seed:
  assumes lr: "l_num < r_num"
    and P_eq: "P = carried_init_same_den l_num (2 ^ k) r_num rp"
    and cs_seed: "hybrid_cs_ok 0 c0 (carried_descartes_count P)"
    and acc_empty: "dyadic_interval_vec_triples acc = []"
  shows "hybrid_refine_invar (Poly P') l_num r_num k (0, 1, e0, k, 0)
           ([l_num], [r_num], [k]) [P] [e0] [0] [c0] [0] rp acc"
  by (rule hybrid_refine_invar_init[OF lr P_eq cs_seed acc_empty
             dyadic_interval_vec_triples_single])

section \<open>The \<open>\<mu>\<close>-measure\<close>

text \<open>\<^bold>\<open>Termination measure.\<close> Bail's \<open>\<mu>\<close> ports unchanged: there are no new node types, and the
  pop-time resolve happens inside one pop, so it adds no steps.

  \<^bold>\<open>The numeric sum below is not the termination measure.\<close> It decreases
  on the pop-only arms (\<open>v = 0\<close>/\<open>v = 1\<close>), as proven below, but not on a two-child push: replacing a node of
  measure \<open>m\<close> by two children of measure \<open>m - 1\<close> gives \<open>Suc (m-1) + Suc (m-1) = 2m\<close> against \<open>Suc m\<close>, which is
  larger. No constant weighting fixes this (an exponential \<open>2\<^sup>m\<close> weighting merely ties).

  \<^bold>\<open>The measure is bail's multiset order\<close> (\<open>Bail_Loop_Refine\<close>, the count-frame \<open>\<mu>\<close>-measure, in particular
  \<open>dyadic_iv_todo_mu_mset_one_smaller_bl\<close>): the worklist is compared as a multiset of per-node
  measures under the multiset order, where replacing one element by finitely many strictly
  smaller elements is a decrease by construction, exactly the split/window shape. \<open>hybrid_mu\<close> is kept because
  the pop-only arms use it and its append lemma is reusable.\<close>
definition hybrid_mu :: "real \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> nat" where
  "hybrid_mu \<delta> ns = (\<Sum>nd \<leftarrow> ns. Suc (dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd))))"

lemma hybrid_mu_Nil[simp]: "hybrid_mu \<delta> [] = 0"
  by (simp add: hybrid_mu_def)

lemma hybrid_mu_append[simp]:
  "hybrid_mu \<delta> (xs @ ys) = hybrid_mu \<delta> xs + hybrid_mu \<delta> ys"
  by (simp add: hybrid_mu_def)

text \<open>\<^bold>\<open>The discard / accept arms strictly decrease \<open>\<mu>\<close>\<close>: they pop one node and push none, and
  every node contributes at least \<open>1\<close> (the \<open>Suc\<close> in the summand is exactly what makes this hold
  without any geometry).\<close>
lemma hybrid_mu_pop_less:
  "hybrid_mu \<delta> ns < hybrid_mu \<delta> (ns @ [nd])"
  by (simp add: hybrid_mu_def)

section \<open>The count bridge (concrete \<open>cnt\<close> \<leftrightarrow> abstract \<open>descartes_list_int\<close>)\<close>

text \<open>\<^bold>\<open>The link the four arms branch on.\<close> The abstract steps are keyed on
  \<open>descartes_list_int a b (coeffs P)\<close> being \<open>0\<close> / \<open>1\<close> / \<open>\<ge> 2\<close>, but the impl dispatches on the
  EXACT count of the node's own carried polynomial. @{thm [source] carried_repr_scalar_count}
  identifies the two whenever the node's poly scalar-represents its count-frame interval — which
  is precisely the per-node invariant bail carries. Restated here in the hybrid naming so the
  arms can consume it directly, and specialised to the three dispatch tests.\<close>
lemma hybrid_count_bridge:
  assumes repr: "carried_repr_scalar P a b Q" and lenP: "0 < length P" and ab: "a \<noteq> b"
  shows "carried_descartes_count Q = descartes_list_int a b P"
  using carried_repr_scalar_count[OF repr lenP ab]
  by (simp add: carried_descartes_count_def)

lemma hybrid_count_bridge_dispatch:
  assumes repr: "carried_repr_scalar P a b Q" and lenP: "0 < length P" and ab: "a \<noteq> b"
  shows "(carried_descartes_count Q = 0) = (descartes_list_int a b P = 0)"
    and "(carried_descartes_count Q = 1) = (descartes_list_int a b P = 1)"
    and "(2 \<le> carried_descartes_count Q) = (2 \<le> descartes_list_int a b P)"
  using hybrid_count_bridge[OF repr lenP ab] by simp_all

section \<open>The children-and-decide prefix, parametric in the continuation\<close>

text \<open>\<^bold>\<open>Why the prefix is parametric in its continuation.\<close> A fused lemma with a trailing \<open>RETURN\<close>
  cannot compose with @{const hybrid_branch_split_monadic}, whose continuation is
  \<open>if code = 2 \<dots>\<close>. Parameterising over the continuation \<open>f\<close> removes the
  mismatch: the caller instantiates \<open>f\<close> with whatever it actually does, and gets the
  children's frames and the midpoint fact as ordinary hypotheses.\<close>
lemma truncate_children_mid_decide_bind:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    and cont: "\<And>ql gl qr gr code.
        \<lbrakk> node_frame (carried_left X) ql gl; node_frame (carried_right X) qr gr;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          4398046511104 \<le> gr \<longrightarrow> qr = carried_right X;
          code = 1 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          code = 0 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0;
          g = 0 \<or> 4398046511104 \<le> g \<longrightarrow> code \<noteq> 2;
          code = 0 \<or> code = 1 \<or> code = 2 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr code \<le> SPEC \<Phi>"
  shows "doN { (ql, gl, qr, gr, mids, midbl) \<leftarrow> truncate_children_mid_monadic g Q;
               code \<leftarrow> truncate_mid_decide_monadic g len mids midbl;
               f ql gl qr gr code }
       \<le> SPEC \<Phi>"
  apply (refine_vcg
      truncate_children_mid_agrees[OF frame lock g_tri Qne Qbound Q_small,
        THEN order_trans])
  apply clarsimp
  apply (refine_vcg
      truncate_mid_decide_agrees[OF frame lock len_eq Qne Q_small, THEN order_trans])
  apply (all \<open>(simp; fail)?\<close>)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

text \<open>\<^bold>\<open>The decomposed-form twin\<close> of the prefix lemma: the shape \<open>refine_vcg\<close> actually produces
  when the prefix sits under an outer bind (it has already split \<open>m \<bind> rest \<le> SPEC \<Phi>\<close> into
  \<open>m \<le> SPEC (\<lambda>x. rest x \<le> SPEC \<Phi>)\<close>). Same content, different decomposition; both twins are supplied
  to \<open>refine_vcg\<close> so whichever shape it produces has a match.

  It is proved by the same script as the bind form rather than by a shape conversion: the goal is exactly what
  \<open>refine_vcg\<close>'s first step produces from the bind form. A conversion is obstructed by the higher-order \<open>f\<close> under a
  \<open>case_prod\<close> lambda: \<open>simp add: bind_rule_complete\<close> and \<open>auto simp: pw_le_iff refine_pw_simps\<close> diverge, and
  \<open>rule bind_rule_complete[THEN iffD1]\<close> does not unify because the goal's \<open>case_prod\<close> binder does not match the
  rule's plain \<open>\<lambda>x\<close>.\<close>
lemma truncate_children_mid_decide_bind_decomp:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    and cont: "\<And>ql gl qr gr code.
        \<lbrakk> node_frame (carried_left X) ql gl; node_frame (carried_right X) qr gr;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          4398046511104 \<le> gr \<longrightarrow> qr = carried_right X;
          code = 1 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          code = 0 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0;
          g = 0 \<or> 4398046511104 \<le> g \<longrightarrow> code \<noteq> 2;
          code = 0 \<or> code = 1 \<or> code = 2 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr code \<le> SPEC \<Phi>"
  shows "truncate_children_mid_monadic g Q
       \<le> SPEC (\<lambda>(ql, gl, qr, gr, mids, midbl).
             truncate_mid_decide_monadic g len mids midbl \<bind> (\<lambda>code. f ql gl qr gr code)
           \<le> SPEC \<Phi>)"
  apply (refine_vcg
      truncate_children_mid_agrees[OF frame lock g_tri Qne Qbound Q_small,
        THEN order_trans])
  apply clarsimp
  apply (refine_vcg
      truncate_mid_decide_agrees[OF frame lock len_eq Qne Q_small, THEN order_trans])
  apply (all \<open>(simp; fail)?\<close>)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

text \<open>\<^bold>\<open>The split arm's STATE RESULT on an exact/LOCKed node\<close> — now reachable, via the
  continuation-parametric prefix. \<open>code \<noteq> 2\<close> kills the rebuild arm, and the two survivors are
  both @{const hybrid_split_pair_state_monadic} calls differing only in the \<open>mid\<close> flag and
  whether the mid-root leaf is pushed onto acc — which is exactly the dichotomy the abstract
  split step consumes.\<close>
lemma hybrid_branch_split_exact_acc:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and gex: "g = 0 \<or> 4398046511104 \<le> g"
    and g_le: "g \<le> 4398046511104"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (\<lambda>(wl, acc').
           (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
              acc' = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1])) \<and>
           (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
              acc' = (al, ar, ak)))"
proof -
  have g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g" using gex by auto
  have lenXrp: "length X = length rp"
    by (simp add: recompute truncate_length_carried_init_same_den)
  have lenL: "length (carried_left X) = length rp"
    and lenR: "length (carried_right X) = length rp" using lenXrp by simp_all
  have lbLX: "length (carried_left X) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lbRX: "length (carried_right X) + 1 < max_snat LENGTH(gmp_poly_len)"
    using rpb lenL lenR by simp_all
  have pbLX: "length (carried_left X) * nat_bitlen (length (carried_left X))
                < max_snat LENGTH(gmp_poly_len)"
    and pbRX: "length (carried_right X) * nat_bitlen (length (carried_right X))
                < max_snat LENGTH(gmp_poly_len)"
    using rp_pb lenL lenR by simp_all
  have gcXL: "4398046511104 + length (carried_left X) < max_snat LENGTH(gmp_poly_len)"
    and gcXR: "4398046511104 + length (carried_right X) < max_snat LENGTH(gmp_poly_len)"
    using rp_small lenL lenR unfolding max_snat_def by simp_all
  have pm: "carried_push_mid_monadic (al, ar, ak) l_num r_num k
      \<le> SPEC (\<lambda>a. a = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1]))"
    by (simp add: cdlr_push_mid_eq[OF accpush])
  have Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    using Q_small unfolding max_snat_def by simp
  have dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)" using Qbound by simp
  have kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    using g_le Q_small unfolding max_snat_def by simp
  show ?thesis
    unfolding hybrid_branch_split_monadic_def poly_length_monadic_def PR_CONST_def
      poly_free_monadic_def
    using gex Qne Qbound Qbound2 dep kcap rpne rpb krp accpush qcap gcap ecap sscap ccap push scap1
    apply (refine_vcg
        hybrid_split_children_classic_gbind[
          OF frame lock gex g_tri Qne Qbound Qbound2 dep Q_small kb rpne rpb krp]
        hybrid_split_children_classic_gbind_decomp[
          OF frame lock gex g_tri Qne Qbound Qbound2 dep Q_small kb rpne rpb krp]
        hybrid_split_pair_state_correct[where XL = "carried_left X" and XR = "carried_right X",
          OF _ _ _ _ lbLX lbRX pbLX pbRX _ _, THEN order_trans]
        hybrid_split_pair_state_left_correct[where XL = "carried_left X",
          OF _ _ lbLX pbLX _, THEN order_trans]
        pm[THEN order_trans])
    \<comment> \<open>the \<open>code = 2\<close> rebuild arm is unreachable here: \<open>cont\<close> hands over
       \<open>g = 0 \<or> 2\<^sup>4\<^sup>2 \<le> g \<longrightarrow> code \<noteq> 2\<close>, and \<open>gex\<close> discharges the antecedent. The
       surviving two arms differ only in the midpoint push, which \<open>pm\<close> evaluates; the code
       trichotomy then pins the \<open>else\<close> arm to \<open>code = 0\<close>, giving \<open>poly \<dots> \<noteq> 0\<close>.\<close>
    apply (all \<open>((rule node_frame_exact_any_g | assumption | simp); fail)?\<close>)
    \<comment> \<open>\<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close> collapses to \<open>\<le> 2\<^sup>4\<^sup>2\<close> under \<open>gex\<close> + \<open>g_le\<close>.\<close>
    apply (all \<open>((insert gex g_le gcXL gcXR, auto simp: max_def); fail)?\<close>)
    done
qed

text \<open>\<^bold>\<open>The ambiguous rebuild arm\<close> (\<open>code = 2\<close>), completing the split arm for a
  general guard. The arm frees the truncated children, rebuilds the node exactly from the retained
  root via @{thm [source] carried_init_inplace_monadic_correct}, which returns literally
  \<open>carried_init_same_den l_num (2\<^sup>k) r_num rp\<close>, i.e. \<open>X\<close>, and then re-runs children and decide at
  guard \<open>0\<close>. That second prefix is the same continuation-parametric lemma instantiated at
  \<open>g = 0\<close>, where \<open>code \<noteq> 2\<close> makes a second ambiguity impossible; so the rebuild arm
  reduces to the exact case already proven.\<close>
lemma carried_init_inplace_gives_X:
  assumes recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "carried_init_inplace_monadic l_num k r_num rp \<le> SPEC (\<lambda>qx. qx = X)"
  using carried_init_inplace_monadic_correct[OF rpne rpb krp] recompute
  by (simp add: pw_le_iff refine_pw_simps)

text \<open>The rebuilt node is its own exact frame at guard \<open>0\<close>, and \<open>X\<close>'s own length/word bounds
  transfer from \<open>rp\<close> — so the second prefix application has every premise it needs.\<close>
lemma hybrid_rebuild_frame:
  assumes recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
  shows "node_frame X X 0" and "4398046511104 \<le> (0::nat) \<longrightarrow> X = X"
    and "(0::nat) < 1099511627776 \<or> 4398046511104 \<le> (0::nat)"
    and "(0::nat) \<le> 4398046511104"
  by (simp_all add: node_frame_exact)

section \<open>The pop-time resolve, parametric in the continuation\<close>

text \<open>The cache coupling in composable form: the resolve hands its continuation the resolved
  class together with @{const dyadic_iv_cs_invar} against the node's EXACT count.\<close>
lemma hybrid_resolve_bind:
  assumes rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_eq: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and cache: "hybrid_cs_ok g c (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> g \<Longrightarrow> Q = X"
    and cont: "\<And>c' Q' g' rp'.
        \<lbrakk> dyadic_iv_cs_invar c' (carried_descartes_count X); rp' = rp;
          4398046511104 \<le> g' \<longrightarrow> Q' = X;
          g' < 4398046511104 \<longrightarrow> Q' = Q \<and> g' = g \<rbrakk>
        \<Longrightarrow> f c' Q' g' rp' \<le> SPEC \<Phi>"
  shows "doN { (c', Q', g', rp') \<leftarrow> hybrid_resolve_count_monadic Q g l_num r_num k rp c;
               f c' Q' g' rp' }
       \<le> SPEC \<Phi>"
  apply (refine_vcg
      hybrid_resolve_count_monadic_classify[OF rp_len rp_bound k_bound Q_bound
        X_pbound X_gbound X_eq cache locked_exact, THEN order_trans])
  apply clarsimp
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

section \<open>The concrete dispatch arms\<close>

lemma hybrid_dispatch_zero_acc:
  assumes cnt0: "cnt = 0"
  shows "hybrid_dispatch_monadic todo qtodo es ss cs gs acc rp1 l_num r_num k e s g1 Q1 cnt
       \<le> SPEC (\<lambda>(wl, acc'). acc' = acc \<and>
             wl = (todo, qtodo, es, ss, cs, gs, rp1))"
  unfolding hybrid_dispatch_monadic_def PR_CONST_def
  apply (simp add: cnt0)
  apply (rule order_trans[OF hybrid_branch_zero_correct])
  apply simp
  done

lemma hybrid_dispatch_one_acc:
  assumes cnt1: "cnt = 1"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
  shows "hybrid_dispatch_monadic todo qtodo es ss cs gs (al, ar, ak) rp1
             l_num r_num k e s g1 Q1 cnt
       \<le> SPEC (\<lambda>(wl, acc'). acc' = (al @ [l_num], ar @ [r_num], ak @ [k]) \<and>
             wl = (todo, qtodo, es, ss, cs, gs, rp1))"
  unfolding hybrid_dispatch_monadic_def PR_CONST_def
  apply (simp add: cnt1)
  apply (rule order_trans[OF hybrid_branch_one_correct[OF accpush]])
  apply simp
  done

text \<open>\<^bold>\<open>The \<open>cnt \<ge> 2\<close> gate fork.\<close> The dispatch's third
  arm evaluates the Newton gate and forks: gate CLOSED \<open>\<rightarrow>\<close> the split arm
  (\<open>hybrid_branch_split_acc\<close> covers it for a GENERAL guard), gate OPEN
  \<open>\<rightarrow>\<close> the window arm. Stated as a pure arm-selection equation over the definition, so it
  carries no side conditions beyond \<open>cnt \<notin> {0, 1}\<close> and leaves the \<open>mop\<close> unresolved for the
  caller -- the gate's VALUE is not needed to select the fork.\<close>
lemma hybrid_dispatch_gate_fork:
  assumes cnt2: "2 \<le> cnt"
  shows "hybrid_dispatch_monadic todo qtodo es ss cs gs acc rp1 l_num r_num k e s g1 Q1 cnt
       = doN {
           gate \<leftarrow> (PR_CONST newton_pol_gate_mop) Q1 e k s;
           if \<not> gate then
             (PR_CONST hybrid_branch_split_monadic)
               todo qtodo es ss cs gs rp1 acc l_num r_num k e s g1 Q1
           else
             (PR_CONST hybrid_gate_open_monadic)
               todo qtodo es ss cs gs acc rp1 l_num r_num k e s cnt g1 Q1
         }"
proof -
  \<comment> \<open>both disequalities in the SIMP-NORMAL form (\<open>Suc 0\<close>, not \<open>1\<close>): a premise stated with
     \<open>1\<close> does not fire on the normalized goal, and \<open>One_nat_def[symmetric]\<close> LOOPS.\<close>
  have n0: "cnt \<noteq> 0" and n1: "cnt \<noteq> Suc 0" using cnt2 by auto
  show ?thesis
    unfolding hybrid_dispatch_monadic_def PR_CONST_def by (simp add: n0 n1)
qed

section \<open>The multiset termination measure\<close>

definition hybrid_mu_mset :: "real \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> nat multiset" where
  "hybrid_mu_mset \<delta> ns = mset (map (\<lambda>nd. dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd))) ns)"

lemma hybrid_mu_mset_Nil[simp]: "hybrid_mu_mset \<delta> [] = {#}"
  by (simp add: hybrid_mu_mset_def)

lemma hybrid_mu_mset_append[simp]:
  "hybrid_mu_mset \<delta> (xs @ ys) = hybrid_mu_mset \<delta> xs + hybrid_mu_mset \<delta> ys"
  by (simp add: hybrid_mu_mset_def)

text \<open>\<^bold>\<open>The three decrease lemmas.\<close> The \<open><\<close> here is the multiset order, not \<open>\<subset>#\<close>. Bail states exactly the
  two step shapes needed (@{thm [source] dyadic_iv_todo_mu_mset_one_smaller_bl},
  @{thm [source] dyadic_iv_todo_mu_mset_two_smaller_bl}), so push1/push2 map straight onto
  them; the pop case adds nothing, so it is the ordered-monoid law \<open>a < a + b \<longleftrightarrow> 0 < b\<close>.\<close>
lemma hybrid_mu_mset_pop_less:
  "hybrid_mu_mset \<delta> ns < hybrid_mu_mset \<delta> (ns @ [nd])"
proof -
  have eq: "hybrid_mu_mset \<delta> (ns @ [nd])
      = hybrid_mu_mset \<delta> ns + {# dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd)) #}"
    by (simp add: hybrid_mu_mset_def)
  have "multp (<) (hybrid_mu_mset \<delta> ns + {#})
                  (hybrid_mu_mset \<delta> ns + {# dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd)) #})"
    by (rule one_step_implies_multp) auto
  then show ?thesis unfolding eq by (simp add: less_multiset_def)
qed

lemma hybrid_mu_mset_push1_less:
  assumes lt: "dyadic_iv_interval_mu \<delta> (fst c, fst (snd c))
             < dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd))"
  shows "hybrid_mu_mset \<delta> (ns @ [c]) < hybrid_mu_mset \<delta> (ns @ [nd])"
  using dyadic_iv_todo_mu_mset_one_smaller_bl[OF lt, where rest = "map (\<lambda>nd. dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd))) ns"]
  by (simp add: hybrid_mu_mset_def)

lemma hybrid_mu_mset_push2_less:
  assumes ltl: "dyadic_iv_interval_mu \<delta> (fst cl, fst (snd cl))
              < dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd))"
    and ltr: "dyadic_iv_interval_mu \<delta> (fst cr, fst (snd cr))
            < dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd))"
  shows "hybrid_mu_mset \<delta> (ns @ [cl, cr]) < hybrid_mu_mset \<delta> (ns @ [nd])"
  using dyadic_iv_todo_mu_mset_two_smaller_bl[OF ltl ltr, where rest = "map (\<lambda>nd. dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd))) ns"]
  by (simp add: hybrid_mu_mset_def)

lemma hybrid_window_choice_abs:
  assumes lenQ0: "0 < length Q" and lenQ: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and lenQ1: "1 < length Q" and ecap: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and lenQ2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>@{thm [source] blr_window_choice_refine_bl} takes the \<open>v\<close> word bound as a premise; the ultimate caller has
       it as \<open>vcap1\<close>.\<close>
    and vb: "int v < max_sint LENGTH(gmp_long_len)"
    and v2: "2 \<le> v" and cQv: "carried_descartes_count Q \<le> v"
    and repr: "carried_repr_scalar P a b Q" and len2: "Suc 0 < length P"
    and ab: "a < b" and l0r0: "lo < ro" and canon: "coeffs (Poly P) = P"
    and abdef: "a = fst (dyadic_iv_node_iv lo ro ko nl nr nk)"
               "b = snd (dyadic_iv_node_iv lo ro ko nl nr nk)"
    and dec: "pol (degree (Poly P)) a b e dk (s, descartes_list_int a b (coeffs (Poly P)))
              = (True, True)"
  shows "newton_window_choice_bail_monadic v e Q
       \<le> SPEC (\<lambda>wc. map_option (\<lambda>(m, _). dyadic_iv_node_iv lo ro ko
                          (fst (newton_window_child nl nr nk e m))
                          (fst (snd (newton_window_child nl nr nk e m)))
                          (snd (snd (newton_window_child nl nr nk e m)))) wc
             = try_window_bail_int
                 (snd (pol (degree (Poly P)) a b e dk
                         (s, descartes_list_int a b (coeffs (Poly P)))))
                 a b (N_of e) (Poly P) v)"
  \<comment> \<open>caller variables RENAMED (\<open>lo ro ko nl nr nk\<close>) so they cannot collide with the cited
     lemma's own \<open>l0 r0 k0 l r k\<close> — the collision that turned \<open>multiple unifiers\<close> into
     \<open>no unifiers\<close> above.\<close>
  apply (rule SPEC_cons_rule[OF blr_window_choice_refine_bl[OF lenQ0 lenQ gate4 lenQ1 ecap
                                  lenQ2 vb v2 cQv]])
  using hybrid_window_pick_at_recorded_dec[where P = P and Q = Q and a = a and b = b
          and pol = pol and e = e and dk = dk and s = s and v = v,
          OF repr len2 ab l0r0 canon abdef dec]
  by simp

text \<open>\<^bold>\<open>Proof notes for the measure lemmas.\<close>

  \<^item> The \<open><\<close> on these measures is the multiset (Dershowitz--Manna) order, not \<open>\<subseteq>#\<close>.
    \<open>_pop_less\<close> is @{thm [source] one_step_implies_multp} at \<open>K = {#}\<close>
    (the \<open>\<forall>k \<in># K\<close> side condition is vacuous) plus \<open>less_multiset_def\<close>;
    \<open>less_add_same_cancel1\<close> cannot be used (simp rewrites \<open>M + {#x#}\<close> to \<open>add_mset x M\<close>
    first, and applying the rule before simp fails too).
  \<^item> A cited lemma carrying \<open>mset ?rest\<close> does not match a goal simp has turned into
    \<open>image_mset\<close>: \<open>rest\<close> is pinned with \<open>where\<close> so the instance is concrete, and simp then
    normalises both sides together (\<open>_push1_less\<close>/\<open>_push2_less\<close>, from bail's
    \<open>dyadic_iv_todo_mu_mset_one_smaller_bl\<close>/\<open>_two_smaller_bl\<close>).
  \<^item> A premise stated with \<open>1\<close> does not fire on a goal simp normalised to \<open>Suc 0\<close>, and
    \<open>One_nat_def[symmetric]\<close> loops, so both disequalities are supplied in \<open>Suc 0\<close> form
    (\<open>hybrid_dispatch_gate_fork\<close>, restated from the definition as a pure arm-selection
    equation since the gate's value is not needed to pick the fork).\<close>

section \<open>The gate-open arm\<close>

lemma hybrid_cond_escalate_exact:
  assumes gex: "g = 0 \<or> 4398046511104 \<le> g"
  shows "hybrid_cond_escalate_monadic rp l_num r_num k Q g = RETURN (Q, rp)"
  unfolding hybrid_cond_escalate_monadic_def PR_CONST_def using gex by auto

lemma hybrid_cond_escalate_trunc:
  assumes g0: "g \<noteq> 0" and glt: "g < 4398046511104"
    and recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_cond_escalate_monadic rp l_num r_num k Q g
       \<le> SPEC (\<lambda>(qx, rpx). qx = X \<and> rpx = rp)"
  unfolding hybrid_cond_escalate_monadic_def PR_CONST_def
  using g0 glt
  apply simp
  apply (rule order_trans[OF carried_escalate_keep_monadic_correct[OF rpne rpb krp]])
  apply (simp add: recompute)
  done

lemma hybrid_cond_escalate_gives_X:
  assumes lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and exact0: "g = 0 \<longrightarrow> Q = X"
    and recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_cond_escalate_monadic rp l_num r_num k Q g
       \<le> SPEC (\<lambda>(qx, rpx). qx = X \<and> rpx = rp)"
proof (cases "g = 0 \<or> 4398046511104 \<le> g")
  case True
  then show ?thesis
    using lock exact0 by (auto simp: hybrid_cond_escalate_exact)
next
  case False
  then show ?thesis
    by (intro hybrid_cond_escalate_trunc[OF _ _ recompute rpne rpb krp]) auto
qed

lemma hybrid_window_v_cached:
  assumes inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and c4: "4 \<le> cnt"
  shows "hybrid_window_v_monadic cnt g Q \<le> SPEC (\<lambda>v. v = carried_descartes_count X)"
  unfolding hybrid_window_v_monadic_def PR_CONST_def
  using c4 inv by (simp add: dyadic_iv_cs_invar_def)

section \<open>After-pop = resolve \<circ> dispatch\<close>

text \<open>The first full after-pop compositions: @{thm [source] hybrid_resolve_bind} hands over
  @{const dyadic_iv_cs_invar} for the resolved class, whose \<open>(c = 0) = (cnt = 0)\<close> conjunct lets
  the node's EXACT count pin the branch -- no cache internals needed.\<close>
lemma hybrid_after_pop_discard_acc:
  assumes rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_eq: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and cache: "hybrid_cs_ok g c (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> g \<Longrightarrow> Q = X"
    and count0: "carried_descartes_count X = 0"
    and Qne: "0 < length Q" and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne: "0 < length X" and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the after-pop op ASSERTs \<open>length Q + 2\<close> on the resolved node; \<open>X_gbound\<close>
       covers the locked branch, this covers the unlocked one. \<^bold>\<open>Last\<close>.\<close>
    and Q_small: "length Q < 1099511627776"
  shows "hybrid_after_pop_monadic todo qtodo es ss cs gs acc rp l_num r_num k e s c g Q
       \<le> SPEC (\<lambda>(wl, acc'). acc' = acc \<and>
             wl = (todo, qtodo, es, ss, cs, gs, rp))"
  unfolding hybrid_after_pop_monadic_def PR_CONST_def
  using Qne Q_bound kcap rp_len rp_bound k_bound
  apply (refine_vcg
      hybrid_resolve_bind[OF rp_len rp_bound k_bound Q_bound X_pbound X_gbound X_eq
        cache locked_exact])
  apply (all \<open>((insert Qne Q_bound X_ne X_len rp_len rp_bound, auto); fail)?\<close>)
  apply (all \<open>((insert Q_small X_gbound X_len Qne, auto simp: max_snat_def); fail)?\<close>)
  subgoal for cnt Q1 g1 rp1
    apply (rule order_trans[OF hybrid_dispatch_zero_acc])
    subgoal using count0 by (simp add: dyadic_iv_cs_invar_def)
    by simp
  done

lemma hybrid_after_pop_accept_acc:
  assumes rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_eq: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and cache: "hybrid_cs_ok g c (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> g \<Longrightarrow> Q = X"
    and count1: "carried_descartes_count X = 1"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and Qne: "0 < length Q" and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne: "0 < length X" and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>see @{thm [source] hybrid_after_pop_discard_acc}'s \<open>Q_small\<close>. \<^bold>\<open>Last\<close>.\<close>
    and Q_small: "length Q < 1099511627776"
  shows "hybrid_after_pop_monadic todo qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s c g Q
       \<le> SPEC (\<lambda>(wl, acc'). acc' = (al @ [l_num], ar @ [r_num], ak @ [k]) \<and>
             wl = (todo, qtodo, es, ss, cs, gs, rp))"
  unfolding hybrid_after_pop_monadic_def PR_CONST_def
  using Qne Q_bound kcap rp_len rp_bound k_bound
  apply (refine_vcg
      hybrid_resolve_bind[OF rp_len rp_bound k_bound Q_bound X_pbound X_gbound X_eq
        cache locked_exact])
  apply (all \<open>((insert Qne Q_bound X_ne X_len rp_len rp_bound, auto); fail)?\<close>)
  apply (all \<open>((insert Q_small X_gbound X_len Qne, auto simp: max_snat_def); fail)?\<close>)
  subgoal for cnt Q1 g1 rp1
    apply (rule order_trans[OF hybrid_dispatch_one_acc[OF _ accpush]])
    subgoal using count1 by (simp add: dyadic_iv_cs_invar_def)
    by simp
  done

text \<open>\<^bold>\<open>The split arm for a general guard.\<close> The exact-case lemma with \<open>gex\<close> dropped, so the ambiguous
  \<open>code = 2\<close> rebuild arm is reachable: it frees the truncated children, rebuilds the node exactly from the retained root
  (@{thm [source] carried_init_inplace_gives_X} returns literally \<open>X\<close>) and re-runs
  children and decide at guard \<open>0\<close>, where \<open>code \<noteq> 2\<close> forbids a second ambiguity.

  \<^bold>\<open>Eta-expansion.\<close> Under an outer bind, \<open>refine_vcg\<close> leaves the inner prefix as
  \<open>m \<le> SPEC (\<lambda>x. (case x of (\<dots>) \<Rightarrow> \<dots>) \<le> SPEC \<Phi>)\<close>, eta-expanded, whereas a lemma written
  \<open>SPEC (\<lambda>(ql, gl, \<dots>). \<dots>)\<close> is eta-contracted, and the two do not unify here. Hence two
  decomposed twins: @{thm [source] truncate_children_mid_decide_bind_decomp} (contracted) and
  \<open>truncate_children_mid_decide_bind_eta\<close> (expanded). The expanded one is what
  this proof needs; both are proven by the bind form's own script. The printer eta-contracts what the unifier will
  not, so the two goals print identically.

  The twin is applied with a plain \<open>rule\<close>, since the goal matches exactly: handed to \<open>refine_vcg\<close> alongside the
  state/push rules it makes the VCG search, and \<open>simp add: bind_rule_complete\<close> or
  \<open>auto simp: pw_le_iff refine_pw_simps\<close> diverge.\<close>

lemma truncate_children_mid_decide_bind_eta:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    and cont: "\<And>ql gl qr gr code.
        \<lbrakk> node_frame (carried_left X) ql gl; node_frame (carried_right X) qr gr;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          4398046511104 \<le> gr \<longrightarrow> qr = carried_right X;
          code = 1 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          code = 0 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0;
          g = 0 \<or> 4398046511104 \<le> g \<longrightarrow> code \<noteq> 2;
          code = 0 \<or> code = 1 \<or> code = 2 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr code \<le> SPEC \<Phi>"
  shows "truncate_children_mid_monadic g Q
       \<le> SPEC (\<lambda>x. (case x of (ql, gl, qr, gr, mids, midbl) \<Rightarrow>
             truncate_mid_decide_monadic g len mids midbl \<bind> (\<lambda>code. f ql gl qr gr code))
           \<le> SPEC \<Phi>)"
  apply (refine_vcg
      truncate_children_mid_agrees[OF frame lock g_tri Qne Qbound Q_small,
        THEN order_trans])
  apply clarsimp
  apply (refine_vcg
      truncate_mid_decide_agrees[OF frame lock len_eq Qne Q_small, THEN order_trans])
  apply (all \<open>(simp; fail)?\<close>)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done



section \<open>The child-guard payload, carried as ONE OPAQUE predicate\<close>

text \<open>\<^bold>\<open>What this section delivers.\<close> @{thm [source] hybrid_refine_invar_split_step}
  needs \<open>g1le\<close>/\<open>g2le\<close>, \<open>g1 \<le> (k1 + 1) * length rp \<or> 2\<^sup>4\<^sup>2 \<le> g1\<close>, for the two pushed children,
  and @{thm [source] truncate_children_mid_agrees} concludes only \<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close>, which
  collapses to \<open>gl \<le> 2\<^sup>4\<^sup>2\<close> whenever \<open>g < 2\<^sup>4\<^sup>2\<close> and so gives neither disjunct. The truncation
  layer must expose the concrete child guard; no reformulation of the coupling conjunct avoids it.

  \<^bold>\<open>Why an opaque predicate and not four raw conjuncts.\<close> With the four facts spelled out in \<open>agrees\<close>'s \<open>shows\<close>
  and the bind twins' \<open>cont\<close>, the \<open>auto simp: max_def\<close> closers in
  @{thm [source] hybrid_branch_split_exact_productive} and \<open>_exact_acc\<close> case-split the two implications and feed
  the nat subtraction to \<open>linarith\<close>. Wrapped in a definition with no \<open>[simp]\<close> and no intro rules, the payload is an
  atom that \<open>auto\<close>/\<open>clarsimp\<close>/\<open>max_def\<close>/\<open>linarith\<close> cannot decompose, case-split or rewrite: it is
  carried by \<open>assumption\<close> and unfolded once, at the single site that consumes it.
  @{const hybrid_cs_ok} rides the whole \<open>branch \<rightarrow> dispatch \<rightarrow> after_pop \<rightarrow> step_args\<close> chain through the same
  closers in the same way.

  The guard facts are stated in a sibling lemma and conjoined with @{thm [source] cdlr_SPEC_conj}. They carry no
  \<open>node_frame\<close> content, so this is a genuinely smaller proof than \<open>agrees\<close> rather than a clone of it.\<close>

text \<open>\<^bold>\<open>Why the lock half carries an \<open>\<or> gl \<le> len\<close> escape hatch.\<close>
  \<open>hybrid_branch_split_acc\<close> reaches the truncation layer by TWO routes at
  DIFFERENT guards: the mid branch at the node's own \<open>g\<close>, and the REBUILD branch at guard
  \<open>0\<close> (@{thm [source] hybrid_rebuild_frame} gives \<open>node_frame X X 0\<close>). A locked parent whose
  child is rebuilt exact therefore has \<open>gl = 0\<close>, which satisfies neither \<open>2\<^sup>4\<^sup>2 \<le> gl\<close> nor any
  bound derived from it — so the flat form is UNPROVABLE on that path. It is also not needed:
  what the invariant wants is \<open>gl \<le> (k+2)\<cdot>len \<or> 2\<^sup>4\<^sup>2 \<le> gl\<close>, and an exact child satisfies the
  FIRST disjunct outright. The hatch is exactly that case, and it is what makes the predicate
  monotone in \<open>g\<close> (\<open>hybrid_child_gok_mono\<close>), which is how the rebuild branch's
  \<open>0\<close>-form is lifted to the shared conclusion.\<close>
definition hybrid_child_gok :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hybrid_child_gok g len gl \<longleftrightarrow>
     gl \<le> g + len \<and> (4398046511104 \<le> g \<longrightarrow> gl = g \<or> gl \<le> len)"

text \<open>The ONLY elimination — keep it out of every simp set so the atom stays inert in transit.\<close>
lemma hybrid_child_gokD:
  assumes "hybrid_child_gok g len gl"
  shows "gl \<le> g + len"
    and "4398046511104 \<le> g \<Longrightarrow> gl = g \<or> gl \<le> len"
  using assms unfolding hybrid_child_gok_def by auto

text \<open>Monotone in the parent guard: an EXACT child (guard \<open>0\<close>, hence \<open>gl \<le> len\<close>) satisfies the
  predicate at ANY \<open>g\<close>. This is the rebuild branch's lift, applied as a \<open>rule\<close> so no arithmetic
  ever enters the arm lemma's closers.\<close>
lemma hybrid_child_gok_mono:
  assumes "hybrid_child_gok 0 len gl"
  shows "hybrid_child_gok g len gl"
  using assms unfolding hybrid_child_gok_def by auto

text \<open>\<^bold>\<open>The shape that TRAVELS, and why it is not @{const hybrid_child_gok}.\<close>
  \<open>hybrid_child_gok\<close> is indexed by the guard the truncation layer actually saw. That guard is
  the RESOLVED one, \<open>g1\<close> — and \<open>hybrid_after_pop_split_acc\<close>'s conclusion cannot mention it.
  Substituting the stored \<open>g\<close> does not work either: \<open>hybrid_resolve_bind\<close>'s \<open>unlockx\<close> does give
  \<open>g1 = g\<close> exactly (the resolve never RAISES an unlocked guard), but its LOCKED branch admits
  \<open>2\<^sup>4\<^sup>2 \<le> g1\<close> while the stored \<open>g\<close> is \<open>< 2\<^sup>4\<^sup>0\<close>, and then \<open>gl \<le> g + len\<close> is simply false.

  So the atom that crosses the resolve is indexed by DEPTH instead, and is literally
  @{thm [source] hybrid_refine_invar_split_step}'s \<open>g1le\<close> at the child's own \<open>k1 = k + 1\<close>.
  Nothing below the arm ever mentions a guard again.\<close>
definition hybrid_child_depth_ok :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hybrid_child_depth_ok k len gl \<longleftrightarrow>
     gl \<le> (k + 1) * len \<or> 4398046511104 \<le> gl"

text \<open>\<^bold>\<open>The one conversion, done once inside the arm.\<close> Both cases of the parent's own coupling
  conjunct land on the child's:
  \<^item> parent UNLOCKED (\<open>g \<le> (k+1)\<cdot>len\<close>): \<open>gl \<le> g + len \<le> (k+2)\<cdot>len\<close> — the first disjunct;
  \<^item> parent LOCKED (\<open>2\<^sup>4\<^sup>2 \<le> g\<close>): the guard half's lock clause gives \<open>2\<^sup>4\<^sup>2 \<le> gl\<close> (second disjunct)
    or the \<open>\<le> len\<close> hatch, and \<open>len \<le> (k+2)\<cdot>len\<close> puts that in the first.\<close>
lemma hybrid_child_depth_okI:
  assumes gok: "hybrid_child_gok g len gl"
    and parent: "g \<le> (k + 1) * len \<or> 4398046511104 \<le> g"
  shows "hybrid_child_depth_ok (k + 1) len gl"
proof (cases "4398046511104 \<le> g")
  case lock: True
  \<comment> \<open>the lock clause now yields \<open>gl = g\<close>, from which \<open>2\<^sup>4\<^sup>2 \<le> gl\<close> needs one step through
     \<open>lock\<close> -- \<open>simp\<close> will not chain it, \<open>auto\<close> does.\<close>
  have "4398046511104 \<le> gl \<or> gl \<le> len"
    using gok lock unfolding hybrid_child_gok_def by auto
  moreover have "len \<le> (k + 1 + 1) * len"
    using mult_le_mono1[of 1 "k + 1 + 1" len] by simp
  ultimately show ?thesis unfolding hybrid_child_depth_ok_def by auto
next
  case False
  with parent have gle: "g \<le> (k + 1) * len" by simp
  have "gl \<le> g + len" using gok unfolding hybrid_child_gok_def by simp
  also have "\<dots> \<le> (k + 1) * len + len" using gle by simp
  also have "\<dots> = (k + 1 + 1) * len" by (simp add: algebra_simps)
  finally show ?thesis unfolding hybrid_child_depth_ok_def by simp
qed

text \<open>The ONLY elimination — used once, where \<open>g1le\<close> is discharged.\<close>
lemma hybrid_child_depth_okD:
  assumes "hybrid_child_depth_ok k len gl"
  shows "gl \<le> (k + 1) * len \<or> 4398046511104 \<le> gl"
  using assms unfolding hybrid_child_depth_ok_def by simp

text \<open>\<^bold>\<open>The fact @{thm [source] cdlr_retrunc_child} does not expose.\<close> Retruncation never RAISES a
  guard above \<open>max gin 1\<close>: three of \<open>carried_retrunc_mop\<close>'s four branches return \<open>g\<close> verbatim
  and the fourth is \<open>retrunc_reset_mop\<close>, which returns \<open>1\<close> or \<open>g - t + 1 \<le> g\<close>. No premises at
  all — the bound is pure branch bookkeeping, with no \<open>gframe\<close> content.\<close>
lemma cdlr_retrunc_child_gbound:
  shows "carried_retrunc_mop child gin \<le> SPEC (\<lambda>(ys, g'). g' \<le> max gin 1)"
  unfolding carried_retrunc_mop_def poly_length_monadic_def
    retrunc_attempt_guard_mop_def retrunc_reset_mop_def trunc_gap_mop_def PR_CONST_def
  apply (refine_vcg poly_trunc_in_place_correct[THEN order_trans]
      lead_budget_mop_nofail[THEN order_trans])
  apply (all \<open>(simp; fail)?\<close>)
  by (auto simp: max_snat_def)

text \<open>\<^bold>\<open>The payload atom.\<close> At a LOCKED node the guard's payload \<open>g - 2\<^sup>4\<^sup>2\<close> bounds the
  node's own count. This is what \<open>hybrid_window_v_exact\<close>'s \<open>pay\<close> premise consumes,
  and hence what makes the capped branch of @{const hybrid_window_v_monadic} exact.

  \<^bold>\<open>Why the antecedent is \<open>2\<^sup>4\<^sup>2 + 2\<close> and not \<open>2\<^sup>4\<^sup>2\<close>\<close>: that is precisely the branch condition
  of @{const hybrid_window_v_monadic}'s capped arm, so the atom says exactly as much as the
  consumer needs and nothing more. A window child's payload is its parent's exact count
  (@{thm [source] newton_window_pick_bail_count}), which is \<open>\<ge> 2\<close>, so the antecedent is live.\<close>
text \<open>\<^bold>\<open>The guard ceiling is the second conjunct, and it is needed.\<close> \<open>hybrid_loop_step_args_\<open>{split,window}\<close>\<close>
  take the trichotomy rather than \<open>g_small\<close>, so a locked node may be popped, and then their \<open>gcap_rp\<close> premise
  \<open>max g 2\<^sup>4\<^sup>2 + length rp < max_snat\<close> has no other source: @{const hybrid_trunc_coupling}'s locked
  disjunct is the bare sentinel \<open>2\<^sup>4\<^sup>2 \<le> g\<close> and bounds the guard from below only.

  \<^bold>\<open>Why it belongs here rather than in its own conjunct\<close>: it is preserved by exactly the two
  facts that already carry the payload, and by nothing else. A window child's guard is
  \<open>2\<^sup>4\<^sup>2 + v\<close> with \<open>v\<close> the parent's own count, so \<open>v \<le> length rp\<close>
  (@{thm [source] carried_descartes_count_le_length_cn}); a split child's is \<open>\<le> max g 2\<^sup>4\<^sup>2\<close>,
  which the parent's own ceiling dominates. Both are self-contained: the ceiling needs no
  \<open>g_room\<close>, no depth bound and no keystone premise.\<close>
definition hybrid_child_pay_ok :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> nat \<Rightarrow> bool" where
  "hybrid_child_pay_ok l1 k1 r1 rp gl \<longleftrightarrow>
     gl \<le> 4398046511104 + length rp \<and>
     (4398046511106 \<le> gl \<longrightarrow>
        carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp)
          \<le> gl - 4398046511104)"

text \<open>The two degenerate instances, both used as \<open>rule\<close>s so no unfolding reaches a closer.
  \<open>_zero\<close> is the REBUILD branch (guard \<open>0\<close>, @{thm [source] hybrid_rebuild_frame}); \<open>_resolved\<close>
  transports the STORED guard's atom across \<open>hybrid_resolve_guard_cases\<close>, whose
  other case \<open>g\<^sub>1 = 2\<^sup>4\<^sup>2\<close> carries payload zero and so satisfies the atom outright.\<close>
lemma hybrid_child_pay_ok_zero: "hybrid_child_pay_ok l1 k1 r1 rp 0"
  unfolding hybrid_child_pay_ok_def by simp

text \<open>The projection the gate-open arm consumes: \<open>hybrid_gate_open_acc\<close>'s \<open>pay\<close> premise is the
  atom's second conjunct read at the node's own poly.\<close>
lemma hybrid_child_pay_okD:
  assumes pay: "hybrid_child_pay_ok l1 k1 r1 rp gl"
    and X_eq: "X = carried_init_same_den l1 (2 ^ k1) r1 rp"
  shows "4398046511106 \<le> gl \<longrightarrow> carried_descartes_count X \<le> gl - 4398046511104"
  using pay unfolding hybrid_child_pay_ok_def X_eq by simp

lemma hybrid_child_pay_ok_resolved:
  assumes cases: "g1 = 4398046511104 \<or> g1 = g"
    and pay: "hybrid_child_pay_ok l1 k1 r1 rp g"
  shows "hybrid_child_pay_ok l1 k1 r1 rp g1"
  using assms unfolding hybrid_child_pay_ok_def by auto

text \<open>\<^bold>\<open>The transfer, and every step of it is now in hand.\<close> Assume the child's guard is
  \<open>\<ge> 2\<^sup>4\<^sup>2 + 2\<close>. Then \<open>gmax\<close> (\<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close>, a \<open>cont\<close> hypothesis of the bind twins) forces
  the PARENT locked; @{const hybrid_child_gok}'s strengthened lock clause then gives
  \<open>gl = g \<or> gl \<le> len\<close>, and \<open>small\<close> kills the second disjunct -- a length cannot reach \<open>2\<^sup>4\<^sup>2\<close>.
  With \<open>gl = g\<close> the parent's own payload bound transfers verbatim, and
  \<open>carried_count_subinterval_mono\<close> supplies \<open>mono\<close>.\<close>
lemma hybrid_child_pay_okI:
  assumes gok: "hybrid_child_gok g len gl"
    and gmax: "gl \<le> max g 4398046511104"
    and small: "len < 1099511627776"
    and ppay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count XP \<le> g - 4398046511104"
    and mono: "carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp)
                 \<le> carried_descartes_count XP"
    \<comment> \<open>\<^bold>\<open>The parent's own ceiling\<close>, \<^bold>\<open>last\<close> so that no \<open>[OF \<dots>]\<close> position moves. It is the second conjunct
       of the parent's atom, so no call site has to find it separately; \<open>hybrid_pay_split_child\<close> projects it.\<close>
    and gpb: "g \<le> 4398046511104 + length rp"
  shows "hybrid_child_pay_ok l1 k1 r1 rp gl"
proof -
  \<comment> \<open>through \<open>\<le>\<close>-monotonicity of \<open>max\<close>, never \<open>max_def\<close> --- \<open>v_guard_cap_arith\<close>'s lesson.\<close>
  have bnd: "gl \<le> 4398046511104 + length rp" using gmax gpb by (simp add: max.bounded_iff)
  have pay: "4398046511106 \<le> gl \<longrightarrow>
               carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp)
                 \<le> gl - 4398046511104"
  proof
    assume big: "4398046511106 \<le> gl"
    have g42: "4398046511104 \<le> g" using big gmax by simp
    have gbig: "4398046511106 \<le> g" using big gmax by simp
    have disj: "gl = g \<or> gl \<le> len" using gok g42 unfolding hybrid_child_gok_def by simp
    have nlen: "\<not> gl \<le> len" using big small by simp
    have gg: "gl = g" using disj nlen by blast
    show "carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp)
            \<le> gl - 4398046511104"
      using ppay gbig mono gg by simp
  qed
  show ?thesis unfolding hybrid_child_pay_ok_def using bnd pay by simp
qed

section \<open>The locked node's payload bound\<close>

text \<open>\<^bold>\<open>Why this exists now.\<close> \<open>hybrid_loop_step_args_{split,window}\<close> demand \<open>g < 2\<^sup>4\<^sup>0\<close> --- an
  UNLOCKED popped node --- while the window arm's own push SETS the lock \<open>2\<^sup>4\<^sup>2 + v\<close>, so a window
  child that later pops with the gate open sits in the excluded band. Every layer of that chain
  generalises to the trichotomy \<open>g < 2\<^sup>4\<^sup>0 \<or> 2\<^sup>4\<^sup>2 \<le> g\<close> --- \<open>hybrid_branch_split_acc\<close>
  always took it and \<open>hybrid_resolved_node_facts\<close> now does --- EXCEPT for one
  obligation: \<open>pay\<close>, the payload bound, whose antecedent \<open>2\<^sup>4\<^sup>2 + 2 \<le> g\<^sub>1\<close> is unsatisfiable under
  \<open>g_small\<close> and live at a locked node.

  @{const hybrid_child_pay_ok} and @{thm [source] hybrid_child_pay_okI} were built for this and
  have no consumer yet. These are the two facts that give them one.\<close>

text \<open>\<^bold>\<open>The WINDOW child's payload, and it needs no invariant at all.\<close> The arm sets the child's
  guard to \<open>2\<^sup>4\<^sup>2 + v\<close> with \<open>v\<close> the parent's exact count, and
  @{thm [source] newton_window_pick_bail_count} says the accepted window PRESERVES that count ---
  so the payload bound holds with EQUALITY. This is the base case of the payload invariant: the
  only arm that creates a lock is the one that also pins the payload.\<close>
lemma hybrid_pay_window_child:
  assumes pk: "newton_window_pick_bail v e X = Some (m, cand)"
    and cand_eq: "cand = carried_init_same_den l1 (2 ^ k1) r1 rp"
    \<comment> \<open>\<^bold>\<open>The ceiling's window case\<close>, \<^bold>\<open>last\<close>. \<open>v\<close> is the parent's own count,
       so this is @{thm [source] carried_descartes_count_le_length_cn} read through
       \<open>length X = length rp\<close> at every call site.\<close>
    and vle: "v \<le> length rp"
  shows "hybrid_child_pay_ok l1 k1 r1 rp (4398046511104 + v)"
  unfolding hybrid_child_pay_ok_def
  using newton_window_pick_bail_count[OF pk] cand_eq vle by simp

text \<open>\<^bold>\<open>The INHERITED case\<close> --- a split (or a rebuild) under a locked parent. This is
  @{thm [source] hybrid_child_pay_okI} with its \<open>ppay\<close> premise expressed as the PARENT's own
  @{const hybrid_child_pay_ok} atom, which is the form the invariant carries, so the
  preservation step reads as "the parent's conjunct plus count monotonicity gives the child's".
  \<open>mono\<close> is \<open>carried_count_subinterval_mono\<close>'s job at every real call site.

  Together with @{thm [source] hybrid_pay_window_child} these are the only two ways a node can
  acquire a guard, so they are the whole of the payload invariant's preservation content;
  everything else is the \<open>\<forall>i\<close> bookkeeping the coupling's existing \<open>_pop\<close>/\<open>_push\<close> lemmas do.\<close>
lemma hybrid_pay_split_child:
  assumes gok: "hybrid_child_gok g (length rp) gl"
    and gmax: "gl \<le> max g 4398046511104"
    and small: "length rp < 1099511627776"
    and ppay: "hybrid_child_pay_ok l k r rp g"
    and XP_eq: "XP = carried_init_same_den l (2 ^ k) r rp"
    and mono: "carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp)
                 \<le> carried_descartes_count XP"
  shows "hybrid_child_pay_ok l1 k1 r1 rp gl"
proof -
  have ppay': "4398046511106 \<le> g \<longrightarrow> carried_descartes_count XP \<le> g - 4398046511104"
    using ppay unfolding hybrid_child_pay_ok_def XP_eq by simp
  \<comment> \<open>the CEILING travels INSIDE the parent's atom, which is why no call site gained a premise.\<close>
  have gpb: "g \<le> 4398046511104 + length rp"
    using ppay unfolding hybrid_child_pay_ok_def by simp
  show ?thesis by (rule hybrid_child_pay_okI[OF gok gmax small ppay' mono gpb])
qed

text \<open>\<^bold>\<open>The cache at a window push, and it is a one-liner because bail already did the work.\<close>
  The accept branch pushes cache \<open>v + 2\<close> at guard \<open>glock = 2\<^sup>4\<^sup>2 + v\<close>. Since \<open>glock \<ge> 2\<^sup>4\<^sup>2\<close>,
  @{const hybrid_cs_ok}'s sentinel disjunct (\<open>c = 4 \<and> g < 2\<^sup>4\<^sup>2\<close>) is dead and the obligation is
  @{const dyadic_iv_cs_invar}\<open> (v+2) (count cand)\<close>, whose \<open>4 \<le> c \<longrightarrow> c = cnt + 2\<close> clause is an
  EQUALITY -- so it demands \<open>count cand = v\<close>, not merely an upper bound.

  \<^bold>\<open>That equality is exactly how bail DEFINES acceptance\<close>:
  \<open>newton_wok v e m Q \<longleftrightarrow> carried_descartes_count (newton_wcand e m Q) = v\<close>, and
  @{thm [source] newton_window_pick_bail_count} already extracts it from a \<open>Some\<close> pick. The
  hybrid arm calls the very same op that @{const newton_window_pick_bail} models
  (@{thm [source] blr_window_choice_refine_bl}), so nothing new is needed here -- only the
  arithmetic that \<open>v \<ge> 2\<close> makes every clause of the trichotomy immediate.\<close>
lemma hybrid_window_child_cs_ok:
  assumes v2: "2 \<le> v"
    and pick: "newton_window_pick_bail v e Q = Some (m, cand)"
  shows "hybrid_cs_ok (4398046511104 + v) (v + 2) (carried_descartes_count cand)"
proof -
  have cv: "carried_descartes_count cand = v" by (rule newton_window_pick_bail_count[OF pick])
  show ?thesis
    unfolding hybrid_cs_ok_def dyadic_iv_cs_invar_def cv using v2 by simp
qed

text \<open>\<^bold>\<open>Descartes count is monotone under interval INCLUSION -- the fact the window arm's
  invariant conjunct rests on, and the one piece of it that did not exist.\<close>

  @{thm [source] carried_window_count_mono} proves only the instance whose OUTER interval is the
  whole of \<open>[0,1]\<close>, i.e. it bounds a child by the count of \<open>rp\<close> itself. The window arm needs the
  bound relative to the node's own PARENT, because a locked node's payload is the parent's count
  and its children inherit that payload unchanged.

  \<^bold>\<open>This is a faithful clone of that proof with the outer interval generalised\<close>, and every
  ingredient was already general -- only its instantiation was not:
  @{thm [source] Bernstein_changes_subinterval_mono} is stated at arbitrary
  \<open>a \<le> a' < b' \<le> b\<close>, and @{thm [source] window_child_formula_repr_scalar} at arbitrary
  \<open>l\<close>/\<open>d\<close>/\<open>r\<close>. So both sides go through @{const descartes_list_int} at the SAME list \<open>xs\<close>
  with only the intervals differing, exactly as in the original.\<close>
lemma carried_count_subinterval_mono:
  fixes l r l' r' :: int and k k' :: nat
  defines "A \<equiv> (rat_of_int l' / rat_of_int (2 ^ k'))"
    and "B \<equiv> (rat_of_int r' / rat_of_int (2 ^ k'))"
    and "A0 \<equiv> (rat_of_int l / rat_of_int (2 ^ k))"
    and "B0 \<equiv> (rat_of_int r / rat_of_int (2 ^ k))"
  assumes len: "0 < length xs"
    and AB: "A < B" and lo: "A0 \<le> A" and hi: "B \<le> B0"
  shows "carried_descartes_count (carried_init_same_den l' (2 ^ k') r' xs)
       \<le> carried_descartes_count (carried_init_same_den l (2 ^ k) r xs)"
proof -
  define P where "P = (map_poly of_int (Poly xs) :: real poly)"
  have jpos: "(0::int) < 2 ^ k'" and jpos0: "(0::int) < 2 ^ k" by simp_all
  have AB0: "A0 < B0" using AB lo hi by simp
  \<comment> \<open>the two \<open>carried_init_same_den\<close>/\<open>window_child_formula\<close> definitions are byte-identical.\<close>
  have child_eq: "carried_init_same_den l' (2 ^ k') r' xs = window_child_formula l' (2 ^ k') r' xs"
    and node_eq: "carried_init_same_den l (2 ^ k) r xs = window_child_formula l (2 ^ k) r xs"
    by (simp_all add: carried_init_same_den_def window_child_formula_def)
  have repr_child: "carried_repr_scalar xs A B (carried_init_same_den l' (2 ^ k') r' xs)"
    unfolding child_eq A_def B_def by (rule window_child_formula_repr_scalar[OF jpos])
  have repr_node: "carried_repr_scalar xs A0 B0 (carried_init_same_den l (2 ^ k) r xs)"
    unfolding node_eq A0_def B0_def by (rule window_child_formula_repr_scalar[OF jpos0])
  have cnt_child: "carried_descartes_count (carried_init_same_den l' (2 ^ k') r' xs)
      = descartes_list_int A B xs"
    unfolding carried_descartes_count_def
    using carried_repr_scalar_count[OF repr_child len] AB by simp
  have cnt_node: "carried_descartes_count (carried_init_same_den l (2 ^ k) r xs)
      = descartes_list_int A0 B0 xs"
    unfolding carried_descartes_count_def
    using carried_repr_scalar_count[OF repr_node len] AB0 by simp
  have degP: "degree P \<le> length xs - 1"
  proof -
    have "degree P \<le> degree (Poly xs)" unfolding P_def by (rule degree_map_poly_le)
    also have "\<dots> \<le> length xs - 1"
      using len by (simp add: degree_le coeff_Poly nth_default_beyond)
    finally show ?thesis .
  qed
  have rlo: "real_of_rat A0 \<le> real_of_rat A" using lo by (simp add: of_rat_less_eq)
  have rAB: "real_of_rat A < real_of_rat B" using AB by (simp add: of_rat_less)
  have rhi: "real_of_rat B \<le> real_of_rat B0" using hi by (simp add: of_rat_less_eq)
  have "int (descartes_list_int A B xs)
      = Bernstein_changes (length xs - 1) (real_of_rat A) (real_of_rat B) P"
    unfolding P_def using descartes_list_int_eq_Bernstein_changes[OF len AB] by simp
  also have "\<dots> \<le> Bernstein_changes (length xs - 1) (real_of_rat A0) (real_of_rat B0) P"
    using Bernstein_changes_subinterval_mono[OF rlo rAB rhi degP] .
  also have "\<dots> = int (descartes_list_int A0 B0 xs)"
    unfolding P_def using descartes_list_int_eq_Bernstein_changes[OF len AB0] by simp
  finally have "descartes_list_int A B xs \<le> descartes_list_int A0 B0 xs" by simp
  thus ?thesis using cnt_child cnt_node by simp
qed

text \<open>\<^bold>\<open>The payload bound's \<open>mono\<close> at the split children\<close>, the only instance the
  invariant's preservation needs, stated at the pushed columns' own values so no
  @{const carried_left}/@{const carried_right} rewrite has to reach the arm's closers.

  Both children are @{thm [source] carried_count_subinterval_mono} at \<open>k' = k + 1\<close>: the left
  half shares the parent's left endpoint (\<open>2l/2\<^sup>k\<^sup>+\<^sup>1 = l/2\<^sup>k\<close>) and the right half its right one,
  so in each case one of the two containment sides is an equality and the other is
  \<open>l \<le> r\<close>. \<open>lr\<close> is what the non-degeneracy is for: the subinterval lemma's \<open>A < B\<close> is
  \<open>2l < l + r\<close> on the left and \<open>l + r < 2r\<close> on the right, and both are exactly \<open>l < r\<close>.\<close>
lemma hybrid_split_child_count_mono:
  fixes l r :: int and k :: nat
  assumes lr: "l < r" and len: "0 < length rp"
  shows "carried_descartes_count (carried_init_same_den (2 * l) (2 ^ (k + 1)) (l + r) rp)
           \<le> carried_descartes_count (carried_init_same_den l (2 ^ k) r rp)"
    and "carried_descartes_count (carried_init_same_den (l + r) (2 ^ (k + 1)) (2 * r) rp)
           \<le> carried_descartes_count (carried_init_same_den l (2 ^ k) r rp)"
  \<comment> \<open>\<^bold>\<open>Every step through \<open>divide_\<open>{strict_,}\<close>right_mono\<close>, never through \<open>simp\<close> on the
     inequality itself.\<close> The \<open>defines\<close> of @{thm [source] carried_count_subinterval_mono} hand
     back the six goals VERBATIM (probed), but \<open>simp\<close> normalises \<open>2\<cdot>l / 2\<^sup>k\<^sup>+\<^sup>1\<close> to \<open>l / 2\<^sup>k\<close> on
     sight -- so a \<open>have\<close> stated in the un-normalised form and proved by \<open>simp\<close> loses the very
     shape the \<open>rule\<close> needs. The two \<open>eq\<close> facts are where the halving is allowed to happen.\<close>
proof -
  have il: "2 * l \<le> l + r" and ir: "l + r \<le> 2 * r"
    and sl: "2 * l < l + r" and sr: "l + r < 2 * r" using lr by linarith+
  have eqL: "rat_of_int (2 * l) / rat_of_int (2 ^ (k + 1)) = rat_of_int l / rat_of_int (2 ^ k)"
    and eqR: "rat_of_int (2 * r) / rat_of_int (2 ^ (k + 1)) = rat_of_int r / rat_of_int (2 ^ k)"
    by simp_all
  have s1: "rat_of_int (2 * l) / rat_of_int (2 ^ (k + 1))
              < rat_of_int (l + r) / rat_of_int (2 ^ (k + 1))"
    by (intro divide_strict_right_mono) (use sl in simp_all)
  have s2: "rat_of_int (l + r) / rat_of_int (2 ^ (k + 1))
              < rat_of_int (2 * r) / rat_of_int (2 ^ (k + 1))"
    by (intro divide_strict_right_mono) (use sr in simp_all)
  have loL: "rat_of_int l / rat_of_int (2 ^ k)
               \<le> rat_of_int (2 * l) / rat_of_int (2 ^ (k + 1))"
    using eqL by simp
  have hiR: "rat_of_int (2 * r) / rat_of_int (2 ^ (k + 1))
               \<le> rat_of_int r / rat_of_int (2 ^ k)"
    using eqR by simp
  have hiL: "rat_of_int (l + r) / rat_of_int (2 ^ (k + 1))
               \<le> rat_of_int r / rat_of_int (2 ^ k)"
  proof -
    have "rat_of_int (l + r) / rat_of_int (2 ^ (k + 1))
            \<le> rat_of_int (2 * r) / rat_of_int (2 ^ (k + 1))"
      by (intro divide_right_mono) (use ir in simp_all)
    thus ?thesis using eqR by simp
  qed
  have loR: "rat_of_int l / rat_of_int (2 ^ k)
               \<le> rat_of_int (l + r) / rat_of_int (2 ^ (k + 1))"
  proof -
    have "rat_of_int (2 * l) / rat_of_int (2 ^ (k + 1))
            \<le> rat_of_int (l + r) / rat_of_int (2 ^ (k + 1))"
      by (intro divide_right_mono) (use il in simp_all)
    thus ?thesis using eqL by simp
  qed
  show "carried_descartes_count (carried_init_same_den (2 * l) (2 ^ (k + 1)) (l + r) rp)
          \<le> carried_descartes_count (carried_init_same_den l (2 ^ k) r rp)"
    by (rule carried_count_subinterval_mono[OF len s1 loL hiL])
  show "carried_descartes_count (carried_init_same_den (l + r) (2 ^ (k + 1)) (2 * r) rp)
          \<le> carried_descartes_count (carried_init_same_den l (2 ^ k) r rp)"
    by (rule carried_count_subinterval_mono[OF len s2 loR hiR])
qed

text \<open>\<^bold>\<open>The window arm's \<open>v\<close> contract is a disjunction.\<close>
  @{const hybrid_window_v_monadic} has three branches, not the one
  @{thm [source] hybrid_window_v_cached} covers:
  (1) \<open>4 \<le> cnt\<close> reads the cached class and returns \<open>cnt - 2\<close>, which
  @{const dyadic_iv_cs_invar}'s \<open>4 \<le> c \<longrightarrow> c = cnt + 2\<close> clause pins to the exact count;
  (2) \<open>2\<^sup>4\<^sup>2 + 2 \<le> g\<close> runs the capped kernel at the parent's payload \<open>b = g - 2\<^sup>4\<^sup>2\<close>;
  (3) otherwise the exact kernel, again the exact count.

  \<^bold>\<open>Branch 2 is why this cannot be an equality.\<close>
  @{thm [source] carried_descartes_count_trunc_cap_monadic_classify} gives
  \<open>(r < cap \<longrightarrow> r = count) \<and> (cap \<le> r \<longrightarrow> cap \<le> count)\<close>, so the returned \<open>min b r\<close> is the exact
  count only when \<open>count \<le> b\<close>, i.e. only when the node's lock payload bounds its own count.
  That is a fact about the invariant, not about this op: this lemma
  states what the op guarantees unconditionally, and the payload bound is discharged
  separately.

  \<^bold>\<open>What it is for.\<close> @{const hybrid_gate_open_monadic} asserts \<open>int v < max_sint\<close> and
  \<open>2\<^sup>4\<^sup>2 + v < max_snat\<close>; both follow from this disjunction plus the caller's own
  \<open>X_gbound\<close>/guard cap, with no need to pin \<open>v\<close>'s value. Pinning it is only required one
  layer up, where @{thm [source] hybrid_window_choice_abs} wants \<open>count \<le> v\<close>.\<close>
lemma hybrid_window_v_bound:
  assumes inv: "dyadic_iv_cs_invar cnt (carried_descartes_count Q)"
    and Qb: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_window_v_monadic cnt g Q
       \<le> SPEC (\<lambda>v. v \<le> carried_descartes_count Q \<or> v \<le> g - 4398046511104)"
proof (cases "4 \<le> cnt")
  case cached: True
  show ?thesis
    unfolding hybrid_window_v_monadic_def PR_CONST_def
    using cached inv by (simp add: dyadic_iv_cs_invar_def)
next
  case ncached: False
  show ?thesis
  proof (cases "4398046511106 \<le> g")
    case payload: True
    have b2: "(2::nat) \<le> g - 4398046511104" using payload by simp
    show ?thesis
      unfolding hybrid_window_v_monadic_def PR_CONST_def
      using ncached payload
      apply simp
      apply (refine_vcg
          carried_descartes_count_trunc_cap_monadic_classify[OF Qb b2, THEN order_trans])
      \<comment> \<open>the op's own \<open>ASSERT (length Q + 1 < max_snat)\<close> survives here and must have \<open>Qb\<close>
         INSERTED -- a word bound as a simp rule cannot close a goal that IS that bound.\<close>
      apply (all \<open>((insert Qb, simp); fail)?\<close>)
      done
  next
    case exact: False
    show ?thesis
      unfolding hybrid_window_v_monadic_def PR_CONST_def
      using ncached exact
      apply simp
      apply (rule order_trans[OF carried_descartes_count_exact_monadic_correct[OF Qb]])
      apply simp
      done
  qed
qed

text \<open>\<^bold>\<open>With the payload bound, the \<open>v\<close> contract collapses to an EQUALITY in all three
  branches\<close> -- and that is what the window arm actually consumes.
  @{thm [source] blr_window_choice_refine_bl} needs \<open>2 \<le> v\<close> and
  \<open>carried_descartes_count Q \<le> v\<close>; @{thm [source] hybrid_window_v_bound} states only what the
  op guarantees unconditionally, which in the capped branch is the WRONG direction.

  \<^bold>\<open>\<open>pay\<close> is the invariant conjunct the window arm needs\<close>: at a
  LOCKED node the payload bounds the node's own count. It is a premise here and is discharged
  from the coupling at the call site. Every case of its preservation is available:
  a window-pushed child has \<open>count = v = glock - 2\<^sup>4\<^sup>2\<close> EXACTLY by
  @{thm [source] newton_window_pick_bail_count}; a locked node's split children inherit the
  payload and shrink the interval, so @{thm [source] carried_count_subinterval_mono} applies; and
  every unlocked push stores a guard \<open>< 2\<^sup>4\<^sup>2\<close>, which falsifies the antecedent.

  Branch by branch, with \<open>b = g - 2\<^sup>4\<^sup>2\<close>:
  the \<open>cs\<close> cache gives \<open>cnt - 2 = count\<close> outright; the exact kernel gives \<open>count\<close>; and the capped
  kernel returns \<open>if b \<le> r then b else r\<close>, where
  @{thm [source] carried_descartes_count_trunc_cap_monadic_classify}'s two halves give \<open>r = count\<close> on
  \<open>r < b\<close> and \<open>b \<le> count\<close> on \<open>b \<le> r\<close> -- and \<open>pay\<close> supplies the opposite inequality, pinning
  \<open>b = count\<close>. So the capped branch is exact too, not merely bounded.\<close>
lemma hybrid_window_v_exact:
  assumes inv: "dyadic_iv_cs_invar cnt (carried_descartes_count Q)"
    and Qb: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count Q \<le> g - 4398046511104"
    and c2: "2 \<le> carried_descartes_count Q"
  \<comment> \<open>\<^bold>\<open>The \<open>2 \<le> v\<close> conjunct is not decoration.\<close> It is
     @{thm [source] blr_window_choice_refine_bl}'s other premise, so the arm wants both facts
     from one \<open>refine_vcg\<close> step -- and stating the postcondition as a bare equality collapses
     \<open>SPEC (\<lambda>v. v = c)\<close> to \<open>RES {c}\<close>, which \<open>refine_vcg\<close> will not decompose a bind against.\<close>
  shows "hybrid_window_v_monadic cnt g Q
       \<le> SPEC (\<lambda>v. v = carried_descartes_count Q \<and> 2 \<le> v)"
proof (cases "4 \<le> cnt")
  case cached: True
  show ?thesis
    unfolding hybrid_window_v_monadic_def PR_CONST_def
    using cached inv c2 by (simp add: dyadic_iv_cs_invar_def)
next
  case ncached: False
  show ?thesis
  proof (cases "4398046511106 \<le> g")
    case payload: True
    have b2: "(2::nat) \<le> g - 4398046511104" using payload by simp
    have cle: "carried_descartes_count Q \<le> g - 4398046511104" using pay payload by simp
    show ?thesis
      unfolding hybrid_window_v_monadic_def PR_CONST_def
      using ncached payload
      apply simp
      \<comment> \<open>\<^bold>\<open>Bail's structure\<close> (\<open>Newton.thy\<close>,
         @{thm [source] carried_try_window_monadic_correct}), not hand-rolled arithmetic: pass
         @{thm [source] cap_count_match_mono_trunc} ALONGSIDE the classify. It is purpose-built for the
         cap-at-\<open>v\<close> step and, given \<open>cle\<close>, yields \<open>(b \<le> r) = (count Q = b)\<close> -- which DECIDES
         the \<open>if\<close> rather than leaving a residual to close. Conjoined by
         @{thm [source] cdlr_SPEC_conj} because \<open>refine_vcg\<close> applies only ONE \<open>\<le> SPEC\<close> fact per
         producer call.\<close>
      apply (refine_vcg
          cdlr_SPEC_conj[OF carried_descartes_count_trunc_cap_monadic_classify[OF Qb b2]
                            cap_count_match_mono_trunc[OF Qb b2 cle], THEN order_trans])
      apply (all \<open>((insert Qb c2 b2 cle, auto); fail)?\<close>)
      done
  next
    case exact: False
    show ?thesis
      unfolding hybrid_window_v_monadic_def PR_CONST_def
      using ncached exact
      apply simp
      apply (rule order_trans[OF carried_descartes_count_exact_monadic_correct[OF Qb]])
      apply (insert c2, simp)
      done
  qed
qed

text \<open>\<^bold>\<open>The guard half of @{thm [source] truncate_children_mid_agrees}\<close>, stated over the same op
  so the two conjoin by @{thm [source] cdlr_SPEC_conj} at any call site.

  \<^bold>\<open>Stated with RAW arithmetic conjuncts, deliberately.\<close> The opaque
  @{const hybrid_child_gok} is an INTERFACE device — it exists to keep the payload inert in
  the \<open>auto simp: max_def\<close> closers of @{thm [source] hybrid_branch_split_exact_productive}
  and \<open>_exact_acc\<close>, five hops downstream. Using it HERE was a category error that cost three
  cycles: @{thm [source] truncate_children_mid_agrees} discharges the identical \<open>refine_vcg\<close>
  residue (the tuple chain \<open>x2b = (x1c, x2c)\<close>, \<open>x2a = (x1b, x2b)\<close>, \<dots>) with a plain
  \<open>(simp; fail)?\<close>, and it can do so ONLY because its conjuncts are arithmetic that \<open>simp\<close>
  rewrites straight THROUGH the chain. An opaque atom gives \<open>simp\<close> nothing to drive, the chain
  never resolves, and \<open>x1a\<close>/\<open>x1c\<close> stall unsubstituted. So: prove transparently here, wrap
  opaquely in \<open>truncate_children_mid_gok\<close> below.

  Branch by branch:
  \<^item> \<open>g = 0\<close>: @{const truncate_child_guards_mop} passes \<open>(0,0)\<close> through, so the children's guards
    are \<open>\<le> max 0 1 = 1 \<le> length Q\<close> — this is where \<open>Qne\<close> is load-bearing, and it must be
    INSERTED in \<open>Suc\<close> form (\<open>simp\<close> normalizes \<open>0 < length Q\<close> to \<open>Q \<noteq> []\<close> by
    @{thm [source] length_greater_0_conv} and then cannot chain the arithmetic). The lock
    conjuncts are vacuous.
  \<^item> LOCK (\<open>2\<^sup>4\<^sup>2 \<le> g\<close>): the guard op returns \<open>(g,g)\<close> and the retrunc is the IDENTITY, so
    \<open>gl = g\<close> EXACTLY. An upper bound would not do — the lock conjunct needs a LOWER bound, and
    only @{thm [source] cdlr_retrunc_child_lock} supplies it. That lemma IS pinned to its child,
    so this branch keeps two \<open>refine_vcg\<close> steps where the others need one.
  \<^item> unlocked: \<open>g_tri\<close> gives \<open>g < 2\<^sup>4\<^sup>0\<close>, so neither saturation branch fires and the guards are
    \<open>(g + len - 1, g + len)\<close>. The lock conjuncts are vacuous again.

  \<^bold>\<open>One \<open>refine_vcg\<close> covers BOTH retruncs\<close> in the \<open>g = 0\<close> and unlocked branches: unlike
  @{thm [source] cdlr_retrunc_child}, @{thm [source] cdlr_retrunc_child_gbound} is premise-free,
  so it is not pinned to one child and fires twice — a second \<open>refine_vcg\<close> then has no goal
  left and ERRORS.\<close>
lemma truncate_children_mid_gbounds:
  assumes g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
  shows "truncate_children_mid_monadic g Q \<le> SPEC (\<lambda>(ql, gl, qr, gr, mids, midbl).
           gl \<le> g + length Q \<and> gr \<le> g + length Q \<and>
           (4398046511104 \<le> g \<longrightarrow> gl = g) \<and>
           (4398046511104 \<le> g \<longrightarrow> gr = g))"
proof -
  have lr_step: "carried_left_right_monadic Q \<bind> f
      \<le> f (carried_left Q, carried_right Q)" for f
  proof -
    have "carried_left_right_monadic Q \<bind> f
        \<le> RETURN (carried_left Q, carried_right Q) \<bind> f"
      by (rule bind_mono(1)[OF carried_left_right_monadic_correct[OF Qne Qbound]]) simp
    also have "\<dots> = f (carried_left Q, carried_right Q)" by simp
    finally show ?thesis .
  qed
  have lb_l: "length (carried_left Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lb_r: "length (carried_right Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qbound by simp_all
  have lne: "0 < length (carried_left Q)" and rne: "0 < length (carried_right Q)"
    using Qne by simp_all
  have rneL: "carried_right Q \<noteq> []"
    using rne length_greater_0_conv[of "carried_right Q"] by blast
  have Qlen1: "Suc 0 \<le> length Q" using Qne by linarith
  show ?thesis
  proof (cases "g = 0")
    case g0: True
    show ?thesis
      unfolding truncate_children_mid_monadic_def truncate_child_guards_mop_def
        poly_length_monadic_def poly_coeff_sgn_monadic_def
        poly_coeff_bitlen2_monadic_def PR_CONST_def
      using Qne Qbound
      apply (simp add: g0)
      apply (rule order_trans[OF lr_step])
      apply (simp add: lb_l rne)
      apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
          cdlr_retrunc_child_gbound[THEN order_trans])
      \<comment> \<open>\<^bold>\<open>\<open>clarsimp\<close> is the DESTRUCTURING step, not a cosmetic one.\<close> \<open>refine_vcg\<close> leaves the
         postcondition against raw tuple variables with the split supplied only as a chain of
         equations (\<open>x2b = (x1c, x2c)\<close>, \<open>x2a = (x1b, x2b)\<close>, \<dots>); plain \<open>simp\<close> does the
         arithmetic but never resolves that chain, so \<open>x1a\<close>/\<open>x1c\<close> stall. \<open>agrees\<close> gets this for
         free from the \<open>clarsimp\<close> it runs BETWEEN its two \<open>refine_vcg\<close> steps — dropping the
         second \<open>refine_vcg\<close> (correct: \<open>gbound\<close> is premise-free and fires twice) deleted that
         step along with it. Cost: 3 cycles.
         The closer is an ALTERNATION of COMPLETE tactics because \<open>clarsimp\<close> closes one of the
         two goals outright — a trailing \<open>insert\<close>/\<open>linarith\<close> would then fail on
         \<open>no subgoals\<close> and roll the whole chain back.\<close>
      apply (all \<open>(simp add: rneL; fail)?\<close>)
      apply (all \<open>clarsimp\<close>)
      apply (all \<open>(insert Qlen1, linarith)\<close>)
      done
  next
    case g_ne0: False
    show ?thesis
    proof (cases "4398046511104 \<le> g")
      case glock: True
      show ?thesis
        unfolding truncate_children_mid_monadic_def truncate_child_guards_mop_def
          poly_length_monadic_def poly_coeff_sgn_monadic_def
          poly_coeff_bitlen2_monadic_def PR_CONST_def
        using Qne Qbound
        apply (simp add: g_ne0 glock)
        apply (rule order_trans[OF lr_step])
        apply (simp add: lb_l rne)
        apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
            cdlr_retrunc_child_lock[OF glock lne lb_l, THEN order_trans])
        apply (all \<open>(simp add: rneL; fail)?\<close>)
        apply (clarsimp simp: lb_r)
        apply (refine_vcg cdlr_retrunc_child_lock[OF glock rne lb_r, THEN order_trans])
        apply (all \<open>(simp add: rneL; fail)?\<close>)
        apply (all \<open>clarsimp\<close>)
        \<comment> \<open>\<open>clarsimp\<close> discharges the guard EQUALITY \<open>gl = g\<close> from
           @{thm [source] cdlr_retrunc_child_lock}'s \<open>g' = gin\<close> and leaves the implication's
           ANTECEDENT \<open>2\<^sup>4\<^sup>2 \<le> g\<close> as the goal -- which is \<open>glock\<close> itself.\<close>
        apply (all \<open>(insert glock, simp)\<close>)
        done
    next
      case gsmall: False
      have g_win: "g < 1099511627776" using g_tri gsmall by simp
      have not_g40: "\<not> 1099511627776 \<le> g" using g_win by simp
      have not_len40: "\<not> 1099511627776 \<le> length Q" using Q_small by simp
      have QneL: "Q \<noteq> []" using Qne by simp
      have gplen: "g + length Q < max_snat LENGTH(gmp_poly_len)"
        using g_win Q_small unfolding max_snat_def by simp
      \<comment> \<open>collapse the \<open>max \<dots> 1\<close> that @{thm [source] cdlr_retrunc_child_gbound} introduces, so the
         closer faces plain arithmetic instead of a case split. Needs \<open>g \<noteq> 0\<close>, and the \<open>Suc\<close>
         form of the length — \<open>simp\<close> would normalize \<open>Qne\<close> away first.\<close>
      obtain nQ where lenQ: "length Q = Suc nQ" using Qne by (cases "length Q") auto
      have mx_l: "max (g + length Q - Suc 0) 1 = g + length Q - Suc 0"
        using g_ne0 unfolding lenQ by (simp add: max_def)
      have mx_r: "max (g + length Q) 1 = g + length Q"
        using g_ne0 unfolding lenQ by (simp add: max_def)
      have dle: "g + length Q - Suc 0 \<le> g + length Q" by simp
      \<comment> \<open>\<^bold>\<open>Both literal forms.\<close> \<open>refine_vcg\<close> presents the guard as \<open>max \<dots> (Suc 0)\<close>, on which the
         \<open>1\<close>-form rule does not fire.\<close>
      have mx_lS: "max (g + length Q - Suc 0) (Suc 0) = g + length Q - Suc 0"
        using g_ne0 unfolding lenQ by (simp add: max_def)
      have mx_rS: "max (g + length Q) (Suc 0) = g + length Q"
        using g_ne0 unfolding lenQ by (simp add: max_def)
      show ?thesis
        unfolding truncate_children_mid_monadic_def truncate_child_guards_mop_def
          poly_length_monadic_def poly_coeff_sgn_monadic_def
          poly_coeff_bitlen2_monadic_def PR_CONST_def
        apply (simp add: g_ne0 gsmall not_g40 not_len40 QneL g_win Q_small gplen)
        apply (rule ASSERT_leI)
        subgoal using gplen by simp
        apply (rule order_trans[OF lr_step])
        apply (simp add: lb_l rne)
        apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
            cdlr_retrunc_child_gbound[THEN order_trans])
        \<comment> \<open>same destructuring step as the \<open>g = 0\<close> branch; \<open>mx_l\<close>/\<open>mx_r\<close> collapse the \<open>max \<dots> 1\<close>
           so no case split is needed, and the left child's residue is pure transitivity
           through the NAT subtraction (@{thm [source] diff_le_self}), which \<open>linarith\<close> alone
           cannot do.\<close>
        apply (all \<open>(simp add: rneL Qbound; fail)?\<close>)
        apply (all \<open>(clarsimp simp: mx_l mx_r mx_lS mx_rS)?\<close>)
        \<comment> \<open>\<^bold>\<open>Two residues needing OPPOSITE tactics, peeled DETERMINISTICALLY.\<close> The leftover
           word bound \<open>Suc (length Q) < max_snat\<close> must have \<open>Qbound\<close> INSERTED, never
           simp-added — a bound as a rewrite cannot close a goal that IS that bound, and
           @{thm [source] truncate_children_mid_agrees} discharges the identical subgoal with
           \<open>subgoal using Qbound by simp\<close> for exactly that reason. The left child's residue is
           instead transitivity through the NAT subtraction, where \<open>dle\<close> lets \<open>linarith\<close> treat
           \<open>g + length Q - Suc 0\<close> as an atom bounded by \<open>g + length Q\<close>. Expressing that as an
           ALTERNATION of two complete tactics spun past the tripwire — both branches share the
           \<open>insert\<close> prefix, so the search re-runs it on every backtrack. Peel the word bound
           with an explicit \<open>subgoal\<close> instead, as the analog does.\<close>
        subgoal using Qbound by simp
        apply (all \<open>(insert dle g_win, linarith)\<close>)
        done
    qed
  qed
qed

text \<open>\<^bold>\<open>The opaque restatement — the ONLY form that travels.\<close> A SPEC weakening of
  @{thm [source] truncate_children_mid_gbounds} into @{const hybrid_child_gok}, via the
  \<open>SPEC_cons_rule\<close> idiom this file already uses at
  @{thm [source] hybrid_window_choice_abs}. From here down the payload is two inert atoms:
  \<open>auto\<close>, \<open>clarsimp\<close>, \<open>max_def\<close> and \<open>linarith\<close> can neither decompose, case-split nor rewrite
  them, so the arm lemmas carry them by \<open>assumption\<close> exactly as they already carry
  @{const hybrid_cs_ok}.\<close>
lemma truncate_children_mid_gok:
  assumes g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
  shows "truncate_children_mid_monadic g Q \<le> SPEC (\<lambda>(ql, gl, qr, gr, mids, midbl).
           hybrid_child_gok g (length Q) gl \<and> hybrid_child_gok g (length Q) gr)"
  by (rule SPEC_cons_rule[OF truncate_children_mid_gbounds[OF g_tri Qne Qbound Q_small ]])
     (auto simp: hybrid_child_gok_def)

text \<open>\<^bold>\<open>The g-carrying eta twin.\<close> A clone of \<open>truncate_children_mid_decide_bind_eta\<close>'s script
  with @{thm [source] cdlr_SPEC_conj} splicing @{thm [source] truncate_children_mid_gok}'s two
  atoms alongside @{thm [source] truncate_children_mid_agrees}'s conclusion, so \<open>cont\<close> gains
  exactly two inert hypotheses.

  \<^bold>\<open>A NEW twin rather than a widening of the existing three.\<close> The existing twins have exactly
  two live consumers between them (\<open>hybrid_branch_split_exact_acc\<close> and
  \<open>hybrid_branch_split_acc\<close>); \<open>_decomp\<close> has NONE. Widening them in place would force
  \<open>hybrid_branch_split_exact_productive\<close> and \<open>_exact_acc\<close> — the two lemmas whose
  \<open>auto simp: max_def\<close> closers are the ones a wider \<open>cont\<close> could actually hurt — back through the
  loop, and would put the freeze marker above \<open>:167\<close>. This way they are never touched.\<close>
lemma truncate_children_mid_decide_gbind:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    and cont: "\<And>ql gl qr gr code.
        \<lbrakk> node_frame (carried_left X) ql gl; node_frame (carried_right X) qr gr;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_gok g (length Q) gl; hybrid_child_gok g (length Q) gr;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          4398046511104 \<le> gr \<longrightarrow> qr = carried_right X;
          code = 1 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          code = 0 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0;
          g = 0 \<or> 4398046511104 \<le> g \<longrightarrow> code \<noteq> 2;
          code = 0 \<or> code = 1 \<or> code = 2 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr code \<le> SPEC \<Phi>"
  shows "doN { (ql, gl, qr, gr, mids, midbl) \<leftarrow> truncate_children_mid_monadic g Q;
               code \<leftarrow> truncate_mid_decide_monadic g len mids midbl;
               f ql gl qr gr code }
       \<le> SPEC \<Phi>"
  apply (refine_vcg
      cdlr_SPEC_conj[OF truncate_children_mid_agrees[OF frame lock g_tri Qne Qbound Q_small]
        truncate_children_mid_gok[OF g_tri Qne Qbound Q_small ], THEN order_trans])
  apply clarsimp
  apply (refine_vcg
      truncate_mid_decide_agrees[OF frame lock len_eq Qne Q_small, THEN order_trans])
  apply (all \<open>(simp; fail)?\<close>)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

lemma truncate_children_mid_decide_gbind_eta:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and len_eq: "len = length Q"
    \<comment> \<open>\<^bold>\<open>The atoms stay at \<open>length Q\<close>; do NOT add a length parameter here.\<close> The invariant wants
       the bound over \<open>length rp\<close>, and a \<open>glen\<close> parameter with \<open>glen = length Q\<close> looks like the
       clean place to convert — but \<open>cont\<close> is an ASSUMPTION, so an \<open>unfolding\<close> never reaches it,
       and pushing \<open>glen_eq\<close> into the closer instead costs a \<open>simp\<close> across all twelve \<open>cont\<close>
       goals and trips the wire. \<open>length Q = length rp\<close> is free from the frame at the ONE site
       that consumes the atom, so convert there and keep every closer here untouched.\<close>
    and cont: "\<And>ql gl qr gr code.
        \<lbrakk> node_frame (carried_left X) ql gl; node_frame (carried_right X) qr gr;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_gok g (length Q) gl; hybrid_child_gok g (length Q) gr;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          4398046511104 \<le> gr \<longrightarrow> qr = carried_right X;
          code = 1 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          code = 0 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0;
          g = 0 \<or> 4398046511104 \<le> g \<longrightarrow> code \<noteq> 2;
          code = 0 \<or> code = 1 \<or> code = 2 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr code \<le> SPEC \<Phi>"
  shows "truncate_children_mid_monadic g Q
       \<le> SPEC (\<lambda>x. (case x of (ql, gl, qr, gr, mids, midbl) \<Rightarrow>
             truncate_mid_decide_monadic g len mids midbl \<bind> (\<lambda>code. f ql gl qr gr code))
           \<le> SPEC \<Phi>)"
  apply (refine_vcg
      cdlr_SPEC_conj[OF truncate_children_mid_agrees[OF frame lock g_tri Qne Qbound Q_small]
        truncate_children_mid_gok[OF g_tri Qne Qbound Q_small ], THEN order_trans])
  apply clarsimp
  apply (refine_vcg
      truncate_mid_decide_agrees[OF frame lock len_eq Qne Q_small, THEN order_trans])
  apply (all \<open>(simp; fail)?\<close>)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

text \<open>\<^bold>\<open>The guard half of the skip-right children build.\<close> The analogue of
  @{thm [source] truncate_children_mid_gbounds} over @{const truncate_children_mid_skip_right_monadic}.
  The guards come from @{const truncate_child_guards_mop} and never see the children, and on
  \<open>rz\<close> the stub's retruncation returns its input guard verbatim, so every bound survives. The one
  new step is the case split on \<open>rz\<close>, which the op's \<open>ASSERT (0 < length qr)\<close> needs.\<close>
lemma truncate_children_mid_skip_right_gbounds:
  assumes g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_children_mid_skip_right_monadic g Q \<le> SPEC (\<lambda>(ql, gl, qr, gr, mids, midbl, rz).
           gl \<le> g + length Q \<and> gr \<le> g + length Q \<and>
           (4398046511104 \<le> g \<longrightarrow> gl = g) \<and>
           (4398046511104 \<le> g \<longrightarrow> gr = g))"
proof -
  have lb_l: "length (carried_left Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lb_r: "length (carried_right Q) + 1 < max_snat LENGTH(gmp_poly_len)"
    using Qbound by simp_all
  have lne: "0 < length (carried_left Q)" and rne: "0 < length (carried_right Q)"
    using Qne by simp_all
  have rneL: "carried_right Q \<noteq> []"
    using rne length_greater_0_conv[of "carried_right Q"] by blast
  have Qlen1: "Suc 0 \<le> length Q" using Qne by linarith
  have stub_rt: "carried_retrunc_mop [s] h \<le> SPEC (\<lambda>(ys, h'). ys = [s] \<and> h' = h)" for s h
    unfolding carried_retrunc_mop_def poly_length_monadic_def PR_CONST_def by simp
  show ?thesis
  proof (cases "g = 0")
    case g0: True
    show ?thesis
      unfolding truncate_children_mid_skip_right_monadic_def truncate_child_guards_mop_def
        poly_length_monadic_def poly_coeff_sgn_monadic_def
        poly_coeff_bitlen2_monadic_def PR_CONST_def
      using Qne Qbound Qbound2 dep
      apply (simp add: g0)
      apply (rule carried_left_right_skip_right_bind[where g = 0, OF Qne Qbound2 dep])
      subgoal using Qbound by simp
      subgoal for r rz
        apply (cases rz)
        subgoal
          apply (simp add: lb_l)
          apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
              cdlr_retrunc_child_gbound[THEN order_trans] stub_rt[THEN order_trans])
          apply (all \<open>(simp; fail)?\<close>)
          apply (all \<open>clarsimp\<close>)
          apply (all \<open>(insert Qlen1, linarith)\<close>)
          done
        subgoal
          apply (simp add: lb_l rne)
          apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
              cdlr_retrunc_child_gbound[THEN order_trans])
          apply (all \<open>(simp add: rneL; fail)?\<close>)
          apply (all \<open>clarsimp\<close>)
          apply (all \<open>(insert Qlen1, linarith)\<close>)
          done
        done
      done
  next
    case g_ne0: False
    show ?thesis
    proof (cases "4398046511104 \<le> g")
      case glock: True
      show ?thesis
        unfolding truncate_children_mid_skip_right_monadic_def truncate_child_guards_mop_def
          poly_length_monadic_def poly_coeff_sgn_monadic_def
          poly_coeff_bitlen2_monadic_def PR_CONST_def
        using Qne Qbound Qbound2 dep
        apply (simp add: g_ne0 glock)
        apply (rule carried_left_right_skip_right_bind[OF Qne Qbound2 dep kb])
        subgoal for r rz
          apply (cases rz)
          subgoal
            apply (simp add: lb_l)
            apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
                cdlr_retrunc_child_lock[OF glock lne lb_l, THEN order_trans]
                stub_rt[THEN order_trans])
            apply (all \<open>(simp; fail)?\<close>)
            apply (all \<open>clarsimp\<close>)
            apply (all \<open>(insert glock, simp)\<close>)
            done
          subgoal
            apply (simp add: lb_l rne)
            apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
                cdlr_retrunc_child_lock[OF glock lne lb_l, THEN order_trans])
            apply (all \<open>(simp add: rneL; fail)?\<close>)
            apply (clarsimp simp: lb_r)
            apply (refine_vcg cdlr_retrunc_child_lock[OF glock rne lb_r, THEN order_trans])
            apply (all \<open>(simp add: rneL; fail)?\<close>)
            apply (all \<open>clarsimp\<close>)
            apply (all \<open>(insert glock, simp)\<close>)
            done
          done
        done
    next
      case gsmall: False
      have g_win: "g < 1099511627776" using g_tri gsmall by simp
      have not_g40: "\<not> 1099511627776 \<le> g" using g_win by simp
      have not_len40: "\<not> 1099511627776 \<le> length Q" using Q_small by simp
      have QneL: "Q \<noteq> []" using Qne by simp
      have gplen: "g + length Q < max_snat LENGTH(gmp_poly_len)"
        using g_win Q_small unfolding max_snat_def by simp
      obtain nQ where lenQ: "length Q = Suc nQ" using Qne by (cases "length Q") auto
      have mx_l: "max (g + length Q - Suc 0) 1 = g + length Q - Suc 0"
        using g_ne0 unfolding lenQ by (simp add: max_def)
      have mx_r: "max (g + length Q) 1 = g + length Q"
        using g_ne0 unfolding lenQ by (simp add: max_def)
      have dle: "g + length Q - Suc 0 \<le> g + length Q" by simp
      have mx_lS: "max (g + length Q - Suc 0) (Suc 0) = g + length Q - Suc 0"
        using g_ne0 unfolding lenQ by (simp add: max_def)
      have mx_rS: "max (g + length Q) (Suc 0) = g + length Q"
        using g_ne0 unfolding lenQ by (simp add: max_def)
      show ?thesis
        unfolding truncate_children_mid_skip_right_monadic_def truncate_child_guards_mop_def
          poly_length_monadic_def poly_coeff_sgn_monadic_def
          poly_coeff_bitlen2_monadic_def PR_CONST_def
        using Qne Qbound Qbound2 dep
        apply (simp add: g_ne0 gsmall not_g40 not_len40 QneL g_win Q_small gplen)
        apply (rule ASSERT_leI)
        subgoal using gplen by simp
        apply (rule carried_left_right_skip_right_bind[OF Qne Qbound2 dep kb])
        subgoal for r rz
          apply (cases rz)
          subgoal
            apply (simp add: lb_l)
            apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
                cdlr_retrunc_child_gbound[THEN order_trans] stub_rt[THEN order_trans])
            apply (all \<open>(simp add: Qbound; fail)?\<close>)
            apply (all \<open>(clarsimp simp: mx_l mx_r mx_lS mx_rS)?\<close>)
            apply (all \<open>(insert dle g_win, linarith)\<close>)
            done
          subgoal
            apply (simp add: lb_l rne)
            apply (refine_vcg hybrid_bitlen2_lower[THEN order_trans]
                cdlr_retrunc_child_gbound[THEN order_trans])
            apply (all \<open>(simp add: rneL Qbound; fail)?\<close>)
            apply (all \<open>(clarsimp simp: mx_l mx_r mx_lS mx_rS)?\<close>)
            apply (all \<open>(insert dle g_win, linarith)\<close>)
            done
          done
        done
    qed
  qed
qed

lemma truncate_children_mid_skip_right_gok:
  assumes g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
  shows "truncate_children_mid_skip_right_monadic g Q \<le> SPEC (\<lambda>(ql, gl, qr, gr, mids, midbl, rz).
           hybrid_child_gok g (length Q) gl \<and> hybrid_child_gok g (length Q) gr)"
  by (rule SPEC_cons_rule[OF
        truncate_children_mid_skip_right_gbounds[OF g_tri Qne Qbound Qbound2 dep Q_small kb]])
     (auto simp: hybrid_child_gok_def)

text \<open>The skip-right twins of \<open>truncate_children_mid_decide_gbind\<close>/\<open>_eta\<close>: the same splice, over
  @{thm [source] truncate_children_mid_skip_right_agrees}. \<open>cont\<close> carries the right child's frame and
  lock under \<open>\<not> rz\<close> and the exact right child's zero count under \<open>rz\<close>, in exactly the shape
  @{thm [source] hybrid_split_children_classic_agrees} hands its caller.\<close>
lemma truncate_children_mid_skip_right_decide_gbind:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and len_eq: "len = length Q"
    and cont: "\<And>ql gl qr gr code rz.
        \<lbrakk> node_frame (carried_left X) ql gl;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_gok g (length Q) gl; hybrid_child_gok g (length Q) gr;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          \<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0;
          code = 1 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          code = 0 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0;
          g = 0 \<or> 4398046511104 \<le> g \<longrightarrow> code \<noteq> 2;
          code = 0 \<or> code = 1 \<or> code = 2 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr code rz \<le> SPEC \<Phi>"
  shows "doN { (ql, gl, qr, gr, mids, midbl, rz) \<leftarrow> truncate_children_mid_skip_right_monadic g Q;
               code \<leftarrow> truncate_mid_decide_monadic g len mids midbl;
               f ql gl qr gr code rz }
       \<le> SPEC \<Phi>"
  apply (refine_vcg
      cdlr_SPEC_conj[OF
        truncate_children_mid_skip_right_agrees[OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb]
        truncate_children_mid_skip_right_gok[OF g_tri Qne Qbound Qbound2 dep Q_small kb],
        THEN order_trans])
  apply clarsimp
  apply (refine_vcg
      truncate_mid_decide_agrees[OF frame lock len_eq Qne Q_small, THEN order_trans])
  apply (all \<open>(simp; fail)?\<close>)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

lemma truncate_children_mid_skip_right_decide_gbind_eta:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and len_eq: "len = length Q"
    and cont: "\<And>ql gl qr gr code rz.
        \<lbrakk> node_frame (carried_left X) ql gl;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_gok g (length Q) gl; hybrid_child_gok g (length Q) gr;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          \<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0;
          code = 1 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          code = 0 \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0;
          g = 0 \<or> 4398046511104 \<le> g \<longrightarrow> code \<noteq> 2;
          code = 0 \<or> code = 1 \<or> code = 2 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr code rz \<le> SPEC \<Phi>"
  shows "truncate_children_mid_skip_right_monadic g Q
       \<le> SPEC (\<lambda>x. (case x of (ql, gl, qr, gr, mids, midbl, rz) \<Rightarrow>
             truncate_mid_decide_monadic g len mids midbl \<bind> (\<lambda>code. f ql gl qr gr code rz))
           \<le> SPEC \<Phi>)"
  apply (refine_vcg
      cdlr_SPEC_conj[OF
        truncate_children_mid_skip_right_agrees[OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb]
        truncate_children_mid_skip_right_gok[OF g_tri Qne Qbound Qbound2 dep Q_small kb],
        THEN order_trans])
  apply clarsimp
  apply (refine_vcg
      truncate_mid_decide_agrees[OF frame lock len_eq Qne Q_small, THEN order_trans])
  apply (all \<open>(simp; fail)?\<close>)
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done
text \<open>\<^bold>\<open>The split arm's pushed columns, as a freestanding step.\<close>
  @{thm [source] hybrid_split_pair_state_correct} already pins every component of the pushed
  worklist, but delivers them under an unsplit \<open>case xb of (todo', \<dots>) \<Rightarrow> \<dots>\<close>. Isolating the
  step makes it one \<open>cases\<close> plus \<open>auto\<close>.

  The todo-column parameter is not named \<open>T\<close>: \<open>T\<close> parses as a constant here, so the premise would demand
  \<open>todo' = <that constant>\<close> and never unify with a concrete triple. \<open>E\<close> has the same problem.\<close>
text \<open>The program's run-length update never gains more than one, which is what keeps \<open>\<sigma> \<le> k\<close>
  across a split (the child's depth gains exactly one).\<close>
lemma hybrid_split_run_len_le: "hybrid_split_run_len mid cl cr s \<le> s + 1"
  unfolding hybrid_split_run_len_def by (simp add: le_SucI)

text \<open>\<^bold>\<open>Building blocks for the arm lemmas.\<close> The four arm lemmas take their \<open>\<alpha>\<close>-shapes as premises;
  these are what discharges them at an arbitrary loop state.\<close>

lemma dyadic_rat_double: "dyadic_rat (2 * l) (Suc k) = dyadic_rat l k"
  by (simp add: dyadic_rat_def)

\<comment> \<open>both orientations: \<open>simp\<close> normalises the pushed column's \<open>2 * l\<close> to \<open>l * 2\<close>, after which
   the \<open>2 * l\<close> form stops firing.\<close>
lemma dyadic_rat_double': "dyadic_rat (l * 2) (Suc k) = dyadic_rat l k"
  by (simp add: dyadic_rat_def)

lemma dyadic_rat_mid: "dyadic_rat (l + r) (Suc k) = (dyadic_rat l k + dyadic_rat r k) / 2"
  by (simp add: dyadic_rat_def add_divide_distrib)

text \<open>The affine identity the midpoint reduces to, stated in the form \<open>field_simps\<close> PRODUCES --
  copied from the probed goal, not guessed. \<open>field_simps\<close> alone leaves it one step short: it
  clears the halving into \<open>\<dots> * 2\<close> and then cannot cancel that factor.\<close>
lemma affine_half_sum:
  fixes A B C D :: rat
  assumes "D - C \<noteq> 0"
  shows "(A * 2 + B * 2 - C * 4) / (D * 2 - C * 2)
       = (A - C) / (D - C) + (B - C) / (D - C)"
  \<comment> \<open>single-rule steps, not one \<open>simp\<close>: the cancellation needs the COMMON-FACTOR form
     \<open>(2 * x) / (2 * y)\<close>, and any \<open>simp\<close> pass distributes it straight back out again.\<close>
proof -
  have "(A * 2 + B * 2 - C * 4) / (D * 2 - C * 2) = (2 * (A + B - 2 * C)) / (2 * (D - C))"
    by (simp add: algebra_simps)
  also have "\<dots> = (A + B - 2 * C) / (D - C)"
    by (rule mult_divide_mult_cancel_left) simp
  also have "\<dots> = ((A - C) + (B - C)) / (D - C)"
    by (simp add: algebra_simps)
  also have "\<dots> = (A - C) / (D - C) + (B - C) / (D - C)"
    by (rule add_divide_distrib)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>The bisection geometry at the \<open>\<alpha>\<close> level\<close>: the pushed children's node views are the
  parent's halves. This is what \<open>geoL\<close>/\<open>geoR\<close> of \<open>hybrid_npush_split_satisfiable\<close>
  need, and the only place the \<open>(l, r, k) \<mapsto> (2l, l+r, k+1)\<close> column arithmetic meets the abstract
  midpoint.\<close>
lemma hybrid_node_iv_split_children:
  assumes lr: "l0 < r0"
  shows "dyadic_iv_node_iv_of l0 r0 k0 ((2 * l, l + r), Suc k)
       = (fst (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)),
          (fst (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))
           + snd (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))) / 2)"
    and "dyadic_iv_node_iv_of l0 r0 k0 ((l + r, 2 * r), Suc k)
       = ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))
           + snd (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))) / 2,
          snd (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)))"
proof -
  have lt: "dyadic_rat l0 k0 < dyadic_rat r0 k0"
    using lr by (simp add: dyadic_rat_def divide_strict_right_mono)
  hence hne: "dyadic_rat r0 k0 - dyadic_rat l0 k0 \<noteq> 0" by simp
  \<comment> \<open>\<open>field_simps\<close> clears the halving denominator into \<open>\<dots> * 2\<close> and then cannot cancel it
     without knowing THAT product is nonzero -- \<open>hne\<close> alone leaves the goal one step short.\<close>
  have hne2: "dyadic_rat r0 k0 * 2 - dyadic_rat l0 k0 * 2 \<noteq> 0"
    using hne by (simp add: algebra_simps)
  show "dyadic_iv_node_iv_of l0 r0 k0 ((2 * l, l + r), Suc k)
       = (fst (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)),
          (fst (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))
           + snd (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))) / 2)"
    unfolding dyadic_iv_node_iv_of_def dyadic_iv_node_iv_def Let_def
    by (simp add: dyadic_rat_double dyadic_rat_double' dyadic_rat_mid hne hne2 field_simps
                  affine_half_sum[OF hne])
  show "dyadic_iv_node_iv_of l0 r0 k0 ((l + r, 2 * r), Suc k)
       = ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))
           + snd (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))) / 2,
          snd (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)))"
    unfolding dyadic_iv_node_iv_of_def dyadic_iv_node_iv_def Let_def
    by (simp add: dyadic_rat_double dyadic_rat_double' dyadic_rat_mid hne hne2 field_simps
                  affine_half_sum[OF hne])
qed

lemma hybrid_split_cols_exI:
  assumes h: "case xb of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                todo' = Tw \<and> qtodo' = qtodo @ [q1, q2] \<and> gs' = gs @ [g1, g2] \<and>
                es' = Ew \<and> rp' = rp \<and>
                (\<exists>cl cr. cs' = cs @ [cl, cr] \<and>
                         ss' = ss @ [hybrid_split_run_len md cl cr sg,
                                     hybrid_split_run_len md cl cr sg] \<and>
                         hybrid_cs_ok g1 cl (carried_descartes_count XL) \<and>
                         hybrid_cs_ok g2 cr (carried_descartes_count XR))"
    \<comment> \<open>the guard atoms ride alongside \<open>hybrid_cs_ok\<close> in the same position and for the same
       reason: \<open>gs @ [gl, gr] = gs @ [g1, g2]\<close> identifies the existential witnesses, so \<open>auto\<close>
       transports them without ever looking inside either predicate. The \<open>gok \<rightarrow> depth_ok\<close>
       conversion is done HERE, as part of a \<open>rule\<close>, so no arithmetic reaches the arm's closers.\<close>
    and gok1: "hybrid_child_gok gg lenQ g1"
    and gok2: "hybrid_child_gok gg lenQ g2"
    \<comment> \<open>the children's frames and lock clauses, straight out of \<open>cont\<close> — \<open>f1\<close>/\<open>f2\<close>/\<open>lk1\<close>/\<open>lk2\<close>
       of @{thm [source] hybrid_refine_invar_split_step}, modulo the bisection rewrite the
       body step applies.\<close>
    and fr1: "node_frame XL q1 g1"
    and fr2: "node_frame XR q2 g2"
    and lck1: "4398046511104 \<le> g1 \<longrightarrow> q1 = XL"
    and lck2: "4398046511104 \<le> g2 \<longrightarrow> q2 = XR"
    \<comment> \<open>\<^bold>\<open>The payload bound's \<open>cont\<close> atom\<close>, placed beside \<open>gok\<close> rather than
       last because it is the same kind of hypothesis:
       @{thm [source] truncate_children_mid_decide_gbind}'s \<open>cont\<close> already supplies it, taken by
       \<open>assumption\<close> at the one call site.\<close>
    and gmx1: "g1 \<le> max gg 4398046511104"
    and gmx2: "g2 \<le> max gg 4398046511104"
    and cpl: "gg \<le> (kk + 1) * lenrp \<or> 4398046511104 \<le> gg"
    and leq: "lenQ = lenrp"
    \<comment> \<open>\<^bold>\<open>The payload atoms, passed EXPLICITLY\<close> --- the parent's own atom plus the two count
       monotonicities. Deriving the children's atoms here rather than at the assembly is forced:
       \<open>gok\<close> and \<open>gmx\<close> are indexed by the guard the TRUNCATION LAYER saw, and
       \<open>hybrid_after_pop_split_acc\<close>'s conclusion cannot mention it --- the same reason
       @{const hybrid_child_depth_ok} exists rather than @{const hybrid_child_gok}.\<close>
    and rpeq: "lenrp = length rp"
    and rp_small: "length rp < 1099511627776"
    and ppay: "hybrid_child_pay_ok lP kP rP rp gg"
    and monoL: "carried_descartes_count (carried_init_same_den lL (2 ^ kL) rL rp)
                  \<le> carried_descartes_count (carried_init_same_den lP (2 ^ kP) rP rp)"
    and monoR: "carried_descartes_count (carried_init_same_den lR (2 ^ kR) rR rp)
                  \<le> carried_descartes_count (carried_init_same_den lP (2 ^ kP) rP rp)"
  shows "\<exists>ql gl qr gr cl cr sv.
           xb = (Tw, qtodo @ [ql, qr], Ew, ss @ [sv, sv], cs @ [cl, cr], gs @ [gl, gr], rp) \<and>
           sv \<le> sg + 1 \<and>
           hybrid_cs_ok gl cl (carried_descartes_count XL) \<and>
           hybrid_cs_ok gr cr (carried_descartes_count XR) \<and>
           hybrid_child_depth_ok (kk + 1) lenrp gl \<and>
           hybrid_child_depth_ok (kk + 1) lenrp gr \<and>
           node_frame XL ql gl \<and> node_frame XR qr gr \<and>
           (4398046511104 \<le> gl \<longrightarrow> ql = XL) \<and>
           (4398046511104 \<le> gr \<longrightarrow> qr = XR) \<and>
           hybrid_child_pay_ok lL kL rL rp gl \<and>
           hybrid_child_pay_ok lR kR rR rp gr"
  \<comment> \<open>\<open>sv \<le> sg + 1\<close> rides along for the same reason the guard atoms do: \<open>h\<close> already pins the
     pushed \<open>ss\<close> entry to @{const hybrid_split_run_len}, which never gains more than one.
     Widening the arms' existential WITHOUT widening this packager makes the \<open>rule\<close> fail, the
     goals fall through to the context-searching closer and the wire trips -- exactly what this
     lemma's own note warns about, and what happened.\<close>
proof -
  have p1: "hybrid_child_pay_ok lL kL rL rp g1"
    by (rule hybrid_pay_split_child[OF gok1[unfolded leq rpeq] gmx1 rp_small ppay refl monoL])
  have p2: "hybrid_child_pay_ok lR kR rR rp g2"
    by (rule hybrid_pay_split_child[OF gok2[unfolded leq rpeq] gmx2 rp_small ppay refl monoR])
  show ?thesis
    using h fr1 fr2 lck1 lck2 p1 p2 hybrid_child_depth_okI[OF gok1[unfolded leq] cpl]
      hybrid_child_depth_okI[OF gok2[unfolded leq] cpl] hybrid_split_run_len_le
    by (cases xb) auto
qed

text \<open>\<^bold>\<open>The REBUILD branch's variant.\<close> That branch reaches the truncation layer at guard \<open>0\<close>
  on \<open>X\<close> (@{thm [source] hybrid_rebuild_frame}), so its atoms arrive at \<open>(0, length X)\<close>.
  @{thm [source] hybrid_child_gok_mono} lifts them to the parent guard first; everything else
  is identical.\<close>
lemma hybrid_split_cols_exI_rebuild:
  assumes h: "case xb of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                todo' = Tw \<and> qtodo' = qtodo @ [q1, q2] \<and> gs' = gs @ [g1, g2] \<and>
                es' = Ew \<and> rp' = rp \<and>
                (\<exists>cl cr. cs' = cs @ [cl, cr] \<and>
                         ss' = ss @ [hybrid_split_run_len md cl cr sg,
                                     hybrid_split_run_len md cl cr sg] \<and>
                         hybrid_cs_ok g1 cl (carried_descartes_count XL) \<and>
                         hybrid_cs_ok g2 cr (carried_descartes_count XR))"
    and gok1: "hybrid_child_gok 0 lenX g1"
    and gok2: "hybrid_child_gok 0 lenX g2"
    \<comment> \<open>the children's frames and lock clauses, straight out of \<open>cont\<close> — \<open>f1\<close>/\<open>f2\<close>/\<open>lk1\<close>/\<open>lk2\<close>
       of @{thm [source] hybrid_refine_invar_split_step}, modulo the bisection rewrite the
       body step applies.\<close>
    and fr1: "node_frame XL q1 g1"
    and fr2: "node_frame XR q2 g2"
    and lck1: "4398046511104 \<le> g1 \<longrightarrow> q1 = XL"
    and lck2: "4398046511104 \<le> g2 \<longrightarrow> q2 = XR"
    \<comment> \<open>\<^bold>\<open>The payload bound, vacuous on this branch by construction\<close>: the truncation ran at
       guard \<open>0\<close>, so \<open>gl \<le> max 0 2\<^sup>4\<^sup>2 = 2\<^sup>4\<^sup>2\<close> and the payload antecedent \<open>2\<^sup>4\<^sup>2 + 2 \<le> gl\<close> cannot
       fire. The parent's atom is therefore not needed (@{thm [source] hybrid_child_pay_ok_zero}
       stands in for it), but the premise set is kept identical to the midpoint twin's so the two
       call sites in @{const hybrid_branch_split_monadic}'s script stay symmetric.\<close>
    and gmx1: "g1 \<le> max 0 4398046511104"
    and gmx2: "g2 \<le> max 0 4398046511104"
    and cpl: "gg \<le> (kk + 1) * lenrp \<or> 4398046511104 \<le> gg"
    and leq: "lenX = lenrp"
    and rpeq: "lenrp = length rp"
    and rp_small: "length rp < 1099511627776"
    and monoL: "carried_descartes_count (carried_init_same_den lL (2 ^ kL) rL rp)
                  \<le> carried_descartes_count (carried_init_same_den lP (2 ^ kP) rP rp)"
    and monoR: "carried_descartes_count (carried_init_same_den lR (2 ^ kR) rR rp)
                  \<le> carried_descartes_count (carried_init_same_den lP (2 ^ kP) rP rp)"
  shows "\<exists>ql gl qr gr cl cr sv.
           xb = (Tw, qtodo @ [ql, qr], Ew, ss @ [sv, sv], cs @ [cl, cr], gs @ [gl, gr], rp) \<and>
           sv \<le> sg + 1 \<and>
           hybrid_cs_ok gl cl (carried_descartes_count XL) \<and>
           hybrid_cs_ok gr cr (carried_descartes_count XR) \<and>
           hybrid_child_depth_ok (kk + 1) lenrp gl \<and>
           hybrid_child_depth_ok (kk + 1) lenrp gr \<and>
           node_frame XL ql gl \<and> node_frame XR qr gr \<and>
           (4398046511104 \<le> gl \<longrightarrow> ql = XL) \<and>
           (4398046511104 \<le> gr \<longrightarrow> qr = XR) \<and>
           hybrid_child_pay_ok lL kL rL rp gl \<and>
           hybrid_child_pay_ok lR kR rR rp gr"
proof -
  have p1: "hybrid_child_pay_ok lL kL rL rp g1"
    by (rule hybrid_pay_split_child[OF gok1[unfolded leq rpeq] gmx1 rp_small
                                        hybrid_child_pay_ok_zero[of lP kP rP rp] refl monoL])
  have p2: "hybrid_child_pay_ok lR kR rR rp g2"
    by (rule hybrid_pay_split_child[OF gok2[unfolded leq rpeq] gmx2 rp_small
                                        hybrid_child_pay_ok_zero[of lP kP rP rp] refl monoR])
  show ?thesis
    using h fr1 fr2 lck1 lck2 p1 p2
      hybrid_child_depth_okI[OF hybrid_child_gok_mono[OF gok1[unfolded leq]] cpl]
      hybrid_child_depth_okI[OF hybrid_child_gok_mono[OF gok2[unfolded leq]] cpl]
      hybrid_split_run_len_le
    by (cases xb) auto
qed

text \<open>\<^bold>\<open>The left-only packager.\<close> The one-push twin of @{thm [source] hybrid_split_cols_exI}:
  on \<open>rz\<close> the arm pushes only the left child (@{thm [source] hybrid_split_pair_state_left_correct},
  whose run-length update reads \<open>cr = 0\<close>), so every column gains one entry. The right child's zero
  count rides through as \<open>rz0\<close>; it is what the body step discards on.\<close>
lemma hybrid_split_cols_exI_left:
  assumes h: "case xb of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                todo' = Tw \<and> qtodo' = qtodo @ [q1] \<and> gs' = gs @ [g1] \<and>
                es' = Ew \<and> rp' = rp \<and>
                (\<exists>cl. cs' = cs @ [cl] \<and>
                      ss' = ss @ [hybrid_split_run_len md cl 0 sg] \<and>
                      hybrid_cs_ok g1 cl (carried_descartes_count XL))"
    and gok1: "hybrid_child_gok gg lenQ g1"
    and fr1: "node_frame XL q1 g1"
    and lck1: "4398046511104 \<le> g1 \<longrightarrow> q1 = XL"
    and gmx1: "g1 \<le> max gg 4398046511104"
    and cpl: "gg \<le> (kk + 1) * lenrp \<or> 4398046511104 \<le> gg"
    and leq: "lenQ = lenrp"
    and rpeq: "lenrp = length rp"
    and rp_small: "length rp < 1099511627776"
    and ppay: "hybrid_child_pay_ok lP kP rP rp gg"
    and monoL: "carried_descartes_count (carried_init_same_den lL (2 ^ kL) rL rp)
                  \<le> carried_descartes_count (carried_init_same_den lP (2 ^ kP) rP rp)"
    and rz0: "rz \<longrightarrow> carried_descartes_count XR = 0"
    and rzh: "rz"
  shows "\<exists>ql gl cl sv.
           xb = (Tw, qtodo @ [ql], Ew, ss @ [sv], cs @ [cl], gs @ [gl], rp) \<and>
           sv \<le> sg + 1 \<and>
           hybrid_cs_ok gl cl (carried_descartes_count XL) \<and>
           hybrid_child_depth_ok (kk + 1) lenrp gl \<and>
           node_frame XL ql gl \<and>
           (4398046511104 \<le> gl \<longrightarrow> ql = XL) \<and>
           hybrid_child_pay_ok lL kL rL rp gl \<and>
           carried_descartes_count XR = 0"
proof -
  have p1: "hybrid_child_pay_ok lL kL rL rp g1"
    by (rule hybrid_pay_split_child[OF gok1[unfolded leq rpeq] gmx1 rp_small ppay refl monoL])
  show ?thesis
    using h fr1 lck1 p1 hybrid_child_depth_okI[OF gok1[unfolded leq] cpl]
      hybrid_split_run_len_le mp[OF rz0 rzh]
    by (cases xb) auto
qed

text \<open>\<^bold>\<open>The two-child packager at the skip-right \<open>cont\<close>'s packed right-child premise.\<close> The skip-right transports
  hand the right child's frame and lock over as one object implication under \<open>\<not> rz\<close>, and the
  \<open>\<not> rz\<close> itself arrives separately from the arm's \<open>if rz\<close> split, so a plain \<open>assumption\<close> can
  match neither. This wrapper takes them in exactly that shape, keeping the arm closer a flat run
  of \<open>assumption\<close>s.\<close>
lemma hybrid_split_cols_exI_nrz:
  assumes h: "case xb of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow>
                todo' = Tw \<and> qtodo' = qtodo @ [q1, q2] \<and> gs' = gs @ [g1, g2] \<and>
                es' = Ew \<and> rp' = rp \<and>
                (\<exists>cl cr. cs' = cs @ [cl, cr] \<and>
                         ss' = ss @ [hybrid_split_run_len md cl cr sg,
                                     hybrid_split_run_len md cl cr sg] \<and>
                         hybrid_cs_ok g1 cl (carried_descartes_count XL) \<and>
                         hybrid_cs_ok g2 cr (carried_descartes_count XR))"
    and gok1: "hybrid_child_gok gg lenQ g1"
    and gok2: "hybrid_child_gok gg lenQ g2"
    and fr1: "node_frame XL q1 g1"
    and lck1: "4398046511104 \<le> g1 \<longrightarrow> q1 = XL"
    and frl2: "\<not> rz \<longrightarrow> node_frame XR q2 g2 \<and> (4398046511104 \<le> g2 \<longrightarrow> q2 = XR)"
    and nrz: "\<not> rz"
    and gmx1: "g1 \<le> max gg 4398046511104"
    and gmx2: "g2 \<le> max gg 4398046511104"
    and cpl: "gg \<le> (kk + 1) * lenrp \<or> 4398046511104 \<le> gg"
    and leq: "lenQ = lenrp"
    and rpeq: "lenrp = length rp"
    and rp_small: "length rp < 1099511627776"
    and ppay: "hybrid_child_pay_ok lP kP rP rp gg"
    and monoL: "carried_descartes_count (carried_init_same_den lL (2 ^ kL) rL rp)
                  \<le> carried_descartes_count (carried_init_same_den lP (2 ^ kP) rP rp)"
    and monoR: "carried_descartes_count (carried_init_same_den lR (2 ^ kR) rR rp)
                  \<le> carried_descartes_count (carried_init_same_den lP (2 ^ kP) rP rp)"
  shows "\<exists>ql gl qr gr cl cr sv.
           xb = (Tw, qtodo @ [ql, qr], Ew, ss @ [sv, sv], cs @ [cl, cr], gs @ [gl, gr], rp) \<and>
           sv \<le> sg + 1 \<and>
           hybrid_cs_ok gl cl (carried_descartes_count XL) \<and>
           hybrid_cs_ok gr cr (carried_descartes_count XR) \<and>
           hybrid_child_depth_ok (kk + 1) lenrp gl \<and>
           hybrid_child_depth_ok (kk + 1) lenrp gr \<and>
           node_frame XL ql gl \<and> node_frame XR qr gr \<and>
           (4398046511104 \<le> gl \<longrightarrow> ql = XL) \<and>
           (4398046511104 \<le> gr \<longrightarrow> qr = XR) \<and>
           hybrid_child_pay_ok lL kL rL rp gl \<and>
           hybrid_child_pay_ok lR kR rR rp gr"
proof -
  have fr2: "node_frame XR q2 g2" and lck2: "4398046511104 \<le> g2 \<longrightarrow> q2 = XR"
    using frl2 nrz by simp_all
  show ?thesis
    by (rule hybrid_split_cols_exI[OF h gok1 gok2 fr1 fr2 lck1 lck2 gmx1 gmx2 cpl leq rpeq
                                        rp_small ppay monoL monoR])
qed

text \<open>\<^bold>\<open>The factored op's rebuild tail, as a freestanding step.\<close>
  @{const hybrid_split_children_classic_monadic} absorbs the \<open>code = 2\<close> escalate arm, so the
  arm lemma below does not see it; the obligation is discharged here. The
  tail runs children and decide a second time at guard \<open>0\<close> on the rebuilt node, which is \<open>X\<close>
  itself, so it is the plain bind form instantiated at \<open>g = 0\<close>.

  \<^bold>\<open>Why the post is stated at \<open>(g, lenQ)\<close> and not at \<open>(0, length X)\<close>.\<close> The rebuild branch's own atoms are
  \<open>hybrid_child_gok 0 (length X) gl\<close>, and @{thm [source] hybrid_child_gok_mono} plus the
  frame's length equality lift them to the midpoint branch's \<open>hybrid_child_gok g lenQ gl\<close>. Both
  arms therefore hand the caller one atom shape, so \<open>hybrid_branch_split_acc\<close> needs a single column closer.\<close>

lemma hybrid_split_children_rebuild_tail:
  assumes Xne: "0 < length X"
    and Xb: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and Xsm: "length X < 1099511627776"
    \<comment> \<open>not \<open>len2\<close>: that is a type class in the word library, so a free variable of
       that name parses as the class predicate \<open>'a itself \<Rightarrow> bool\<close> and the lemma fails
       type inference.\<close>
    and lenr_eq: "lenr = length X"
    and lenXQ: "length X = lenQ"
  \<comment> \<open>\<^bold>\<open>DECOMPOSED shape\<close>, because that is what \<open>refine_vcg\<close> has already produced by the
     time the escalate arm reaches here -- the comparison sits OUTSIDE the case-lambda.\<close>
  shows "truncate_children_mid_monadic 0 X
      \<le> SPEC (\<lambda>xa. (case xa of (ql, gl, qr, gr, mids, midbl) \<Rightarrow>
                 truncate_mid_decide_monadic 0 lenr mids midbl \<bind>
                   (\<lambda>code. RETURN (ql, gl, qr, gr, code = 1)))
             \<le> SPEC (\<lambda>(ql, gl, qr, gr, mid).
          node_frame (carried_left X) ql gl \<and> node_frame (carried_right X) qr gr \<and>
          gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
          hybrid_child_gok g lenQ gl \<and> hybrid_child_gok g lenQ gr \<and>
          (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
          (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X) \<and>
          (mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0) \<and>
          (\<not> mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0)))"
  apply (rule truncate_children_mid_decide_gbind_eta[
        OF node_frame_exact _ _ Xne Xb Xsm lenr_eq])
  apply simp
  apply simp
  \<comment> \<open>\<open>code \<noteq> 2\<close> is \<open>cont\<close>'s own ninth premise at \<open>g = 0\<close>, so the returned Boolean
     \<open>code = 1\<close> is decisive in BOTH directions; \<open>gl \<le> max 0 2\<^sup>4\<^sup>2\<close> entails
     \<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close> for any \<open>g\<close>, and the two \<open>gok\<close> atoms lift by
     @{thm [source] hybrid_child_gok_mono} once \<open>lenXQ\<close> has rewritten the length.\<close>
  apply (simp only: lenXQ[symmetric])
  apply (rule RETURN_rule)
  apply (simp only: prod.case)
  \<comment> \<open>\<^bold>\<open>The \<open>gok\<close> lift goes through an explicit \<open>rule\<close>, never \<open>auto intro:\<close>.\<close>
     @{thm [source] hybrid_child_gok_mono} instantiates its own conclusion at \<open>g := 0\<close>, so as
     an \<open>intro\<close> rule it rewrites \<open>hybrid_child_gok 0 \<dots>\<close> to itself and the search does not
     terminate. Ordering the alternation with the explicit \<open>rule\<close> first keeps it a single step.\<close>
  apply (intro conjI impI)
  apply (all \<open>((assumption
              | (rule hybrid_child_gok_mono, assumption)
              | (simp add: max_def)
              | fastforce); fail)?\<close>)
  done

text \<open>\<^bold>\<open>The GENERAL-guard transport for the factored child build\<close> -- the twin of
  \<open>hybrid_split_children_classic_agrees\<close> without \<open>gex\<close>, so the \<open>code = 2\<close> rebuild arm
  is LIVE and is discharged by the tail lemma above. Same \<open>cont\<close> atoms as
  \<open>truncate_children_mid_decide_gbind\<close> supplies, with \<open>code\<close> replaced by the op's returned
  Boolean: the caller never sees the escalate sentinel because the op has already resolved it.\<close>

text \<open>\<^bold>\<open>The rebuild tail over the skip-right children build.\<close> The \<open>code = 2\<close> arm of
  @{const hybrid_split_children_classic_monadic} runs
  @{const truncate_children_mid_skip_right_monadic} at guard \<open>0\<close> on the rebuilt node, so its tail
  carries the second \<open>rz\<close> the op returns. Same script as
  @{thm [source] hybrid_split_children_rebuild_tail}; the skip-right op adds the \<open>+2\<close>/depth pair and
  \<open>kb\<close>, all at guard \<open>0\<close>.\<close>
lemma hybrid_split_children_rebuild_tail_skip_right:
  assumes Xne: "0 < length X"
    and Xb: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and Xb2: "length X + 2 < max_snat LENGTH(gmp_poly_len)"
    and Xdep: "1 * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
    and Xsm: "length X < 1099511627776"
    and lenr_eq: "lenr = length X"
    and lenXQ: "length X = lenQ"
  shows "truncate_children_mid_skip_right_monadic 0 X
      \<le> SPEC (\<lambda>xa. (case xa of (ql, gl, qr, gr, mids, midbl, rz) \<Rightarrow>
                 truncate_mid_decide_monadic 0 lenr mids midbl \<bind>
                   (\<lambda>code. RETURN (ql, gl, qr, gr, code = 1, rz)))
             \<le> SPEC (\<lambda>(ql, gl, qr, gr, mid, rz).
          node_frame (carried_left X) ql gl \<and>
          gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
          hybrid_child_gok g lenQ gl \<and> hybrid_child_gok g lenQ gr \<and>
          (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
          (\<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X)) \<and>
          (rz \<longrightarrow> carried_descartes_count (carried_right X) = 0) \<and>
          (mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0) \<and>
          (\<not> mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0)))"
  apply (rule truncate_children_mid_skip_right_decide_gbind_eta[
        OF node_frame_exact _ _ Xne Xb Xb2 Xdep Xsm _ lenr_eq])
  apply simp
  apply simp
  apply (insert Xb, simp)
  apply (simp only: lenXQ[symmetric])
  apply (rule RETURN_rule)
  apply (simp only: prod.case)
  apply (intro conjI impI)
  apply (all \<open>((assumption
              | (rule hybrid_child_gok_mono, assumption)
              | (simp add: max_def)
              | fastforce); fail)?\<close>)
  done

text \<open>\<^bold>\<open>The general-guard transport on the 6-tuple.\<close> The escalate arm is
  discharged by @{thm [source] hybrid_split_children_rebuild_tail_skip_right}; the decisive arms return
  the first \<open>rz\<close> unchanged.\<close>
lemma hybrid_split_children_classic_gagrees:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and len_eq: "len = length Q"
    and recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_split_children_classic_monadic l_num r_num k rp g len Q
      \<le> SPEC (\<lambda>(ql, gl, qr, gr, mid, rz).
          node_frame (carried_left X) ql gl \<and>
          gl \<le> max g 4398046511104 \<and> gr \<le> max g 4398046511104 \<and>
          hybrid_child_gok g (length Q) gl \<and> hybrid_child_gok g (length Q) gr \<and>
          (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
          (\<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X)) \<and>
          (rz \<longrightarrow> carried_descartes_count (carried_right X) = 0) \<and>
          (mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0) \<and>
          (\<not> mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0))"
proof -
  have lenXQ: "length X = length Q" using cdlr_node_frame_len[OF frame] by simp
  have Xne: "0 < length X" using Qne lenXQ by simp
  have Xb: "length X + 1 < max_snat LENGTH(gmp_poly_len)" using Qbound lenXQ by simp
  have Xb2: "length X + 2 < max_snat LENGTH(gmp_poly_len)" using Qbound2 lenXQ by simp
  have Xdep: "1 * (length X - 1) < max_snat LENGTH(gmp_poly_len)" using dep lenXQ by simp
  have Xsm: "length X < 1099511627776" using Q_small lenXQ by simp
  show ?thesis
    unfolding hybrid_split_children_classic_monadic_def poly_length_monadic_def PR_CONST_def
    apply (rule ASSERT_leI[OF Qne], rule ASSERT_leI[OF Qbound], rule ASSERT_leI[OF Qbound2],
           rule ASSERT_leI[OF dep], rule ASSERT_leI[OF rpne], rule ASSERT_leI[OF rpb],
           rule ASSERT_leI[OF krp])
    apply (rule truncate_children_mid_skip_right_decide_gbind[
          OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb len_eq])
    subgoal for ql gl qr gr code rz
      \<comment> \<open>\<open>split if_split\<close>, NOT \<open>cases\<close>-then-\<open>simp\<close> --- see the 5-tuple original's note: a
         \<open>simp\<close> re-associates the postcondition's \<open>case_prod\<close> and the tail then fails to unify.\<close>
      apply (split if_split)
      apply (intro conjI impI)
      subgoal
        apply (refine_vcg
            carried_init_inplace_gives_X[OF recompute rpne rpb krp, THEN order_trans])
        apply (all \<open>((insert Xne Xb Xb2 Xdep, simp); fail)?\<close>)
        apply hypsubst
        apply (rule hybrid_split_children_rebuild_tail_skip_right[OF Xne Xb Xb2 Xdep Xsm refl lenXQ])
        done
      subgoal by auto
      done
    done
qed

text \<open>\<^bold>\<open>The cont-style twins of the general-guard transport.\<close> The bare \<open>\<le> SPEC\<close>
  form above hands the caller its atoms PACKED, as one conjunction under a \<open>case_prod\<close>; the
  arm lemma's column closers finish with \<open>assumption\<close>s and so need them UNPACKED, as
  separate meta-premises. That is exactly what a \<open>cont\<close> assumption does, which is why every
  transport in this file is written this way and not as a plain postcondition.
  Both shapes are supplied for the reason recorded at
  \<open>truncate_children_mid_decide_bind_decomp\<close>: \<open>refine_vcg\<close> produces the decomposed
  goal whenever the op sits under an outer bind, and a fed rule that does not match is silent.\<close>

lemma hybrid_split_children_classic_ggbind:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and len_eq: "len = length Q"
    and recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>ql gl qr gr mid rz.
        \<lbrakk> node_frame (carried_left X) ql gl;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_gok g (length Q) gl; hybrid_child_gok g (length Q) gr;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          \<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0;
          mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          \<not> mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr mid rz \<le> SPEC \<Phi>"
  shows "(doN { (ql, gl, qr, gr, mid, rz) \<leftarrow>
                 hybrid_split_children_classic_monadic l_num r_num k rp g len Q;
               f ql gl qr gr mid rz })
       \<le> SPEC \<Phi>"
  apply (refine_vcg hybrid_split_children_classic_gagrees[
        OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb len_eq recompute rpne rpb krp,
        THEN order_trans])
  apply clarsimp
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

lemma hybrid_split_children_classic_ggbind_decomp:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    and len_eq: "len = length Q"
    and recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and cont: "\<And>ql gl qr gr mid rz.
        \<lbrakk> node_frame (carried_left X) ql gl;
          gl \<le> max g 4398046511104; gr \<le> max g 4398046511104;
          hybrid_child_gok g (length Q) gl; hybrid_child_gok g (length Q) gr;
          4398046511104 \<le> gl \<longrightarrow> ql = carried_left X;
          \<not> rz \<longrightarrow> node_frame (carried_right X) qr gr \<and>
                    (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X);
          rz \<longrightarrow> carried_descartes_count (carried_right X) = 0;
          mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0;
          \<not> mid \<longrightarrow> poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<rbrakk>
        \<Longrightarrow> f ql gl qr gr mid rz \<le> SPEC \<Phi>"
  shows "hybrid_split_children_classic_monadic l_num r_num k rp g len Q
       \<le> SPEC (\<lambda>x. (case x of (ql, gl, qr, gr, mid, rz) \<Rightarrow> f ql gl qr gr mid rz)
             \<le> SPEC \<Phi>)"
  apply (refine_vcg hybrid_split_children_classic_gagrees[
        OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb len_eq recompute rpne rpb krp,
        THEN order_trans])
  apply clarsimp
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done
text \<open>\<^bold>\<open>The split arm's worklist outcome, named.\<close> Either both children are pushed, or the decide proved the
  right child empty and only the left child is pushed, in which case the exact right child's count is \<open>0\<close>, which is
  what the body step discards it on. The clause is named because it travels verbatim through eleven statements (both arm
  chains, both body steps, both assemblies and both discharges): as an inert atom \<open>simp\<close> leaves it
  alone, and only its two producers and two consumers unfold it.\<close>
definition hybrid_split_wl ::
  "gmp_poly \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> nat list \<Rightarrow> gmp_poly list \<Rightarrow> nat list \<Rightarrow>
     nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
     hybrid_worklist \<Rightarrow> bool" where
  "hybrid_split_wl X lns rns ks qtodo es ss cs gs rp l_num r_num k e s wl \<longleftrightarrow>
     (\<exists>ql gl qr gr cl cr sv.
        wl = ((lns @ [2 * l_num, l_num + r_num], rns @ [l_num + r_num, 2 * r_num],
               ks @ [k + 1, k + 1]),
              qtodo @ [ql, qr],
              es @ [newton_child_exp e, newton_child_exp e],
              ss @ [sv, sv], cs @ [cl, cr], gs @ [gl, gr], rp) \<and>
        sv \<le> s + 1 \<and>
        hybrid_cs_ok gl cl (carried_descartes_count (carried_left X)) \<and>
        hybrid_cs_ok gr cr (carried_descartes_count (carried_right X)) \<and>
        hybrid_child_depth_ok (k + 1) (length rp) gl \<and>
        hybrid_child_depth_ok (k + 1) (length rp) gr \<and>
        node_frame (carried_left X) ql gl \<and>
        node_frame (carried_right X) qr gr \<and>
        (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
        (4398046511104 \<le> gr \<longrightarrow> qr = carried_right X) \<and>
        hybrid_child_pay_ok (2 * l_num) (k + 1) (l_num + r_num) rp gl \<and>
        hybrid_child_pay_ok (l_num + r_num) (k + 1) (2 * r_num) rp gr) \<or>
     (\<exists>ql gl cl sv.
        wl = ((lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [k + 1]),
              qtodo @ [ql], es @ [newton_child_exp e],
              ss @ [sv], cs @ [cl], gs @ [gl], rp) \<and>
        sv \<le> s + 1 \<and>
        hybrid_cs_ok gl cl (carried_descartes_count (carried_left X)) \<and>
        hybrid_child_depth_ok (k + 1) (length rp) gl \<and>
        node_frame (carried_left X) ql gl \<and>
        (4398046511104 \<le> gl \<longrightarrow> ql = carried_left X) \<and>
        hybrid_child_pay_ok (2 * l_num) (k + 1) (l_num + r_num) rp gl \<and>
        carried_descartes_count (carried_right X) = 0)"

text \<open>The ONE elimination, used only by the two body steps: each conjunct becomes a separate
  hypothesis, which is the shape the body steps' \<open>clarsimp\<close>-then-\<open>assumption\<close> closers take.\<close>
lemma hybrid_split_wlE:
  assumes "hybrid_split_wl X lns rns ks qtodo es ss cs gs rp l_num r_num k e s wl"
  obtains (two) ql gl qr gr cl cr sv where
      "wl = ((lns @ [2 * l_num, l_num + r_num], rns @ [l_num + r_num, 2 * r_num],
              ks @ [k + 1, k + 1]),
             qtodo @ [ql, qr], es @ [newton_child_exp e, newton_child_exp e],
             ss @ [sv, sv], cs @ [cl, cr], gs @ [gl, gr], rp)"
      "sv \<le> s + 1"
      "hybrid_cs_ok gl cl (carried_descartes_count (carried_left X))"
      "hybrid_cs_ok gr cr (carried_descartes_count (carried_right X))"
      "hybrid_child_depth_ok (k + 1) (length rp) gl"
      "hybrid_child_depth_ok (k + 1) (length rp) gr"
      "node_frame (carried_left X) ql gl"
      "node_frame (carried_right X) qr gr"
      "4398046511104 \<le> gl \<longrightarrow> ql = carried_left X"
      "4398046511104 \<le> gr \<longrightarrow> qr = carried_right X"
      "hybrid_child_pay_ok (2 * l_num) (k + 1) (l_num + r_num) rp gl"
      "hybrid_child_pay_ok (l_num + r_num) (k + 1) (2 * r_num) rp gr"
  | (one) ql gl cl sv where
      "wl = ((lns @ [2 * l_num], rns @ [l_num + r_num], ks @ [k + 1]),
             qtodo @ [ql], es @ [newton_child_exp e], ss @ [sv], cs @ [cl], gs @ [gl], rp)"
      "sv \<le> s + 1"
      "hybrid_cs_ok gl cl (carried_descartes_count (carried_left X))"
      "hybrid_child_depth_ok (k + 1) (length rp) gl"
      "node_frame (carried_left X) ql gl"
      "4398046511104 \<le> gl \<longrightarrow> ql = carried_left X"
      "hybrid_child_pay_ok (2 * l_num) (k + 1) (l_num + r_num) rp gl"
      "carried_descartes_count (carried_right X) = 0"
  using assms unfolding hybrid_split_wl_def by blast

lemma hybrid_branch_split_acc:
  assumes frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    \<comment> \<open>the parent's own coupling conjunct — the only new premise route 1-c adds, and the
       thing that converts the truncation layer's guard bound into the invariant's depth one.\<close>
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The payload bound's two inputs\<close>, \<^bold>\<open>last\<close> so that no \<open>[OF \<dots>]\<close> position
       moves. \<open>ppay\<close> is the popped node's own atom at the guard the truncation layer sees (the
       resolved one; \<open>hybrid_after_pop_split_acc\<close> transports the stored one across
       \<open>hybrid_resolve_guard_cases\<close> with @{thm [source] hybrid_child_pay_ok_resolved}).
       \<open>lr\<close> is the node's non-degeneracy, present because
       @{thm [source] carried_count_subinterval_mono} needs \<open>A < B\<close>; the assemblies read it back
       off \<open>hybrid_cap_invar\<close>'s own conjunct through the node view.\<close>
    and ppay: "hybrid_child_pay_ok l_num k r_num rp g"
    and lr: "l_num < r_num"
  \<comment> \<open>\<^bold>\<open>The worklist clause is a disjunction.\<close> Either both children are pushed, or the decide proved the
     right child empty and only the left child is pushed, and then the exact right child's count is \<open>0\<close>, which is what
     the body step discards it on.\<close>
  shows "hybrid_branch_split_monadic (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)
             l_num r_num k e s g Q
       \<le> SPEC (\<lambda>(wl, acc').
           (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
              acc' = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1])) \<and>
           (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
              acc' = (al, ar, ak)) \<and>
           hybrid_split_wl X lns rns ks qtodo es ss cs gs rp l_num r_num k e s wl)"
proof -
  have monoL: "carried_descartes_count
                 (carried_init_same_den (2 * l_num) (2 ^ (k + 1)) (l_num + r_num) rp)
               \<le> carried_descartes_count (carried_init_same_den l_num (2 ^ k) r_num rp)"
    and monoR: "carried_descartes_count
                  (carried_init_same_den (l_num + r_num) (2 ^ (k + 1)) (2 * r_num) rp)
                \<le> carried_descartes_count (carried_init_same_den l_num (2 ^ k) r_num rp)"
    using hybrid_split_child_count_mono[OF lr rpne] by simp_all
  have lenXrp: "length X = length rp"
    by (simp add: recompute truncate_length_carried_init_same_den)
  have lenQrp: "length Q = length rp"
    using cdlr_node_frame_len[OF frame] lenXrp by simp
  have lenL: "length (carried_left X) = length rp"
    and lenR: "length (carried_right X) = length rp" using lenXrp by simp_all
  have lbLX: "length (carried_left X) + 1 < max_snat LENGTH(gmp_poly_len)"
    and lbRX: "length (carried_right X) + 1 < max_snat LENGTH(gmp_poly_len)"
    using rpb lenL lenR by simp_all
  have pbLX: "length (carried_left X) * nat_bitlen (length (carried_left X))
                < max_snat LENGTH(gmp_poly_len)"
    and pbRX: "length (carried_right X) * nat_bitlen (length (carried_right X))
                < max_snat LENGTH(gmp_poly_len)"
    using rp_pb lenL lenR by simp_all
  have gcXL: "max g 4398046511104 + length (carried_left X) < max_snat LENGTH(gmp_poly_len)"
    and gcXR: "max g 4398046511104 + length (carried_right X) < max_snat LENGTH(gmp_poly_len)"
    using gcap_rp lenL lenR by simp_all
  have Xne: "0 < length X" using rpne lenXrp by simp
  have Xb: "length X + 1 < max_snat LENGTH(gmp_poly_len)" using rpb lenXrp by simp
  have Xsm: "length X < 1099511627776" using rp_small lenXrp by simp
  have pm: "carried_push_mid_monadic (al, ar, ak) l_num r_num k
      \<le> SPEC (\<lambda>a. a = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1]))"
    by (simp add: cdlr_push_mid_eq[OF accpush])
  \<comment> \<open>three extra premises, none a new caller obligation: \<open>kb\<close> is \<open>gcap_rp\<close> at the
     frame's length, the other two are \<open>Q_small\<close>/\<open>Qbound\<close>.\<close>
  have Qbound2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    using Q_small unfolding max_snat_def by simp
  have dep: "1 * (length Q - 1) < max_snat LENGTH(gmp_poly_len)" using Qbound by simp
  have kb: "g + length Q < max_snat LENGTH(gmp_poly_len)"
    using gcap_rp lenQrp by (simp add: max_def split: if_splits)
  show ?thesis
    unfolding hybrid_branch_split_monadic_def poly_length_monadic_def PR_CONST_def
      poly_free_monadic_def hybrid_split_wl_def
    using Qne Qbound Qbound2 dep kcap rpne rpb krp accpush qcap gcap ecap sscap ccap push scap1
      Xne Xb Xsm
    apply (refine_vcg
        hybrid_split_children_classic_ggbind[
          OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb refl recompute rpne rpb krp]
        hybrid_split_children_classic_ggbind_decomp[
          OF frame lock g_tri Qne Qbound Qbound2 dep Q_small kb refl recompute rpne rpb krp]
        hybrid_split_pair_state_correct[where XL = "carried_left X" and XR = "carried_right X",
          OF _ _ _ _ lbLX lbRX pbLX pbRX _ _, THEN order_trans]
        hybrid_split_pair_state_left_correct[where XL = "carried_left X",
          OF _ _ lbLX pbLX _, THEN order_trans]
        pm[THEN order_trans])
    apply (all \<open>((elim Pair_inject, hypsubst, rule disjI1,
                  rule hybrid_split_cols_exI_nrz[OF _ _ _ _ _ _ _ _ _ g_cpl lenQrp refl rp_small
                                                  ppay monoL monoR],
                  assumption, assumption, assumption, assumption, assumption,
                  assumption, assumption, assumption, assumption); fail)?\<close>)
    apply (all \<open>((elim Pair_inject, hypsubst, rule disjI2,
                  rule hybrid_split_cols_exI_left[OF _ _ _ _ _ g_cpl lenQrp refl rp_small
                                                       ppay monoL],
                  assumption, assumption, assumption, assumption, assumption,
                  assumption, assumption); fail)?\<close>)
    apply (all \<open>((rule node_frame_exact_any_g | assumption); fail)?\<close>)
    \<comment> \<open>\<open>simp\<close> first for the trivial side goals (the freed stub, the lock orientation, \<open>Suc k\<close>,
       the acc equations); the \<open>max\<close> arithmetic then gets only the guard bounds. A single \<open>auto\<close> is too slow.\<close>
    apply (all \<open>(simp (no_asm_use); fail)?\<close>)
    apply (all \<open>((insert gcXL gcXR, auto simp: max_def); fail)?\<close>)
    done
qed
text \<open>\<^bold>\<open>The \<open>cnt \<ge> 2\<close> fork body, gate-closed arm.\<close> Composing
  @{thm [source] hybrid_dispatch_gate_fork} (which selects the third arm) with
  @{thm [source] hybrid_branch_split_acc} (which covers a general guard). The gate's
  value is determined: \<open>newton_pol_gate_mop\<close> is \<open>poly_length_monadic\<close> followed by a \<open>RETURN\<close>
  of \<open>newton_pol_gate_len\<close>, so a hypothesis on \<open>newton_pol_gate_len (length Q) e k s\<close> fixes
  which branch runs.\<close>
lemma hybrid_dispatch_split_acc:
  assumes cnt2: "2 \<le> cnt"
    and gate_closed: "\<not> newton_pol_gate_len (length Q) e k s"
    and frame: "node_frame X Q g"
    and lock: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    \<comment> \<open>the parent's own coupling conjunct — the only new premise route 1-c adds, and the
       thing that converts the truncation layer's guard bound into the invariant's depth one.\<close>
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and recompute: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The payload bound\<close>, \<^bold>\<open>last\<close> so that no \<open>[OF \<dots>]\<close>
       position moves.\<close>
    and ppay: "hybrid_child_pay_ok l_num k r_num rp g"
    and lr: "l_num < r_num"
  shows "hybrid_dispatch_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s g Q cnt
       \<le> SPEC (\<lambda>(wl, acc').
           (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
              acc' = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1])) \<and>
           (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
              acc' = (al, ar, ak)) \<and>
           hybrid_split_wl X lns rns ks qtodo es ss cs gs rp l_num r_num k e s wl)"  unfolding hybrid_dispatch_gate_fork[OF cnt2] newton_pol_gate_mop_def
            poly_length_monadic_def PR_CONST_def
  using Qne Qbound
  apply (simp add: gate_closed)
  \<comment> \<open>\<open>simplified\<close>: the surrounding \<open>simp\<close> has normalized the GOAL (\<open>k + 1 \<rightarrow> Suc k\<close>,
     \<open>map_poly rat_of_int \<rightarrow> of_int_poly\<close>), so the cited fact must be put through the same
     normalization or it will not match.\<close>
  apply (rule hybrid_branch_split_acc[OF frame lock g_tri g_cpl gcap_rp Qne Qbound Q_small 
      rpne rpb krp kcap accpush recompute rp_small rp_pb qcap gcap ecap sscap ccap push scap1
      ppay lr, simplified])
  done

text \<open>\<^bold>\<open>The window push.\<close> @{const hybrid_window_push_monadic} is a GMP chain (free, shift, sub, mul, add-ui,
  mul, add, add, discards) followed by six column appends. It is stated at column level; note \<open>(1::nat) << e\<close> is
  \<open>2 ^ e\<close>. The pushed box is exactly \<open>newton_window_child nl nr nk e m\<close>: \<open>base = l_num \<cdot> 2\<^sup>2\<^sup>^\<^sup>e\<^sup>+\<^sup>2\<close> (an
  immediate shift on a copy, no materialised power), \<open>w = r_num - l_num\<close>, and the two endpoints
  are \<open>base + m\<cdot>w\<close> and \<open>base + (m+4)\<cdot>w\<close> at depth \<open>k + 2\<^sup>e + 2\<close>.

  Two appends are not this op's job: the \<open>cs\<close> cache entry \<open>v + 2\<close> (whose
  @{const dyadic_iv_cs_invar} needs the \<open>count cand = v\<close> acceptance certificate) and the \<open>gs\<close>
  lock payload \<open>2\<^sup>4\<^sup>2 + v\<close> are appended by the caller \<open>hybrid_gate_open_monadic\<close>, the
  only place holding the exact \<open>v\<close>.\<close>

text \<open>After unfolding, \<open>refine_vcg\<close> discharges the whole op chain except the shift step, which needs the shift
  op's own correctness lemma, and a notation bridge: the definition writes the shift amount as
  \<open>((1::nat) << e) + 2\<close> while the statement (and \<open>newton_window_child\<close>) say \<open>2 ^ e + 2\<close>, so
  \<open>((1::nat) << e) = 2 ^ e\<close> is proved once as a local fact.\<close>

lemma hybrid_window_push_cols:
  assumes ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and qlen: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)"
    and elen: "length es + 1 < max_snat LENGTH(gmp_poly_len)"
    and slen: "length ss + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_window_push_monadic (lns, rns, ks) qtodo es ss cs gs rp
             l_num r_num k e s m Q cand
       \<le> SPEC (\<lambda>wl. wl = ((lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                              rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                              ks @ [k + (2 ^ e + 2)]),
                             qtodo @ [cand], es @ [e + 1], ss @ [s], cs, gs, rp))"
  unfolding hybrid_window_push_monadic_def PR_CONST_def mpzb_discard_monadic_def poly_push_coeff_monadic_def poly_vec_push_monadic_def
  using ecap ecap2 kcap ecap3 push kslen qlen elen slen
  apply (refine_vcg mpz_shift_left_snat_monadic_spec_plain[THEN order_trans]
      mpz_add_ui_snat_monadic_spec[THEN order_trans])
  apply (all \<open>(simp add: push_bit_eq_mult max_snat_def dyadic_interval_vec_pushable_def; fail)?\<close>)
  done

text \<open>\<^bold>\<open>The gate-open accept arm, at column level.\<close> Stated over the literal sub-program
  (the \<open>else\<close> block of @{const hybrid_gate_open_monadic}) rather than over the whole op, so
  that no premise mentions an op output: the branch is chosen by \<open>wc\<close>, which the caller
  cannot see. This is @{thm [source] hybrid_window_push_cols} plus the two column appends the
  definition assigns to the caller: the \<open>cs\<close> cache entry \<open>v + 2\<close> and the \<open>gs\<close> lock payload
  \<open>glock = 2\<^sup>4\<^sup>2 + v\<close>. \<open>acc\<close> is returned untouched: the accept arm pushes a window child, it
  does not accept a root.\<close>
lemma hybrid_gate_open_accept_cols:
  assumes ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and qlen: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)"
    and elen: "length es + 1 < max_snat LENGTH(gmp_poly_len)"
    and slen: "length ss + 1 < max_snat LENGTH(gmp_poly_len)"
    and clen: "length cs + 1 < max_snat LENGTH(gmp_poly_len)"
    and glen: "length gs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "doN {
           cs' \<leftarrow> mop_list_append cs (v + 2);
           gs' \<leftarrow> mop_list_append gs glock;
           triple \<leftarrow> hybrid_window_push_monadic (lns, rns, ks) qtodo es ss cs' gs' rpx
                       l_num r_num k e s m qx cand;
           RETURN (triple, acc)
         }
       \<le> SPEC (\<lambda>(wl, acc'). acc' = acc \<and>
             wl = ((lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                    rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                    ks @ [k + (2 ^ e + 2)]),
                   qtodo @ [cand], es @ [e + 1], ss @ [s],
                   cs @ [v + 2], gs @ [glock], rpx))"
  apply (refine_vcg hybrid_window_push_cols[OF ecap ecap2 kcap ecap3 push kslen qlen elen slen,
      THEN order_trans])
  apply (all \<open>((insert clen glen, simp); fail)?\<close>)
  done

text \<open>\<^bold>\<open>The gate-open reject arm and the lock guard.\<close> The reject arm of @{const hybrid_gate_open_monadic}
  calls @{const hybrid_branch_split_monadic} at guard \<open>glock = 2\<^sup>4\<^sup>2 + v\<close>, the lock guard carrying the node's exact
  count \<open>v\<close> as its payload. The code is correct there: \<open>2\<^sup>4\<^sup>2 \<le> g\<close> means locked, \<open>truncate_child_guards_mop\<close>'s
  lock branch is \<open>if 4398046511104 \<le> g then RETURN (g, g)\<close>, and the children inherit \<open>2\<^sup>4\<^sup>2 + v\<close>. So the split
  lemmas must not cap the guard at \<open>2\<^sup>4\<^sup>2\<close>, which would cover \<open>glock\<close> only at \<open>v = 0\<close>; and a hypothesis
  \<open>glock \<le> 2\<^sup>4\<^sup>2\<close> would be false at every call site, making the result vacuous exactly where the window arm fires.

  The truncation-layer bound is therefore carried as \<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close>, and the word bounds the split needs are
  stated directly: \<open>hybrid_split_pair_state_correct\<close> takes \<open>gbL: gl + length XL < max_snat\<close> and
  \<open>gbR: gr + length XR < max_snat\<close> (its guards are input parameters, so these are dischargeable), which follow from
  \<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close> and a caller-level \<open>max g 2\<^sup>4\<^sup>2 + length XL < max_snat\<close>. For \<open>g \<le> 2\<^sup>4\<^sup>2\<close> that is the
  unguarded bound; for the payload guard it is the caller's own ASSERT \<open>2\<^sup>4\<^sup>2 + v < max_snat\<close> strengthened by the
  child length bound.\<close>


text \<open>\<^bold>\<open>The \<open>2\<^sup>4\<^sup>2\<close> cap is off the reject-arm path.\<close>
  @{thm [source] hybrid_branch_split_acc} and @{thm [source] hybrid_dispatch_split_acc}
  take \<open>gcap_rp: max g 2\<^sup>4\<^sup>2 + length rp < max_snat\<close>, so they accept a payload lock guard \<open>g = 2\<^sup>4\<^sup>2 + v\<close> directly.
  A cap \<open>g \<le> 2\<^sup>4\<^sup>2\<close> remains only in the two exact-case lemmas
  (\<open>hybrid_branch_split_exact_productive\<close>/\<open>_exact_acc\<close>), where \<open>gex\<close> pins \<open>g \<in> {0, 2\<^sup>4\<^sup>2}\<close> and it is harmless.

  \<^bold>\<open>So the gate-open reject arm needs no new lemma.\<close> That arm is literally
  \<open>hybrid_branch_split_monadic todo qtodo es ss cs gs rpx acc l_num r_num k e s glock qx\<close>,
  a direct instance of @{thm [source] hybrid_branch_split_acc} at \<open>g := glock\<close>, \<open>Q := qx\<close>, \<open>rp := rpx\<close>. Its
  \<open>gcap_rp\<close> obligation discharges from the caller's own ASSERT \<open>2\<^sup>4\<^sup>2 + v < max_snat\<close>
  together with the escalated root's length bound, and \<open>g_tri\<close> from \<open>2\<^sup>4\<^sup>2 \<le> glock\<close>.

  \<^bold>\<open>The loop rule is \<open>WHILEIT_refine_new_invar\<close>\<close> (\<open>Refine_While\<close>), not \<open>WHILEIT_rule\<close>.
  \<open>hybrid_loop_stateful_monadic\<close> is
  \<open>WHILEIT hybrid_loop_safe_invar hybrid_loop_cond hybrid_loop_body_checked_monadic st0\<close> over the flattened state
  \<open>((todo, qtodo, es, ss, cs, gs, rp), acc)\<close>, so the invariant baked into the term is the runtime-safety one;
  \<open>WHILEIT_rule\<close> unifies \<open>?I\<close> with exactly that and gives no way to run the stronger \<open>hybrid_refine_invar\<close>. The
  new-invariant refinement rule is shaped for precisely this:
  \<^verbatim>\<open>[| I' x' ==> (x, x') : R;  [| I' x'; (x,x') : R |] ==> I x;
   !!x x'. [| (x,x') : R; I x; I' x' |] ==> b x = b' x';
   !!x x'. [| (x,x') : R; b x; b' x'; I x; I' x' |] ==> f x <= Down R (f' x');
   !!x x'. [| nofail (f x); (x,x') : R; b x; b' x'; I x; I' x' |] ==> f x <= SPEC I |]
==> WHILEIT I b f x <= Down R (WHILEIT I' b' f' x')\<close>
  with \<open>I := hybrid_loop_safe_invar\<close> (re-established by the last premise); \<open>R :=\<close> the relation carrying
  @{const hybrid_refine_invar} between the concrete state and the abstract \<open>newdsc_pol_bail_int\<close> node list;
  \<open>b := hybrid_loop_cond\<close>, with @{thm [source] hybrid_loop_cond_exit_triples} for \<open>b x = b' x'\<close>;
  \<open>f := hybrid_loop_body_checked_monadic\<close>, whose \<open>\<Down> R\<close> obligation splits on \<open>cnt\<close> into the
  four arms, discharged by the \<open>hybrid_refine_invar_*_step\<close> lemmas with the arms' concrete state results from
  \<open>hybrid_after_pop_*\<close> / \<open>hybrid_dispatch_*\<close> / \<open>hybrid_gate_open_accept_cols\<close> and, for the reject arm,
  @{thm [source] hybrid_branch_split_acc} at \<open>g := glock\<close>. Entry is
  @{thm [source] hybrid_refine_invar_seed}, exit @{thm [source] hybrid_refine_invar_exit_cond}, and termination
  is \<open>hybrid_mu_mset\<close> with its three decrease lemmas.\<close>



text \<open>\<^bold>\<open>Bridge: the RESOLVED node's facts, both branches at once.\<close>
  @{thm [source] hybrid_resolve_bind} hands over \<open>(c', Q', g')\<close> with only two implications
  about them (LOCKED \<open>\<Rightarrow>\<close> exact, UNLOCKED \<open>\<Rightarrow>\<close> unchanged), but
  @{thm [source] hybrid_dispatch_split_acc} wants six facts AT the resolved node. Deriving
  them inline forces a case split in the middle of an \<open>apply\<close> chain; factored out it is one
  \<open>cases\<close>. \<open>g_tri\<close> is the interesting one: LOCKED gives the second disjunct outright, UNLOCKED
  gives \<open>g1 = g\<close> and needs \<open>g_small\<close> -- which is exactly what the
  @{const hybrid_trunc_coupling} bound supplies at the call site.\<close>
lemma hybrid_resolved_node_facts:
  assumes lockx: "4398046511104 \<le> g1 \<longrightarrow> Q1 = X"
    and unlockx: "g1 < 4398046511104 \<longrightarrow> Q1 = Q \<and> g1 = g"
    and frame: "node_frame X Q g"
    \<comment> \<open>\<^bold>\<open>The trichotomy, not \<open>g < 2\<^sup>4\<^sup>0\<close>.\<close> A locked pop is reachable (the window arm's own push sets
       \<open>2\<^sup>4\<^sup>2 + v\<close>), so an unlocked-only form would make this lemma inapplicable exactly where the window arm needs
       it. Nothing in the proof wants the stronger fact: in the \<open>g\<^sub>1 < 2\<^sup>4\<^sup>2\<close> branch \<open>unlockx\<close> gives \<open>g\<^sub>1 = g\<close>, which
       already rules out this disjunct's locked half, and in the other branch the conclusions hold outright.
       @{thm [source] hybrid_branch_split_acc} takes the same shape.\<close>
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and Qne: "0 < length Q" and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and X_ne: "0 < length X" and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length X < 1099511627776"
    \<comment> \<open>\<^bold>\<open>Last\<close>, so every other \<open>[OF \<dots>]\<close> position is unaffected. The
       stored guard's coupling conjunct, in the trichotomy form the coupling states it in; the locked case is not
       excluded on the way in.\<close>
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
  shows "node_frame X Q1 g1"
    and "g1 < 1099511627776 \<or> 4398046511104 \<le> g1"
    and "0 < length Q1"
    and "length Q1 + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length Q1 < 1099511627776"
    and "length Q1 = length Q"
    \<comment> \<open>\<^bold>\<open>The conjunct that crosses the resolve.\<close> LOCKED gives the second disjunct outright;
       UNLOCKED gives \<open>g1 = g\<close> exactly (\<open>unlockx\<close> — the resolve never RAISES an unlocked guard),
       and then \<open>g_dep\<close> is the first. This is the premise \<open>hybrid_dispatch_split_acc\<close> needs at
       the RESOLVED node, and the reason the carried atom is depth-indexed rather than
       guard-indexed.\<close>
    and "g1 \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g1"
  using assms cdlr_node_frame_len[OF frame]
  by (cases "4398046511104 \<le> g1", (auto simp: node_frame_exact_any_g))+


text \<open>\<^bold>\<open>The arithmetic \<open>gcap_rp\<close> needs\<close>, stated freestanding rather than inside the long apply chain that
  consumes it.\<close>
lemma v_guard_cap_arith:
  assumes g: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and cases: "g1 = 4398046511104 \<or> g1 = g"
  shows "max g1 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
  \<comment> \<open>\<^bold>\<open>Through \<open>\<le>\<close>, not through \<open>max_def\<close>.\<close> Unfolding \<open>max\<close> makes the closer depend on
     whether \<open>simp\<close> case-splits the HYPOTHESIS's \<open>max g 2\<^sup>4\<^sup>2\<close>, which depends on the ambient
     simpset. The monotonicity step is simpset-free.\<close>
proof -
  have "max g1 4398046511104 \<le> max g 4398046511104" using cases by auto
  thus ?thesis using g by simp
qed

text \<open>\<^bold>\<open>The gate-OPEN arm, at column level -- and its conclusion is a
  DISJUNCTION by necessity.\<close> @{const hybrid_gate_open_monadic} contains BOTH sub-branches:
  \<open>wc = None\<close> falls through to @{const hybrid_branch_split_monadic} at the LOCK guard
  \<open>glock = 2\<^sup>4\<^sup>2 + v\<close>, and \<open>wc = Some\<close> pushes the window child. \<open>wc\<close> is an op OUTPUT, so the two
  cannot be separated by a premise without dragging @{thm [source] hybrid_window_choice_abs}'s
  policy hypotheses down to the state layer -- which is exactly where they do not belong.

  \<^bold>\<open>Both halves are existing lemmas.\<close> The reject half IS
  @{thm [source] hybrid_branch_split_acc} at \<open>g := glock\<close>, \<open>Q := qx\<close>, \<open>rp := rpx\<close> -- and
  @{thm [source] hybrid_cond_escalate_gives_X} pins \<open>(qx, rpx) = (X, rp)\<close>, so it is the same
  instance the gate-CLOSED arm uses. The accept half is
  @{thm [source] hybrid_gate_open_accept_cols}. Nothing new is proved here; the work is
  discharging the op's ASSERT cascade and threading \<open>v\<close>.

  \<^bold>\<open>\<open>pay\<close> is the payload invariant\<close>: the locked node's payload bounds its own count. It is a
  premise here and is discharged from the coupling at the call site; every case of its
  preservation is available (@{thm [source] newton_window_pick_bail_count} for a window
  push, @{thm [source] carried_count_subinterval_mono} for a locked split, a false antecedent
  otherwise).\<close>
lemma hybrid_gate_open_acc:
  assumes cnt2: "2 \<le> cnt"
    and gate_open: "newton_pol_gate_len (length Q) e k s"
    and inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and count2: "2 \<le> carried_descartes_count X"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and X_eq: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and lockX: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and exact0: "g = 0 \<longrightarrow> Q = X"
    and frame: "node_frame X Q g"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne1: "1 < length X"
    and X_b2: "length X + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length X < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>stated AT the exact value, not \<open>\<And>v\<close>-quantified: @{thm [source] hybrid_window_v_exact}
       pins \<open>v = carried_descartes_count X\<close>, so a general form would only be re-instantiated.\<close>
    and vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count X
                  < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>At \<open>g\<close>, not \<open>\<And>g1\<close>.\<close> The free-variable form would be
       unsatisfiable (see \<open>hybrid_step_args_gcap_rp_forall_g_is_vacuous\<close>). The guard the
       truncation layer sees is the resolved one, and \<open>hybrid_resolve_guard_cases\<close>
       pins it to \<open>2\<^sup>4\<^sup>2\<close> or \<open>g\<close>, so \<open>max g 2\<^sup>4\<^sup>2\<close> dominates it; @{thm [source] hybrid_branch_split_acc}
       has the same shape.\<close>
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>and the LOCK instance\<close>: the gate-open reject arm hands
       \<open>hybrid_branch_split_acc\<close> the lock guard \<open>2\<^sup>4\<^sup>2 + v\<close>, which \<open>max g 2\<^sup>4\<^sup>2\<close> does not
       dominate --- it carries the payload. Both instances are satisfiable; the free-variable
       form that covered them at once was not.\<close>
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The payload bound's only input here\<close>, \<^bold>\<open>last\<close>. The reject arm hands the
       split the lock guard \<open>2\<^sup>4\<^sup>2 + v\<close> and its payload atom is derived below (the payload is
       this node's own count), so the parent atom is not a premise; only the non-degeneracy
       the children's count monotonicity needs.\<close>
    and lr: "l_num < r_num"
  shows "hybrid_gate_open_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s cnt g Q
       \<le> SPEC (\<lambda>(wl, acc').
           ((poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                 acc' = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1])) \<and>
              (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
                            hybrid_split_wl X lns rns ks qtodo es ss cs gs rp l_num r_num k e s wl)
           \<or>
           (\<exists>m cand v. acc' = (al, ar, ak) \<and>
              v = carried_descartes_count X \<and>
              carried_descartes_count cand = v \<and>
              newton_window_pick_bail v e X = Some (m, cand) \<and>
              wl = ((lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                     rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                     ks @ [k + (2 ^ e + 2)]),
                    qtodo @ [cand], es @ [e + 1], ss @ [s],
                    cs @ [v + 2], gs @ [4398046511104 + v], rp)))"
  \<comment> \<open>\<^bold>\<open>Bounds in \<open>using\<close>, not a post-hoc \<open>clarsimp\<close>\<close> -- @{thm [source] hybrid_branch_split_acc}'s
     own structure. The op's ASSERT cascade then discharges inline against the caller's \<open>X\<close>
     bounds instead of leaving eight goals to be destructured one by one.\<close>
proof -
  have X_b1: "length X + 1 < max_snat LENGTH(gmp_poly_len)" using X_b2 by simp
  have X_ne0: "0 < length X" using X_ne1 by simp
  \<comment> \<open>the reject arm's split ASSERTs the depth product at multiplier \<open>1\<close> on the escalated
     node; stated once so the ASSERT cascade's \<open>clarsimp\<close> closes it by assumption.\<close>
  have X_dep: "1 * (length X - 1) < max_snat LENGTH(gmp_poly_len)" using X_b2 by simp
  \<comment> \<open>the reject branch calls the split arm at the LOCK guard \<open>glock = 2\<^sup>4\<^sup>2 + v\<close> on the EXACT
     poly \<open>X\<close>, so all four of its guard-shaped premises are immediate at that guard.\<close>
  have fX: "node_frame X X (4398046511104 + carried_descartes_count X)"
    by (rule node_frame_exact_any_g)
  have lkX: "4398046511104 \<le> 4398046511104 + carried_descartes_count X \<longrightarrow> X = X" by simp
  have triX: "4398046511104 + carried_descartes_count X < 1099511627776
              \<or> 4398046511104 \<le> 4398046511104 + carried_descartes_count X" by simp
  have cplX: "4398046511104 + carried_descartes_count X \<le> (k + 1) * length rp
              \<or> 4398046511104 \<le> 4398046511104 + carried_descartes_count X" by simp
  \<comment> \<open>\<^bold>\<open>The guard cap at the lock\<close>, the instance the reject arm needs. \<open>fX\<close>/\<open>lkX\<close>/\<open>triX\<close>/
     \<open>cplX\<close> all pin \<open>hybrid_branch_split_acc\<close>'s \<open>g\<close> to \<open>2\<^sup>4\<^sup>2 + count X\<close>, at which \<open>max g 2\<^sup>4\<^sup>2\<close>
     collapses to \<open>g\<close> itself, so this is \<open>gcap_lock\<close> and nothing more.\<close>
  have gcap_lk: "max (4398046511104 + carried_descartes_count X) 4398046511104 + length rp
                   < max_snat LENGTH(gmp_poly_len)"
    using gcap_lock by simp
  \<comment> \<open>\<^bold>\<open>The payload at the LOCK this arm SETS.\<close> The pushed guard is \<open>2\<^sup>4\<^sup>2 + count X\<close> and the node it
     guards IS \<open>X\<close>, so the payload bound holds with EQUALITY; the ceiling is
     @{thm [source] carried_descartes_count_le_length_cn} read through \<open>length X = length rp\<close>.\<close>
  have vlen: "carried_descartes_count X \<le> length rp"
    using carried_descartes_count_le_length_cn[of X]
    by (simp add: X_eq truncate_length_carried_init_same_den)
  have ppayX: "hybrid_child_pay_ok l_num k r_num rp
                 (4398046511104 + carried_descartes_count X)"
    unfolding hybrid_child_pay_ok_def using X_eq vlen by simp
  have qlen1: "length qtodo + 1 < max_snat LENGTH(gmp_poly_len)" using qcap by simp
  have elen1: "length es + 1 < max_snat LENGTH(gmp_poly_len)" using ecapl by simp
  have slen1: "length ss + 1 < max_snat LENGTH(gmp_poly_len)" using sscap by simp
  have clen1: "length cs + 1 < max_snat LENGTH(gmp_poly_len)" using ccap by simp
  have glen1: "length gs + 1 < max_snat LENGTH(gmp_poly_len)" using gcap by simp
  show ?thesis
    unfolding hybrid_gate_open_monadic_def PR_CONST_def
    using rpne rpb krp X_ne1 X_b2 ecap ecap3 ecap2 kcap2 gate4 X_dep
    apply (refine_vcg
        hybrid_cond_escalate_gives_X[OF lockX exact0 X_eq rpne rpb krp, THEN order_trans])
    \<comment> \<open>the ASSERT cascade, once the escalate's \<open>qx = X\<close> is destructured out of its \<open>case\<close>
       wrapper.\<close>
    apply (all \<open>(clarsimp; fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>Then substitute \<open>qx = X\<close> on the SURVIVING goal before the \<open>v\<close> step\<close>: that lemma is
       stated at \<open>X\<close> (its \<open>inv\<close>/\<open>pay\<close>/\<open>count2\<close> all are), so it cannot fire while the program
       still says \<open>qx\<close>.\<close>
    apply clarsimp
    apply (refine_vcg hybrid_window_v_exact[OF inv X_b1 pay count2, THEN order_trans])
    \<comment> \<open>the two \<open>v\<close> ASSERTs, at the pinned value.\<close>
    apply (all \<open>((clarsimp, insert vcap1 vcap2, simp); fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>The \<open>wc\<close> fork.\<close> @{thm [source] blr_window_choice_refine_bl} pins the op to bail's PURE
       model @{const newton_window_pick_bail}; with \<open>v\<close> now exactly \<open>carried_descartes_count X\<close>
       its \<open>2 \<le> v\<close> and \<open>count Q \<le> v\<close> premises are \<open>count2\<close> and \<open>order_refl\<close>. \<open>clarsimp\<close> first, so
       the goal speaks of \<open>count X\<close> rather than the bound \<open>x\<close>.\<close>
    apply clarsimp
    apply (refine_vcg blr_window_choice_refine_bl[OF X_ne0 X_b1 gate4 X_ne1 ecap2 X_b2
                        vcap1 count2 order_refl, THEN order_trans])
    \<comment> \<open>\<^bold>\<open>REJECT\<close>: the split arm verbatim at \<open>glock\<close>, then inject into the LEFT disjunct.\<close>
    \<comment> \<open>the acc' implications sit INSIDE the existential in this lemma's disjunct and OUTSIDE it
       in the arm's conclusion; they mention none of the bound variables, so the reshuffle is
       pure logic and \<open>blast\<close> does it.\<close>
    apply (rule SPEC_cons_rule[OF hybrid_branch_split_acc[OF fX lkX triX cplX gcap_lk
                 X_ne0 X_b1 X_small rpne rpb krp kcap accpush X_eq rp_small rp_pb
                 qcap gcap ecapl sscap ccap push2 scap1 ppayX lr]])
    \<comment> \<open>\<open>clarsimp\<close> ALONE closes the weakening -- do not append \<open>blast\<close>, which then fails on
       \<open>no subgoals\<close> and rolls the whole composite back.\<close>
    apply clarsimp
    \<comment> \<open>\<^bold>\<open>ACCEPT\<close>: the push ASSERTs, then @{thm [source] hybrid_gate_open_accept_cols}.\<close>
    apply (all \<open>((insert push1 qlen1 elen1 slen1 clen1 glen1 vcap2, simp); fail)?\<close>)
    \<comment> \<open>the appends are already done at this point, so the remaining goal is the PUSH itself --
       @{thm [source] hybrid_window_push_cols}, not the \<open>_accept_cols\<close> wrapper (which also
       performs the two appends).\<close>
    apply (rule SPEC_cons_rule[OF hybrid_window_push_cols[OF ecap ecap2 kcap2 ecap3
                 push1 kslen qlen1 elen1 slen1]])
    \<comment> \<open>the single residue is \<open>count cand = count X\<close> -- bail's
       @{thm [source] newton_window_pick_bail_count}, i.e. the accepted window PRESERVES the
       count, which is the whole reason the Newton step loses no roots.\<close>
    \<comment> \<open>\<^bold>\<open>The pick is now EXPORTED, not dropped.\<close> It was already in the context here --
       @{thm [source] newton_window_pick_bail_count} is applied to it by \<open>erule\<close> -- and it is the
       only thing that ties the window index \<open>m\<close> to an abstract interval. Dropping it is what
       made \<open>hybrid_body_step_window\<close>'s \<open>\<And>m\<close> premises unsatisfiable
       (\<open>hybrid_npush_w_forall_m_forces_one_window\<close>).\<close>
    \<comment> \<open>\<open>clarsimp\<close> discharges the exported pick from the assumption itself, so the count is
       still the ONLY residue -- a \<open>rule conjI\<close> here is a step PAST the closing step.\<close>
    \<comment> \<open>\<open>disjI2\<close> explicitly. The split disjunct is the opaque @{const hybrid_split_wl},
       which \<open>clarsimp\<close> cannot refute against the window's one-slot push (both append
       exactly one element), so it must be told which disjunct the accept half proves.\<close>
    apply (clarsimp intro!: disjI2)
    apply (erule newton_window_pick_bail_count)
    \<comment> \<open>\<^bold>\<open>The guard cap at the resolved guard.\<close> With \<open>gcap_rp\<close> stated at \<open>g\<close>, the truncation layer's own
       \<open>max g\<^sub>1 2\<^sup>4\<^sup>2 + length rp\<close> goal is not a literal copy of a premise. It is one case split away:
       \<open>hybrid_resolve_guard_cases\<close> is already in the goal's context, and in both of its cases
       \<open>max g\<^sub>1 2\<^sup>4\<^sup>2 \<le> max g 2\<^sup>4\<^sup>2\<close>.\<close>
    apply (all \<open>((rule v_guard_cap_arith[OF gcap_rp], assumption); fail)?\<close>)
    done
qed




text \<open>\<^bold>\<open>What the resolve does to the GUARD, which its classify drops.\<close>
  @{const hybrid_resolve_count_monadic} has exactly two arms: the escalate branch returns the
  EXACT-LOCK sentinel \<open>4398046511104\<close> \<^emph>\<open>literally\<close> (payload zero), and the else branch returns
  \<open>g\<close> untouched. So the resolved guard is always one of the two.

  \<^bold>\<open>Why this matters for the payload invariant.\<close> @{thm [source] hybrid_resolve_count_monadic_classify}
  exposes only \<open>2\<^sup>4\<^sup>2 \<le> g\<^sub>1 \<longrightarrow> Q\<^sub>1 = X\<close> and \<open>g\<^sub>1 < 2\<^sup>4\<^sup>2 \<longrightarrow> g\<^sub>1 = g\<close>, which says nothing about a PAYLOAD.
  With this lemma and the caller's own \<open>g < 2\<^sup>4\<^sup>0\<close>, the resolved guard is either \<open>2\<^sup>4\<^sup>2\<close> or
  \<open>< 2\<^sup>4\<^sup>0\<close> -- so \<open>2\<^sup>4\<^sup>2 + 2 \<le> g\<^sub>1\<close> is FALSE and the window arm's payload premise is VACUOUS at
  the resolved node. The capped branch of @{const hybrid_window_v_monadic} is therefore
  unreachable from an unlocked pop, which is why it needs no invariant support there.\<close>
lemma hybrid_resolve_guard_cases:
  assumes rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and X_eq: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_resolve_count_monadic Q g l_num r_num k rp c
       \<le> SPEC (\<lambda>(c', Q', g', rp'). g' = 4398046511104 \<or> g' = g)"
proof -
  \<comment> \<open>the escalate branch hands the count kernel the EXACT poly at the sentinel guard, so its
     classify applies with the trivial frame; nothing about the COUNT is needed here -- only
     that the kernel does not fail.\<close>
  have fXX: "node_frame X X 4398046511104" by (rule node_frame_exact_any_g)
  have lkXX: "(4398046511104::nat) \<le> 4398046511104 \<longrightarrow> X = X" by simp
  show ?thesis
    unfolding hybrid_resolve_count_monadic_def PR_CONST_def
    apply (refine_vcg
        carried_escalate_keep_monadic_correct[OF rp_len rp_bound k_bound, THEN order_trans])
    apply (all \<open>((insert X_eq X_len, clarsimp); fail)?\<close>)
    apply (clarsimp simp: X_eq[symmetric])
    apply (refine_vcg carried_descartes_count_g_monadic_classify[OF fXX X_len X_pbound
                        X_gbound lkXX, THEN order_trans])
    apply (all \<open>(simp; fail)?\<close>)
    done
qed

text \<open>\<^bold>\<open>The resolve bind that also EXPOSES the guard cases.\<close> Same content as
  @{thm [source] hybrid_resolve_bind}, with @{thm [source] hybrid_resolve_guard_cases}
  spliced in by @{thm [source] cdlr_SPEC_conj}, so \<open>cont\<close> additionally learns
  \<open>g\<^sub>1 = 2\<^sup>4\<^sup>2 \<or> g\<^sub>1 = g\<close>. The window arm needs it and the split arm does not, so this is a
  sibling rather than a widening -- the same reason the g-carrying bind twins are siblings of
  the originals.\<close>
lemma hybrid_resolve_gbind:
  assumes rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_eq: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and cache: "hybrid_cs_ok g c (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> g \<Longrightarrow> Q = X"
    and cont: "\<And>c' Q' g' rp'.
        \<lbrakk> dyadic_iv_cs_invar c' (carried_descartes_count X); rp' = rp;
          4398046511104 \<le> g' \<longrightarrow> Q' = X;
          g' < 4398046511104 \<longrightarrow> Q' = Q \<and> g' = g;
          g' = 4398046511104 \<or> g' = g \<rbrakk>
        \<Longrightarrow> f c' Q' g' rp' \<le> SPEC \<Phi>"
  shows "doN { (c', Q', g', rp') \<leftarrow> hybrid_resolve_count_monadic Q g l_num r_num k rp c;
               f c' Q' g' rp' }
       \<le> SPEC \<Phi>"
  apply (refine_vcg
      cdlr_SPEC_conj[OF hybrid_resolve_count_monadic_classify[OF rp_len rp_bound k_bound
                          Q_bound X_pbound X_gbound X_eq cache locked_exact]
                        hybrid_resolve_guard_cases[OF rp_len rp_bound k_bound X_eq X_len
                          X_pbound X_gbound], THEN order_trans])
  apply clarsimp
  apply (rule cont)
  apply (all \<open>((assumption | simp); fail)?\<close>)
  done

text \<open>\<^bold>\<open>The \<open>cnt \<ge> 2\<close> fork body, gate-OPEN arm.\<close> The exact mirror of
  @{thm [source] hybrid_dispatch_split_acc}: @{thm [source] hybrid_dispatch_gate_fork}
  selects the arm from \<open>2 \<le> cnt\<close>, and a hypothesis on \<open>newton_pol_gate_len\<close> fixes WHICH
  one, since @{const newton_pol_gate_mop} is @{const poly_length_monadic} followed by a
  \<open>RETURN\<close> of that pure predicate. Thin by construction -- all the content is in
  @{thm [source] hybrid_gate_open_acc}.\<close>
lemma hybrid_dispatch_gate_open_acc:
  assumes cnt2: "2 \<le> cnt"
    and gate_open: "newton_pol_gate_len (length Q) e k s"
    and inv: "dyadic_iv_cs_invar cnt (carried_descartes_count X)"
    and count2: "2 \<le> carried_descartes_count X"
    and pay: "4398046511106 \<le> g \<longrightarrow> carried_descartes_count X \<le> g - 4398046511104"
    and X_eq: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and lockX: "4398046511104 \<le> g \<longrightarrow> Q = X"
    and exact0: "g = 0 \<longrightarrow> Q = X"
    and frame: "node_frame X Q g"
    and rpne: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Qbound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne1: "1 < length X"
    and X_b2: "length X + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length X < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>stated AT the exact value, not \<open>\<And>v\<close>-quantified: @{thm [source] hybrid_window_v_exact}
       pins \<open>v = carried_descartes_count X\<close>, so a general form would only be re-instantiated.\<close>
    and vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count X
                  < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>At \<open>g\<close>, not \<open>\<And>g1\<close>.\<close> The free-variable form would be
       unsatisfiable (see \<open>hybrid_step_args_gcap_rp_forall_g_is_vacuous\<close>). The guard the
       truncation layer sees is the resolved one, and @{thm [source] hybrid_resolve_guard_cases}
       pins it to \<open>2\<^sup>4\<^sup>2\<close> or \<open>g\<close>, so \<open>max g 2\<^sup>4\<^sup>2\<close> dominates it; @{thm [source] hybrid_branch_split_acc}
       has the same shape.\<close>
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>and the LOCK instance\<close>: the gate-open reject arm hands
       \<open>hybrid_branch_split_acc\<close> the lock guard \<open>2\<^sup>4\<^sup>2 + v\<close>, which \<open>max g 2\<^sup>4\<^sup>2\<close> does not
       dominate --- it carries the payload. Both instances are satisfiable; the free-variable
       form that covered them at once was not.\<close>
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The payload bound\<close>, \<^bold>\<open>last\<close> so that no \<open>[OF \<dots>]\<close>
       position moves.\<close>
    and lr: "l_num < r_num"
  shows "hybrid_dispatch_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s g Q cnt
       \<le> SPEC (\<lambda>(wl, acc').
           ((poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                 acc' = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1])) \<and>
              (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
                            hybrid_split_wl X lns rns ks qtodo es ss cs gs rp l_num r_num k e s wl)
           \<or>
           (\<exists>m cand v. acc' = (al, ar, ak) \<and>
              v = carried_descartes_count X \<and>
              carried_descartes_count cand = v \<and>
              newton_window_pick_bail v e X = Some (m, cand) \<and>
              wl = ((lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                     rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                     ks @ [k + (2 ^ e + 2)]),
                    qtodo @ [cand], es @ [e + 1], ss @ [s],
                    cs @ [v + 2], gs @ [4398046511104 + v], rp)))"
  \<comment> \<open>\<^bold>\<open>Bounds in \<open>using\<close>, not a post-hoc \<open>clarsimp\<close>\<close> -- @{thm [source] hybrid_branch_split_acc}'s
     own structure. The op's ASSERT cascade then discharges inline against the caller's \<open>X\<close>
     bounds instead of leaving eight goals to be destructured one by one.\<close>  unfolding hybrid_dispatch_gate_fork[OF cnt2] newton_pol_gate_mop_def
            poly_length_monadic_def PR_CONST_def
  using Qne Qbound
  apply (simp add: gate_open)
  \<comment> \<open>\<open>simplified\<close>: the surrounding \<open>simp\<close> normalises the GOAL, so the cited fact must
     go through the same normalisation or it will not match -- the split arm's note.\<close>
  apply (rule hybrid_gate_open_acc[OF cnt2 gate_open inv count2 pay X_eq lockX exact0 frame rpne rpb krp Qne Qbound X_ne1 X_b2 X_small ecap ecap2 ecap3 kcap2 gate4 vcap1 vcap2 gcap_rp gcap_lock kcap accpush rp_small rp_pb qcap gcap ecapl sscap ccap push2 push1 kslen scap1 lr, simplified])
  \<comment> \<open>the resolved-guard cap, as in \<open>hybrid_gate_open_acc\<close>.\<close>
  apply (all \<open>((rule v_guard_cap_arith[OF gcap_rp], assumption); fail)?\<close>)
  done

text \<open>\<^bold>\<open>The gate-OPEN arm's after-pop composition.\<close> Same skeleton as
  \<open>hybrid_after_pop_split_acc\<close>: the resolve hands the continuation the resolved
  \<open>(c', Q', g', rp')\<close>, then the dispatch fires. Two differences, both forced:
  it goes through @{thm [source] hybrid_resolve_gbind} (the window arm needs the resolved
  guard's CASES, not just its lock/unlock implications), and its conclusion is the gate-OPEN
  DISJUNCTION.

  \<^bold>\<open>\<open>pay\<close> is VACUOUS here, and that is the point of \<open>hybrid_resolve_guard_cases\<close>.\<close> The
  resolved guard is \<open>2\<^sup>4\<^sup>2\<close> (payload zero) or \<open>g\<close> itself, and \<open>g_small\<close> puts \<open>g\<close> below \<open>2\<^sup>4\<^sup>0\<close> --
  so \<open>2\<^sup>4\<^sup>2 + 2 \<le> g\<^sub>1\<close> is unsatisfiable and the capped branch of
  @{const hybrid_window_v_monadic} is unreachable from an unlocked pop. The payload invariant
  is therefore NOT needed on this path.\<close>
lemma hybrid_after_pop_window_acc:
  assumes gate_open: "newton_pol_gate_len (length Q) e k s"
    and count2: "2 \<le> carried_descartes_count X"
    \<comment> \<open>\<^bold>\<open>The trichotomy, not \<open>g_small\<close>.\<close> The window pushes \<open>2\<^sup>4\<^sup>2 + v\<close>, so a window child that pops with
       the gate open is locked, and then \<open>pay\<close> is not vacuous: the invariant's payload conjunct supplies it
       (\<open>ppay\<close>).\<close>
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    and X_eq: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and cache: "hybrid_cs_ok g c (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> g \<Longrightarrow> Q = X"
    and exact0: "g = 0 \<longrightarrow> Q = X"
    and frame: "node_frame X Q g"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q"
    and Q_small: "length Q < 1099511627776"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_ne: "0 < length X"
    and X_ne1: "1 < length X"
    and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_b2: "length X + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length X < 1099511627776"
    and ecap: "e < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "e + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "k + (2 ^ e + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count X < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>At \<open>g\<close>, not \<open>\<And>g1\<close>.\<close> The free-variable form would be
       unsatisfiable (see \<open>hybrid_step_args_gcap_rp_forall_g_is_vacuous\<close>). The guard the
       truncation layer sees is the resolved one, and @{thm [source] hybrid_resolve_guard_cases}
       pins it to \<open>2\<^sup>4\<^sup>2\<close> or \<open>g\<close>, so \<open>max g 2\<^sup>4\<^sup>2\<close> dominates it; @{thm [source] hybrid_branch_split_acc}
       has the same shape.\<close>
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>and the LOCK instance\<close>: the gate-open reject arm hands
       \<open>hybrid_branch_split_acc\<close> the lock guard \<open>2\<^sup>4\<^sup>2 + v\<close>, which \<open>max g 2\<^sup>4\<^sup>2\<close> does not
       dominate --- it carries the payload. Both instances are satisfiable; the free-variable
       form that covered them at once was not.\<close>
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and push1: "dyadic_interval_vec_pushable (lns, rns, ks)"
    and kslen: "length ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The payload bound\<close>, \<^bold>\<open>last\<close> so that no \<open>[OF \<dots>]\<close>
       position moves. \<open>lr\<close> is the node non-degeneracy the split children's count
       monotonicity needs; \<open>ppay\<close> is the popped node's own payload atom at the stored guard,
       which @{thm [source] hybrid_child_pay_ok_resolved} moves onto the resolved one.\<close>
    and ppay: "hybrid_child_pay_ok l_num k r_num rp g"
    and lr: "l_num < r_num"
  shows "hybrid_after_pop_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s c g Q
       \<le> SPEC (\<lambda>(wl, acc').
           ((poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                 acc' = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1])) \<and>
              (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
                            hybrid_split_wl X lns rns ks qtodo es ss cs gs rp l_num r_num k e s wl)
           \<or>
           (\<exists>m cand v. acc' = (al, ar, ak) \<and>
              v = carried_descartes_count X \<and>
              carried_descartes_count cand = v \<and>
              newton_window_pick_bail v e X = Some (m, cand) \<and>
              wl = ((lns @ [l_num * 2 ^ (2 ^ e + 2) + m * (r_num - l_num)],
                     rns @ [l_num * 2 ^ (2 ^ e + 2) + (m + 4) * (r_num - l_num)],
                     ks @ [k + (2 ^ e + 2)]),
                    qtodo @ [cand], es @ [e + 1], ss @ [s],
                    cs @ [v + 2], gs @ [4398046511104 + v], rp)))"
  \<comment> \<open>\<^bold>\<open>Bounds in \<open>using\<close>, not a post-hoc \<open>clarsimp\<close>\<close> -- @{thm [source] hybrid_branch_split_acc}'s
     own structure. The op's ASSERT cascade then discharges inline against the caller's \<open>X\<close>
     bounds instead of leaving eight goals to be destructured one by one.\<close>  unfolding hybrid_after_pop_monadic_def PR_CONST_def
  using Qne Q_bound kcap rp_len rp_bound k_bound
  apply (refine_vcg
      hybrid_resolve_gbind[OF rp_len rp_bound k_bound Q_bound X_pbound X_gbound X_len
        X_eq cache locked_exact])
  apply (all \<open>((insert Qne Q_bound X_ne X_len rp_len rp_bound, auto); fail)?\<close>)
  \<comment> \<open>the after-pop op's \<open>+2\<close> ASSERT on the resolved node.\<close>
  apply (all \<open>((insert Q_small X_b2 Qne X_ne, auto simp: max_snat_def); fail)?\<close>)
  subgoal for cnt Q1 g1 rp1
    \<comment> \<open>\<open>rp1 = rp\<close>: retire it before the rule, or the dispatch call (at \<open>rp1\<close>) and this
       lemma's own SPEC (at \<open>rp\<close>) cannot unify -- the split arm's note.\<close>
    apply hypsubst
    apply (rule hybrid_dispatch_gate_open_acc[where X = X and Q = Q1 and g = g1 and cnt = cnt])
    supply rn = hybrid_resolved_node_facts[OF _ _ frame g_tri Qne Q_bound
                  Q_small X_ne X_len X_small g_cpl]
    apply (all \<open>(assumption; fail)?\<close>)
    apply (all \<open>((insert count2 X_eq X_ne1 X_b2 X_small ecap ecap2 ecap3
                    kcap2 gate4 vcap1 vcap2 gcap_rp gcap_lock kcap accpush rp_small rp_pb qcap gcap
                    ecapl sscap ccap push2 push1 kslen scap1 lr rn, assumption); fail)?\<close>)
    \<comment> \<open>\<open>2 \<le> cnt\<close>: the resolved class is only @{const dyadic_iv_cs_invar}-related to the EXACT
       count, and its \<open>(2 \<le> c) = (2 \<le> cnt)\<close> conjunct is what pins the arm -- the split arm's
       step verbatim.\<close>
    apply (all \<open>((insert count2, simp add: dyadic_iv_cs_invar_def); fail)?\<close>)
    \<comment> \<open>\<open>pay\<close> and \<open>exact0\<close> at the RESOLVED guard: both fall out of
       @{thm [source] hybrid_resolve_guard_cases}' \<open>g\<^sub>1 = 2\<^sup>4\<^sup>2 \<or> g\<^sub>1 = g\<close> together with
       \<open>g_small\<close> -- the payload antecedent is unsatisfiable and \<open>g\<^sub>1 = 0\<close> forces \<open>g\<^sub>1 = g\<close>.\<close>
    \<comment> \<open>\<^bold>\<open>\<open>pay\<close> at the resolved guard\<close>: under the trichotomy the antecedent \<open>2\<^sup>4\<^sup>2 + 2 \<le> g\<^sub>1\<close> can hold, and
       the payload bound is the invariant's own conjunct carried across \<open>hybrid_resolve_guard_cases\<close>.
       \<open>exact0\<close>: \<open>g\<^sub>1 = 0\<close> forces the unlocked branch.\<close>
    apply (all \<open>((rule hybrid_child_pay_okD[OF _ X_eq],
                  rule hybrid_child_pay_ok_resolved[OF _ ppay], assumption); fail)?\<close>)
    apply (all \<open>((insert exact0, auto); fail)?\<close>)
    \<comment> \<open>the truncation cap at the resolved guard. Stated at \<open>g\<close>, it needs
       the one case split \<open>hybrid_resolve_guard_cases\<close> already put in the context.\<close>
    apply (all \<open>((rule v_guard_cap_arith[OF gcap_rp], assumption); fail)?\<close>)
    apply (insert Q_small, simp add: gate_open rn(6) max_snat_def)
    done
  done

text \<open>\<^bold>\<open>The split arm's after-pop composition\<close> (\<open>cnt \<ge> 2\<close>, gate CLOSED). Same skeleton as
  @{thm [source] hybrid_after_pop_discard_acc}: @{thm [source] hybrid_resolve_bind} hands the
  continuation the resolved \<open>(c', Q', g', rp')\<close>, then the dispatch fires. The one extra step over
  the \<open>cnt = 0\<close>/\<open>cnt = 1\<close> arms is that @{thm [source] hybrid_dispatch_split_acc} needs the
  resolved node's FRAME and \<open>g_tri\<close>, and those must be derived in BOTH resolve branches:
  \<^item> LOCKED (\<open>2\<^sup>4\<^sup>2 \<le> g'\<close>): \<open>Q' = X\<close>, so the frame is @{thm [source] node_frame_exact_any_g} and
    \<open>g_tri\<close> is the second disjunct outright;
  \<^item> UNLOCKED (\<open>g' < 2\<^sup>4\<^sup>2\<close>): \<open>Q' = Q \<and> g' = g\<close>, so the frame is the caller's own \<open>frame\<close> and
    \<open>g_tri\<close> is the FIRST disjunct, which is why \<open>g_small\<close> is a premise here --
    the @{const hybrid_trunc_coupling} bound is what discharges it at the call site.\<close>
lemma hybrid_after_pop_split_acc:
  assumes rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_eq: "X = carried_init_same_den l_num (2 ^ k) r_num rp"
    and cache: "hybrid_cs_ok g c (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> g \<Longrightarrow> Q = X"
    and frame: "node_frame X Q g"
    \<comment> \<open>\<^bold>\<open>The trichotomy, not \<open>g_small\<close>\<close>: a locked pop is reachable, and
       @{thm [source] hybrid_resolved_node_facts} takes this form.\<close>
    and g_tri: "g < 1099511627776 \<or> 4398046511104 \<le> g"
    and count2: "2 \<le> carried_descartes_count X"
    and gate_closed: "\<not> newton_pol_gate_len (length Q) e k s"
    \<comment> \<open>\<^bold>\<open>At \<open>g\<close>, not \<open>\<And>g1\<close>.\<close> The free-variable form would be
       unsatisfiable (see \<open>hybrid_step_args_gcap_rp_forall_g_is_vacuous\<close>). The guard the
       truncation layer sees is the resolved one, and @{thm [source] hybrid_resolve_guard_cases}
       pins it to \<open>2\<^sup>4\<^sup>2\<close> or \<open>g\<close>, so \<open>max g 2\<^sup>4\<^sup>2\<close> dominates it; @{thm [source] hybrid_branch_split_acc}
       has the same shape.\<close>
    and gcap_rp: "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>and the LOCK instance\<close>: the gate-open reject arm hands
       \<open>hybrid_branch_split_acc\<close> the lock guard \<open>2\<^sup>4\<^sup>2 + v\<close>, which \<open>max g 2\<^sup>4\<^sup>2\<close> does not
       dominate --- it carries the payload. Both instances are satisfiable; the free-variable
       form that covered them at once was not.\<close>
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length Q" and kcap: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne: "0 < length X" and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length Q < 1099511627776"
    and X_small: "length X < 1099511627776"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length gs + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and push: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and scap1: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the stored guard's coupling conjunct; @{thm [source] hybrid_resolved_node_facts}
       carries it across the resolve to the form the dispatch needs.\<close>
    and g_cpl: "g \<le> (k + 1) * length rp \<or> 4398046511104 \<le> g"
    \<comment> \<open>\<^bold>\<open>The payload bound\<close>, \<^bold>\<open>last\<close>. \<open>ppay\<close> is the stored guard's
       atom (what the invariant carries); \<open>hybrid_child_pay_ok_resolved\<close> moves it onto the
       resolved guard inside the proof, which is the guard the dispatch is stated at.\<close>
    and ppay: "hybrid_child_pay_ok l_num k r_num rp g"
    and lr: "l_num < r_num"
  shows "hybrid_after_pop_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
             l_num r_num k e s c g Q
       \<le> SPEC (\<lambda>(wl, acc').
           (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
              acc' = (al @ [l_num + r_num], ar @ [l_num + r_num], ak @ [k + 1])) \<and>
           (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
              acc' = (al, ar, ak)) \<and>
           hybrid_split_wl X lns rns ks qtodo es ss cs gs rp l_num r_num k e s wl)"
  unfolding hybrid_after_pop_monadic_def PR_CONST_def
  using Qne Q_bound kcap rp_len rp_bound k_bound  \<comment> \<open>\<^bold>\<open>\<open>_gbind\<close>, not \<open>_bind\<close>\<close>: the \<open>g\<close>-carrying sibling, which additionally hands
     \<open>cont\<close> the guard cases \<open>g\<^sub>1 = 2\<^sup>4\<^sup>2 \<or> g\<^sub>1 = g\<close>. The split arm needs them because \<open>gcap_rp\<close> is stated at \<open>g\<close>.\<close>
  apply (refine_vcg
      hybrid_resolve_gbind[OF rp_len rp_bound k_bound Q_bound X_pbound X_gbound X_len X_eq
        cache locked_exact])
  apply (all \<open>((insert Qne Q_bound X_ne X_len rp_len rp_bound, auto); fail)?\<close>)
  \<comment> \<open>the after-pop op's \<open>+2\<close> ASSERT on the resolved node.\<close>
  apply (all \<open>((insert Q_small X_small Qne X_ne, auto simp: max_snat_def); fail)?\<close>)
  subgoal for cnt Q1 g1 rp1
    \<comment> \<open>the resolve returns \<open>rp1\<close> with \<open>rp1 = rp\<close>; retire it before the rule, or the dispatch
       call (at \<open>rp1\<close>) and this lemma's own SPEC (at \<open>rp\<close>) cannot unify.\<close>
    apply hypsubst
    apply (rule hybrid_dispatch_split_acc
        [where X = X and Q = Q1 and g = g1 and cnt = cnt])
    \<comment> \<open>\<open>assumption\<close> FIRST: most of the dispatch's 26 premises are literal copies of this
       lemma's own, and handing all of them to one \<open>auto\<close> with ~20 inserted facts re-derives
       from a huge context 26 times. Only the resolved-node facts need work,
       and they arrive as six SEPARATE conclusions rather than one conjunction.\<close>
    supply rn = hybrid_resolved_node_facts[OF _ _ frame g_tri Qne Q_bound
                  Q_small X_ne X_len X_small g_cpl]
    apply (all \<open>(assumption; fail)?\<close>)
    \<comment> \<open>the rest are this lemma's OWN assumptions, which are not hypotheses of the subgoal —
       \<open>insert\<close> them and \<open>assumption\<close> is enough. \<open>rn\<close> supplies the six resolved-node facts.\<close>
    apply (all \<open>((insert gate_closed gcap_rp accpush X_eq rp_small rp_pb qcap gcap ecap
                          sscap ccap push scap1 lr rn, assumption); fail)?\<close>)
    \<comment> \<open>\<^bold>\<open>The payload bound across the resolve\<close>: the dispatch wants the atom at \<open>g\<^sub>1\<close>, the invariant
       carries it at \<open>g\<close>, and \<open>hybrid_resolve_guard_cases\<close>, already in this subgoal's
       context, is the only step between them. Same \<open>rule \<dots>, assumption\<close> shape as the
       guard cap just below.\<close>
    apply (all \<open>((rule hybrid_child_pay_ok_resolved[OF _ ppay], assumption); fail)?\<close>)
    \<comment> \<open>\<open>2 \<le> cnt\<close>: the resolved class is only \<open>dyadic_iv_cs_invar\<close>-related to the EXACT count,
       and its \<open>(2 \<le> c) = (2 \<le> cnt)\<close> conjunct is what pins the arm.
       \<open>gate_closed\<close> is \<open>\<And>\<close>-quantified over the node, so it needs \<open>rule\<close>, not \<open>assumption\<close>.\<close>
    \<comment> \<open>the truncation cap at the resolved guard, as in the window twin; the
       \<open>assumption\<close> pass above does not absorb it, since \<open>gcap_rp\<close> is stated at \<open>g\<close>.\<close>
    apply (all \<open>((rule v_guard_cap_arith[OF gcap_rp], assumption); fail)?\<close>)
    apply (all \<open>((insert count2, simp add: dyadic_iv_cs_invar_def); fail)?\<close>)
    \<comment> \<open>as in @{thm [source] hybrid_dispatch_split_acc}, this premise is discharged with \<open>simp add:\<close>; a bare
       \<open>rule gate_closed\<close> does not apply.\<close>
    apply (simp add: gate_closed rn(6))
    done
  done


text \<open>\<^bold>\<open>Assembly, step 1: the concrete loop as a bare \<open>WHILEIT\<close>.\<close> The analogue of bail's
  \<open>blr_loop_monadic_unfold_bl\<close> (\<open>Bail_Loop_Refine\<close>), the first line of that theory's
  \<open>WHILEIT_refine\<close> proof, which is the template this assembly follows.\<close>
lemma hybrid_loop_monadic_unfold:
  "hybrid_loop_monadic todo qtodo es ss cs gs rp acc
     = WHILEIT hybrid_loop_safe_invar hybrid_loop_cond
         hybrid_loop_body_checked_monadic ((todo, qtodo, es, ss, cs, gs, rp), acc)"
  unfolding hybrid_loop_monadic_def hybrid_loop_stateful_monadic_def PR_CONST_def
  by simp

text \<open>\<^bold>\<open>Assembly, step 3: run the strong invariant inside the loop.\<close> The \<open>WHILEIT\<close> in
  @{const hybrid_loop_stateful_monadic} is annotated with the runtime-safety predicate
  \<open>hybrid_loop_safe_invar\<close>, so \<open>WHILEIT_rule\<close> can only hand over that at the exit, far
  too weak for the \<open>\<exists>pol\<close> conclusion. Bail sidesteps this by data-refining to an abstract loop
  (\<open>WHILEIT_refine\<close> with \<open>br blr_alpha \<dots>\<close>), but the hybrid step lemmas are pure invariant
  preservation over the concrete columns (no \<open>\<Down>R\<close>, no abstract step function), so the
  cheaper and exact route here is invariant strengthening:

  \<open>ASSERT\<close>ing more can only move a program up the refinement order (\<open>FAIL\<close> is top), so a
  loop annotated with a stronger invariant is an upper bound for the original one
  (\<open>WHILEIT_weaken\<close>). The strengthened loop is proved \<open>\<le> SPEC \<Phi>\<close> with
  \<open>WHILEIT_rule\<close> (invariant = safety \<open>\<and>\<close> @{const hybrid_refine_invar}, measure =
  \<open>hybrid_mu_mset\<close>), and the result transfers to the original loop by transitivity.\<close>
text \<open>\<^bold>\<open>A non-degenerate interval has \<open>\<mu> \<ge> 1\<close>, hence budget \<open>\<ge> 2\<close>.\<close> This is the step bail's
  \<open>blr_refine_invar\<close> docstring asserts when it says the potential implies \<open>k + 1 < max_snat\<close>,
  and it is what turns the potential's \<open>\<le> \<kappa>\<close> into strict headroom for the \<open>+1\<close> stores.

  \<open>mu\<close> is \<open>Suc (nat \<lceil>log\<^sub>2 (max 1 ((b-a)/\<delta>))\<rceil>)\<close>, so the \<open>Suc\<close> gives \<open>\<ge> 1\<close> outright, and the
  hypotheses are not needed for it; they are kept because the caller passes them. Under a bare
  \<open>nat \<lceil>log\<^sub>2 \<dots>\<rceil>\<close> they would NOT suffice, which is why the \<open>Suc\<close> is in the definition.\<close>
lemma mu_ge_1:
  assumes dpos: "0 < \<delta>" and ab: "a < b" shows "1 \<le> mu \<delta> a b"
  unfolding mu_def by simp

text \<open>\<^bold>\<open>A live node's \<open>\<mu>\<close> is at least one\<close> --- @{thm [source] mu_ge_1} read through the node
  view. The k-potential is stated over \<open>\<mu>\<close> itself rather than over the budget
  \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 - 2\<close>, so this, and not \<open>dyadic_iv_interval_budget_ge_2\<close> below, is what gives every
  live node the headroom its \<open>+1\<close> stores need.\<close>
lemma dyadic_iv_interval_mu_ge_1:
  assumes dpos: "0 < \<delta>" and ab: "fst I < snd I"
  shows "1 \<le> dyadic_iv_interval_mu \<delta> I"
  unfolding dyadic_iv_interval_mu_def
  by (rule mu_ge_1[OF dpos]) (simp add: ab of_rat_less)

lemma dyadic_iv_interval_budget_ge_2:
  assumes dpos: "0 < \<delta>" and ab: "fst I < snd I"
  shows "2 \<le> dyadic_iv_interval_todo_budget \<delta> I"
proof -
  have "1 \<le> dyadic_iv_interval_mu \<delta> I" by (rule dyadic_iv_interval_mu_ge_1[OF dpos ab])
  \<comment> \<open>\<^bold>\<open>Not \<open>metis\<close>\<close> -- it runs away on this (the file's standing note, paid again).
     \<open>power_increasing\<close> at \<open>2\<^sup>1 \<le> 2\<^sup>\<mu>\<close>, then \<open>2\<^sup>\<mu>\<^sup>\<^sup>+\<^sup>\<^sup>1 = 2 \<cdot> 2\<^sup>\<mu>\<close> is linear.\<close>
  hence P2: "(2::nat) ^ 1 \<le> 2 ^ dyadic_iv_interval_mu \<delta> I"
    by (intro power_increasing) simp_all
  have F4: "(4::nat) \<le> 2 ^ Suc (dyadic_iv_interval_mu \<delta> I)"
    using P2 by simp
  \<comment> \<open>\<open>linarith\<close>, not \<open>simp\<close>: the goal is over \<open>int\<close> and \<open>F4\<close> over \<open>nat\<close>, and \<open>simp\<close> pushes
     the coercion inside instead of lifting -- the same trap as \<open>hybrid_potential_step\<close>.\<close>
  show ?thesis unfolding dyadic_iv_interval_todo_budget_def using F4 by linarith
qed

text \<open>\<^bold>\<open>The k-potential, ported from bail\<close> (\<open>blr_refine_invar\<close>, \<open>Bail_Loop_Refine\<close>): the two column-value
  bounds \<open>hybrid_loop_step_pre\<close> needs at the node that will be popped next, which no other conjunct supplies.

  \<^bold>\<open>A plain per-node depth bound does not work\<close>: the window
  jump \<open>k' = k + 2\<^sup>e + 2\<close> defeats \<open>k + 1 < max_snat\<close>, and \<open>\<forall>i. ks ! i \<le> \<mu>\<close> is falsified by the window arm. The
  potential \<open>k + C \<cdot> \<mu>\<close> (\<open>C = 2\<^sup>e\<^sup>c\<^sup>a\<^sup>p + 2\<close>) survives because every push strictly drops the child's \<open>\<mu>\<close>,
  and one \<open>\<mu>\<close> level is worth \<open>C\<close>, which pays for the gate-bounded jump; it implies
  \<open>k + 1 < max_snat\<close> on its own. \<open>\<forall>i. ks ! i \<le> k\<^sub>0 + C \<cdot> \<mu>\<close>
  is the weakest statement of that shape that survives, and it is what this potential gives.

  \<^bold>\<open>The measure is \<open>\<mu>\<close>, not the budget \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 - 2\<close>.\<close> The preservation argument does not use the size of
  the measure: both push arms go through \<open>hybrid_potential_step\<close> below, whose only input is that the child's \<open>\<mu>\<close> is
  strictly smaller, so any strictly decreasing measure works and the smallest one is \<open>\<mu>\<close> itself.
  The size does reach the caller: \<open>k_depth_safe\<close>/\<open>g_room\<close> are quantified over \<open>kD \<le> \<kappa>\<close>, so an
  exponential \<open>\<kappa>\<close> would make the entry's guard-headroom obligation exponential in \<open>1/\<delta>\<close>,
  a root-separation floor on a solver meant for clustered roots. With linear \<open>\<kappa>\<close>
  the duty is \<open>(k\<^sub>0 + C\<cdot>\<mu> + 1) \<cdot> len < 2\<^sup>4\<^sup>0\<close>, and with \<open>\<mu> \<le> 61\<close> (\<open>mucap\<close>, the word premise
  the append/acc budget needs anyway) a bound on \<open>len\<close> alone. The budget appears
  in \<open>hybrid_budget_invar\<close> below, where the node count is the quantity being bounded.

  \<^bold>\<open>\<open>\<sigma>\<close> needs no potential of its own\<close>: bail carries \<open>s \<le> k\<close> (the run-length counter never
  exceeds the dyadic depth: \<open>s' \<le> s + 1 \<le> k + 1 = k'\<close> on a split, \<open>s\<close> unchanged on a window),
  and with the k-potential that yields the \<open>s + 1 < max_snat\<close> the \<open>\<sigma>\<close> store needs.

  It is stated column-indexed here, where bail states it over a node set.\<close>
\<comment> \<open>\<^bold>\<open>Stated MONOTONELY, against the root's own potential\<close> -- not \<open>< max_snat\<close> as bail states
   it, so \<open>\<le> \<kappa>\<close> feeds this keystone's \<open>kcap\<close>/\<open>k_depth_safe\<close> premises directly while bail's
   \<open>< max_snat\<close> form does not (bail's own word caps are stated that way; ours are not). The
   second conjunct is non-degeneracy, which is what makes \<open>\<mu> \<ge> 1\<close> and hence the \<open>+1\<close> stores
   fit.\<close>
definition hybrid_root_potential :: "real \<Rightarrow> nat \<Rightarrow> int" where
  "hybrid_root_potential \<delta> k0 =
     int k0 + int (2 ^ newton_pol_ecap + 2) * int (dyadic_iv_interval_mu \<delta> (0, 1))"

definition hybrid_cap_invar ::
  "real \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> nat list \<Rightarrow> bool" where
  "hybrid_cap_invar \<delta> l0 r0 k0 todo ss \<longleftrightarrow>
     (case todo of (lns, rns, ks) \<Rightarrow>
        (\<forall>i < length ks.
           int (ks ! i) + int (2 ^ newton_pol_ecap + 2)
             * int (dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0 ((lns ! i, rns ! i), ks ! i)))
           \<le> hybrid_root_potential \<delta> k0
           \<and> fst (dyadic_iv_node_iv_of l0 r0 k0 ((lns ! i, rns ! i), ks ! i)) < snd (dyadic_iv_node_iv_of l0 r0 k0 ((lns ! i, rns ! i), ks ! i))) \<and>
        (\<forall>i < length ss. ss ! i \<le> ks ! i))"

lemma dyadic_iv_interval_budget_nonneg: "0 \<le> dyadic_iv_interval_todo_budget \<delta> I"
proof -
  have P1: "(2::nat) ^ 1 \<le> 2 ^ Suc (dyadic_iv_interval_mu \<delta> I)"
    by (intro power_increasing) simp_all
  \<comment> \<open>evaluate \<open>2\<^sup>1\<close> BEFORE handing it to \<open>linarith\<close>: as a power it is an opaque atom.\<close>
  have "(2::nat) \<le> 2 ^ Suc (dyadic_iv_interval_mu \<delta> I)" using P1 by simp
  thus ?thesis unfolding dyadic_iv_interval_todo_budget_def by linarith
qed

lemma hybrid_cap_invar_nth:
  assumes c: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss" and i: "i < length ks"
  shows "int (ks ! i) + int (2 ^ newton_pol_ecap + 2)
           * int (dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0 ((lns ! i, rns ! i), ks ! i)))
         \<le> hybrid_root_potential \<delta> k0"
  using c i unfolding hybrid_cap_invar_def by simp

lemma hybrid_cap_invar_nondeg:
  assumes c: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss" and i: "i < length ks"
  shows "fst (dyadic_iv_node_iv_of l0 r0 k0 ((lns ! i, rns ! i), ks ! i)) < snd (dyadic_iv_node_iv_of l0 r0 k0 ((lns ! i, rns ! i), ks ! i))"
  using c i unfolding hybrid_cap_invar_def by simp

text \<open>The two consumer shapes: the depth is bounded by \<open>\<kappa>\<close> (which \<open>k_depth_safe\<close> takes), and
  with strict headroom, since a live node's \<open>\<mu>\<close> is at least one and one \<open>\<mu>\<close> level is worth
  \<open>C = 258\<close>.\<close>
lemma hybrid_cap_invar_depth_le:
  assumes c: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss" and i: "i < length ks"
  shows "int (ks ! i) \<le> hybrid_root_potential \<delta> k0"
proof -
  have "0 \<le> int (2 ^ newton_pol_ecap + 2)
              * int (dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0 ((lns ! i, rns ! i), ks ! i)))"
    by simp
  thus ?thesis using hybrid_cap_invar_nth[OF c i] by linarith
qed

lemma hybrid_cap_invar_depth_succ_le:
  assumes c: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss" and i: "i < length ks"
    and dpos: "0 < \<delta>"
  shows "int (ks ! i) + 1 \<le> hybrid_root_potential \<delta> k0"
proof -
  have b2: "1 \<le> dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0 ((lns ! i, rns ! i), ks ! i))"
    by (rule dyadic_iv_interval_mu_ge_1[OF dpos hybrid_cap_invar_nondeg[OF c i]])
  have "2 \<le> int (2 ^ newton_pol_ecap + 2)
              * int (dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0 ((lns ! i, rns ! i), ks ! i)))"
  proof -
    have "(2::int) * 1
        \<le> int (2 ^ newton_pol_ecap + 2)
            * int (dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0 ((lns ! i, rns ! i), ks ! i)))"
      using b2 by (intro mult_mono) (simp_all add: newton_pol_ecap_def)
    thus ?thesis by simp
  qed
  thus ?thesis using hybrid_cap_invar_nth[OF c i] by linarith
qed

lemma hybrid_cap_invar_sigma_nth:
  assumes c: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss" and i: "i < length ss"
  shows "ss ! i \<le> ks ! i"
  using c i unfolding hybrid_cap_invar_def by simp

text \<open>\<^bold>\<open>Pop preservation\<close>: a uniform \<open>butlast\<close> keeps every surviving index at its own value, so
  both conjuncts are inherited. This is the whole of the discard/accept arms' obligation.\<close>
lemma hybrid_cap_invar_pop:
  assumes c: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    \<comment> \<open>the column lengths are needed for \<open>nth_butlast\<close>'s side condition on \<open>lns\<close>/\<open>rns\<close>: only
       \<open>ks\<close>'s length is in scope otherwise, so their \<open>butlast\<close>s never get rewritten.\<close>
    and lr: "length lns = length ks" and rr: "length rns = length ks"
    and sk: "length ss = length ks"
  shows "hybrid_cap_invar \<delta> l0 r0 k0 (butlast lns, butlast rns, butlast ks) (butlast ss)"
  using c lr rr sk unfolding hybrid_cap_invar_def
  by (auto simp: nth_butlast dest!: less_le_trans[OF _ diff_le_self])

text \<open>\<^bold>\<open>The budget arithmetic the two PUSH arms need\<close>, ported verbatim from bail
  (\<open>blr_budget_power_children_le_bl\<close> \<open>:2529\<close> / \<open>blr_budget_power_single_le_bl\<close> \<open>:2555\<close>): a child
  whose \<open>\<mu>\<close> is strictly smaller has at most the parent's budget, and TWO such children together
  still do. This is what makes the potential pay for the depth jump.\<close>
lemma hybrid_budget_children_le:
  assumes "x < z" and "y < z"
  shows "int ((2::nat) ^ Suc x) + int ((2::nat) ^ Suc y) \<le> int ((2::nat) ^ Suc z)"
proof -
  have "(2::nat) ^ Suc x \<le> 2 ^ z" using assms(1) by (intro power_increasing) simp_all
  moreover have "(2::nat) ^ Suc y \<le> 2 ^ z" using assms(2) by (intro power_increasing) simp_all
  ultimately have "int ((2::nat) ^ Suc x) + int ((2::nat) ^ Suc y) \<le> int (2 ^ z) + int (2 ^ z)"
    by linarith
  also have "\<dots> = int ((2::nat) ^ Suc z)" by simp
  finally show ?thesis .
qed

lemma hybrid_budget_single_le:
  assumes "x < z" shows "int ((2::nat) ^ Suc x) \<le> int ((2::nat) ^ Suc z)"
  using assms by (simp add: power_increasing)

lemma hybrid_todo_budget_single_le:
  assumes "dyadic_iv_interval_mu \<delta> I < dyadic_iv_interval_mu \<delta> J"
  shows "dyadic_iv_interval_todo_budget \<delta> I \<le> dyadic_iv_interval_todo_budget \<delta> J"
  using hybrid_budget_single_le[OF assms]
  by (simp add: dyadic_iv_interval_todo_budget_def)

text \<open>\<^bold>\<open>The potential step -- the mathematical core of the port.\<close> A child whose \<open>\<mu>\<close> is strictly
  smaller can absorb ANY depth jump up to \<open>C = 2\<^sup>e\<^sup>c\<^sup>a\<^sup>p + 2\<close>, because one \<open>\<mu>\<close> level is worth \<open>C\<close>:
  \<open>C \<cdot> \<mu>\<^sub>p - C \<cdot> \<mu>\<^sub>c \<ge> C\<close> as soon as \<open>\<mu>\<^sub>c < \<mu>\<^sub>p\<close>. Both push arms are
  instances: the split jumps by \<open>1\<close>, the window by \<open>2\<^sup>e + 2 \<le> C\<close> under its gate. This is what
  bail's \<open>blr_refine_invar\<close> docstring means by "the window's budget drop pays the
  gate-bounded jump", and it is the reason a plain depth bound cannot work. The hypothesis
  \<open>\<mu>\<^sub>c < \<mu>\<^sub>p\<close> is all either arm supplies.\<close>
lemma hybrid_potential_step:
  fixes k j :: nat and P :: int
  assumes mu: "dyadic_iv_interval_mu \<delta> Ic < dyadic_iv_interval_mu \<delta> Ip"
    and jump: "int j \<le> int (2 ^ newton_pol_ecap + 2)"
    and par: "int k + int (2 ^ newton_pol_ecap + 2)
                * int (dyadic_iv_interval_mu \<delta> Ip) \<le> P"
  shows "int (k + j) + int (2 ^ newton_pol_ecap + 2)
           * int (dyadic_iv_interval_mu \<delta> Ic) \<le> P"
proof -
  let ?C = "int (2 ^ newton_pol_ecap + 2)"
  let ?mc = "dyadic_iv_interval_mu \<delta> Ic" and ?mp = "dyadic_iv_interval_mu \<delta> Ip"
  \<comment> \<open>one \<open>\<mu>\<close> level, in \<open>int\<close> throughout: the strict \<open>\<mu>\<close> drop is \<open>\<le> -1\<close> and \<open>C > 0\<close>, so the
     product drops by at least \<open>C\<close>, which is the whole of the argument.\<close>
  have D: "int ?mc \<le> int ?mp - 1" using mu by linarith
  have "?C * int ?mc \<le> ?C * (int ?mp - 1)"
    using D by (rule mult_left_mono) simp
  also have "\<dots> = ?C * int ?mp - ?C" by (simp add: algebra_simps)
  finally have E: "?C * int ?mc \<le> ?C * int ?mp - ?C" .
  show ?thesis using E jump par by simp
qed

text \<open>\<^bold>\<open>Push preservation, two children\<close> -- the split arm's obligation on the potential. Each new
  entry is @{thm [source] hybrid_potential_step} at the parent's potential with a jump of one;
  the \<open>\<mu>\<close>-drops are the bisection halving the arm already supplies.\<close>
lemma hybrid_cap_invar_push2:
  assumes c: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and lr: "length lns = length ks" and rr: "length rns = length ks"
    and sk: "length ss = length ks" and kne: "ks \<noteq> []"
    and muL: "dyadic_iv_interval_mu \<delta>
                (dyadic_iv_node_iv_of l0 r0 k0 ((2 * last lns, last lns + last rns), Suc (last ks)))
              < dyadic_iv_interval_mu \<delta>
                (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    and muR: "dyadic_iv_interval_mu \<delta>
                (dyadic_iv_node_iv_of l0 r0 k0 ((last lns + last rns, 2 * last rns), Suc (last ks)))
              < dyadic_iv_interval_mu \<delta>
                (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    and svb: "sv \<le> last ss + 1"
    \<comment> \<open>the children are non-degenerate -- the conjunct that keeps the budget \<open>\<ge> 2\<close>, and hence
       the \<open>+1\<close> stores in headroom. Both arms already have it (\<open>ab\<close> / \<open>wprop\<close>).\<close>
    and ndL: "fst (dyadic_iv_node_iv_of l0 r0 k0
                    ((2 * last lns, last lns + last rns), Suc (last ks)))
              < snd (dyadic_iv_node_iv_of l0 r0 k0
                    ((2 * last lns, last lns + last rns), Suc (last ks)))"
    and ndR: "fst (dyadic_iv_node_iv_of l0 r0 k0
                    ((last lns + last rns, 2 * last rns), Suc (last ks)))
              < snd (dyadic_iv_node_iv_of l0 r0 k0
                    ((last lns + last rns, 2 * last rns), Suc (last ks)))"
  shows "hybrid_cap_invar \<delta> l0 r0 k0
           (butlast lns @ [2 * last lns, last lns + last rns],
            butlast rns @ [last lns + last rns, 2 * last rns],
            butlast ks @ [last ks + 1, last ks + 1])
           (butlast ss @ [sv, sv])"
proof -
  have kpos: "0 < length ks" using kne by simp
  have ilast: "length ks - 1 < length ks" using kpos by simp
  \<comment> \<open>\<open>last_conv_nth\<close> fires per column and needs each one non-empty; with only \<open>ks \<noteq> []\<close> in
     scope the \<open>lns\<close>/\<open>rns\<close>/\<open>ss\<close> occurrences stay folded and stop matching.\<close>
  have lne: "lns \<noteq> []" and rne: "rns \<noteq> []" and sne: "ss \<noteq> []"
    using kne lr rr sk by auto
  \<comment> \<open>the parent's own potential, read off at the popped index.\<close>
  have par: "int (last ks) + int (2 ^ newton_pol_ecap + 2)
               * int (dyadic_iv_interval_mu \<delta>
                   (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
             \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_nth[OF c ilast] lr rr kne lne rne
    by (simp add: last_conv_nth)
  have sig: "last ss \<le> last ks"
    using hybrid_cap_invar_sigma_nth[OF c, of "length ks - 1"] ilast sk kne sne
    by (simp add: last_conv_nth)
  \<comment> \<open>each child: the potential step at a jump of one.\<close>
  have PL: "int (last ks + 1) + int (2 ^ newton_pol_ecap + 2)
              * int (dyadic_iv_interval_mu \<delta>
                  (dyadic_iv_node_iv_of l0 r0 k0
                     ((2 * last lns, last lns + last rns), Suc (last ks))))
            \<le> hybrid_root_potential \<delta> k0"
    by (rule hybrid_potential_step[OF muL _ par]) simp
  have PR: "int (last ks + 1) + int (2 ^ newton_pol_ecap + 2)
              * int (dyadic_iv_interval_mu \<delta>
                  (dyadic_iv_node_iv_of l0 r0 k0
                     ((last lns + last rns, 2 * last rns), Suc (last ks))))
            \<le> hybrid_root_potential \<delta> k0"
    by (rule hybrid_potential_step[OF muR _ par]) simp
  have svk: "sv \<le> Suc (last ks)" using svb sig by simp
  show ?thesis
    using hybrid_cap_invar_pop[OF c lr rr sk] PL PR svk ndL ndR
    unfolding hybrid_cap_invar_def
    by (auto simp: nth_append lr rr sk less_Suc_eq)
qed

text \<open>\<^bold>\<open>Push preservation, one child\<close> -- the window arm. Same step at the gate-bounded jump
  \<open>2\<^sup>e + 2 \<le> C\<close>, and \<open>\<sigma>\<close> is carried over unchanged, so \<open>\<sigma> \<le> k\<close> only gets easier.\<close>
lemma hybrid_cap_invar_push1:
  assumes c: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and lr: "length lns = length ks" and rr: "length rns = length ks"
    and sk: "length ss = length ks" and kne: "ks \<noteq> []"
    and muW: "dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0 ((lw, rw), kw))
              < dyadic_iv_interval_mu \<delta>
                (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    and kwj: "kw = last ks + j" and jle: "int j \<le> int (2 ^ newton_pol_ecap + 2)"
    and ndW: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((lw, rw), kw))
              < snd (dyadic_iv_node_iv_of l0 r0 k0 ((lw, rw), kw))"
  shows "hybrid_cap_invar \<delta> l0 r0 k0
           (butlast lns @ [lw], butlast rns @ [rw], butlast ks @ [kw]) (butlast ss @ [last ss])"
proof -
  have kpos: "0 < length ks" using kne by simp
  have ilast: "length ks - 1 < length ks" using kpos by simp
  \<comment> \<open>\<open>last_conv_nth\<close> fires per column and needs each one non-empty; with only \<open>ks \<noteq> []\<close> in
     scope the \<open>lns\<close>/\<open>rns\<close>/\<open>ss\<close> occurrences stay folded and stop matching.\<close>
  have lne: "lns \<noteq> []" and rne: "rns \<noteq> []" and sne: "ss \<noteq> []"
    using kne lr rr sk by auto
  have par: "int (last ks) + int (2 ^ newton_pol_ecap + 2)
               * int (dyadic_iv_interval_mu \<delta>
                   (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
             \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_nth[OF c ilast] lr rr kne lne rne
    by (simp add: last_conv_nth)
  have sig: "last ss \<le> last ks"
    using hybrid_cap_invar_sigma_nth[OF c, of "length ks - 1"] ilast sk kne sne
    by (simp add: last_conv_nth)
  \<comment> \<open>\<open>rule\<close>, not \<open>simp add:\<close> -- the lemma concludes at \<open>int (k + j)\<close> and \<open>simp\<close> has already
     split the goal into \<open>int k + int j\<close>, after which it no longer matches.\<close>
  have PW: "int (last ks + j) + int (2 ^ newton_pol_ecap + 2)
              * int (dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0 ((lw, rw), kw)))
            \<le> hybrid_root_potential \<delta> k0"
    by (rule hybrid_potential_step[OF muW jle par])
  show ?thesis
    using hybrid_cap_invar_pop[OF c lr rr sk] PW sig kwj ndW
    unfolding hybrid_cap_invar_def
    by (auto simp: nth_append lr rr sk less_Suc_eq)
qed

text \<open>\<^bold>\<open>The ACC BUDGET, ported from bail\<close> (\<open>blr_refine_invar\<close>, \<open>Bail_Loop_Refine.thy\<close>).
  The k-potential bounds the node columns; this bounds the ACCUMULATOR, and the accept arm needs
  it for the same reason: its \<open>safe'\<close> is at the popped state with a GROWN accumulator, so
  \<open>step_pre\<close> must hold for \<open>al @ [last lns]\<close>, which needs \<open>length al + 2 < max_snat\<close> where
  \<open>step_pre\<close> supplies only \<open>pushable acc\<close>.

  The device is the same: every live node carries budget \<open>2\<^sup>\<mu>\<^sup>\<^sup>+\<^sup>\<^sup>1 - 1 \<ge> 1\<close>, so a non-empty
  worklist pays for the one accumulator slot the accept arm is about to consume, and a split's
  two children pay for their own plus the midpoint root
  (@{thm [source] hybrid_budget_children_le}).\<close>
lemma dyadic_iv_interval_acc_budget_ge_1: "1 \<le> dyadic_iv_interval_acc_budget \<delta> I"
proof -
  have P1: "(2::nat) ^ 1 \<le> 2 ^ Suc (dyadic_iv_interval_mu \<delta> I)"
    by (intro power_increasing) simp_all
  have "(2::nat) \<le> 2 ^ Suc (dyadic_iv_interval_mu \<delta> I)" using P1 by simp
  thus ?thesis unfolding dyadic_iv_interval_acc_budget_def by linarith
qed

\<comment> \<open>renamed off \<open>dyadic_iv_\<close>: that prefix already carries this name in
   \<open>Newton_Loop_Refine\<close>, and co-loading would shadow silently.\<close>
lemma hybrid_acc_budget_nonneg: "0 \<le> dyadic_iv_todo_acc_budget \<delta> vs"
  unfolding dyadic_iv_todo_acc_budget_def
proof (induct vs)
  case Nil show ?case by simp
next
  case (Cons v vs)
  have "1 \<le> dyadic_iv_interval_acc_budget \<delta> v" by (rule dyadic_iv_interval_acc_budget_ge_1)
  with Cons show ?case by simp
qed

lemma dyadic_iv_todo_acc_budget_snoc:
  "dyadic_iv_todo_acc_budget \<delta> (vs @ [v])
     = dyadic_iv_todo_acc_budget \<delta> vs + dyadic_iv_interval_acc_budget \<delta> v"
  unfolding dyadic_iv_todo_acc_budget_def by simp

text \<open>\<^bold>\<open>The todo-append budget\<close>: bail's \<open>blr_refine_invar\<close> conjunct 3 (\<open>Bail_Loop_Refine\<close>), the third of
  bail's word-bound conjuncts.

  \<^bold>\<open>Why it is needed.\<close> @{const hybrid_loop_step_pre} asserts
  \<open>dyadic_interval_vec_pushable2\<close> of the popped vector, i.e. \<open>length lns + 1 < max_snat\<close>. At the
  two-child pushed state the same conjunct is asserted one column longer, i.e.
  \<open>length lns + 2 < max_snat\<close>, strictly more than what is in hand, on every one of the six
  columns. Nothing else in \<open>hybrid_state_invar\<close> bounds the worklist length, so
  \<open>safe'\<close> on the split arm is unprovable without this (see \<open>hybrid_loop_safe_invar_push2_all\<close> below).

  \<^bold>\<open>The device is the acc budget's, one level over.\<close> A live node carries todo-budget
  \<open>2\<^sup>\<mu>\<^sup>\<^sup>+\<^sup>\<^sup>1 - 2\<close>; two children whose \<open>\<mu>\<close> is strictly smaller cost the parent minus two, against a
  worklist that grows by one, so the sum strictly drops and pays for the new slot. The
  arithmetic is @{thm [source] hybrid_budget_children_le}.\<close>

lemma hybrid_append_budget_nonneg: "0 \<le> dyadic_iv_todo_append_budget \<delta> vs"
  unfolding dyadic_iv_todo_append_budget_def
proof (induct vs)
  case Nil show ?case by simp
next
  case (Cons v vs)
  have "0 \<le> dyadic_iv_interval_todo_budget \<delta> v" by (rule dyadic_iv_interval_budget_nonneg)
  with Cons show ?case by simp
qed

lemma dyadic_iv_todo_append_budget_snoc:
  "dyadic_iv_todo_append_budget \<delta> (vs @ [v])
     = dyadic_iv_todo_append_budget \<delta> vs + dyadic_iv_interval_todo_budget \<delta> v"
  unfolding dyadic_iv_todo_append_budget_def by simp

lemma dyadic_iv_todo_append_budget_snoc2:
  "dyadic_iv_todo_append_budget \<delta> (vs @ [v, w])
     = dyadic_iv_todo_append_budget \<delta> vs + dyadic_iv_interval_todo_budget \<delta> v
       + dyadic_iv_interval_todo_budget \<delta> w"
  unfolding dyadic_iv_todo_append_budget_def by simp

lemma dyadic_iv_todo_acc_budget_snoc2:
  "dyadic_iv_todo_acc_budget \<delta> (vs @ [v, w])
     = dyadic_iv_todo_acc_budget \<delta> vs + dyadic_iv_interval_acc_budget \<delta> v
       + dyadic_iv_interval_acc_budget \<delta> w"
  unfolding dyadic_iv_todo_acc_budget_def by simp

text \<open>\<^bold>\<open>Two children cost the parent minus two\<close> (todo) \<^bold>\<open>and minus one\<close> (acc) -- the two
  inequalities the split arm's growth is paid from, both instances of
  @{thm [source] hybrid_budget_children_le}. The \<open>- 2\<close> is what makes the todo side survive a
  worklist that lengthened by one; the \<open>- 1\<close> is what pays the accumulator's midpoint root.\<close>
lemma hybrid_todo_budget_children_le:
  assumes "dyadic_iv_interval_mu \<delta> IL < dyadic_iv_interval_mu \<delta> I"
    and "dyadic_iv_interval_mu \<delta> IR < dyadic_iv_interval_mu \<delta> I"
  shows "dyadic_iv_interval_todo_budget \<delta> IL + dyadic_iv_interval_todo_budget \<delta> IR
         \<le> dyadic_iv_interval_todo_budget \<delta> I - 2"
  using hybrid_budget_children_le[OF assms]
  by (simp add: dyadic_iv_interval_todo_budget_def)

lemma hybrid_acc_budget_children_le:
  assumes "dyadic_iv_interval_mu \<delta> IL < dyadic_iv_interval_mu \<delta> I"
    and "dyadic_iv_interval_mu \<delta> IR < dyadic_iv_interval_mu \<delta> I"
  shows "dyadic_iv_interval_acc_budget \<delta> IL + dyadic_iv_interval_acc_budget \<delta> IR
         \<le> dyadic_iv_interval_acc_budget \<delta> I - 1"
  using hybrid_budget_children_le[OF assms]
  by (simp add: dyadic_iv_interval_acc_budget_def)

lemma hybrid_acc_budget_single_le:
  assumes "dyadic_iv_interval_mu \<delta> J < dyadic_iv_interval_mu \<delta> I"
  shows "dyadic_iv_interval_acc_budget \<delta> J \<le> dyadic_iv_interval_acc_budget \<delta> I"
  \<comment> \<open>\<open>unfolding\<close> then \<open>linarith\<close>, exactly as \<open>blr_acc_budget_single_le_bl\<close>: as
     \<open>simp add: \<dots>_def\<close> the cited \<open>\<le>\<close> is used as a REWRITE and the goal comes back strict.\<close>
  using hybrid_budget_single_le[OF assms]
  unfolding dyadic_iv_interval_acc_budget_def by linarith

text \<open>\<^bold>\<open>The two word budgets, bundled.\<close> They are stated together because they are preserved
  together by the same four arms and consumed together by \<open>safe'\<close>: each
  @{const hybrid_loop_body_checked_monadic} step gains one subgoal rather than two.\<close>
definition hybrid_budget_invar ::
  "real \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "hybrid_budget_invar \<delta> l0 r0 k0 todo acc \<longleftrightarrow>
     (case todo of (lns, rns, ks) \<Rightarrow>
        (case acc of (al, ar, ak) \<Rightarrow>
           int (length lns)
             + dyadic_iv_todo_append_budget \<delta> (hybrid_alpha_views l0 r0 k0 todo) + 2
             < int (max_snat LENGTH(gmp_poly_len))
         \<and> int (length al)
             + dyadic_iv_todo_acc_budget \<delta> (hybrid_alpha_views l0 r0 k0 todo) + 1
             < int (max_snat LENGTH(gmp_poly_len))))"

text \<open>\<^bold>\<open>What it is FOR, todo side\<close>: the column cap \<open>step_pre\<close> asserts one slot longer than the
  state it is given. This is the fact the probe showed to be missing.\<close>
lemma hybrid_budget_invar_todo_cap:
  assumes b0: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) acc"
  shows "length lns + 2 < max_snat LENGTH(gmp_poly_len)"
proof -
  obtain al ar ak where accd: "acc = (al, ar, ak)" by (cases acc)
  note b = b0[unfolded accd]
  have nn: "0 \<le> dyadic_iv_todo_append_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks))"
    by (rule hybrid_append_budget_nonneg)
  \<comment> \<open>the conjunct is SELECTED by \<open>simp\<close> and the budget is dropped by \<open>linarith\<close> -- one step
     each. Chaining the nonnegativity into a single \<open>simp\<close> does neither.\<close>
  have B: "int (length lns)
             + dyadic_iv_todo_append_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks)) + 2
           < int (max_snat LENGTH(gmp_poly_len))"
    using b unfolding hybrid_budget_invar_def by simp
  have "int (length lns) + 2 < int (max_snat LENGTH(gmp_poly_len))" using B nn by linarith
  thus ?thesis by linarith
qed

text \<open>\<^bold>\<open>What it is FOR, acc side\<close>: the accumulator can take one more entry, which is
  exactly what the accept arm's \<open>safe'\<close> needs and \<open>step_pre\<close> does not give.\<close>
lemma hybrid_budget_invar_acc_grown:
  assumes b: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and lne: "lns \<noteq> []" and lr: "length rns = length lns" and lk: "length ks = length lns"
  shows "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
proof -
  have ne2: "rns \<noteq> []" "ks \<noteq> []" using lne lr lk by auto
  have vne: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) \<noteq> []"
    using lne ne2 by (simp add: hybrid_alpha_views_def dyadic_interval_vec_triples_def)
  then obtain vs v where dec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) = vs @ [v]"
    by (cases "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)" rule: rev_cases) auto
  have "1 \<le> dyadic_iv_interval_acc_budget \<delta> v" by (rule dyadic_iv_interval_acc_budget_ge_1)
  moreover have "0 \<le> dyadic_iv_todo_acc_budget \<delta> vs" by (rule hybrid_acc_budget_nonneg)
  ultimately have one: "1 \<le> dyadic_iv_todo_acc_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks))"
    unfolding dec dyadic_iv_todo_acc_budget_snoc by linarith
  have B: "int (length al)
             + dyadic_iv_todo_acc_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks)) + 1
           < int (max_snat LENGTH(gmp_poly_len))"
    using b unfolding hybrid_budget_invar_def by simp
  show ?thesis using B one by linarith
qed

text \<open>\<^bold>\<open>The accessor pair.\<close> Every preservation step below is "read the two scalar inequalities,
  rewrite the views by the arm's own decomposition, \<open>linarith\<close>, rebuild" -- so the destruction and
  introduction are factored out once rather than each step fighting the two nested \<open>case\<close>s.\<close>
lemma hybrid_budget_invarD:
  assumes "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
  shows "int (length lns)
           + dyadic_iv_todo_append_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks)) + 2
         < int (max_snat LENGTH(gmp_poly_len))"
    and "int (length al)
           + dyadic_iv_todo_acc_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks)) + 1
         < int (max_snat LENGTH(gmp_poly_len))"
  using assms unfolding hybrid_budget_invar_def by simp_all

lemma hybrid_budget_invarI:
  assumes "int (length lns)
             + dyadic_iv_todo_append_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks)) + 2
           < int (max_snat LENGTH(gmp_poly_len))"
    and "int (length al)
           + dyadic_iv_todo_acc_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks)) + 1
         < int (max_snat LENGTH(gmp_poly_len))"
  shows "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
  using assms unfolding hybrid_budget_invar_def by simp

text \<open>\<^bold>\<open>The acc cap, unconditionally.\<close> Companion to
  @{thm [source] hybrid_budget_invar_acc_grown}, and the one the loop exit needs: \<open>_acc_grown\<close>
  gives the stronger \<open>+ 2\<close> but only for a non-empty worklist, because it spends the last live
  node's budget of \<open>\<ge> 1\<close>. At exit the worklist is empty by the loop condition, so that
  hypothesis is not available; dropping the whole budget by
  @{thm [source] hybrid_acc_budget_nonneg} instead costs one slot and needs nothing.

  \<^bold>\<open>What it is for.\<close> \<open>length al + 1 < max_snat\<close> is @{const dyadic_interval_vec_pushable} of the
  accumulator, i.e. the bound on the number of emitted intervals that the back-map's push capacity needs
  (\<open>qsolve\<close>'s fourth conjunct). It holds in the invariant and \<open>hybrid_loop_expol\<close> (below) keeps it at the exit,
  as it keeps the isolation and vector-invariant conjuncts.\<close>
lemma hybrid_budget_invar_acc_cap:
  assumes b: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
  shows "length al + 1 < max_snat LENGTH(gmp_poly_len)"
proof -
  have nn: "0 \<le> dyadic_iv_todo_acc_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks))"
    by (rule hybrid_acc_budget_nonneg)
  have B: "int (length al)
             + dyadic_iv_todo_acc_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks)) + 1
           < int (max_snat LENGTH(gmp_poly_len))"
    by (rule hybrid_budget_invarD(2)[OF b])
  have "int (length al) + 1 < int (max_snat LENGTH(gmp_poly_len))" using B nn by linarith
  thus ?thesis by linarith
qed

text \<open>\<^bold>\<open>Pop preservation\<close> -- the discard arm's whole obligation, and the prefix half of every
  other arm's. Both sides only shrink: the column is one shorter and the popped node's two
  budgets are non-negative.\<close>
lemma hybrid_budget_invar_pop:
  \<comment> \<open>\<open>acc\<close> stays a VARIABLE here (unlike every other preservation step): the discard arm carries
     its accumulator undestructured, and a triple pattern would not match it.\<close>
  assumes b0: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) acc"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
               = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks) @ [I]"
  shows "hybrid_budget_invar \<delta> l0 r0 k0 (butlast lns, butlast rns, butlast ks) acc"
proof -
  obtain al ar ak where accd: "acc = (al, ar, ak)" by (cases acc)
  note b = b0[unfolded accd]
  show ?thesis unfolding accd
proof (rule hybrid_budget_invarI)
  have bt: "0 \<le> dyadic_iv_interval_todo_budget \<delta> I" by (rule dyadic_iv_interval_budget_nonneg)
  have ba: "1 \<le> dyadic_iv_interval_acc_budget \<delta> I" by (rule dyadic_iv_interval_acc_budget_ge_1)
  have lb: "int (length (butlast lns)) \<le> int (length lns)" by simp
  note D = hybrid_budget_invarD[OF b, unfolded vdec
             dyadic_iv_todo_append_budget_snoc dyadic_iv_todo_acc_budget_snoc]
  show "int (length (butlast lns))
          + dyadic_iv_todo_append_budget \<delta>
              (hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)) + 2
        < int (max_snat LENGTH(gmp_poly_len))"
    using D(1) bt lb by linarith
  show "int (length al)
          + dyadic_iv_todo_acc_budget \<delta>
              (hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    using D(2) ba by linarith
  qed
qed

text \<open>\<^bold>\<open>Accept preservation\<close> -- pop, and the accumulator takes ONE more entry. That slot is paid
  for by the popped node's own acc-budget, which is \<open>\<ge> 1\<close>: exactly the device the acc budget
  exists for.\<close>
lemma hybrid_budget_invar_accept:
  assumes b: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
               = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks) @ [I]"
    and accg: "length al' \<le> length al + 1"
  shows "hybrid_budget_invar \<delta> l0 r0 k0 (butlast lns, butlast rns, butlast ks) (al', ar', ak')"
proof (rule hybrid_budget_invarI)
  have bt: "0 \<le> dyadic_iv_interval_todo_budget \<delta> I" by (rule dyadic_iv_interval_budget_nonneg)
  have ba: "1 \<le> dyadic_iv_interval_acc_budget \<delta> I" by (rule dyadic_iv_interval_acc_budget_ge_1)
  have lb: "int (length (butlast lns)) \<le> int (length lns)" by simp
  have ag: "int (length al') \<le> int (length al) + 1" using accg by linarith
  note D = hybrid_budget_invarD[OF b, unfolded vdec
             dyadic_iv_todo_append_budget_snoc dyadic_iv_todo_acc_budget_snoc]
  show "int (length (butlast lns))
          + dyadic_iv_todo_append_budget \<delta>
              (hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)) + 2
        < int (max_snat LENGTH(gmp_poly_len))"
    using D(1) bt lb by linarith
  show "int (length al')
          + dyadic_iv_todo_acc_budget \<delta>
              (hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    using D(2) ba ag by linarith
qed

text \<open>\<^bold>\<open>Two-child push preservation\<close> -- the split arm, and the window arm's REJECT half. This is
  the step the whole conjunct exists for: the worklist grows by one, and the two children's
  todo-budgets are the parent's MINUS TWO
  (@{thm [source] hybrid_todo_budget_children_le}), so the sum strictly drops and pays for the
  new slot. The accumulator may take the midpoint root at the same time, paid by the acc side's
  own MINUS ONE.

  Stated over the arm's OWN \<open>vsplit\<close>/\<open>vpush\<close> decomposition (a free prefix \<open>VS\<close>), which is
  verbatim what the four \<open>hybrid_body_step_*\<close> lemmas already carry.\<close>
lemma hybrid_budget_invar_push2:
  assumes b: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) = VS @ [I]"
    and vpush: "hybrid_alpha_views l0 r0 k0 (lns', rns', ks') = VS @ [IL, IR]"
    and len': "length lns' = length lns + 1"
    and muL: "dyadic_iv_interval_mu \<delta> IL < dyadic_iv_interval_mu \<delta> I"
    and muR: "dyadic_iv_interval_mu \<delta> IR < dyadic_iv_interval_mu \<delta> I"
    and accg: "length al' \<le> length al + 1"
  shows "hybrid_budget_invar \<delta> l0 r0 k0 (lns', rns', ks') (al', ar', ak')"
proof (rule hybrid_budget_invarI)
  have ct: "dyadic_iv_interval_todo_budget \<delta> IL + dyadic_iv_interval_todo_budget \<delta> IR
            \<le> dyadic_iv_interval_todo_budget \<delta> I - 2"
    by (rule hybrid_todo_budget_children_le[OF muL muR])
  have ca: "dyadic_iv_interval_acc_budget \<delta> IL + dyadic_iv_interval_acc_budget \<delta> IR
            \<le> dyadic_iv_interval_acc_budget \<delta> I - 1"
    by (rule hybrid_acc_budget_children_le[OF muL muR])
  have lb: "int (length lns') = int (length lns) + 1" using len' by simp
  have ag: "int (length al') \<le> int (length al) + 1" using accg by linarith
  note D = hybrid_budget_invarD[OF b, unfolded vdec
             dyadic_iv_todo_append_budget_snoc dyadic_iv_todo_acc_budget_snoc]
  show "int (length lns')
          + dyadic_iv_todo_append_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns', rns', ks')) + 2
        < int (max_snat LENGTH(gmp_poly_len))"
    unfolding vpush dyadic_iv_todo_append_budget_snoc2 using D(1) ct lb by linarith
  show "int (length al')
          + dyadic_iv_todo_acc_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns', rns', ks')) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    unfolding vpush dyadic_iv_todo_acc_budget_snoc2 using D(2) ca ag by linarith
qed

text \<open>\<^bold>\<open>The split arm's accumulator is BRANCHED\<close>, not fixed: it grows by the midpoint root or
  stays, under the two implications the arm's SPEC leaves in the context. Rather than case-split
  inside the body step's apply-script, the branch is absorbed here -- both branches feed the same
  @{thm [source] hybrid_budget_invar_push2}, differing only in the trailing length side
  condition.\<close>
lemma hybrid_budget_invar_push2_branched:
  assumes b: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) = VS @ [I]"
    and vpush: "hybrid_alpha_views l0 r0 k0 (lns', rns', ks') = VS @ [IL, IR]"
    and len': "length lns' = length lns + 1"
    and muL: "dyadic_iv_interval_mu \<delta> IL < dyadic_iv_interval_mu \<delta> I"
    and muR: "dyadic_iv_interval_mu \<delta> IR < dyadic_iv_interval_mu \<delta> I"
    \<comment> \<open>\<^bold>\<open>OBJECT implications and COMPONENTWISE equations\<close> -- both, because that is exactly
       the shape \<open>clarsimp\<close> leaves in the arm's context, so the body step discharges each by
       \<open>assumption\<close> the way \<open>accgrow\<close>'s twin is discharged beside it. Stated as a meta
       implication, or over the acc TRIPLE, \<open>assumption\<close> cannot unify and \<open>Q\<close>/\<open>x\<close>/\<open>y\<close>/\<open>z\<close>
       stay schematic with nothing to fix them.\<close>
    and grow: "Q \<longrightarrow> al' = al @ [x] \<and> ar' = ar @ [y] \<and> ak' = ak @ [z]"
    and keep: "\<not> Q \<longrightarrow> al' = al \<and> ar' = ar \<and> ak' = ak"
  shows "hybrid_budget_invar \<delta> l0 r0 k0 (lns', rns', ks') (al', ar', ak')"
proof (cases Q)
  case True
  have "length al' \<le> length al + 1" using mp[OF grow True] by simp
  thus ?thesis by (rule hybrid_budget_invar_push2[OF b vdec vpush len' muL muR])
next
  case False
  have "length al' \<le> length al + 1" using mp[OF keep False] by simp
  thus ?thesis by (rule hybrid_budget_invar_push2[OF b vdec vpush len' muL muR])
qed

text \<open>\<^bold>\<open>One-child push preservation\<close> -- the window arm's ACCEPT half. Net worklist size unchanged
  and no accepted interval added, so the single child's strictly smaller \<open>\<mu>\<close> is all it takes
  (@{thm [source] hybrid_todo_budget_single_le} / @{thm [source] hybrid_acc_budget_single_le}).\<close>
lemma hybrid_budget_invar_push1:
  assumes b: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and vdec: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) = VS @ [I]"
    and vpush: "hybrid_alpha_views l0 r0 k0 (lns', rns', ks') = VS @ [J]"
    and len': "length lns' \<le> length lns"
    and muJ: "dyadic_iv_interval_mu \<delta> J < dyadic_iv_interval_mu \<delta> I"
    and accs: "length al' \<le> length al"
  shows "hybrid_budget_invar \<delta> l0 r0 k0 (lns', rns', ks') (al', ar', ak')"
proof (rule hybrid_budget_invarI)
  have st: "dyadic_iv_interval_todo_budget \<delta> J \<le> dyadic_iv_interval_todo_budget \<delta> I"
    by (rule hybrid_todo_budget_single_le[OF muJ])
  have sa: "dyadic_iv_interval_acc_budget \<delta> J \<le> dyadic_iv_interval_acc_budget \<delta> I"
    by (rule hybrid_acc_budget_single_le[OF muJ])
  have lb: "int (length lns') \<le> int (length lns)" using len' by linarith
  have ag: "int (length al') \<le> int (length al)" using accs by linarith
  note D = hybrid_budget_invarD[OF b, unfolded vdec
             dyadic_iv_todo_append_budget_snoc dyadic_iv_todo_acc_budget_snoc]
  show "int (length lns')
          + dyadic_iv_todo_append_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns', rns', ks')) + 2
        < int (max_snat LENGTH(gmp_poly_len))"
    unfolding vpush dyadic_iv_todo_append_budget_snoc using D(1) st lb by linarith
  show "int (length al')
          + dyadic_iv_todo_acc_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns', rns', ks')) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    unfolding vpush dyadic_iv_todo_acc_budget_snoc using D(2) sa ag by linarith
qed

text \<open>\<^bold>\<open>The seed instance.\<close> The seed worklist is the single root node, whose view is \<open>(0, 1)\<close>,
  and \<open>dyadic_iv_interval_todo_budget \<delta> (0,1)\<close> unfolds to \<open>int (2\<^sup>S\<^sup>u\<^sup>c\<^sup>\<^sup>(\<^sup>\<mu>\<^sup>\<^sup>(\<^sup>0\<^sup>,\<^sup>1\<^sup>)\<^sup>)) - 2\<close>, so the
  todo side is \<open>1 + (2\<^sup>\<mu>\<^sup>+\<^sup>1 - 2) + 2 < max_snat\<close>, i.e. \<open>mucap\<close> exactly. The accumulator is
  empty and its budget is one larger, so the same premise covers both sides.

  \<^bold>\<open>It takes \<open>mucap\<close>, not \<open>cap\<close> + \<open>kcap\<close>.\<close> What this invariant bounds is the worklist length, i.e. the node
  count of a depth-\<open>\<mu>\<close> tree, and \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 + 1 < max_snat\<close> is the direct statement of that; the linear
  k-potential @{const hybrid_root_potential} does not dominate it. It is also verbatim a clause
  \<open>dsc_isolate_all_split_pre\<close> already carries.\<close>
lemma hybrid_budget_invar_seed:
  assumes mucap: "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
                  < int (max_snat LENGTH(gmp_poly_len))"
    and vseed: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks) = [(0, 1)]"
    and lone: "length lns = 1"
  shows "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) ([], [], [])"
proof (rule hybrid_budget_invarI)
  show "int (length lns)
          + dyadic_iv_todo_append_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks)) + 2
        < int (max_snat LENGTH(gmp_poly_len))"
    unfolding vseed lone using mucap
    by (simp add: dyadic_iv_todo_append_budget_def dyadic_iv_interval_todo_budget_def)
  show "int (length ([] :: int list))
          + dyadic_iv_todo_acc_budget \<delta> (hybrid_alpha_views l0 r0 k0 (lns, rns, ks)) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    unfolding vseed using mucap
    by (simp add: dyadic_iv_todo_acc_budget_def dyadic_iv_interval_acc_budget_def)
qed

text \<open>\<^bold>\<open>The payload bound as its own predicate\<close>, following @{const hybrid_budget_invar}'s
  precedent rather than widening @{const hybrid_trunc_coupling}: a separate predicate is threaded and projected
  exactly as the budget invariant is, so the four body steps gain one subgoal each instead of a definition-wide
  re-check.

  \<^bold>\<open>What it says\<close>: a locked worklist slot's guard payload bounds that slot's own count. Only two
  arms can create a guard, and both are covered: @{thm [source] hybrid_pay_window_child}
  (the window push, with equality) and @{thm [source] hybrid_pay_split_child} (inheritance
  under a locked parent). Everything else is \<open>\<forall>i\<close> bookkeeping.\<close>
definition hybrid_pay_invar ::
  "gmp_dyadic_interval_vec \<Rightarrow> nat list \<Rightarrow> gmp_poly \<Rightarrow> bool" where
  "hybrid_pay_invar todo gs rp \<longleftrightarrow>
     (case todo of (lns, rns, ks) \<Rightarrow>
        (\<forall>i < length gs. hybrid_child_pay_ok (lns ! i) (ks ! i) (rns ! i) rp (gs ! i)))"

lemma hybrid_pay_invarD:
  assumes "hybrid_pay_invar (lns, rns, ks) gs rp" and "i < length gs"
  shows "hybrid_child_pay_ok (lns ! i) (ks ! i) (rns ! i) rp (gs ! i)"
  using assms unfolding hybrid_pay_invar_def by simp

text \<open>\<^bold>\<open>Seed\<close>: the root carries guard \<open>0\<close>, so the payload antecedent \<open>2\<^sup>4\<^sup>2 + 2 \<le> 0\<close> is false.\<close>
lemma hybrid_pay_invar_seed: "hybrid_pay_invar ([l], [r], [k]) [0] rp"
  by (simp add: hybrid_pay_invar_def hybrid_child_pay_ok_def)

text \<open>\<^bold>\<open>Pop\<close>: dropping the LIFO-last slot keeps every remaining one.\<close>
lemma hybrid_pay_invar_pop:
  assumes c: "hybrid_pay_invar (lns, rns, ks) gs rp"
    and L: "length lns = length gs" and R: "length rns = length gs"
    and K: "length ks = length gs"
  shows "hybrid_pay_invar (butlast lns, butlast rns, butlast ks) (butlast gs) rp"
  using c L R K unfolding hybrid_pay_invar_def
  by (auto simp: nth_butlast)

text \<open>\<^bold>\<open>One-child push\<close> (the window arm), \<^bold>\<open>two-child push\<close> (split). Same shape as
  @{thm [source] hybrid_trunc_coupling_push}: the prefix is untouched and each new slot arrives
  with its own atom already proved.\<close>
lemma hybrid_pay_invar_push1:
  assumes c: "hybrid_pay_invar (lns, rns, ks) gs rp"
    and L: "length lns = length gs" and R: "length rns = length gs"
    and K: "length ks = length gs"
    and p1: "hybrid_child_pay_ok l1 k1 r1 rp g1"
  shows "hybrid_pay_invar (lns @ [l1], rns @ [r1], ks @ [k1]) (gs @ [g1]) rp"
  using c L R K p1 unfolding hybrid_pay_invar_def
  by (auto simp: nth_append less_Suc_eq)

lemma hybrid_pay_invar_push2:
  assumes c: "hybrid_pay_invar (lns, rns, ks) gs rp"
    and L: "length lns = length gs" and R: "length rns = length gs"
    and K: "length ks = length gs"
    and p1: "hybrid_child_pay_ok l1 k1 r1 rp g1"
    and p2: "hybrid_child_pay_ok l2 k2 r2 rp g2"
  shows "hybrid_pay_invar (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
           (gs @ [g1, g2]) rp"
  using c L R K p1 p2 unfolding hybrid_pay_invar_def
  by (auto simp: nth_append less_Suc_eq)

\<comment> \<open>\<^bold>\<open>Carries the k-potential too\<close> (\<open>\<delta>\<close> is a parameter for that reason): the WHILEIT invariant
   is where the two column-value bounds have to live, because \<open>safe'\<close> at the popped state
   needs them for the node popped next and no column-length conjunct reaches it.
   \<^bold>\<open>And the two word budgets\<close>, for the same reason one level up: \<open>safe'\<close> at
   a pushed state needs a column cap one slot longer than \<open>step_pre\<close> gives, and a \<open>pushable\<close>
   accumulator after the accept arm has grown it. Neither is derivable from anything else here.
   \<^bold>\<open>And the root relation\<close> \<open>coeffs P = carried_init_same_den l0 2\<^sup>k\<^sup>0 r0 rp\<close>,
   bail's per-node \<open>newton_gmp_node_inv\<close> conjunct, obtained here at the state level. It is what
   makes \<open>hybrid_loop_correct\<close>'s \<open>\<And>s\<close> step usable: \<open>rp\<close> is a component of \<open>s\<close>, so the
   keystone's \<open>P_eq\<close> says nothing about an arbitrary \<open>s\<close>'s \<open>rp\<close>, and every \<open>rp\<close>-length premise
   the arms need (\<open>rp_len\<close>/\<open>rp_pb\<close>/\<open>rp_gb\<close>/\<open>rp_small\<close>/\<open>g_room\<close>) rides on it, since
   @{const carried_init_same_den} preserves length. It is preserved trivially: no arm touches \<open>P\<close>
   or \<open>rp\<close>.\<close>
definition hybrid_state_invar ::
  "real \<Rightarrow> int poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat)
     \<Rightarrow> hybrid_state \<Rightarrow> bool" where
  "hybrid_state_invar \<delta> P l0 r0 k0 seed st \<longleftrightarrow>
     (case st of ((todo, qtodo, es, ss, cs, gs, rp), acc) \<Rightarrow>
        hybrid_refine_invar P l0 r0 k0 seed todo qtodo es ss cs gs rp acc \<and>
        hybrid_cap_invar \<delta> l0 r0 k0 todo ss \<and>
        hybrid_budget_invar \<delta> l0 r0 k0 todo acc \<and>
        hybrid_pay_invar todo gs rp \<and>
        coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp)"

lemma hybrid_state_invar_simp[simp]:
  "hybrid_state_invar \<delta> P l0 r0 k0 seed ((todo, qtodo, es, ss, cs, gs, rp), acc)
     \<longleftrightarrow> hybrid_refine_invar P l0 r0 k0 seed todo qtodo es ss cs gs rp acc \<and>
         hybrid_cap_invar \<delta> l0 r0 k0 todo ss \<and>
         hybrid_budget_invar \<delta> l0 r0 k0 todo acc \<and>
         hybrid_pay_invar todo gs rp \<and>
         coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
  by (simp add: hybrid_state_invar_def)

lemma hybrid_loop_strengthened:
  "hybrid_loop_monadic todo qtodo es ss cs gs rp acc
     \<le> WHILEIT (\<lambda>st. hybrid_loop_safe_invar st \<and> hybrid_state_invar \<delta> P l0 r0 k0 seed st)
         hybrid_loop_cond hybrid_loop_body_checked_monadic
         ((todo, qtodo, es, ss, cs, gs, rp), acc)"
  unfolding hybrid_loop_monadic_unfold
  by (rule WHILEIT_weaken) simp

text \<open>\<^bold>\<open>Assembly, step 2: the \<open>\<alpha>\<close> projection of the whole loop state.\<close> Bail's \<open>blr_alpha\<close> zips the
  concrete polynomial column into the abstract node; the hybrid route is \<open>\<exists>pol\<close>, so the node
  carries only \<open>(a, b, e, depth, s)\<close> and @{const hybrid_alpha_nodes} (with \<open>_butlast\<close>/\<open>_append2\<close> laws here) is
  the todo side. acc projects exactly as bail's.\<close>
definition hybrid_alpha ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> hybrid_state
     \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list \<times> ((int \<times> int) \<times> nat) list" where
  "hybrid_alpha l0 r0 k0 st =
     (case st of ((todo, qtodo, es, ss, cs, gs, rp), acc) \<Rightarrow>
        (hybrid_alpha_nodes l0 r0 k0 todo es ss, dyadic_interval_vec_triples acc))"

lemma hybrid_alpha_simp[simp]:
  "hybrid_alpha l0 r0 k0 ((todo, qtodo, es, ss, cs, gs, rp), acc)
     = (hybrid_alpha_nodes l0 r0 k0 todo es ss, dyadic_interval_vec_triples acc)"
  by (simp add: hybrid_alpha_def)

text \<open>\<^bold>\<open>Assembly, step 4: the termination relation.\<close> \<open>WHILEIT_rule\<close> wants a well-founded \<open>R\<close>; the
  measure is @{const hybrid_mu_mset} on the node projection, and the multiset order it
  lives in is well-founded, so \<open>R\<close> is an \<open>inv_image\<close> of it. Bail's analogue is
  \<open>blr_mu_mset_rel_wf_bl\<close>.\<close>
definition hybrid_state_mu ::
  "real \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> hybrid_state \<Rightarrow> nat multiset" where
  "hybrid_state_mu \<delta> l0 r0 k0 st =
     (case st of ((todo, qtodo, es, ss, cs, gs, rp), acc) \<Rightarrow>
        hybrid_mu_mset \<delta> (hybrid_alpha_nodes l0 r0 k0 todo es ss))"

lemma hybrid_state_mu_simp[simp]:
  "hybrid_state_mu \<delta> l0 r0 k0 ((todo, qtodo, es, ss, cs, gs, rp), acc)
     = hybrid_mu_mset \<delta> (hybrid_alpha_nodes l0 r0 k0 todo es ss)"
  by (simp add: hybrid_state_mu_def)

lemma hybrid_state_mu_wf:
  "wf {(st', st). hybrid_state_mu \<delta> l0 r0 k0 st' < hybrid_state_mu \<delta> l0 r0 k0 st}"
proof -
  \<comment> \<open>same argument as bail's \<open>dyadic_iv_todo_mu_mset_list_rel_wf_bl\<close> (\<open>:2018\<close>): the multiset
     order on \<open>nat multiset\<close> is well-founded as a PREDICATE (\<open>wfp\<close>, by \<open>simp\<close>), converted to the
     set form via \<open>wfp_def\<close>; there is no \<open>wf_less_multiset\<close> in scope.\<close>
  have wf_ms_pred: "wfp ((<) :: nat multiset \<Rightarrow> nat multiset \<Rightarrow> bool)" by simp
  have wf_ms: "wf ({(x, y). x < y} :: (nat multiset \<times> nat multiset) set)"
    using wf_ms_pred by (simp add: wfp_def)
  show ?thesis
    using wf_inv_image[OF wf_ms, of "hybrid_state_mu \<delta> l0 r0 k0"]
    by (simp add: inv_image_def)
qed

text \<open>\<^bold>\<open>Assembly, step 5: the loop capstone.\<close> \<open>WHILEIT_rule\<close> on the strengthened loop (step 3),
  with the well-founded measure of step 4, transferred back to
  @{const hybrid_loop_monadic} by \<open>order_trans\<close>. Its three obligations are exactly
  seed / body step / exit, so the keystone reduces to the body-step obligation: every arm
  preserves @{const hybrid_refine_invar} and strictly decreases
  @{const hybrid_mu_mset}. Seed is @{thm [source] hybrid_refine_invar_seed}, exit is
  @{thm [source] hybrid_refine_invar_exit_cond}, and the four arms' invariant halves
  (\<open>hybrid_refine_invar_*_step\<close>) and decrease lemmas
  (\<open>hybrid_mu_mset_{pop,push1,push2}_less\<close>) are proven above.\<close>
lemma hybrid_loop_correct:
  assumes init: "hybrid_loop_safe_invar ((todo, qtodo, es, ss, cs, gs, rp), acc)
                 \<and> hybrid_state_invar \<delta> P l0 r0 k0 seed ((todo, qtodo, es, ss, cs, gs, rp), acc)"
    and step: "\<And>s. \<lbrakk> hybrid_loop_safe_invar s \<and> hybrid_state_invar \<delta> P l0 r0 k0 seed s;
                      hybrid_loop_cond s \<rbrakk>
               \<Longrightarrow> hybrid_loop_body_checked_monadic s
                 \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s'
                                 \<and> hybrid_state_invar \<delta> P l0 r0 k0 seed s')
                          \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                            < hybrid_state_mu \<delta> l0 r0 k0 s)"
    and exit: "\<And>s. \<lbrakk> hybrid_loop_safe_invar s \<and> hybrid_state_invar \<delta> P l0 r0 k0 seed s;
                      \<not> hybrid_loop_cond s \<rbrakk> \<Longrightarrow> \<Phi> s"
  shows "hybrid_loop_monadic todo qtodo es ss cs gs rp acc \<le> SPEC \<Phi>"
  apply (rule order_trans[OF hybrid_loop_strengthened])
  apply (rule WHILEIT_rule[where
      R = "{(st', st). hybrid_state_mu \<delta> l0 r0 k0 st' < hybrid_state_mu \<delta> l0 r0 k0 st}"])
  \<comment> \<open>bare \<open>apply\<close>, not \<open>subgoal by \<dots>\<close>: \<open>?P1 ?l0.1 ?r0.1 ?k0.1 ?seed1\<close> are still schematic
     here and are shared across the three subgoals, and a \<open>subgoal\<close> block fixes them, so
     \<open>rule init\<close> could not instantiate them.\<close>
  apply (rule hybrid_state_mu_wf)
  apply (rule init)
  apply (simp only: mem_Collect_eq prod.case)
  apply (rule step, assumption+)
  apply (rule exit, assumption+)
  done

text \<open>\<^bold>\<open>Assembly, step 6: the body reduces to the step.\<close> @{const hybrid_loop_body_checked_monadic}
  is only a re-check of the loop condition (\<open>Hybrid_Solver_Pipeline\<close>), so under the condition it is
  @{const hybrid_loop_step_monadic}. This peels the wrapper off the remaining
  obligation of @{thm [source] hybrid_loop_correct}.\<close>
lemma hybrid_loop_body_under_cond:
  assumes c: "hybrid_loop_cond st"
  shows "hybrid_loop_body_checked_monadic st = hybrid_loop_step_monadic st"
  unfolding hybrid_loop_body_checked_monadic_def PR_CONST_def using c by simp

text \<open>\<^bold>\<open>Assembly, step 7: the step reduces to the args form.\<close> @{const hybrid_loop_step_monadic}
  only destructures the flattened state, so the body obligation of
  @{thm [source] hybrid_loop_correct} is an obligation on
  @{const hybrid_loop_step_args_monadic}, the shape
  @{thm [source] hybrid_loop_step_args_pop} and the \<open>hybrid_after_pop_*\<close> compositions are
  stated against.\<close>
lemma hybrid_loop_step_unfold:
  "hybrid_loop_step_monadic ((todo, qtodo, es, ss, cs, gs, rp), acc)
     = hybrid_loop_step_args_monadic todo qtodo es ss cs gs acc rp"
  unfolding hybrid_loop_step_monadic_def PR_CONST_def by simp

text \<open>\<^bold>\<open>The pop's two word bounds, from \<open>2\<^sup>4\<^sup>0\<close>.\<close> Stated as \<open>rule\<close>s so the closers never
  unfold @{const max_snat} across a 30-hypothesis context, which is slow as a \<open>simp\<close>.\<close>
lemma small_len_b2: "n < 1099511627776 \<Longrightarrow> n + 2 < max_snat LENGTH(gmp_poly_len)"
  by (simp add: max_snat_def)

lemma small_len_dep: "n < 1099511627776 \<Longrightarrow> 1 * (n - 1) < max_snat LENGTH(gmp_poly_len)"
  by (simp add: max_snat_def)

text \<open>\<^bold>\<open>Assembly, step 8: the discard arm's body step.\<close> Chains
  @{thm [source] hybrid_loop_step_args_pop} (step \<open>\<rightarrow>\<close> ASSERTs \<open>\<rightarrow>\<close> after-pop) with
  @{thm [source] hybrid_after_pop_discard_acc} (resolve \<open>\<circ>\<close> dispatch on \<open>cnt = 0\<close>). The
  popped node's columns are the \<open>butlast\<close> of each, which is exactly the shape the abstract
  step lemma @{thm [source] hybrid_refine_invar_discard_step} consumes.\<close>
lemma hybrid_loop_step_args_discard:
  assumes tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lne: "lns \<noteq> []" and lr: "length rns = length lns" and lk: "length ks = length lns"
    and qne: "qtodo \<noteq> []" and ene: "es \<noteq> []" and sne: "ss \<noteq> []"
    and cne: "cs \<noteq> []" and gne: "gs \<noteq> []"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "last ks * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and cache: "hybrid_cs_ok (last gs) (last cs) (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> last gs \<Longrightarrow> last qtodo = X"
    and count0: "carried_descartes_count X = 0"
    and Qne: "0 < length (last qtodo)"
    and kcap: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne: "0 < length X"
    and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "last ss + 1 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    and accpush: "dyadic_interval_vec_pushable acc"
    and qcap: "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length (butlast gs) + 2 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the pop's two word bounds come from here (@{thm [source] small_len_b2}).
       \<^bold>\<open>Last\<close>, so that no \<open>[OF \<dots>]\<close> position moves.\<close>
    and Q_small: "length (last qtodo) < 1099511627776"
  shows "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs acc rp
       \<le> SPEC (\<lambda>(wl, acc'). acc' = acc \<and>
             wl = ((butlast lns, butlast rns, butlast ks), butlast qtodo,
                   butlast es, butlast ss, butlast cs, butlast gs, rp))"
  apply (rule order_trans[OF hybrid_loop_step_args_pop[OF tinv lne lr lk qne ene sne cne gne]])
  apply (refine_vcg hybrid_after_pop_discard_acc[OF rp_len rp_bound k_bound Q_bound
        X_pbound X_gbound X_eq cache locked_exact count0 Qne kcap X_ne X_len, THEN order_trans])
  apply (all \<open>((rule small_len_b2[OF Q_small] | rule small_len_dep[OF Q_small]); fail)?\<close>)
  apply (all \<open>((insert Qne Q_bound kcap scap1 rp_len rp_bound k_bound push2 accpush
                        qcap ecap sscap ccap gcap Q_small, (assumption | simp)); fail)?\<close>)
  done

text \<open>\<^bold>\<open>The step-args level for the \<open>cnt \<ge> 2\<close> gate-CLOSED arm.\<close> Same chain as
  @{thm [source] hybrid_loop_step_args_discard} -- @{thm [source] hybrid_loop_step_args_pop}
  then the after-pop composition -- but the popped node's columns are now the \<open>butlast\<close> of each
  WITH THE TWO CHILDREN APPENDED, which is the shape
  @{thm [source] hybrid_refine_invar_split_step} consumes. The after-pop lemma is cited BARE
  (\<open>rule\<close> + \<open>insert\<close>) rather than through a 32-slot \<open>[OF \<dots>]\<close>, to avoid re-counting arguments.\<close>
lemma hybrid_loop_step_args_split:
  assumes tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lne: "lns \<noteq> []" and lr: "length rns = length lns" and lk: "length ks = length lns"
    and qne: "qtodo \<noteq> []" and ene: "es \<noteq> []" and sne: "ss \<noteq> []"
    and cne: "cs \<noteq> []" and gne: "gs \<noteq> []"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "last ks * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and cache: "hybrid_cs_ok (last gs) (last cs) (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> last gs \<Longrightarrow> last qtodo = X"
    and frame: "node_frame X (last qtodo) (last gs)"
    \<comment> \<open>\<^bold>\<open>The trichotomy, not \<open>g_small\<close>.\<close> A locked pop is reachable (the window arm's own push sets
       \<open>2\<^sup>4\<^sup>2 + v\<close>), so an unlocked-only form would make this lemma inapplicable at exactly the node the window arm
       creates. Every layer below takes the trichotomy (\<open>hybrid_branch_split_acc\<close>,
       \<open>hybrid_resolved_node_facts\<close>). \<open>g_cpl\<close> is the coupling conjunct in the form the coupling states it.\<close>
    and g_tri: "last gs < 1099511627776 \<or> 4398046511104 \<le> last gs"
    and count2: "2 \<le> carried_descartes_count X"
    and gate_closed: "\<not> newton_pol_gate_len (length (last qtodo)) (last es) (last ks) (last ss)"
    \<comment> \<open>\<^bold>\<open>At \<open>g\<close>, not \<open>\<And>g1\<close>.\<close> The free-variable form would be
       unsatisfiable (see \<open>hybrid_step_args_gcap_rp_forall_g_is_vacuous\<close>). The guard the
       truncation layer sees is the resolved one, and @{thm [source] hybrid_resolve_guard_cases}
       pins it to \<open>2\<^sup>4\<^sup>2\<close> or \<open>g\<close>, so \<open>max g 2\<^sup>4\<^sup>2\<close> dominates it; @{thm [source] hybrid_branch_split_acc}
       has the same shape.\<close>
    and gcap_rp: "max (last gs) 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>and the LOCK instance\<close>: the gate-open reject arm hands
       \<open>hybrid_branch_split_acc\<close> the lock guard \<open>2\<^sup>4\<^sup>2 + v\<close>, which \<open>max g 2\<^sup>4\<^sup>2\<close> does not
       dominate --- it carries the payload. Both instances are satisfiable; the free-variable
       form that covered them at once was not.\<close>
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length (last qtodo)"
    and kcap: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne: "0 < length X"
    and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and Q_small: "length (last qtodo) < 1099511627776"
    and X_small: "length X < 1099511627776"
    and scap1: "last ss + 1 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length (butlast gs) + 2 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the popped node's coupling conjunct, at its own depth. Discharged at the body step
       from @{const hybrid_trunc_coupling} at the last index — the same place \<open>g_small\<close>
       comes from.\<close>
    and g_cpl: "last gs \<le> (last ks + 1) * length rp \<or> 4398046511104 \<le> last gs"
    \<comment> \<open>\<^bold>\<open>The payload bound\<close>, \<^bold>\<open>last\<close> so that no \<open>[OF \<dots>]\<close> position moves.
       \<open>payg\<close> is the popped node's own conjunct of @{const hybrid_pay_invar}; \<open>lr\<close> is the node
       non-degeneracy, read off \<open>hybrid_cap_invar\<close> through the node view at the assembly.\<close>
    and payg: "hybrid_child_pay_ok (last lns) (last ks) (last rns) rp (last gs)"
    \<comment> \<open>\<^bold>\<open>\<open>lrne\<close>, not \<open>lr\<close>\<close>: \<open>lr\<close> is already this lemma's \<open>length rns = length lns\<close>, and the
       shadow made @{thm [source] hybrid_loop_step_args_pop} unmatchable --- reported as a bare
       \<open>OF: no unifiers\<close> naming no premise.\<close>
    and lrne: "last lns < last rns"
  shows "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
       \<le> SPEC (\<lambda>(wl, acc').
           (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
              acc' = (al @ [last lns + last rns], ar @ [last lns + last rns],
                      ak @ [last ks + 1])) \<and>
           (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
           hybrid_split_wl X (butlast lns) (butlast rns) (butlast ks) (butlast qtodo) (butlast es) (butlast ss) (butlast cs) (butlast gs) rp (last lns) (last rns) (last ks) (last es) (last ss) wl)"
  apply (rule order_trans[OF hybrid_loop_step_args_pop[OF tinv lne lr lk qne ene sne cne gne]])
  apply (refine_vcg hybrid_after_pop_split_acc[THEN order_trans])
  \<comment> \<open>the pop's two ASSERTs (\<open>+2\<close> and the depth product at multiplier \<open>1\<close>) on the popped
     node, both from \<open>Q_small\<close>.\<close>
  apply (all \<open>((rule small_len_b2[OF Q_small] | rule small_len_dep[OF Q_small]); fail)?\<close>)
  apply (all \<open>((insert rp_len rp_bound k_bound Q_bound X_pbound X_gbound X_eq cache
                        locked_exact frame g_tri count2 gate_closed gcap_rp gcap_lock Qne kcap
                        X_ne X_len Q_small X_small accpush rp_small rp_pb
                        qcap gcap ecap sscap ccap push2 scap1 g_cpl payg lrne,
                 (assumption | simp)); fail)?\<close>)
  done

text \<open>\<^bold>\<open>The step-args level for the \<open>cnt \<ge> 2\<close> gate-OPEN arm.\<close> Same chain as
  @{thm [source] hybrid_loop_step_args_split} -- @{thm [source] hybrid_loop_step_args_pop}
  then the after-pop composition -- with the popped node's columns the \<open>butlast\<close> of each and
  the gate-OPEN DISJUNCTION as the conclusion.\<close>
lemma hybrid_loop_step_args_window:
  assumes tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lne: "lns \<noteq> []" and lr: "length rns = length lns" and lk: "length ks = length lns"
    and qne: "qtodo \<noteq> []" and ene: "es \<noteq> []" and sne: "ss \<noteq> []"
    and cne: "cs \<noteq> []" and gne: "gs \<noteq> []"
    and gate_open: "newton_pol_gate_len (length (last qtodo)) (last es) (last ks) (last ss)"
    and count2: "2 \<le> carried_descartes_count X"
    \<comment> \<open>\<^bold>\<open>The trichotomy, not \<open>g_small\<close>\<close>, as in the split twin:
       a window child pops with the lock \<open>2\<^sup>4\<^sup>2 + v\<close> set, and the unlocked-only form would exclude
       exactly that node.\<close>
    and g_tri: "last gs < 1099511627776 \<or> 4398046511104 \<le> last gs"
    and g_cpl: "last gs \<le> (last ks + 1) * length rp \<or> 4398046511104 \<le> last gs"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and cache: "hybrid_cs_ok (last gs) (last cs) (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> last gs \<Longrightarrow> last qtodo = X"
    and exact0: "last gs = 0 \<longrightarrow> last qtodo = X"
    and frame: "node_frame X (last qtodo) (last gs)"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "last ks * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len)"
    and Qne: "0 < length (last qtodo)"
    and Q_small: "length (last qtodo) < 1099511627776"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_ne: "0 < length X"
    and X_ne1: "1 < length X"
    and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_b2: "length X + 2 < max_snat LENGTH(gmp_poly_len)"
    and X_small: "length X < 1099511627776"
    and ecap: "last es < LENGTH(gmp_poly_len)"
    and ecap2: "2 ^ last es + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap3: "last es + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap2: "last ks + (2 ^ last es + 2) < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ last es + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
    and vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    and vcap2: "4398046511104 + carried_descartes_count X < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>At \<open>g\<close>, not \<open>\<And>g1\<close>.\<close> The free-variable form would be
       unsatisfiable (see \<open>hybrid_step_args_gcap_rp_forall_g_is_vacuous\<close>). The guard the
       truncation layer sees is the resolved one, and @{thm [source] hybrid_resolve_guard_cases}
       pins it to \<open>2\<^sup>4\<^sup>2\<close> or \<open>g\<close>, so \<open>max g 2\<^sup>4\<^sup>2\<close> dominates it; @{thm [source] hybrid_branch_split_acc}
       has the same shape.\<close>
    and gcap_rp: "max (last gs) 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>and the LOCK instance\<close>: the gate-open reject arm hands
       \<open>hybrid_branch_split_acc\<close> the lock guard \<open>2\<^sup>4\<^sup>2 + v\<close>, which \<open>max g 2\<^sup>4\<^sup>2\<close> does not
       dominate --- it carries the payload. Both instances are satisfiable; the free-variable
       form that covered them at once was not.\<close>
    and gcap_lock: "4398046511104 + carried_descartes_count X + length rp
                      < max_snat LENGTH(gmp_poly_len)"
    and kcap: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and rp_small: "length rp < 1099511627776"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and qcap: "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length (butlast gs) + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecapl: "length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    and push1: "dyadic_interval_vec_pushable (butlast lns, butlast rns, butlast ks)"
    and kslen: "length (butlast ks) + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "last ss + 1 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The payload bound\<close>, \<^bold>\<open>last\<close>. \<open>payg\<close> is the popped node's own conjunct of
       @{const hybrid_pay_invar}; \<open>lr\<close> is its non-degeneracy.\<close>
    and payg: "hybrid_child_pay_ok (last lns) (last ks) (last rns) rp (last gs)"
    and lrne: "last lns < last rns"
  shows "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
       \<le> SPEC (\<lambda>(wl, acc').
           ((poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                 acc' = (al @ [last lns + last rns], ar @ [last lns + last rns], ak @ [last ks + 1])) \<and>
              (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
                            hybrid_split_wl X (butlast lns) (butlast rns) (butlast ks) (butlast qtodo) (butlast es) (butlast ss) (butlast cs) (butlast gs) rp (last lns) (last rns) (last ks) (last es) (last ss) wl)
           \<or>
           (\<exists>m cand v. acc' = (al, ar, ak) \<and>
              v = carried_descartes_count X \<and>
              carried_descartes_count cand = v \<and>
              newton_window_pick_bail v (last es) X = Some (m, cand) \<and>
              wl = ((butlast lns @ [last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns)],
                     butlast rns @ [last lns * 2 ^ (2 ^ last es + 2) + (m + 4) * (last rns - last lns)],
                     butlast ks @ [last ks + (2 ^ last es + 2)]),
                    butlast qtodo @ [cand], butlast es @ [last es + 1], butlast ss @ [last ss],
                    butlast cs @ [v + 2], butlast gs @ [4398046511104 + v], rp)))"
  apply (rule order_trans[OF hybrid_loop_step_args_pop[OF tinv lne lr lk qne ene sne cne gne]])
  \<comment> \<open>\<^bold>\<open>Pin \<open>X\<close>\<close>: without it \<open>refine_vcg\<close> unifies the lemma's \<open>X\<close> with the op's \<open>Q\<close>
     (\<open>last qtodo\<close>), and every premise stated at \<open>X\<close> then arrives at the wrong node.\<close>
  apply (refine_vcg hybrid_after_pop_window_acc[where X = X, THEN order_trans])
  apply (all \<open>((rule small_len_b2[OF Q_small] | rule small_len_dep[OF Q_small]); fail)?\<close>)
  \<comment> \<open>\<^bold>\<open>\<open>assumption\<close> pass FIRST\<close>: nearly every premise is a literal copy of one of this
     lemma's own, and handing all 44 to a single \<open>simp\<close> re-derives from a huge context once
     per goal and trips the wire -- \<open>hybrid_after_pop_split_acc\<close>'s own note, which this
     lemma reproduced verbatim by ignoring it.\<close>
  apply (all \<open>((insert gate_open count2 g_tri g_cpl X_eq cache locked_exact exact0 frame
                        rp_len rp_bound k_bound Q_bound Qne Q_small X_pbound X_gbound
                        X_ne X_ne1 X_len X_b2 X_small ecap ecap2 ecap3 kcap2 gate4
                        vcap1 vcap2 gcap_rp gcap_lock kcap accpush rp_small rp_pb qcap gcap ecapl
                        sscap ccap push2 push1 kslen scap1 payg lrne,
                 assumption); fail)?\<close>)
  \<comment> \<open>ONE survivor, and it needs ONE fact: \<open>last gs = 0 \<Longrightarrow> last qtodo = X\<close> is \<open>exact0\<close> in
     meta form. Inserting the whole 44-premise list here is what tripped the wire twice.\<close>
  apply (insert exact0, simp)
  done

text \<open>\<^bold>\<open>Assembly, step 9: the accept arm.\<close> Chains
  @{thm [source] hybrid_loop_step_args_pop} (step \<open>\<rightarrow>\<close> ASSERTs \<open>\<rightarrow>\<close> after-pop) with
  @{thm [source] hybrid_after_pop_accept_acc} (resolve \<open>\<circ>\<close> dispatch on \<open>cnt = 1\<close>). The
  popped node's columns are the \<open>butlast\<close> of each, which is exactly the shape the abstract
  step lemma @{thm [source] hybrid_refine_invar_accept_step} consumes.\<close>
lemma hybrid_loop_step_args_accept:
  assumes tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lne: "lns \<noteq> []" and lr: "length rns = length lns" and lk: "length ks = length lns"
    and qne: "qtodo \<noteq> []" and ene: "es \<noteq> []" and sne: "ss \<noteq> []"
    and cne: "cs \<noteq> []" and gne: "gs \<noteq> []"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and k_bound: "last ks * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and Q_bound: "length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and cache: "hybrid_cs_ok (last gs) (last cs) (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> last gs \<Longrightarrow> last qtodo = X"
    and count1: "carried_descartes_count X = 1"
    and Qne: "0 < length (last qtodo)"
    and kcap: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and X_ne: "0 < length X"
    and X_len: "length X + 1 < max_snat LENGTH(gmp_poly_len)"
    and scap1: "last ss + 1 < max_snat LENGTH(gmp_poly_len)"
    and push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    and accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    and qcap: "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    and ecap: "length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len)"
    and sscap: "length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len)"
    and ccap: "length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len)"
    and gcap: "length (butlast gs) + 2 < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the pop's two word bounds come from here (@{thm [source] small_len_b2}).
       \<^bold>\<open>Last\<close>, so that no \<open>[OF \<dots>]\<close> position moves.\<close>
    and Q_small: "length (last qtodo) < 1099511627776"
  shows "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
       \<le> SPEC (\<lambda>(wl, acc').
             acc' = (al @ [last lns], ar @ [last rns], ak @ [last ks]) \<and>
             wl = ((butlast lns, butlast rns, butlast ks), butlast qtodo,
                   butlast es, butlast ss, butlast cs, butlast gs, rp))"
  apply (rule order_trans[OF hybrid_loop_step_args_pop[OF tinv lne lr lk qne ene sne cne gne]])
  apply (refine_vcg hybrid_after_pop_accept_acc[OF rp_len rp_bound k_bound Q_bound
        X_pbound X_gbound X_eq cache locked_exact count1 accpush Qne kcap X_ne X_len,
        THEN order_trans])
  apply (all \<open>((rule small_len_b2[OF Q_small] | rule small_len_dep[OF Q_small]); fail)?\<close>)
  apply (all \<open>((insert Qne Q_bound kcap scap1 rp_len rp_bound k_bound push2 accpush
                        qcap ecap sscap ccap gcap Q_small, (assumption | simp)); fail)?\<close>)
  done

text \<open>\<^bold>\<open>Assembly, step 10: the loop, with the keystone's own conclusion.\<close> Instantiates
  @{thm [source] hybrid_loop_correct} at \<open>\<Phi> :=\<close> the \<open>\<exists>pol\<close> property and discharges its exit
  obligation with @{thm [source] hybrid_refine_invar_exit_cond}. What is left is exactly the
  loop-entry invariant and the body step, i.e. the four arms.\<close>
lemma hybrid_loop_expol:
  assumes init: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)
                 \<and> hybrid_state_invar \<delta> P l0 r0 k0 (a, b, e0, dk0, 0)
                     (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and step: "\<And>s. \<lbrakk> hybrid_loop_safe_invar s
                      \<and> hybrid_state_invar \<delta> P l0 r0 k0 (a, b, e0, dk0, 0) s;
                      hybrid_loop_cond s \<rbrakk>
               \<Longrightarrow> hybrid_loop_body_checked_monadic s
                 \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s'
                                 \<and> hybrid_state_invar \<delta> P l0 r0 k0 (a, b, e0, dk0, 0) s')
                          \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                            < hybrid_state_mu \<delta> l0 r0 k0 s)"
  shows "hybrid_loop_monadic (lns, rns, ks) qtodo es ss cs gs rp acc
       \<le> SPEC (\<lambda>(wl, acc').
             (case wl of (todo', qtodo', es', ss', cs', gs', rp') \<Rightarrow> qtodo' = []) \<and>
             dyadic_interval_vec_invar acc' \<and>
             length (dyadic_interval_vec_triples acc') + 1
               < max_snat LENGTH(gmp_poly_len) \<and>
             (\<exists>pol.
               mset (dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc'))
                 = mset (newdsc_pol_bail_int pol a b e0 dk0 P)))"
  apply (rule hybrid_loop_correct[OF init step])
  apply assumption
  apply assumption
  apply (clarsimp simp: hybrid_state_invar_def split: prod.splits)
  apply (intro conjI)
  \<comment> \<open>\<open>qtodo = []\<close>: the loop cond is \<open>lns \<noteq> []\<close>, so its negation empties the todo column,
     and @{const hybrid_loop_state_invar}'s equal-column-lengths conjunct carries that to
     \<open>qtodo\<close>. Needed by the wrapper's \<open>ASSERT (qtodo = [])\<close>.\<close>
    apply (auto simp: hybrid_loop_safe_invar_def hybrid_loop_state_invar_def
                      hybrid_loop_cond_def Let_def)[1]
  \<comment> \<open>\<open>dyadic_interval_vec_invar acc\<close>: a direct conjunct of the same invariant, and the
     keystone's own first conclusion conjunct.\<close>
   apply (auto simp: hybrid_loop_safe_invar_def hybrid_loop_state_invar_def Let_def)[1]
  \<comment> \<open>\<^bold>\<open>The acc cap\<close>, \<open>length acc + 1 < max_snat\<close>, from
     @{const hybrid_budget_invar}, which is an unguarded conjunct of
     @{const hybrid_state_invar} and therefore still holds at the exit state. The worklist is
     empty here, which is why @{thm [source] hybrid_budget_invar_acc_cap} is the
     accessor and not \<open>_acc_grown\<close>. \<open>triples\<close> is a \<open>zip\<close>, so its length is the \<open>lns\<close> column's
     under the vector invariant's equal-length conjunct.\<close>
   apply (clarsimp simp: hybrid_loop_safe_invar_def hybrid_loop_state_invar_def
                         dyadic_interval_vec_invar_def dyadic_interval_vec_triples_def Let_def)
   \<comment> \<open>\<open>drule\<close> then \<open>simp\<close>, not \<open>erule\<close>: the cap is about the FIRST column and \<open>clarsimp\<close> has
      already normalised the \<open>zip\<close>'s length to the SECOND, so the two are joined by the
      equal-column-lengths conjunct rather than by unification.\<close>
   apply (drule hybrid_budget_invar_acc_cap)
   apply simp
  apply (rule hybrid_refine_invar_exit_cond; assumption)
  done

text \<open>\<^bold>\<open>Assembly, step 11: the runtime-safety half, pop case.\<close> \<open>hybrid_loop_state_invar\<close> is
  the vector invariant on \<open>todo\<close>/\<open>acc\<close> plus equal column lengths, so a uniform \<open>butlast\<close> preserves it.\<close>
lemma hybrid_loop_state_invar_pop:
  assumes "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
  shows "hybrid_loop_state_invar
           (((butlast lns, butlast rns, butlast ks), butlast qtodo,
             butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
  using assms unfolding hybrid_loop_state_invar_def
  by (auto simp: Let_def dyadic_interval_vec_invar_def)

text \<open>\<^bold>\<open>Three list helpers, kept ADJACENT to their only use.\<close> This file's dependency order is
  not its reading order, and relocating a block by hand after the fact loses lemmas silently --
  which cost a whole reverted attempt at the lemma below.\<close>
lemma butlast_ne_iff: "butlast xs \<noteq> [] \<longleftrightarrow> 1 < length xs"
  by (cases xs rule: rev_cases) auto

text \<open>The column caps are all \<open>length (butlast c) + 2 < max_snat\<close> and the popped state needs them
  one \<open>butlast\<close> deeper. HOL carries no \<open>length (butlast xs) \<le> length xs\<close> to chain on
  (\<open>find_theorems\<close> confirms), so one \<open>linarith\<close> step supplies it.\<close>
lemma butlast_cap_mono:
  assumes "length (butlast xs) + 2 < M"
  shows "length (butlast (butlast xs)) + 2 < M"
proof -
  have "length (butlast (butlast xs)) \<le> length (butlast xs)" by simp
  thus ?thesis using assms by linarith
qed

text \<open>\<^bold>\<open>The index bridge.\<close> \<open>hybrid_loop_step_pre\<close> speaks of \<open>last (butlast c)\<close> while every
  invariant conjunct is indexed, and a \<open>find_theorems\<close> on \<open>last (butlast _)\<close> finds nothing -- so
  rewrite to the index form FIRST rather than handing \<open>simp\<close> both and letting it search.\<close>
lemma last_butlast_conv_nth:
  assumes ne: "butlast xs \<noteq> []" shows "last (butlast xs) = xs ! (length xs - 2)"
proof -
  have L: "1 < length xs" using ne by (simp add: butlast_ne_iff)
  have "last (butlast xs) = butlast xs ! (length (butlast xs) - 1)"
    using ne by (simp add: last_conv_nth)
  also have "\<dots> = xs ! (length xs - 2)"
    using L by (simp add: nth_butlast numeral_2_eq_2)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>\<open>safe'\<close> at the popped state\<close> -- the premise all four arm lemmas take, and the reason the
  k-potential is in the invariant at all. @{const hybrid_loop_safe_invar} is not
  inductive on its own: @{const hybrid_loop_step_pre} states its capacity facts at the \<open>last\<close>
  node, so after a pop they are needed for a DIFFERENT element, which no column-length conjunct
  reaches. Each has a source -- the depth from
  @{thm [source] hybrid_cap_invar_depth_succ_le} against \<open>kcap\<close>, the depth-times-length product
  from @{thm [source] hybrid_cap_invar_depth_le} fed to \<open>kdepth\<close>, the run length from
  @{thm [source] hybrid_cap_invar_sigma_nth}, and the popped node's polynomial length from the
  coupling's frame, which pins EVERY stored poly to \<open>length rp\<close>.

  \<open>kcap\<close>/\<open>kdepth\<close> are stated against @{const hybrid_root_potential} because that is verbatim
  the shape the keystone's own \<open>kcap\<close>/\<open>k_depth_safe\<close> premises have.

  \<^bold>\<open>The two column-length fact sets orient the same equality OPPOSITE ways\<close> (\<open>L\<close> from the
  coupling gives \<open>length lns = length qtodo\<close>, \<open>SL\<close> from the state invariant the reverse), so
  handing \<open>simp\<close> both is a REWRITE LOOP. Take \<open>SL\<close>
  and \<open>K\<close>, plus \<open>L(2)\<close> alone for the one column \<open>SL\<close> does not cover.\<close>
lemma hybrid_loop_safe_invar_pop_all:
  assumes stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and cpl: "hybrid_trunc_coupling (lns, rns, ks) qtodo gs rp"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and dpos: "0 < \<delta>"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_loop_safe_invar
           (((butlast lns, butlast rns, butlast ks), butlast qtodo,
             butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
proof -
  have L: "length lns = length qtodo" "length rns = length qtodo"
     and K: "length ks = length qtodo" "length gs = length qtodo"
    using cpl unfolding hybrid_trunc_coupling_def by simp_all
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have body: "\<And>i. i < length qtodo \<Longrightarrow>
      node_frame (carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp) (qtodo ! i) (gs ! i)"
    using cpl unfolding hybrid_trunc_coupling_def by simp
  have qlen: "\<And>i. i < length qtodo \<Longrightarrow> length (qtodo ! i) = length rp"
  proof -
    fix i :: nat assume ilt: "i < length qtodo"
    have "length (carried_init_same_den (lns ! i) (2 ^ (ks ! i)) (rns ! i) rp) = length rp"
      by (simp add: truncate_length_carried_init_same_den)
    thus "length (qtodo ! i) = length rp"
      using cdlr_node_frame_len[OF body[OF ilt]] by simp
  qed
  have stinv': "hybrid_loop_state_invar
                  (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                    butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
    by (rule hybrid_loop_state_invar_pop[OF stinv])
  show ?thesis
  proof (cases "butlast lns = []")
    case True
    \<comment> \<open>the popped worklist is empty, so the loop condition is false and \<open>step_pre\<close> is not
       required at all -- \<open>safe_invar\<close> is then just the state invariant.\<close>
    thus ?thesis
      using stinv' by (simp add: hybrid_loop_safe_invar_def hybrid_loop_cond_def)
  next
    case False
    hence lne': "butlast lns \<noteq> []" .
    have lgt: "1 < length lns" using lne' by (simp add: butlast_ne_iff)
    have ilt: "length ks - 2 < length ks" using lgt K SL by simp
    have iltq: "length qtodo - 2 < length qtodo" using lgt SL by simp
    have ne': "butlast qtodo \<noteq> []" "butlast es \<noteq> []" "butlast ss \<noteq> []"
       "butlast cs \<noteq> []" "butlast gs \<noteq> []" "butlast ks \<noteq> []" "butlast rns \<noteq> []"
      using lgt SL K L(2) by (simp_all add: butlast_ne_iff)
    \<comment> \<open>the three column-VALUE facts, at the index that is about to become last.\<close>
    have kb1: "int (ks ! (length ks - 2)) + 1 \<le> hybrid_root_potential \<delta> k0"
      by (rule hybrid_cap_invar_depth_succ_le[OF capinv ilt dpos])
    have kb2: "int (ks ! (length ks - 2)) \<le> hybrid_root_potential \<delta> k0"
      by (rule hybrid_cap_invar_depth_le[OF capinv ilt])
    have sb: "ss ! (length ks - 2) \<le> ks ! (length ks - 2)"
      by (rule hybrid_cap_invar_sigma_nth[OF capinv]) (use ilt SL K in simp)
    \<comment> \<open>as NAT facts at the index first; the \<open>last\<close>-form rewrite is then pure bookkeeping with no
       coercion in it.\<close>
    have kbn: "ks ! (length ks - 2) + 1 < max_snat LENGTH(gmp_poly_len)"
      using kb1 kcap by linarith
    have kbp: "ks ! (length ks - 2) * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
      by (rule kdepth[OF kb2])
    have sbn: "ss ! (length ks - 2) + 1 < max_snat LENGTH(gmp_poly_len)"
      using sb kbn by simp
    have kb1': "last (butlast ks) + 1 < max_snat LENGTH(gmp_poly_len)"
      using kbn by (simp add: last_butlast_conv_nth[OF ne'(6)])
    have kb2': "last (butlast ks) * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
      using kbp by (simp add: last_butlast_conv_nth[OF ne'(6)])
    have sb': "last (butlast ss) + 1 < max_snat LENGTH(gmp_poly_len)"
      using sbn by (simp add: last_butlast_conv_nth[OF ne'(3)] SL K)
    have Qlen: "length (last (butlast qtodo)) = length rp"
      using qlen[OF iltq] by (simp add: last_butlast_conv_nth[OF ne'(1)])
    \<comment> \<open>and non-emptiness, which \<open>step_pre\<close> states as \<open>0 < length \<dots>\<close> but \<open>simp\<close> normalises to
       \<open>\<noteq> []\<close> -- it does not cross that on its own from the length equation.\<close>
    have Qne': "last (butlast qtodo) \<noteq> []" and Qne2: "0 < length (last (butlast qtodo))"
      using Qlen rp_len by auto
    note Pu = pre[unfolded hybrid_loop_step_pre_def]
    show ?thesis
      unfolding hybrid_loop_safe_invar_def hybrid_loop_step_pre_def
    proof (intro conjI impI)
      show "hybrid_loop_state_invar
              (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
        by (rule stinv')
    \<comment> \<open>\<open>Qne'\<close> goes in the \<open>add:\<close> list, not the \<open>use\<close> list: as a chained fact \<open>simp\<close> discards it
       (derivable from \<open>Qlen\<close> and \<open>rp_len\<close> in context, so it counts as trivial) and the goal it
       would have closed survives; as a simp RULE a non-equational fact becomes \<open>A \<equiv> True\<close> and
       rewrites that goal away.\<close>
    qed (use lne' ne' Pu kb1' kb2' sb' Qlen rp_len rp_bound SL K in
           \<open>simp_all add: dyadic_interval_vec_pushable2_def dyadic_interval_vec_pushable_def
                          butlast_ne_iff butlast_cap_mono Qne' Qne2\<close>)
  qed
qed

text \<open>\<^bold>\<open>\<open>safe'\<close> at a TWO-CHILD pushed state\<close> -- the PUSH twin of
  @{thm [source] hybrid_loop_safe_invar_pop_all}, and the lemma that discharges the split arm's
  (and the window arm's REJECT half's) \<open>safe'\<close>. Same four sources as the pop twin, plus the one
  the pop twin does not need: the worklist LENGTHENED, so
  @{thm [source] hybrid_budget_invar_todo_cap} supplies the extra column slot that
  @{const hybrid_loop_step_pre} asserts one longer than it gives.

  \<^bold>\<open>Every column cap collapses onto two\<close>: \<open>simp\<close> rewrites \<open>length qtodo\<close>/\<open>es\<close>/\<open>ss\<close>/\<open>cs\<close>/\<open>gs\<close>
  through the state invariant's equalities down to \<open>length rns\<close>, so proving the \<open>rns\<close> and \<open>ks\<close>
  forms covers all six. The accumulator is UNCHANGED here (the split arm's mid-root growth is a
  separate premise shape); the pushed polynomials enter only through their lengths, which is
  exactly what the arm's exported @{const node_frame} gives via
  @{thm [source] cdlr_node_frame_len}.\<close>
text \<open>\<^bold>\<open>Swapping the accumulator out of a safety fact\<close>: the accept arm's
  \<open>safe\<close>\<open>'\<close>, which is @{thm [source] hybrid_loop_safe_invar_pop_all} at a grown accumulator.
  It is a swap and not a re-proof because \<open>acc\<close> enters @{const hybrid_loop_safe_invar} through
  exactly two conjuncts: \<open>dyadic_interval_vec_invar acc\<close> in the state invariant and
  \<open>dyadic_interval_vec_pushable acc\<close> in \<open>step_pre\<close>. Nothing else in either predicate mentions it.\<close>
lemma hybrid_loop_safe_invar_acc_swap:
  assumes s: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and inv': "dyadic_interval_vec_invar acc'"
    and push': "dyadic_interval_vec_pushable acc'"
  shows "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc')"
  using assms
  unfolding hybrid_loop_safe_invar_def hybrid_loop_state_invar_def
            hybrid_loop_step_pre_def hybrid_loop_cond_def
  by (auto simp: Let_def)

lemma hybrid_loop_safe_invar_push2_all:
  assumes stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and capinv': "hybrid_cap_invar \<delta> l0 r0 k0
                    (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [j1, j2])
                    (butlast ss @ [sv1, sv2])"
    and qlenr: "length qr = length rp"
    \<comment> \<open>\<^bold>\<open>The accumulator may have GROWN by the midpoint root\<close> -- the split and window arms
       both branch on it, and \<open>\<le> \<dots> + 1\<close> covers the unchanged branch too, so one shape serves
       both. The extra slot is paid by @{thm [source] hybrid_budget_invar_acc_grown}.\<close>
    and accg: "length al' \<le> length al + 1"
    and accinv: "dyadic_interval_vec_invar (al', ar', ak')"
    and dpos: "0 < \<delta>"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_loop_safe_invar
           (((butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [j1, j2]),
             butlast qtodo @ [ql, qr], butlast es @ [e1, e2],
             butlast ss @ [sv1, sv2], butlast cs @ [c1, c2], butlast gs @ [g1, g2], rp),
            (al', ar', ak'))"
proof -
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have lne: "lns \<noteq> []" using pre unfolding hybrid_loop_step_pre_def by simp
  have tcap: "length lns + 2 < max_snat LENGTH(gmp_poly_len)"
    by (rule hybrid_budget_invar_todo_cap[OF budinv])
  \<comment> \<open>the accumulator's own cap, for the branch that grew it. \<open>ar'\<close>/\<open>ak'\<close> ride on \<open>al'\<close>
     through \<open>accinv\<close>, which is why the three columns need only ONE length premise.\<close>
  have acap: "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
    by (rule hybrid_budget_invar_acc_grown[OF budinv lne VL(1) VL(2)])
  have apush: "dyadic_interval_vec_pushable (al', ar', ak')"
    using acap accg accinv
    unfolding dyadic_interval_vec_pushable_def dyadic_interval_vec_invar_def by simp
  \<comment> \<open>the two column-VALUE facts at the index that IS last after the push. \<^bold>\<open>Stated at
     \<open>Suc (length ks - Suc 0)\<close>, the form \<open>simp\<close> PRODUCES\<close>, not at the \<open>length (butlast ks) + 1\<close>
     the push writes: instantiated the other way the \<open>nth\<close> rewrite stops firing on the cited
     fact -- this file's iron rule, paid for again here.\<close>
  have kidx: "Suc (length ks - Suc 0) < length (butlast ks @ [j1, j2])" by simp
  have knth: "(butlast ks @ [j1, j2]) ! Suc (length ks - Suc 0) = j2"
    by (simp add: nth_append)
  have sidx: "Suc (length ks - Suc 0) < length (butlast ss @ [sv1, sv2])"
    using SL VL by simp
  have snth: "(butlast ss @ [sv1, sv2]) ! Suc (length ks - Suc 0) = sv2"
    using SL VL by (simp add: nth_append)
  have kb1: "int j2 + 1 \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_succ_le[OF capinv' kidx dpos] by (simp add: knth)
  have kb2: "int j2 \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_le[OF capinv' kidx] by (simp add: knth)
  have sb: "sv2 \<le> j2"
    using hybrid_cap_invar_sigma_nth[OF capinv' sidx] by (simp add: knth snth)
  have kbn: "j2 + 1 < max_snat LENGTH(gmp_poly_len)" using kb1 kcap by linarith
  have kbp: "j2 * (length rp - 1) < max_snat LENGTH(gmp_poly_len)" by (rule kdepth[OF kb2])
  have sbn: "sv2 + 1 < max_snat LENGTH(gmp_poly_len)" using sb kbn by simp
  \<comment> \<open>\<open>Qne\<close> goes in the \<open>add:\<close> list, not the \<open>use\<close> list, as in the pop twin.\<close>
  have Qne: "qr \<noteq> []" and Qne2: "0 < length qr" using qlenr rp_len by auto
  have Qcap: "length qr + 1 < max_snat LENGTH(gmp_poly_len)" using qlenr rp_bound by simp
  note Pu = pre[unfolded hybrid_loop_step_pre_def]
  show ?thesis
    unfolding hybrid_loop_safe_invar_def hybrid_loop_step_pre_def
  proof (intro conjI impI)
    show "hybrid_loop_state_invar
            (((butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [j1, j2]),
              butlast qtodo @ [ql, qr], butlast es @ [e1, e2],
              butlast ss @ [sv1, sv2], butlast cs @ [c1, c2], butlast gs @ [g1, g2], rp),
             (al', ar', ak'))"
      using stinv accinv
      by (auto simp: hybrid_loop_state_invar_def dyadic_interval_vec_invar_def Let_def)
  qed (use Pu tcap VL SL kbn kbp sbn Qcap rp_len rp_bound apush in
         \<open>simp_all add: dyadic_interval_vec_pushable2_def dyadic_interval_vec_pushable_def
                        Qne Qne2\<close>)
qed

text \<open>\<^bold>\<open>\<open>safe'\<close> at a ONE-CHILD pushed state\<close> -- the window arm's ACCEPT half. Simpler than the
  two-child twin in exactly one way: the worklist does not lengthen, so \<open>step_pre\<close>'s own
  \<open>pushable2\<close> already covers every column cap and the budget invariant is not needed here at all.
  The depth and run-length still come from the pushed state's k-potential, and the pushed
  polynomial's length still from the arm's exported @{const node_frame}.\<close>
lemma hybrid_loop_safe_invar_push1_all:
  assumes stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and capinv': "hybrid_cap_invar \<delta> l0 r0 k0
                    (butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [j1])
                    (butlast ss @ [sv1])"
    and qlen: "length q1 = length rp"
    and dpos: "0 < \<delta>"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_loop_safe_invar
           (((butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [j1]),
             butlast qtodo @ [q1], butlast es @ [e1],
             butlast ss @ [sv1], butlast cs @ [c1], butlast gs @ [g1], rp), acc)"
proof -
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have kidx: "length ks - Suc 0 < length (butlast ks @ [j1])" by simp
  have knth: "(butlast ks @ [j1]) ! (length ks - Suc 0) = j1"
    by (simp add: nth_append)
  have sidx: "length ks - Suc 0 < length (butlast ss @ [sv1])"
    using SL VL by simp
  have snth: "(butlast ss @ [sv1]) ! (length ks - Suc 0) = sv1"
    using SL VL by (simp add: nth_append)
  have kb1: "int j1 + 1 \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_succ_le[OF capinv' kidx dpos] by (simp add: knth)
  have kb2: "int j1 \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_le[OF capinv' kidx] by (simp add: knth)
  have sb: "sv1 \<le> j1"
    using hybrid_cap_invar_sigma_nth[OF capinv' sidx] by (simp add: knth snth)
  have kbn: "j1 + 1 < max_snat LENGTH(gmp_poly_len)" using kb1 kcap by linarith
  have kbp: "j1 * (length rp - 1) < max_snat LENGTH(gmp_poly_len)" by (rule kdepth[OF kb2])
  have sbn: "sv1 + 1 < max_snat LENGTH(gmp_poly_len)" using sb kbn by simp
  have Qne: "q1 \<noteq> []" and Qne2: "0 < length q1" using qlen rp_len by auto
  have Qcap: "length q1 + 1 < max_snat LENGTH(gmp_poly_len)" using qlen rp_bound by simp
  \<comment> \<open>\<^bold>\<open>\<open>lfix\<close> is what makes the column caps MATCH.\<close> The one-child push leaves the vector the
     same length, so \<open>step_pre\<close>'s own cap already covers it -- but the goal normalises to
     \<open>Suc (length lns)\<close> while the hypothesis stays at \<open>Suc (Suc (length lns - Suc 0))\<close>, and
     \<open>lns \<noteq> []\<close> sits inside a premise CONJUNCTION where \<open>simp\<close> will not mine it. As a simp rule
     \<open>lfix\<close> rewrites both sides to the same form.\<close>
  have lne: "lns \<noteq> []" using pre unfolding hybrid_loop_step_pre_def by simp
  have lfix: "Suc (length lns - Suc 0) = length lns" using lne by simp
  note Pu = pre[unfolded hybrid_loop_step_pre_def]
  show ?thesis
    unfolding hybrid_loop_safe_invar_def hybrid_loop_step_pre_def
  proof (intro conjI impI)
    show "hybrid_loop_state_invar
            (((butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [j1]),
              butlast qtodo @ [q1], butlast es @ [e1],
              butlast ss @ [sv1], butlast cs @ [c1], butlast gs @ [g1], rp), acc)"
      using stinv
      by (auto simp: hybrid_loop_state_invar_def dyadic_interval_vec_invar_def Let_def)
  qed (use Pu VL SL kbn kbp sbn Qcap rp_len rp_bound in
         \<open>simp_all add: dyadic_interval_vec_pushable2_def dyadic_interval_vec_pushable_def
                        lfix Qne Qne2\<close>)
qed

text \<open>\<^bold>\<open>Assembly, step 12: the measure strictly drops on a pop.\<close> Lifts
  @{thm [source] hybrid_mu_mset_pop_less} from the node list to the loop state, which is the
  form @{thm [source] hybrid_loop_correct}'s body obligation needs.\<close>
lemma hybrid_state_mu_pop_less:
  assumes nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                   = hybrid_alpha_nodes l0 r0 k0
                       (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                     @ [nd]"
  shows "hybrid_state_mu \<delta> l0 r0 k0
           (((butlast lns, butlast rns, butlast ks), butlast qtodo,
             butlast es, butlast ss, butlast cs, butlast gs, rp), acc)
       < hybrid_state_mu \<delta> l0 r0 k0 (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
  using hybrid_mu_mset_pop_less[of \<delta>
          "hybrid_alpha_nodes l0 r0 k0 (butlast lns, butlast rns, butlast ks)
             (butlast es) (butlast ss)" nd]
  by (simp add: nsplit)

text \<open>\<^bold>\<open>The measure lift for a TWO-child push\<close>, the split counterpart of
  @{thm [source] hybrid_state_mu_pop_less}. @{const hybrid_state_mu} ignores \<open>acc\<close>
  (@{thm [source] hybrid_state_mu_simp}), so the accept/reject fork on the midpoint root does
  not enter here — only the node columns do.\<close>
lemma hybrid_state_mu_push2_less:
  assumes nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                   = hybrid_alpha_nodes l0 r0 k0
                       (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                     @ [nd]"
    and npush: "hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
                   (butlast es @ [e1, e2]) (butlast ss @ [s1, s2])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [cl, cr]"
    and ltl: "dyadic_iv_interval_mu \<delta> (fst cl, fst (snd cl))
              < dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd))"
    and ltr: "dyadic_iv_interval_mu \<delta> (fst cr, fst (snd cr))
              < dyadic_iv_interval_mu \<delta> (fst nd, fst (snd nd))"
  shows "hybrid_state_mu \<delta> l0 r0 k0
           (((butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2]),
             qt', butlast es @ [e1, e2], butlast ss @ [s1, s2], cs', gs', rp), acc')
       < hybrid_state_mu \<delta> l0 r0 k0 (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
  using hybrid_mu_mset_push2_less[OF ltl ltr] by (simp add: nsplit npush)

text \<open>\<^bold>\<open>The bisection halving, in \<open>dyadic_iv_interval_mu\<close> terms.\<close> Port of the derivation bail
  runs inline (\<open>Bail_Loop_Refine.thy\<close>): \<open>mu_halve_strict\<close> at the rational endpoints,
  with the \<open>of_rat\<close> arithmetic pushed through @{const dyadic_iv_interval_mu}'s definition.

  \<^bold>\<open>\<open>wide\<close> is a genuine side condition, not bookkeeping\<close> — \<open>mu\<close> stops decreasing once an
  interval is narrower than \<open>\<delta>\<close>. Bail discharges it by contradiction from \<open>2 \<le> v\<close> (a \<open>\<le> \<delta>\<close>-wide
  interval has count \<open>\<le> 1\<close>); here it is a premise, because \<open>\<delta>\<close> is still free at this layer —
  @{thm [source] hybrid_loop_correct} does not constrain it. Both it and \<open>dpos\<close> are discharged
  once, at the per-arm step discharge, where \<open>\<delta>\<close> is instantiated.\<close>
lemma hybrid_mu_halve:
  assumes dpos: "0 < \<delta>"
    and ab: "(a :: rat) < b"
    and wide: "\<delta> < real_of_rat b - real_of_rat a"
  shows "dyadic_iv_interval_mu \<delta> (a, (a + b) / 2) < dyadic_iv_interval_mu \<delta> (a, b)"
    and "dyadic_iv_interval_mu \<delta> ((a + b) / 2, b) < dyadic_iv_interval_mu \<delta> (a, b)"
  using mu_halve_strict(1)[of \<delta> "real_of_rat a" "real_of_rat b"]
    mu_halve_strict(2)[of \<delta> "real_of_rat a" "real_of_rat b"] dpos ab wide
  by (simp_all add: dyadic_iv_interval_mu_def of_rat_add of_rat_divide of_rat_less)

text \<open>\<^bold>\<open>Assembly, step 13: the discard arm's complete body step\<close>, the exact shape
  @{thm [source] hybrid_loop_correct} takes as its \<open>step\<close> hypothesis, for this arm. Joins the
  concrete state result (@{thm [source] hybrid_loop_step_args_discard}) with the three
  preservation halves: safety (@{thm [source] hybrid_loop_state_invar_pop}), the refinement
  invariant (@{thm [source] hybrid_refine_invar_discard_step}) and the measure
  (@{thm [source] hybrid_state_mu_pop_less}).\<close>
lemma hybrid_body_step_discard:
  assumes stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp acc"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, b, e, dk, sv)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and ab: "a < b"
    and zero: "descartes_list_int a b (coeffs P) = 0"
    and safe': "hybrid_loop_safe_invar
                  (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                    butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
    \<comment> \<open>the k-potential half of the invariant, which the popped/pushed state must carry too.\<close>
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    \<comment> \<open>and the word-budget half -- a pure pop, so both budgets only shrink.\<close>
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) acc"
    and clr: "length lns = length ks" and crr: "length rns = length ks"
    and csk: "length ss = length ks"
    and arm: "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs acc rp
              \<le> SPEC (\<lambda>(wl, acc'). acc' = acc \<and>
                    wl = ((butlast lns, butlast rns, butlast ks), butlast qtodo,
                          butlast es, butlast ss, butlast cs, butlast gs, rp))"
    \<comment> \<open>\<^bold>\<open>The payload bound at the popped state\<close>: the discard arm pushes nothing, so this is
       @{thm [source] hybrid_pay_invar_pop}. \<^bold>\<open>Last\<close>.\<close>
    and paypop: "hybrid_pay_invar (butlast lns, butlast rns, butlast ks) (butlast gs) rp"
    \<comment> \<open>\<^bold>\<open>The root relation\<close>, @{const hybrid_state_invar}'s fifth
       conjunct, \<^bold>\<open>last\<close>. It is the same proposition at the pushed state as at the popped one
       (no arm touches \<open>P\<close> or \<open>rp\<close>), so it passes straight through; it exists so that
       \<open>hybrid_loop_correct\<close>'s \<open>\<And>s\<close> step can reach \<open>s\<close>'s own \<open>rp\<close>.\<close>
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
  shows "hybrid_loop_body_checked_monadic (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc))"
  apply (subst hybrid_loop_body_under_cond[OF cond])
  apply (subst hybrid_loop_step_unfold)
  apply (rule order_trans[OF arm])
  apply (rule SPEC_rule)
  \<comment> \<open>do NOT \<open>clarsimp\<close> first: it destructures \<open>acc\<close> into \<open>(ag, ah, bb)\<close>, after which the
     three facts (all stated at \<open>acc\<close>) no longer match syntactically.\<close>
  using safe' hybrid_refine_invar_discard_step[OF inv nsplit vsplit ab zero]
        hybrid_state_mu_pop_less[OF nsplit]
        hybrid_cap_invar_pop[OF capinv clr crr csk]
        hybrid_budget_invar_pop[OF budinv vsplit]
        \<comment> \<open>the payload bound: the discard arm pops only.\<close>
        paypop Pcoeffs
  by auto

text \<open>\<^bold>\<open>Assembly, step 14: the accept arm's complete body step.\<close> Same join as the discard arm, with
  @{thm [source] hybrid_refine_invar_accept_step} (which additionally consumes the \<open>accgrow\<close>
  accounting for the newly accepted interval) and the accept arm's state result.\<close>
lemma hybrid_body_step_accept:
  assumes cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, b, e, dk, sv)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and ab: "a < b"
    and one: "descartes_list_int a b (coeffs P) = 1"
    and accgrow: "dyadic_iv_acc_ivs l0 r0 k0
                    (dyadic_interval_vec_triples (al @ [last lns], ar @ [last rns], ak @ [last ks]))
                  = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak)) @ [(a, b)]"
    and safe': "hybrid_loop_safe_invar
                  (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                    butlast es, butlast ss, butlast cs, butlast gs, rp),
                   (al @ [last lns], ar @ [last rns], ak @ [last ks]))"
    \<comment> \<open>the k-potential half of the invariant, which the popped/pushed state must carry too.\<close>
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    \<comment> \<open>and the word-budget half: the accumulator takes ONE more slot, paid by the popped node's
       own acc-budget. This is the step @{const hybrid_budget_invar}'s acc side exists for.\<close>
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and clr: "length lns = length ks" and crr: "length rns = length ks"
    and csk: "length ss = length ks"
    and arm: "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
              \<le> SPEC (\<lambda>(wl, acc').
                    acc' = (al @ [last lns], ar @ [last rns], ak @ [last ks]) \<and>
                    wl = ((butlast lns, butlast rns, butlast ks), butlast qtodo,
                          butlast es, butlast ss, butlast cs, butlast gs, rp))"
    \<comment> \<open>\<^bold>\<open>The payload bound at the popped state.\<close> Stated at the successor rather than the current
       state, exactly as \<open>safe\<close>\<open>'\<close> above is, so the assembly discharges it once with
       @{thm [source] hybrid_pay_invar_pop} and the body step needs no column lengths.
       \<^bold>\<open>Last\<close>, so every other \<open>[OF \<dots>]\<close> position is unchanged.\<close>
    and paypop: "hybrid_pay_invar (butlast lns, butlast rns, butlast ks) (butlast gs) rp"
    \<comment> \<open>\<^bold>\<open>The root relation\<close>, @{const hybrid_state_invar}'s fifth
       conjunct, \<^bold>\<open>last\<close>. It is the same proposition at the pushed state as at the popped one
       (no arm touches \<open>P\<close> or \<open>rp\<close>), so it passes straight through; it exists so that
       \<open>hybrid_loop_correct\<close>'s \<open>\<And>s\<close> step can reach \<open>s\<close>'s own \<open>rp\<close>.\<close>
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
  shows "hybrid_loop_body_checked_monadic
           (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
  apply (subst hybrid_loop_body_under_cond[OF cond])
  apply (subst hybrid_loop_step_unfold)
  apply (rule order_trans[OF arm])
  apply (rule SPEC_rule)
  using safe' hybrid_refine_invar_accept_step[OF inv nsplit vsplit ab one accgrow]
        hybrid_state_mu_pop_less[OF nsplit]
        hybrid_cap_invar_pop[OF capinv clr crr csk]
        hybrid_budget_invar_accept[OF budinv vsplit, of "al @ [last lns]"]
        \<comment> \<open>the payload bound: the accept arm only pops the worklist, so the payload conjunct is
           @{thm [source] hybrid_pay_invar_pop} and nothing more.\<close>
        paypop Pcoeffs
  by auto

text \<open>\<^bold>\<open>Dropping the right slot of a two-child push.\<close> The one-push columns are the two-push
  columns minus their last slot, so their \<open>\<alpha>\<close>-images are the two-push images minus the last
  node. Stated from the two-push decomposition the split arm already carries (\<open>npush\<close>/\<open>vpush\<close>),
  which is how the left-only case reads its own node and view without new geometry.\<close>
lemma hybrid_alpha_nodes_push2_drop:
  assumes lr: "length lns = length rns" and rk: "length rns = length ks"
    and le: "length es = length ks" and ls: "length ss = length ks"
    and np: "hybrid_alpha_nodes l0 r0 k0 (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
               (es @ [e1, e2]) (ss @ [s1, s2]) = NS @ [cl, cr]"
  shows "hybrid_alpha_nodes l0 r0 k0 (lns @ [l1], rns @ [r1], ks @ [k1]) (es @ [e1]) (ss @ [s1])
           = NS @ [cl]"
    and "hybrid_alpha_nodes l0 r0 k0 (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
           (es @ [e1, e2]) (ss @ [s1, s2])
         = hybrid_alpha_nodes l0 r0 k0 (lns @ [l1], rns @ [r1], ks @ [k1]) (es @ [e1]) (ss @ [s1])
           @ [cr]"
proof -
  have A1: "hybrid_alpha_nodes l0 r0 k0 (lns @ [l1], rns @ [r1], ks @ [k1]) (es @ [e1]) (ss @ [s1])
      = hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
        @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((l1, r1), k1)),
            snd (dyadic_iv_node_iv_of l0 r0 k0 ((l1, r1), k1)), e1, k1, s1)]"
    using lr rk le ls by (simp add: hybrid_alpha_nodes_def dyadic_interval_vec_triples_def)
  show "hybrid_alpha_nodes l0 r0 k0 (lns @ [l1], rns @ [r1], ks @ [k1]) (es @ [e1]) (ss @ [s1])
          = NS @ [cl]"
    using np[THEN arg_cong[where f = butlast]]
    unfolding A1 hybrid_alpha_nodes_append2[OF lr rk le ls] by (simp add: butlast_append)
  show "hybrid_alpha_nodes l0 r0 k0 (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
          (es @ [e1, e2]) (ss @ [s1, s2])
        = hybrid_alpha_nodes l0 r0 k0 (lns @ [l1], rns @ [r1], ks @ [k1]) (es @ [e1]) (ss @ [s1])
          @ [cr]"
    using np[THEN arg_cong[where f = last]]
    unfolding A1 hybrid_alpha_nodes_append2[OF lr rk le ls] by (simp add: butlast_append)
qed

lemma hybrid_alpha_views_push2_drop:
  assumes lr: "length lns = length rns" and rk: "length rns = length ks"
    and vp: "hybrid_alpha_views l0 r0 k0 (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
               = VS @ [il, ir]"
  shows "hybrid_alpha_views l0 r0 k0 (lns @ [l1], rns @ [r1], ks @ [k1]) = VS @ [il]"
    and "hybrid_alpha_views l0 r0 k0 (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
         = hybrid_alpha_views l0 r0 k0 (lns @ [l1], rns @ [r1], ks @ [k1]) @ [ir]"
proof -
  have A1: "hybrid_alpha_views l0 r0 k0 (lns @ [l1], rns @ [r1], ks @ [k1])
      = hybrid_alpha_views l0 r0 k0 (lns, rns, ks) @ [dyadic_iv_node_iv_of l0 r0 k0 ((l1, r1), k1)]"
    using lr rk by (simp add: hybrid_alpha_views_def dyadic_interval_vec_triples_def)
  show "hybrid_alpha_views l0 r0 k0 (lns @ [l1], rns @ [r1], ks @ [k1]) = VS @ [il]"
    using vp[THEN arg_cong[where f = butlast]]
    unfolding A1 hybrid_alpha_views_append2[OF lr rk] by (simp add: butlast_append)
  show "hybrid_alpha_views l0 r0 k0 (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
        = hybrid_alpha_views l0 r0 k0 (lns @ [l1], rns @ [r1], ks @ [k1]) @ [ir]"
    using vp[THEN arg_cong[where f = last]]
    unfolding A1 hybrid_alpha_views_append2[OF lr rk] by (simp add: butlast_append)
qed

text \<open>\<^bold>\<open>The left-only split step\<close>: the refinement invariant across a pop that pushes only
  the left child, because the right one was proved empty. No new abstract step: it is
  @{thm [source] hybrid_refine_invar_split_step} onto a phantom two-push state whose right slot
  holds the exact right child (guard \<open>0\<close>, so @{thm [source] node_frame_exact}; cache \<open>4\<close>, the
  ambiguous sentinel, which @{const hybrid_cs_ok} admits at any count), followed by
  @{thm [source] hybrid_refine_invar_discard_step} popping that phantom on its count \<open>0\<close>. LIFO is
  what makes this exact: the phantom is the very next pop, and the discard frees it untouched.\<close>
lemma hybrid_refine_invar_split_left_step:
  assumes inv: "hybrid_refine_invar P l0 r0 k0 seed (lns, rns, ks) qtodo es ss cs gs rp acc"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, b, e, dk, s)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and npush: "hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
                   (butlast es @ [e1, e2]) (butlast ss @ [s1, s2])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, t1),
                      ((a + b) / 2, b, max 1 (e - 1), dk + 1, t2)]"
    and vpush: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, (a + b) / 2), ((a + b) / 2, b)]"
    and accgrow: "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc')
                  = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples acc)
                    @ (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                       then [((a + b) / 2, (a + b) / 2)] else [])"
    and ab: "a < b"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and f1: "node_frame (carried_init_same_den l1 (2 ^ k1) r1 rp) q1 g1"
    and g1le: "g1 \<le> (k1 + 1) * length rp \<or> 4398046511104 \<le> g1"
    and lk1: "4398046511104 \<le> g1 \<longrightarrow> q1 = carried_init_same_den l1 (2 ^ k1) r1 rp"
    and ok1: "hybrid_cs_ok g1 c1
                (carried_descartes_count (carried_init_same_den l1 (2 ^ k1) r1 rp))"
    \<comment> \<open>the right half is root-free: the one fact the decide contributes.\<close>
    and zero: "descartes_list_int ((a + b) / 2) b (coeffs P) = 0"
    and lr: "length (butlast lns) = length (butlast rns)"
    and rk: "length (butlast rns) = length (butlast ks)"
    and le: "length (butlast es) = length (butlast ks)"
    and ls: "length (butlast ss) = length (butlast ks)"
  shows "hybrid_refine_invar P l0 r0 k0 seed
           (butlast lns @ [l1], butlast rns @ [r1], butlast ks @ [k1])
           (butlast qtodo @ [q1]) (butlast es @ [e1]) (butlast ss @ [s1])
           (butlast cs @ [c1]) (butlast gs @ [g1]) rp acc'"
proof -
  have G: "hybrid_refine_invar P l0 r0 k0 seed
             (butlast lns @ [l1, l2], butlast rns @ [r1, r2], butlast ks @ [k1, k2])
             (butlast qtodo @ [q1, carried_init_same_den l2 (2 ^ k2) r2 rp])
             (butlast es @ [e1, e2]) (butlast ss @ [s1, s2])
             (butlast cs @ [c1, 4]) (butlast gs @ [g1, 0]) rp acc'"
    by (rule hybrid_refine_invar_split_step[OF inv nsplit vsplit npush vpush accgrow ab P0 p0 sf v2
             f1 node_frame_exact g1le _ lk1 _ ok1 _])
       (simp_all add: hybrid_cs_ok_def)
  note ND = hybrid_alpha_nodes_push2_drop(2)[OF lr rk le ls npush]
  note VD = hybrid_alpha_views_push2_drop(2)[OF lr rk vpush]
  have mid: "(a + b) / 2 < b" using ab by (simp add: field_simps)
  have "hybrid_refine_invar P l0 r0 k0 seed
          (butlast (butlast lns @ [l1, l2]), butlast (butlast rns @ [r1, r2]),
           butlast (butlast ks @ [k1, k2]))
          (butlast (butlast qtodo @ [q1, carried_init_same_den l2 (2 ^ k2) r2 rp]))
          (butlast (butlast es @ [e1, e2])) (butlast (butlast ss @ [s1, s2]))
          (butlast (butlast cs @ [c1, 4])) (butlast (butlast gs @ [g1, 0])) rp acc'"
    by (rule hybrid_refine_invar_discard_step[where a = "(a + b) / 2" and b = b
             and e = "max 1 (e - 1)" and dk = "dk + 1" and s = t2, OF G])
       (use ND VD mid zero in \<open>simp_all add: butlast_append\<close>)
  thus ?thesis by (simp add: butlast_append)
qed

text \<open>\<^bold>\<open>Assembly, step 15: the split arm's complete body step.\<close> The join
  @{thm [source] hybrid_body_step_discard} performs, but over an existential state result:
  the split arm pins the pushed columns only up to the children \<open>ql\<close>/\<open>qr\<close>, their caches
  \<open>cl\<close>/\<open>cr\<close>, guards \<open>gl\<close>/\<open>gr\<close> and run length \<open>sv\<close>. So the three preservation halves must hold
  for arbitrary witnesses, which is why \<open>npush\<close>/\<open>vpush\<close>/\<open>accgrow\<close>/\<open>safe'\<close> are \<open>\<And>\<close>-quantified
  here where the discard arm states them at a fixed state.

  \<^bold>\<open>The bisection rewrite is the one piece of real content.\<close> The arm speaks of
  \<open>carried_left X\<close>/\<open>carried_right X\<close>; @{thm [source] hybrid_refine_invar_split_step} speaks of
  \<open>carried_init_same_den l1 (2 ^ k1) r1 rp\<close> at the child's own \<open>(l1, k1, r1)\<close>. They are the same
  polynomial by @{thm [source] carried_left_right_reconstruct}, which is stated in exactly the
  \<open>2 ^ k\<close> form the pushed columns use and needs no side condition.\<close>
lemma hybrid_body_step_split:
  assumes cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, b, e, dk, sv0)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and npush: "\<And>sv. hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [last ks + 1, last ks + 1])
                   (butlast es @ [newton_child_exp (last es), newton_child_exp (last es)])
                   (butlast ss @ [sv, sv])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, sv),
                      ((a + b) / 2, b, max 1 (e - 1), dk + 1, sv)]"
    and vpush: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [last ks + 1, last ks + 1])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, (a + b) / 2), ((a + b) / 2, b)]"
    and accgrow: "\<And>ag ah bb.
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                     ag = al @ [last lns + last rns] \<and> ah = ar @ [last lns + last rns] \<and>
                     bb = ak @ [last ks + 1]) \<Longrightarrow>
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
                     ag = al \<and> ah = ar \<and> bb = ak) \<Longrightarrow>
                  dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (ag, ah, bb))
                  = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak))
                    @ (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                       then [((a + b) / 2, (a + b) / 2)] else [])"
    and ab: "a < b"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and dpos: "0 < \<delta>"
    and wide: "\<delta> < real_of_rat b - real_of_rat a"
    \<comment> \<open>the k-potential half: its input, the column lengths it needs, and the node view the
       geometry lemma turns into the children's halves.\<close>
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    \<comment> \<open>the word-budget half: the worklist LENGTHENS here, which is the step the todo-append
       budget exists for. The accumulator is branched, absorbed by
       @{thm [source] hybrid_budget_invar_push2_branched}.\<close>
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and clr: "length lns = length ks" and crr: "length rns = length ks"
    and csk: "length ss = length ks" and kne: "ks \<noteq> []" and lr0: "l0 < r0"
    and abnode: "dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks) = (a, b)"
    \<comment> \<open>the ambient word caps \<open>safe'\<close> needs, in the same shape the discard arm and
       @{thm [source] hybrid_loop_safe_invar_pop_all} take them.\<close>
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and arm: "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
              \<le> SPEC (\<lambda>(wl, acc').
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                     acc' = (al @ [last lns + last rns], ar @ [last lns + last rns],
                             ak @ [last ks + 1])) \<and>
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
                  hybrid_split_wl X (butlast lns) (butlast rns) (butlast ks) (butlast qtodo) (butlast es) (butlast ss) (butlast cs) (butlast gs) rp (last lns) (last rns) (last ks) (last es) (last ss) wl)"
    \<comment> \<open>\<^bold>\<open>The payload bound at the pushed state\<close>, \<open>\<And>\<close>-quantified over the children's guards exactly
       as \<open>npush\<close>/\<open>safe\<close>\<open>'\<close> are over the other witnesses. \<^bold>\<open>Last\<close>, so that no \<open>[OF \<dots>]\<close> position moves.
       Its source is @{thm [source] hybrid_pay_invar_push2} on the two children's own atoms,
       and those come from @{thm [source] hybrid_pay_split_child}, which consumes the
       \<open>hybrid_child_gok\<close> and \<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close> facts the split arm's SPEC exports
       (via @{thm [source] hybrid_child_pay_okI}).\<close>
    \<comment> \<open>\<^bold>\<open>Conditioned on the arm's own exports.\<close> A \<open>\<And>gl gr\<close> form with a free right-hand side would claim the
       pushed state satisfies @{const hybrid_pay_invar} for arbitrary child guards, which is
       false. So it is conditioned, as \<open>safe\<close>\<open>'\<close> is, on the
       two atoms the arm's SPEC exports, and discharged with
       @{thm [source] hybrid_pay_invar_push2}.\<close>
    and paypush: "\<And>gl gr. hybrid_child_pay_ok (2 * last lns) (last ks + 1) (last lns + last rns) rp gl \<Longrightarrow>
                    hybrid_child_pay_ok (last lns + last rns) (last ks + 1) (2 * last rns) rp gr \<Longrightarrow> hybrid_pay_invar
                    (butlast lns @ [2 * last lns, last lns + last rns],
                     butlast rns @ [last lns + last rns, 2 * last rns],
                     butlast ks @ [last ks + 1, last ks + 1])
                    (butlast gs @ [gl, gr]) rp"
    \<comment> \<open>\<^bold>\<open>The root relation\<close>, @{const hybrid_state_invar}'s fifth
       conjunct, \<^bold>\<open>last\<close>. It is the same proposition at the pushed state as at the popped one
       (no arm touches \<open>P\<close> or \<open>rp\<close>), so it passes straight through; it exists so that
       \<open>hybrid_loop_correct\<close>'s \<open>\<And>s\<close> step can reach \<open>s\<close>'s own \<open>rp\<close>.\<close>
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    \<comment> \<open>\<^bold>\<open>The right half is root-free whenever the decide says so.\<close> The node bridge it
       needs (\<open>hybrid_node_count_bridge\<close>, via \<open>hybrid_split_right_zero\<close>) sits later in
       this theory, so the assembly discharges it. \<^bold>\<open>Last\<close>, so that no \<open>[OF \<dots>]\<close> position moves.\<close>
    and zeroR: "carried_descartes_count (carried_right X) = 0 \<Longrightarrow>
                  descartes_list_int ((a + b) / 2) b (coeffs P) = 0"
  shows "hybrid_loop_body_checked_monadic
           (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  \<comment> \<open>the bisection rewrite, in the \<open>2 ^ k\<close> form the pushed columns use.\<close>
  \<comment> \<open>\<^bold>\<open>Stated with \<open>2 * l\<close>, not \<open>l + l\<close>\<close>: @{thm [source] carried_left_right_reconstruct}
     produces the doubled-sum form while the pushed column is \<open>2 * last lns\<close>.
     \<open>mult_2\<close> is an \<open>unfolding\<close> step, not a simp rule: as \<open>simp add: mult_2\<close> it
     loops, while a single left-to-right \<open>unfolding\<close> pass cannot.\<close>
  have recL: "carried_left X
      = carried_init_same_den (2 * last lns) (2 ^ (last ks + 1)) (last lns + last rns) rp"
    unfolding X_eq mult_2 by (rule carried_left_right_reconstruct(1))
  have recR: "carried_right X
      = carried_init_same_den (last lns + last rns) (2 ^ (last ks + 1)) (2 * last rns) rp"
    unfolding X_eq mult_2 by (rule carried_left_right_reconstruct(2))
  have mu1: "dyadic_iv_interval_mu \<delta> (a, (a + b) / 2) < dyadic_iv_interval_mu \<delta> (a, b)"
    and mu2: "dyadic_iv_interval_mu \<delta> ((a + b) / 2, b) < dyadic_iv_interval_mu \<delta> (a, b)"
    by (rule hybrid_mu_halve[OF dpos ab wide])+
  \<comment> \<open>the worklist's own length after a two-child push, which the todo-append budget is stated
     against. (The window arm's ACCEPT half pushes ONE child and leaves the length alone, so it
     needs no counterpart.)\<close>
  have lne: "lns \<noteq> []" using kne clr by auto
  have lpush: "length (butlast lns @ [2 * last lns, last lns + last rns]) = length lns + 1"
    using lne by simp
  \<comment> \<open>the same drops at the NODE VIEW, which is what the potential is indexed by.\<close>
  have muL: "dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0
                  ((2 * last lns, last lns + last rns), Suc (last ks)))
             < dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using mu1 by (simp add: hybrid_node_iv_split_children(1)[OF lr0] abnode)
  have muR: "dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0
                  ((last lns + last rns, 2 * last rns), Suc (last ks)))
             < dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using mu2 by (simp add: hybrid_node_iv_split_children(2)[OF lr0] abnode)
  have ndL: "fst (dyadic_iv_node_iv_of l0 r0 k0
                    ((2 * last lns, last lns + last rns), Suc (last ks)))
             < snd (dyadic_iv_node_iv_of l0 r0 k0
                    ((2 * last lns, last lns + last rns), Suc (last ks)))"
    using ab by (simp add: hybrid_node_iv_split_children(1)[OF lr0] abnode)
  have ndR: "fst (dyadic_iv_node_iv_of l0 r0 k0
                    ((last lns + last rns, 2 * last rns), Suc (last ks)))
             < snd (dyadic_iv_node_iv_of l0 r0 k0
                    ((last lns + last rns, 2 * last rns), Suc (last ks)))"
    using ab by (simp add: hybrid_node_iv_split_children(2)[OF lr0] abnode)
  \<comment> \<open>\<^bold>\<open>\<open>safe'\<close> is derived here, not assumed.\<close> As a premise in the \<open>\<And>\<close>-over-every-\<open>qr\<close> form it would be
     contradictory (\<open>hybrid_safe_push_forall_q_is_vacuous\<close>, below), so it is derived at the one site that already
     has the geometry (\<open>muL\<close>/\<open>muR\<close>/\<open>ndL\<close>/\<open>ndR\<close>).\<close>
  have rp_len: "0 < length rp" and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    using pre unfolding hybrid_loop_step_pre_def by simp_all
  have accinv0: "dyadic_interval_vec_invar (al, ar, ak)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have Xlen: "length X = length rp"
    unfolding X_eq by (simp add: truncate_length_carried_init_same_den)
  {
    fix ql qr cl cr gl gr sv ag ah bb
    assume nf: "node_frame (carried_right X) qr gr"
       and svb: "sv \<le> last ss + 1"
       and g1: "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                  ag = al @ [last lns + last rns] \<and> ah = ar @ [last lns + last rns] \<and>
                  bb = ak @ [last ks + 1]"
       and g0: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
                  ag = al \<and> ah = ar \<and> bb = ak"
    have qlen: "length qr = length rp"
      using cdlr_node_frame_len[OF nf] Xlen by simp
    have accg: "length ag \<le> length al + 1"
      using g1 g0 by (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0") auto
    have accinv: "dyadic_interval_vec_invar (ag, ah, bb)"
      using g1 g0 accinv0
      by (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0")
         (auto simp: dyadic_interval_vec_invar_def)
    have capinv': "hybrid_cap_invar \<delta> l0 r0 k0
                     (butlast lns @ [2 * last lns, last lns + last rns],
                      butlast rns @ [last lns + last rns, 2 * last rns],
                      butlast ks @ [last ks + 1, last ks + 1])
                     (butlast ss @ [sv, sv])"
      by (rule hybrid_cap_invar_push2[OF capinv clr crr csk kne muL muR svb ndL ndR])
    have "hybrid_loop_safe_invar
            (((butlast lns @ [2 * last lns, last lns + last rns],
               butlast rns @ [last lns + last rns, 2 * last rns],
               butlast ks @ [last ks + 1, last ks + 1]),
              butlast qtodo @ [ql, qr],
              butlast es @ [newton_child_exp (last es), newton_child_exp (last es)],
              butlast ss @ [sv, sv], butlast cs @ [cl, cr], butlast gs @ [gl, gr], rp),
             (ag, ah, bb))"
      by (rule hybrid_loop_safe_invar_push2_all[OF stinv pre budinv capinv' qlen accg accinv
                 dpos rp_len rp_bound kcap kdepth])
  }
  note safe' = this
  \<comment> \<open>\<^bold>\<open>The left-only push\<close>, prepared exactly as \<open>safe'\<close> is: every fact the one-push case
     needs, \<open>\<And>\<close>-quantified over the arm's witnesses. The right child was never built, so the
     refinement, cap and budget halves go through the phantom two-push state: its push2 lemma,
     then a pop of the phantom (@{thm [source] hybrid_refine_invar_split_left_step}). Safety does
     not need the phantom: @{thm [source] hybrid_loop_safe_invar_push1_all} then an accumulator
     swap, since the \<open>mid\<close> branch may have grown \<open>acc\<close>.\<close>
  have VL: "length rns = length lns" "length ks = length lns" using clr crr by simp_all
  have SLg: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have BL: "length (butlast lns) = length (butlast rns)" "length (butlast rns) = length (butlast ks)"
     "length (butlast es) = length (butlast ks)" "length (butlast ss) = length (butlast ks)"
    using VL SLg by simp_all
  {
    fix ql gl cl sv ag ah bb
    assume svb: "sv \<le> last ss + 1"
       and okL: "hybrid_cs_ok gl cl (carried_descartes_count (carried_left X))"
       and depL: "hybrid_child_depth_ok (last ks + 1) (length rp) gl"
       and nf: "node_frame (carried_left X) ql gl"
       and lkL: "4398046511104 \<le> gl \<longrightarrow> ql = carried_left X"
       and plL: "hybrid_child_pay_ok (2 * last lns) (last ks + 1) (last lns + last rns) rp gl"
       and rz0: "carried_descartes_count (carried_right X) = 0"
       and g1: "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                  ag = al @ [last lns + last rns] \<and> ah = ar @ [last lns + last rns] \<and>
                  bb = ak @ [last ks + 1]"
       and g0: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
                  ag = al \<and> ah = ar \<and> bb = ak"
    have qlen: "length ql = length rp"
      using cdlr_node_frame_len[OF nf] Xlen by simp
    have accg: "length ag \<le> length al + 1"
      using g1 g0 by (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0") auto
    have accinv: "dyadic_interval_vec_invar (ag, ah, bb)"
      using g1 g0 accinv0
      by (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0")
         (auto simp: dyadic_interval_vec_invar_def)
    have acap: "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
      by (rule hybrid_budget_invar_acc_grown[OF budinv lne VL])
    have apush: "dyadic_interval_vec_pushable (ag, ah, bb)"
      using acap accg accinv
      unfolding dyadic_interval_vec_pushable_def dyadic_interval_vec_invar_def by simp
    have capG: "hybrid_cap_invar \<delta> l0 r0 k0
                  (butlast lns @ [2 * last lns, last lns + last rns],
                   butlast rns @ [last lns + last rns, 2 * last rns],
                   butlast ks @ [last ks + 1, last ks + 1])
                  (butlast ss @ [sv, sv])"
      by (rule hybrid_cap_invar_push2[OF capinv clr crr csk kne muL muR svb ndL ndR])
    have cap1: "hybrid_cap_invar \<delta> l0 r0 k0
                  (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                   butlast ks @ [last ks + 1])
                  (butlast ss @ [sv])"
      using hybrid_cap_invar_pop[OF capG] clr crr csk by (simp add: butlast_append)
    have safe1: "hybrid_loop_safe_invar
            (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
               butlast ks @ [last ks + 1]),
              butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
              butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp),
             (ag, ah, bb))"
      by (rule hybrid_loop_safe_invar_acc_swap[OF
            hybrid_loop_safe_invar_push1_all[OF stinv pre cap1 qlen dpos rp_len rp_bound kcap kdepth]
            accinv apush])
    have ref1: "hybrid_refine_invar P l0 r0 k0 sd
            (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
             butlast ks @ [last ks + 1])
            (butlast qtodo @ [ql]) (butlast es @ [newton_child_exp (last es)])
            (butlast ss @ [sv]) (butlast cs @ [cl]) (butlast gs @ [gl]) rp (ag, ah, bb)"
      by (rule hybrid_refine_invar_split_left_step[OF inv nsplit vsplit npush vpush
            accgrow[OF g1 g0] ab P0 p0 sf v2 nf[unfolded recL] hybrid_child_depth_okD[OF depL]
            lkL[unfolded recL] okL[unfolded recL] zeroR[OF rz0] BL])
    have budG: "hybrid_budget_invar \<delta> l0 r0 k0
                  (butlast lns @ [2 * last lns, last lns + last rns],
                   butlast rns @ [last lns + last rns, 2 * last rns],
                   butlast ks @ [last ks + 1, last ks + 1]) (ag, ah, bb)"
      by (rule hybrid_budget_invar_push2_branched[OF budinv vsplit vpush lpush mu1 mu2 g1 g0])
    note VD = hybrid_alpha_views_push2_drop(2)[OF BL(1) BL(2) vpush]
    have bud1: "hybrid_budget_invar \<delta> l0 r0 k0
                  (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                   butlast ks @ [last ks + 1]) (ag, ah, bb)"
      using hybrid_budget_invar_pop[OF budG, where I = "((a + b) / 2, b)"] VD by (simp add: butlast_append)
    have payG: "hybrid_pay_invar
                  (butlast lns @ [2 * last lns, last lns + last rns],
                   butlast rns @ [last lns + last rns, 2 * last rns],
                   butlast ks @ [last ks + 1, last ks + 1])
                  (butlast gs @ [gl, 0]) rp"
      by (rule paypush[OF plL hybrid_child_pay_ok_zero])
    have pay1: "hybrid_pay_invar
                  (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                   butlast ks @ [last ks + 1])
                  (butlast gs @ [gl]) rp"
      using hybrid_pay_invar_pop[OF payG] VL SLg by (simp add: butlast_append)
    have ND1: "hybrid_alpha_nodes l0 r0 k0
                 (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                  butlast ks @ [last ks + 1])
                 (butlast es @ [newton_child_exp (last es)]) (butlast ss @ [sv])
               = hybrid_alpha_nodes l0 r0 k0
                   (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                 @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, sv)]"
      by (rule hybrid_alpha_nodes_push2_drop(1)[OF BL npush])
    have mu1': "hybrid_mu_mset \<delta>
            (hybrid_alpha_nodes l0 r0 k0
              (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
               butlast ks @ [last ks + 1])
              (butlast es @ [newton_child_exp (last es)]) (butlast ss @ [sv]))
          < hybrid_mu_mset \<delta> (hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss)"
      unfolding ND1 nsplit by (rule hybrid_mu_mset_push1_less) (simp add: mu1)
    note safe1 ref1 cap1 bud1 pay1 mu1'
  }
  note one' = this

  show ?thesis
    apply (subst hybrid_loop_body_under_cond[OF cond])
    apply (subst hybrid_loop_step_unfold)
    apply (rule order_trans[OF arm])
    apply (rule SPEC_rule)
    \<comment> \<open>\<open>simp del: One_nat_def\<close> is needed: without it \<open>clarsimp\<close> normalises every
       \<open>last ks + 1\<close> to \<open>Suc (last ks)\<close> and the \<open>+1\<close>-form premises stop firing.\<close>
    apply (clarsimp simp del: One_nat_def)
    \<comment> \<open>\<^bold>\<open>The arm's worklist outcome is a disjunction\<close> (@{const hybrid_split_wl}); its one
       elimination splits it into the two-child case, closed by the script below,
       and the left-only case, closed further down.\<close>
    apply (erule hybrid_split_wlE)
     apply (clarsimp simp del: One_nat_def)
     apply (intro conjI)
     subgoal by (rule safe'; assumption)
     subgoal
       apply (rule hybrid_refine_invar_split_step[where a = a and b = b
                     and e = e and dk = dk and s = sv0])
       apply (all \<open>(((rule inv nsplit vsplit npush vpush ab P0 p0 sf v2)
                     | (rule accgrow, assumption, assumption)
                     | (rule hybrid_child_depth_okD, assumption)
                     | (simp only: recL[symmetric] recR[symmetric])); fail)?\<close>)
       done
     subgoal
       by (rule hybrid_cap_invar_push2[OF capinv clr crr csk kne muL muR _ ndL ndR]) assumption
     subgoal
       apply (rule hybrid_budget_invar_push2_branched[OF budinv vsplit vpush])
           apply (rule lpush)
          apply (rule mu1)
         apply (rule mu2)
        apply assumption
       apply assumption
       done
     subgoal by (rule paypush; assumption)
     subgoal by (rule Pcoeffs)
     subgoal
       apply (simp only: nsplit npush)
       apply (rule hybrid_mu_mset_push2_less)
        apply (simp add: mu1)
       apply (simp add: mu2)
       done
    apply (clarsimp simp del: One_nat_def)
    \<comment> \<open>the LEFT-only case: the seven conjuncts are the block \<open>one'\<close> above, in order, bar the
       root relation, which passes straight through.\<close>
    apply (intro conjI)
          subgoal by (rule one'(1); assumption)
         subgoal by (rule one'(2); assumption)
        subgoal by (rule one'(3); assumption)
       subgoal by (rule one'(4); assumption)
      subgoal by (rule one'(5); assumption)
     subgoal by (rule Pcoeffs)
    subgoal by (rule one'(6); assumption)
    done
qed



text \<open>\<^bold>\<open>The gate-OPEN arm's complete body step.\<close> The join
  @{thm [source] hybrid_body_step_split} performs, over the gate-OPEN DISJUNCTION -- so it
  splits into two independent three-way joins: the REJECT half is the split arm's verbatim
  (@{thm [source] hybrid_refine_invar_split_step} +
  @{thm [source] hybrid_mu_mset_push2_less}), the ACCEPT half its one-child counterpart
  (@{thm [source] hybrid_refine_invar_window_step} +
  @{thm [source] hybrid_mu_mset_push1_less}).

  \<^bold>\<open>The accept half's premises are stated in the forms \<open>clarsimp\<close> PRODUCES\<close>, not the ones
  @{thm [source] hybrid_gate_open_acc}'s conclusion carries: \<open>2 ^ (2 ^ last es + 2)\<close> appears
  here as \<open>4 * 2 ^ 2 ^ last es\<close> and \<open>last ks + (2 ^ last es + 2)\<close> as \<open>Suc (Suc \<dots>)\<close>, so the body
  is \<open>clarsimp simp del: One_nat_def\<close> then \<open>intro conjI\<close>, as in
  @{thm [source] hybrid_body_step_split}.

  \<^bold>\<open>Why the accept half's per-child facts are PREMISES.\<close> The pushed poly is
  @{const newton_wcand}, built from the NODE poly, while the invariant's node poly is built from
  the ROOT \<open>rp\<close>; identifying them needs the \<open>carried_init_same_den\<close>-composition identity
  (the structural lemma below). So \<open>fw\<close>/\<open>lkw\<close>/\<open>okw\<close> enter as premises exactly as \<open>win\<close> does,
  and are discharged where that identity is in scope.\<close>
lemma hybrid_body_step_window:
  assumes cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, b, e, dk, sv0)]"
    and vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, b)]"
    and ab: "a < b"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and dpos: "0 < \<delta>" and wide: "\<delta> < real_of_rat b - real_of_rat a"
    \<comment> \<open>the k-potential half: its input, the column lengths it needs, and the node view the
       geometry lemma turns into the children's halves.\<close>
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    \<comment> \<open>the word-budget half. The REJECT branch LENGTHENS the worklist (the todo-append
       budget's own step); the ACCEPT branch replaces one node by one node and needs only the
       single child's \<open>\<mu>\<close>-drop.\<close>
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and clr: "length lns = length ks" and crr: "length rns = length ks"
    and csk: "length ss = length ks" and kne: "ks \<noteq> []" and lr0: "l0 < r0"
    and abnode: "dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks) = (a, b)"
    and npush_s: "\<And>sv. hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [last ks + 1, last ks + 1])
                   (butlast es @ [newton_child_exp (last es), newton_child_exp (last es)])
                   (butlast ss @ [sv, sv])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, sv),
                      ((a + b) / 2, b, max 1 (e - 1), dk + 1, sv)]"
    and vpush_s: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [last ks + 1, last ks + 1])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, (a + b) / 2), ((a + b) / 2, b)]"
    and accgrow_s: "\<And>ag ah bb.
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                     ag = al @ [last lns + last rns] \<and> ah = ar @ [last lns + last rns] \<and>
                     bb = ak @ [last ks + 1]) \<Longrightarrow>
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
                     ag = al \<and> ah = ar \<and> bb = ak) \<Longrightarrow>
                  dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (ag, ah, bb))
                  = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak))
                    @ (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                       then [((a + b) / 2, (a + b) / 2)] else [])"
    \<comment> \<open>the ambient word caps; \<open>safe_s\<close> is DERIVED below, not assumed.\<close>
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The window interval is a function of the index, \<open>Iw m\<close>, and every window premise is
       conditioned on the arm's own pick.\<close> A fixed \<open>I\<close> under \<open>\<And>m\<close> would force every window child to
       be the same interval (\<open>hybrid_npush_w_forall_m_forces_one_window\<close>). The pick, which the arm exports, ties
       \<open>m\<close> to an abstract interval, so these are assumptions about the one window the run actually took.
       \<open>mu_w\<close> is stated at \<open>Iw m\<close>, not \<open>(fst (Iw m), snd (Iw m))\<close>: the same pair, but the
       measure goal carries the latter and \<open>simp\<close> collapses it, while \<open>wsub\<close>/\<open>wprop\<close> must be in
       the projected form the invariant step demands.

       \<^bold>\<open>Stated at the actual count, not \<open>\<And>v\<close>.\<close> None of these four right-hand
       sides mentions \<open>v\<close>, so a \<open>\<And>v\<close> form would demand that
       every \<open>v\<close> admitting a pick land on the same window, which together with \<open>npush_w\<close>'s \<open>\<And>m\<close>
       (forcing \<open>Iw m\<close> to be the \<open>m\<close>-th child's view) is not satisfiable in general. The
       arm's SPEC pins \<open>v = \<close>@{const carried_descartes_count}\<open> X\<close>; that is the only instance
       these are used at, and the only one \<open>hybrid_window_pick_abs_node\<close> and
       \<open>hybrid_window_geometry_node\<close> prove (both below; plain names, since at this point they are forward
       references).\<close>
    and win: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                 try_window_bail_int (snd (dec :: bool \<times> bool)) a b (N_of e) P
                   (descartes_list_int a b (coeffs P)) = Some (Iw m)"
    and wsub: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                 alr_ivl_pss (fst (Iw m), snd (Iw m)) (a, b)"
    and wprop: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow> fst (Iw m) < snd (Iw m)"
    and mu_w: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                 dyadic_iv_interval_mu \<delta> (Iw m) < dyadic_iv_interval_mu \<delta> (a, b)"
    and npush_w: "\<And>m. hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)], butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)], butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
                   (butlast es @ [last es + 1]) (butlast ss @ [last ss])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(fst (Iw m), snd (Iw m), e + 1, dk + (2 ^ e + 2), sv0)]"
    and vpush_w: "\<And>m. hybrid_alpha_views l0 r0 k0 (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)], butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)], butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(fst (Iw m), snd (Iw m))]"
    and fw: "\<And>m cand v. newton_window_pick_bail v (last es) X = Some (m, cand) \<Longrightarrow> node_frame (carried_init_same_den (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)) (2 ^ (Suc (Suc (last ks + 2 ^ last es))))
                  (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp) cand (4398046511104 + v)"
    and gw: "\<And>v :: nat. 4398046511104 + v \<le> (Suc (Suc (last ks + 2 ^ last es)) + 1) * length rp
                 \<or> 4398046511104 \<le> 4398046511104 + v"
    \<comment> \<open>\<^bold>\<open>\<open>v :: nat\<close> is load-bearing.\<close> \<open>v\<close>'s only constraint here is
       \<open>2\<^sup>4\<^sup>2 \<le> 2\<^sup>4\<^sup>2 + v\<close> -- pure numerals -- so Isabelle generalises it to a FIXED type variable
       \<open>'a\<close>, and \<open>rule\<close> can then never match the \<open>nat\<close> goal. Diagnosed by inserting \<open>lkw\<close> beside
       the goal and reading the two forms: \<open>(4398046511104::'a)\<close> against \<open>nat\<close>.\<close>
    and lkw: "\<And>m cand (v :: nat). newton_window_pick_bail v (last es) X = Some (m, cand) \<Longrightarrow>
                 4398046511104 \<le> 4398046511104 + v \<longrightarrow> cand = (carried_init_same_den (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)) (2 ^ (Suc (Suc (last ks + 2 ^ last es))))
                  (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp)"
    and okw: "\<And>m cand v. newton_window_pick_bail v (last es) X = Some (m, cand) \<Longrightarrow>
               v = carried_descartes_count X \<Longrightarrow>
               hybrid_cs_ok (4398046511104 + v) (Suc (Suc v))
                 (carried_descartes_count (carried_init_same_den (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)) (2 ^ (Suc (Suc (last ks + 2 ^ last es))))
                  (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp))"
    \<comment> \<open>the k-potential's window inputs: the accepted child's \<open>\<mu>\<close>-drop at the NODE VIEW, and
       the gate's own exponent cap, which is what bounds the depth jump by \<open>C\<close>.\<close>
    and muW: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                     last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                    Suc (Suc (last ks + 2 ^ last es))))
                < dyadic_iv_interval_mu \<delta>
                    (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    and jw: "int (2 ^ last es + 2) \<le> int (2 ^ newton_pol_ecap + 2)"
    and ndW: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                fst (dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                     last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                    Suc (Suc (last ks + 2 ^ last es))))
                < snd (dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                     last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                    Suc (Suc (last ks + 2 ^ last es))))"
    \<comment> \<open>\<^bold>\<open>\<open>safe_w\<close> is also at the actual count.\<close> Unlike the six above, its right-hand side
       does mention \<open>v\<close> (in the pushed \<open>cs\<close>/\<open>gs\<close> entries), so a \<open>\<And>v\<close> form would not be vacuous,
       but it would be unprovable, because its cap-invariant input travels through \<open>muW\<close>/\<open>ndW\<close>,
       which hold only for the window the run actually picked.\<close>
    and safe_w: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                            = Some (m, cand) \<Longrightarrow> hybrid_loop_safe_invar
                  (((butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)], butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)], butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
                    butlast qtodo @ [cand], butlast es @ [last es + 1],
                    butlast ss @ [last ss], butlast cs @ [Suc (Suc (carried_descartes_count X))],
                    butlast gs @ [4398046511104 + carried_descartes_count X], rp),
                   (al, ar, ak))"
    and arm: "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
              \<le> SPEC (\<lambda>(wl, acc').
           ((poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                 acc' = (al @ [last lns + last rns], ar @ [last lns + last rns], ak @ [last ks + 1])) \<and>
              (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
                            hybrid_split_wl X (butlast lns) (butlast rns) (butlast ks) (butlast qtodo) (butlast es) (butlast ss) (butlast cs) (butlast gs) rp (last lns) (last rns) (last ks) (last es) (last ss) wl)
           \<or>
           (\<exists>m cand v. acc' = (al, ar, ak) \<and>
              v = carried_descartes_count X \<and>
              carried_descartes_count cand = v \<and>
              newton_window_pick_bail v (last es) X = Some (m, cand) \<and>
              wl = ((butlast lns @ [last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns)],
                     butlast rns @ [last lns * 2 ^ (2 ^ last es + 2) + (m + 4) * (last rns - last lns)],
                     butlast ks @ [last ks + (2 ^ last es + 2)]),
                    butlast qtodo @ [cand], butlast es @ [last es + 1], butlast ss @ [last ss],
                    butlast cs @ [v + 2], butlast gs @ [4398046511104 + v], rp)))"
    \<comment> \<open>\<^bold>\<open>The payload bound at the pushed state.\<close> The window arm is the one arm that creates a lock,
       and it also pins the payload: the child's guard is \<open>2\<^sup>4\<^sup>2 + v\<close> and its
       count is \<open>v\<close> (@{thm [source] newton_window_pick_bail_count}), so the assembly discharges
       this outright via @{thm [source] hybrid_pay_window_child}. \<^bold>\<open>Last\<close>.\<close>
    \<comment> \<open>\<^bold>\<open>Conditioned on the PICK, and at the actual count\<close> --- an unconditional \<open>\<And>m v\<close> form
       would assert the payload bound for every index and every payload, which is false.\<close>
    and paypush_w: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                                = Some (m, cand) \<Longrightarrow> hybrid_pay_invar
                      (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)],
                       butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)],
                       butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
                      (butlast gs @ [4398046511104 + carried_descartes_count X]) rp"
    \<comment> \<open>\<^bold>\<open>The payload bound, reject half\<close>: when the window pick returns \<open>None\<close> the arm falls through
       to the split at the lock guard, so this half pushes two children and needs the
       two-child shape as well as \<open>paypush_w\<close>. \<^bold>\<open>Last\<close>.\<close>
    \<comment> \<open>\<^bold>\<open>Conditioned on the arm's own exports.\<close> A \<open>\<And>gl gr\<close> form with a free right-hand side would claim the
       pushed state satisfies @{const hybrid_pay_invar} for arbitrary child guards, which is
       false. So it is conditioned, as \<open>safe\<close>\<open>'\<close> is, on the
       two atoms the arm's SPEC exports, and discharged with
       @{thm [source] hybrid_pay_invar_push2}.\<close>
    and paypush_s: "\<And>gl gr. hybrid_child_pay_ok (2 * last lns) (last ks + 1) (last lns + last rns) rp gl \<Longrightarrow>
                      hybrid_child_pay_ok (last lns + last rns) (last ks + 1) (2 * last rns) rp gr \<Longrightarrow> hybrid_pay_invar
                      (butlast lns @ [2 * last lns, last lns + last rns],
                       butlast rns @ [last lns + last rns, 2 * last rns],
                       butlast ks @ [last ks + 1, last ks + 1])
                      (butlast gs @ [gl, gr]) rp"
    \<comment> \<open>\<^bold>\<open>The root relation\<close>, @{const hybrid_state_invar}'s fifth
       conjunct, \<^bold>\<open>last\<close>. It is the same proposition at the pushed state as at the popped one
       (no arm touches \<open>P\<close> or \<open>rp\<close>), so it passes straight through; it exists so that
       \<open>hybrid_loop_correct\<close>'s \<open>\<And>s\<close> step can reach \<open>s\<close>'s own \<open>rp\<close>.\<close>
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    \<comment> \<open>the reject half's left-only case, as in @{thm [source] hybrid_body_step_split}.
       \<^bold>\<open>Last\<close>.\<close>
    and zeroR: "carried_descartes_count (carried_right X) = 0 \<Longrightarrow>
                  descartes_list_int ((a + b) / 2) b (coeffs P) = 0"
  shows "hybrid_loop_body_checked_monadic
           (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have recL: "carried_left X
      = carried_init_same_den (2 * last lns) (2 ^ (last ks + 1)) (last lns + last rns) rp"
    unfolding X_eq mult_2 by (rule carried_left_right_reconstruct(1))
  have recR: "carried_right X
      = carried_init_same_den (last lns + last rns) (2 ^ (last ks + 1)) (2 * last rns) rp"
    unfolding X_eq mult_2 by (rule carried_left_right_reconstruct(2))
  have mu1: "dyadic_iv_interval_mu \<delta> (a, (a + b) / 2) < dyadic_iv_interval_mu \<delta> (a, b)"
    and mu2: "dyadic_iv_interval_mu \<delta> ((a + b) / 2, b) < dyadic_iv_interval_mu \<delta> (a, b)"
    by (rule hybrid_mu_halve[OF dpos ab wide])+
  \<comment> \<open>the worklist's own length after a two-child push, which the todo-append budget is stated
     against. (The window arm's ACCEPT half pushes ONE child and leaves the length alone, so it
     needs no counterpart.)\<close>
  have lne: "lns \<noteq> []" using kne clr by auto
  have lpush: "length (butlast lns @ [2 * last lns, last lns + last rns]) = length lns + 1"
    using lne by simp
  \<comment> \<open>the same drops at the NODE VIEW, which is what the potential is indexed by.\<close>
  have muL: "dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0
                  ((2 * last lns, last lns + last rns), Suc (last ks)))
             < dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using mu1 by (simp add: hybrid_node_iv_split_children(1)[OF lr0] abnode)
  have muR: "dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0
                  ((last lns + last rns, 2 * last rns), Suc (last ks)))
             < dyadic_iv_interval_mu \<delta>
               (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using mu2 by (simp add: hybrid_node_iv_split_children(2)[OF lr0] abnode)
  have ndL: "fst (dyadic_iv_node_iv_of l0 r0 k0
                    ((2 * last lns, last lns + last rns), Suc (last ks)))
             < snd (dyadic_iv_node_iv_of l0 r0 k0
                    ((2 * last lns, last lns + last rns), Suc (last ks)))"
    using ab by (simp add: hybrid_node_iv_split_children(1)[OF lr0] abnode)
  have ndR: "fst (dyadic_iv_node_iv_of l0 r0 k0
                    ((last lns + last rns, 2 * last rns), Suc (last ks)))
             < snd (dyadic_iv_node_iv_of l0 r0 k0
                    ((last lns + last rns, 2 * last rns), Suc (last ks)))"
    using ab by (simp add: hybrid_node_iv_split_children(2)[OF lr0] abnode)
  \<comment> \<open>\<^bold>\<open>\<open>safe_s\<close> is derived here, not assumed.\<close> As a premise in the \<open>\<And>\<close>-over-every-\<open>qr\<close> form it would be
     contradictory (\<open>hybrid_safe_push_forall_q_is_vacuous\<close>, below), so it is derived at the one site that already
     has the geometry (\<open>muL\<close>/\<open>muR\<close>/\<open>ndL\<close>/\<open>ndR\<close>).\<close>
  have rp_len: "0 < length rp" and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    using pre unfolding hybrid_loop_step_pre_def by simp_all
  have accinv0: "dyadic_interval_vec_invar (al, ar, ak)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have Xlen: "length X = length rp"
    unfolding X_eq by (simp add: truncate_length_carried_init_same_den)
  {
    fix ql qr cl cr gl gr sv ag ah bb
    assume nf: "node_frame (carried_right X) qr gr"
       and svb: "sv \<le> last ss + 1"
       and g1: "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                  ag = al @ [last lns + last rns] \<and> ah = ar @ [last lns + last rns] \<and>
                  bb = ak @ [last ks + 1]"
       and g0: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
                  ag = al \<and> ah = ar \<and> bb = ak"
    have qlen: "length qr = length rp"
      using cdlr_node_frame_len[OF nf] Xlen by simp
    have accg: "length ag \<le> length al + 1"
      using g1 g0 by (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0") auto
    have accinv: "dyadic_interval_vec_invar (ag, ah, bb)"
      using g1 g0 accinv0
      by (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0")
         (auto simp: dyadic_interval_vec_invar_def)
    have capinv': "hybrid_cap_invar \<delta> l0 r0 k0
                     (butlast lns @ [2 * last lns, last lns + last rns],
                      butlast rns @ [last lns + last rns, 2 * last rns],
                      butlast ks @ [last ks + 1, last ks + 1])
                     (butlast ss @ [sv, sv])"
      by (rule hybrid_cap_invar_push2[OF capinv clr crr csk kne muL muR svb ndL ndR])
    have "hybrid_loop_safe_invar
            (((butlast lns @ [2 * last lns, last lns + last rns],
               butlast rns @ [last lns + last rns, 2 * last rns],
               butlast ks @ [last ks + 1, last ks + 1]),
              butlast qtodo @ [ql, qr],
              butlast es @ [newton_child_exp (last es), newton_child_exp (last es)],
              butlast ss @ [sv, sv], butlast cs @ [cl, cr], butlast gs @ [gl, gr], rp),
             (ag, ah, bb))"
      by (rule hybrid_loop_safe_invar_push2_all[OF stinv pre budinv capinv' qlen accg accinv
                 dpos rp_len rp_bound kcap kdepth])
  }
  note safe_s = this
  \<comment> \<open>\<^bold>\<open>The left-only push\<close>, prepared exactly as \<open>safe'\<close> is: every fact the one-push case
     needs, \<open>\<And>\<close>-quantified over the arm's witnesses. The right child was never built, so the
     refinement, cap and budget halves go through the phantom two-push state: its push2 lemma,
     then a pop of the phantom (@{thm [source] hybrid_refine_invar_split_left_step}). Safety does
     not need the phantom: @{thm [source] hybrid_loop_safe_invar_push1_all} then an accumulator
     swap, since the \<open>mid\<close> branch may have grown \<open>acc\<close>.\<close>
  have VL: "length rns = length lns" "length ks = length lns" using clr crr by simp_all
  have SLg: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have BL: "length (butlast lns) = length (butlast rns)" "length (butlast rns) = length (butlast ks)"
     "length (butlast es) = length (butlast ks)" "length (butlast ss) = length (butlast ks)"
    using VL SLg by simp_all
  {
    fix ql gl cl sv ag ah bb
    assume svb: "sv \<le> last ss + 1"
       and okL: "hybrid_cs_ok gl cl (carried_descartes_count (carried_left X))"
       and depL: "hybrid_child_depth_ok (last ks + 1) (length rp) gl"
       and nf: "node_frame (carried_left X) ql gl"
       and lkL: "4398046511104 \<le> gl \<longrightarrow> ql = carried_left X"
       and plL: "hybrid_child_pay_ok (2 * last lns) (last ks + 1) (last lns + last rns) rp gl"
       and rz0: "carried_descartes_count (carried_right X) = 0"
       and g1: "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                  ag = al @ [last lns + last rns] \<and> ah = ar @ [last lns + last rns] \<and>
                  bb = ak @ [last ks + 1]"
       and g0: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
                  ag = al \<and> ah = ar \<and> bb = ak"
    have qlen: "length ql = length rp"
      using cdlr_node_frame_len[OF nf] Xlen by simp
    have accg: "length ag \<le> length al + 1"
      using g1 g0 by (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0") auto
    have accinv: "dyadic_interval_vec_invar (ag, ah, bb)"
      using g1 g0 accinv0
      by (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0")
         (auto simp: dyadic_interval_vec_invar_def)
    have acap: "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
      by (rule hybrid_budget_invar_acc_grown[OF budinv lne VL])
    have apush: "dyadic_interval_vec_pushable (ag, ah, bb)"
      using acap accg accinv
      unfolding dyadic_interval_vec_pushable_def dyadic_interval_vec_invar_def by simp
    have capG: "hybrid_cap_invar \<delta> l0 r0 k0
                  (butlast lns @ [2 * last lns, last lns + last rns],
                   butlast rns @ [last lns + last rns, 2 * last rns],
                   butlast ks @ [last ks + 1, last ks + 1])
                  (butlast ss @ [sv, sv])"
      by (rule hybrid_cap_invar_push2[OF capinv clr crr csk kne muL muR svb ndL ndR])
    have cap1: "hybrid_cap_invar \<delta> l0 r0 k0
                  (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                   butlast ks @ [last ks + 1])
                  (butlast ss @ [sv])"
      using hybrid_cap_invar_pop[OF capG] clr crr csk by (simp add: butlast_append)
    have safe1: "hybrid_loop_safe_invar
            (((butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
               butlast ks @ [last ks + 1]),
              butlast qtodo @ [ql], butlast es @ [newton_child_exp (last es)],
              butlast ss @ [sv], butlast cs @ [cl], butlast gs @ [gl], rp),
             (ag, ah, bb))"
      by (rule hybrid_loop_safe_invar_acc_swap[OF
            hybrid_loop_safe_invar_push1_all[OF stinv pre cap1 qlen dpos rp_len rp_bound kcap kdepth]
            accinv apush])
    have ref1: "hybrid_refine_invar P l0 r0 k0 sd
            (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
             butlast ks @ [last ks + 1])
            (butlast qtodo @ [ql]) (butlast es @ [newton_child_exp (last es)])
            (butlast ss @ [sv]) (butlast cs @ [cl]) (butlast gs @ [gl]) rp (ag, ah, bb)"
      by (rule hybrid_refine_invar_split_left_step[OF inv nsplit vsplit npush_s vpush_s
            accgrow_s[OF g1 g0] ab P0 p0 sf v2 nf[unfolded recL] hybrid_child_depth_okD[OF depL]
            lkL[unfolded recL] okL[unfolded recL] zeroR[OF rz0] BL])
    have budG: "hybrid_budget_invar \<delta> l0 r0 k0
                  (butlast lns @ [2 * last lns, last lns + last rns],
                   butlast rns @ [last lns + last rns, 2 * last rns],
                   butlast ks @ [last ks + 1, last ks + 1]) (ag, ah, bb)"
      by (rule hybrid_budget_invar_push2_branched[OF budinv vsplit vpush_s lpush mu1 mu2 g1 g0])
    note VD = hybrid_alpha_views_push2_drop(2)[OF BL(1) BL(2) vpush_s]
    have bud1: "hybrid_budget_invar \<delta> l0 r0 k0
                  (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                   butlast ks @ [last ks + 1]) (ag, ah, bb)"
      using hybrid_budget_invar_pop[OF budG, where I = "((a + b) / 2, b)"] VD by (simp add: butlast_append)
    have payG: "hybrid_pay_invar
                  (butlast lns @ [2 * last lns, last lns + last rns],
                   butlast rns @ [last lns + last rns, 2 * last rns],
                   butlast ks @ [last ks + 1, last ks + 1])
                  (butlast gs @ [gl, 0]) rp"
      by (rule paypush_s[OF plL hybrid_child_pay_ok_zero])
    have pay1: "hybrid_pay_invar
                  (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                   butlast ks @ [last ks + 1])
                  (butlast gs @ [gl]) rp"
      using hybrid_pay_invar_pop[OF payG] VL SLg by (simp add: butlast_append)
    have ND1: "hybrid_alpha_nodes l0 r0 k0
                 (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
                  butlast ks @ [last ks + 1])
                 (butlast es @ [newton_child_exp (last es)]) (butlast ss @ [sv])
               = hybrid_alpha_nodes l0 r0 k0
                   (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                 @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, sv)]"
      by (rule hybrid_alpha_nodes_push2_drop(1)[OF BL npush_s])
    have mu1': "hybrid_mu_mset \<delta>
            (hybrid_alpha_nodes l0 r0 k0
              (butlast lns @ [2 * last lns], butlast rns @ [last lns + last rns],
               butlast ks @ [last ks + 1])
              (butlast es @ [newton_child_exp (last es)]) (butlast ss @ [sv]))
          < hybrid_mu_mset \<delta> (hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss)"
      unfolding ND1 nsplit by (rule hybrid_mu_mset_push1_less) (simp add: mu1)
    note safe1 ref1 cap1 bud1 pay1 mu1'
  }
  note one_s' = this
  show ?thesis
    apply (subst hybrid_loop_body_under_cond[OF cond])
    apply (subst hybrid_loop_step_unfold)
    apply (rule order_trans[OF arm])
    apply (rule SPEC_rule)
    \<comment> \<open>\<^bold>\<open>Why this needs MORE than @{thm [source] hybrid_body_step_split}'s step.\<close> That
       template's arm is EXISTENTIAL-FREE -- its \<open>wl\<close> is fully determined, so \<open>clarsimp\<close> alone
       substitutes everything and \<open>intro conjI\<close> follows. Both disjuncts here are existential
       (\<open>\<exists>ql gl qr gr cl cr sv\<close> / \<open>\<exists>m cand v\<close>), so after \<open>clarsimp\<close> the columns are
       \<open>\<And>\<close>-bound and need \<open>elim conjE exE\<close> + \<open>hypsubst\<close>. The template cannot show that,
       because it never has the problem.\<close>
    apply (clarsimp simp del: One_nat_def)
    apply (elim disjE)
    \<comment> \<open>\<^bold>\<open>REJECT half\<close> -- the split arm's three-way join, verbatim.\<close>
    subgoal
      apply (elim conjE)
      apply (erule hybrid_split_wlE)
       apply (clarsimp simp del: One_nat_def)
       apply (intro conjI)
      subgoal by (rule safe_s; assumption)
      subgoal
        apply (rule hybrid_refine_invar_split_step[where a = a and b = b
                      and e = e and dk = dk and s = sv0])
        apply (all \<open>(((rule inv nsplit vsplit npush_s vpush_s ab P0 p0 sf v2)
                      | (rule accgrow_s, assumption, assumption)
                      | (rule hybrid_child_depth_okD, assumption)
                      | (simp only: recL[symmetric] recR[symmetric])); fail)?\<close>)
        done
      subgoal
        by (rule hybrid_cap_invar_push2[OF capinv clr crr csk kne muL muR _ ndL ndR]) assumption
      subgoal
        apply (rule hybrid_budget_invar_push2_branched[OF budinv vsplit vpush_s])
            apply (rule lpush)
           apply (rule mu1)
          apply (rule mu2)
         apply assumption
        apply assumption
        done
      \<comment> \<open>The payload invariant, REJECT half: the lock guard falls through to the split, so this half
         pushes two children exactly as the split arm does.\<close>
      subgoal by (rule paypush_s; assumption)
      subgoal by (rule Pcoeffs)
      subgoal
        apply (simp only: nsplit npush_s)
        apply (rule hybrid_mu_mset_push2_less)
         apply (simp add: mu1)
        apply (simp add: mu2)
        done
      \<comment> \<open>the left-only case, the block \<open>one_s'\<close> in order.\<close>
      apply (clarsimp simp del: One_nat_def)
      apply (intro conjI)
            subgoal by (rule one_s'(1); assumption)
           subgoal by (rule one_s'(2); assumption)
          subgoal by (rule one_s'(3); assumption)
         subgoal by (rule one_s'(4); assumption)
        subgoal by (rule one_s'(5); assumption)
       subgoal by (rule Pcoeffs)
      subgoal by (rule one_s'(6); assumption)
      done
    \<comment> \<open>\<^bold>\<open>ACCEPT half\<close> -- the one-child counterpart. Its premises are stated in the forms
       \<open>clarsimp\<close> PRODUCES, so the same destructuring serves both halves.\<close>
    subgoal
      apply (elim conjE exE)
      apply hypsubst
      apply (intro conjI)
      subgoal by (rule safe_w, assumption)
      \<comment> \<open>\<open>I\<close> is NOT pinned by \<open>where\<close> any more: it is \<open>Iw m\<close> for the \<open>m\<close> the arm produced, and
         \<open>m\<close> is bound in this subgoal, so no method text can name it. Left schematic, the first
         window goal the alternation reaches instantiates it, and the rest must then agree --
         which they do, there being one \<open>m\<close> in context.\<close>
      subgoal
        apply (rule hybrid_refine_invar_window_step[where a = a and b = b
                      and e = e and dk = dk and s = sv0 and dec = dec])
        apply (all \<open>(((rule inv nsplit vsplit npush_w vpush_w ab P0 p0 sf v2)
                      | (rule win, assumption) | (rule wsub, assumption)
                      | (rule wprop, assumption) | (rule fw, assumption) | (rule gw)
                      | (rule okw, assumption, rule refl)); fail)?\<close>)
        \<comment> \<open>\<open>lk1\<close> is the one the alternation does not take -- close it directly.\<close>
        apply (rule lkw, assumption)
        done
      subgoal
        apply (rule hybrid_cap_invar_push1[OF capinv clr crr csk kne,
                      where j = "2 ^ last es + 2"])
           apply (rule muW, assumption)
          apply simp
         apply (rule jw)
        apply (rule ndW, assumption)
        done
      subgoal
        apply (rule hybrid_budget_invar_push1[OF budinv vsplit vpush_w])
          apply (simp add: lne)
         apply (simp add: mu_w)
        apply simp
        done
      \<comment> \<open>The payload invariant, ACCEPT half: the window child, whose payload IS its count.\<close>
      subgoal by (rule paypush_w; assumption)
      subgoal by (rule Pcoeffs)
      subgoal
        apply (simp only: nsplit npush_w)
        apply (rule hybrid_mu_mset_push1_less)
        apply (simp add: mu_w)
        done
      done
    done

qed

text \<open>\<^bold>\<open>The one-child \<open>\<alpha>\<close> push law\<close>, the window counterpart of
  @{thm [source] hybrid_alpha_nodes_append2}. It never existed, which is why the window arm's
  \<open>npush_w\<close> was a premise nobody could discharge.\<close>
lemma hybrid_alpha_nodes_append1:
  assumes lr: "length lns = length rns" and rk: "length rns = length ks"
    and le: "length es = length ks" and ls: "length ss = length ks"
  shows "hybrid_alpha_nodes l0 r0 k0 (lns @ [x], rns @ [y], ks @ [p]) (es @ [e1]) (ss @ [s1])
       = hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
         @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((x, y), p)),
             snd (dyadic_iv_node_iv_of l0 r0 k0 ((x, y), p)), e1, p, s1)]"
  using assms
  by (simp add: hybrid_alpha_nodes_def dyadic_interval_vec_triples_def)

text \<open>\<^bold>\<open>And the window \<open>npush_w\<close> IS satisfiable\<close> once \<open>Iw\<close> is the \<open>\<alpha>\<close>-image of the pushed
  column -- for EVERY \<open>m\<close>, which is exactly what the old fixed-\<open>I\<close> form could not be. Same
  standard as \<open>hybrid_npush_split_satisfiable\<close>: a repaired premise is not
  repaired until something can discharge it.\<close>
lemma hybrid_npush_w_satisfiable:
  assumes lr: "length (butlast lns) = length (butlast rns)"
    and rk: "length (butlast rns) = length (butlast ks)"
    and le: "length (butlast es) = length (butlast ks)"
    and ls: "length (butlast ss) = length (butlast ks)"
    and Iw: "Iw m = dyadic_iv_node_iv_of l0 r0 k0
                      ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                        last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                       Suc (Suc (last ks + 2 ^ last es)))"
    \<comment> \<open>oriented so \<open>simp\<close> rewrites the GOAL into \<open>last \<dots>\<close> terms, the direction that worked for
       the split twin -- the reverse leaves the geometry stated at variables the goal no longer
       mentions.\<close>
    and ee: "e = last es" and dd: "dk = last ks" and sv: "sv0 = last ss"
  shows "hybrid_alpha_nodes l0 r0 k0
           (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)],
            butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)],
            butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
           (butlast es @ [last es + 1]) (butlast ss @ [last ss])
       = hybrid_alpha_nodes l0 r0 k0
           (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
         @ [(fst (Iw m), snd (Iw m), e + 1, dk + (2 ^ e + 2), sv0)]"
  by (simp add: hybrid_alpha_nodes_append1[OF lr rk le ls] Iw ee dd sv)

lemma hybrid_alpha_views_append1:
  assumes lr: "length lns = length rns" and rk: "length rns = length ks"
  shows "hybrid_alpha_views l0 r0 k0 (lns @ [x], rns @ [y], ks @ [p])
       = hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
         @ [dyadic_iv_node_iv_of l0 r0 k0 ((x, y), p)]"
  using assms
  by (simp add: hybrid_alpha_views_def dyadic_interval_vec_triples_def)

text \<open>\<^bold>\<open>The pop decomposition\<close> -- \<open>nsplit\<close>/\<open>vsplit\<close> at an arbitrary loop state, which is what
  every arm lemma opens with. Via the append laws on \<open>butlast \<dots> @ [last \<dots>]\<close> rather than via the
  base's \<open>butlast\<close>-of-\<open>\<alpha>\<close> pair, since that direction leaves the popped node's SHAPE implicit and
  the arms need it explicit.\<close>
lemma hybrid_alpha_nodes_pop_decomp:
  assumes lne: "lns \<noteq> []" and lr: "length rns = length lns" and lk: "length ks = length lns"
    and le: "length es = length lns" and ls: "length ss = length lns"
  shows "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
       = hybrid_alpha_nodes l0 r0 k0
           (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
         @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
             snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
             last es, last ks, last ss)]"
proof -
  have ne: "rns \<noteq> []" "ks \<noteq> []" "es \<noteq> []" "ss \<noteq> []" using lne lr lk le ls by auto
  have L: "length (butlast lns) = length (butlast rns)"
    "length (butlast rns) = length (butlast ks)"
    "length (butlast es) = length (butlast ks)"
    "length (butlast ss) = length (butlast ks)"
    using lr lk le ls by simp_all
  have "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
      = hybrid_alpha_nodes l0 r0 k0
          (butlast lns @ [last lns], butlast rns @ [last rns], butlast ks @ [last ks])
          (butlast es @ [last es]) (butlast ss @ [last ss])"
    using lne ne by (simp add: append_butlast_last_id)
  also have "\<dots> = hybrid_alpha_nodes l0 r0 k0
           (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
         @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
             snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
             last es, last ks, last ss)]"
    by (rule hybrid_alpha_nodes_append1[OF L(1) L(2) L(3) L(4)])
  finally show ?thesis .
qed

lemma hybrid_alpha_views_pop_decomp:
  assumes lne: "lns \<noteq> []" and lr: "length rns = length lns" and lk: "length ks = length lns"
  shows "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
       = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
         @ [dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)]"
proof -
  have ne: "rns \<noteq> []" "ks \<noteq> []" using lne lr lk by auto
  have L: "length (butlast lns) = length (butlast rns)"
    "length (butlast rns) = length (butlast ks)" using lr lk by simp_all
  have "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
      = hybrid_alpha_views l0 r0 k0
          (butlast lns @ [last lns], butlast rns @ [last rns], butlast ks @ [last ks])"
    using lne ne by (simp add: append_butlast_last_id)
  also have "\<dots> = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
         @ [dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)]"
    by (rule hybrid_alpha_views_append1[OF L(1) L(2)])
  finally show ?thesis .
qed


text \<open>\<^bold>\<open>And the corrected shape IS satisfiable.\<close> With the \<open>\<sigma>\<close> slot carrying the arm's own
  \<open>sv\<close>, \<open>npush\<close> is just @{thm [source] hybrid_alpha_nodes_append2} plus the child GEOMETRY,
  and the two geometry facts are exactly what the step assembly has to supply anyway. Contrast
  \<open>hybrid_npush_forall_sv_is_vacuous\<close>, whose \<open>sv\<close>-independent right-hand side no lengths or
  geometry could ever satisfy.\<close>
lemma hybrid_npush_split_satisfiable:
  assumes lr: "length (butlast lns) = length (butlast rns)"
    and rk: "length (butlast rns) = length (butlast ks)"
    and le: "length (butlast es) = length (butlast ks)"
    and ls: "length (butlast ss) = length (butlast ks)"
    \<comment> \<open>stated in the form \<open>simp\<close> PRODUCES (\<open>Suc (last ks)\<close>, \<open>last ks = dk\<close>), not the
       \<open>+ 1\<close> form the pushed column carries -- this file's iron rule, paid for again here.\<close>
    and geoL: "dyadic_iv_node_iv_of l0 r0 k0 ((2 * last lns, last lns + last rns), Suc (last ks))
               = (a, (a + b) / 2)"
    and geoR: "dyadic_iv_node_iv_of l0 r0 k0 ((last lns + last rns, 2 * last rns), Suc (last ks))
               = ((a + b) / 2, b)"
    and ee: "newton_child_exp (last es) = max 1 (e - 1)"
    \<comment> \<open>oriented \<open>dk \<rightarrow> last ks\<close>: the other way round \<open>simp\<close> rewrites the GOAL's depth to
       \<open>Suc dk\<close> and then \<open>geoL\<close>/\<open>geoR\<close>, stated at \<open>last ks\<close>, stop firing.\<close>
    and dd: "dk = last ks"
  shows "hybrid_alpha_nodes l0 r0 k0
           (butlast lns @ [2 * last lns, last lns + last rns],
            butlast rns @ [last lns + last rns, 2 * last rns],
            butlast ks @ [last ks + 1, last ks + 1])
           (butlast es @ [newton_child_exp (last es), newton_child_exp (last es)])
           (butlast ss @ [sv, sv])
       = hybrid_alpha_nodes l0 r0 k0
           (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
         @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, sv),
            ((a + b) / 2, b, max 1 (e - 1), dk + 1, sv)]"
  by (simp add: hybrid_alpha_nodes_append2[OF lr rk le ls] geoL geoR ee dd)

text \<open>\<^bold>\<open>The STRUCTURAL lemma\<close> -- \<open>carried_init_same_den\<close> at the @{const Poly} level,
  and the single fact both (c\<acute>) and (d) are corollaries of. Nothing here is new: it is the three
  existing \<open>Poly\<close>-level laws composed in the order @{const carried_init_same_den}'s own
  definition applies them.

  \<^bold>\<open>@{const carried_init_same_den} IS an affine substitution\<close>: homogenise by \<open>d\<close>, shift by
  \<open>l\<close>, dilate by \<open>r - l\<close> -- which composes to \<open>y \<mapsto> (l + (r - l) y) / d\<close>, i.e. the map
  taking \<open>[0, 1]\<close> onto the node \<open>[l/d, r/d]\<close>. The \<open>smult\<close> factor \<open>d\<^sup>n\<^sup>-\<^sup>1\<close> is the
  homogenisation's, and it is NONZERO -- which is what makes the vanishing-iff of (c\<acute>) exact.

  Reuses @{thm [source] cdlr_Poly_rev_scale_rev} (the homogenise step, proven for the
  bisection route), @{thm [source] Poly_taylor_shift_list} and @{thm [source] Poly_scale_poly_list}
  (\<open>Dsc_Taylor\<close>/\<open>Dsc_Int\<close>). Stated over \<rat> because that is the field
  @{thm [source] cdlr_Poly_rev_scale_rev} needs for \<open>1/d\<close>.\<close>
lemma cdlr_Poly_carried_frame_rat:
  fixes d l r :: rat
  assumes d0: "d \<noteq> 0"
  shows "Poly (scale_poly_list (r - l) (taylor_shift_list l (rev (scale_poly_list d (rev X)))))
       = smult (d ^ (length X - 1)) (pcompose (Poly X) [:l / d, (r - l) / d:])"
proof -
  have inner: "Poly (rev (scale_poly_list d (rev X)))
             = smult (d ^ (length X - 1)) (pcompose (Poly X) [:0, 1 / d:])"
    by (rule cdlr_Poly_rev_scale_rev[OF d0])
  have "Poly (scale_poly_list (r - l) (taylor_shift_list l (rev (scale_poly_list d (rev X)))))
      = pcompose (Poly (taylor_shift_list l (rev (scale_poly_list d (rev X))))) [:0, r - l:]"
    by (rule Poly_scale_poly_list)
  also have "\<dots> = pcompose (pcompose (Poly (rev (scale_poly_list d (rev X)))) [:l, 1:])
                    [:0, r - l:]"
    by (simp add: Poly_taylor_shift_list)
  also have "\<dots> = pcompose (pcompose (smult (d ^ (length X - 1))
                      (pcompose (Poly X) [:0, 1 / d:])) [:l, 1:]) [:0, r - l:]"
    by (simp only: inner)
  \<comment> \<open>\<^bold>\<open>The \<open>smult\<close> first, the three linear maps second -- as ONE \<open>simp\<close> this does not
     close\<close>: \<open>smult c p = smult c q\<close> splits into \<open>p = q \<or> c = 0\<close> and the goal comes back a
     DISJUNCTION with \<open>d = 0\<close> in it. Riding the \<open>smult\<close> out on its own leaves a pure
     \<open>pcompose\<close> identity, which associativity plus the two linear collapses then close.\<close>
  also have "\<dots> = smult (d ^ (length X - 1))
                    (pcompose (pcompose (pcompose (Poly X) [:0, 1 / d:]) [:l, 1:]) [:0, r - l:])"
    by (simp add: pcompose_smult)
  also have "pcompose (pcompose (pcompose (Poly X) [:0, 1 / d:]) [:l, 1:]) [:0, r - l:]
           = pcompose (Poly X) [:l / d, (r - l) / d:]"
  proof -
    \<comment> \<open>\<^bold>\<open>\<open>pcompose_assoc\<close> must be used \<open>[symmetric]\<close> here.\<close> It is stated
       \<open>p \<circ>\<^sub>p (q \<circ>\<^sub>p r) = (p \<circ>\<^sub>p q) \<circ>\<^sub>p r\<close> -- RIGHT-nested to LEFT-nested. This goal is already
       left-nested, so as a plain simp rule it is a NO-OP. Reversed, it exposes \<open>B \<circ>\<^sub>p C\<close> and then
       \<open>A \<circ>\<^sub>p (\<dots>)\<close>, which are the two collapses below.\<close>
    have A: "pcompose [:l, 1:] [:0, r - l:] = [:l, r - l:]" by simp
    have B: "pcompose [:0, 1 / d:] [:l, r - l:] = [:l / d, (r - l) / d:]" by simp
    show ?thesis by (simp only: pcompose_assoc[symmetric] A B)
  qed
  finally show ?thesis .
qed


text \<open>\<^bold>\<open>The int-level form, and the (c\<acute>) evaluation bridge.\<close> Reuses
  @{thm [source] Poly_map_rat_of_int} and @{thm [source] poly_eq_same_length} (\<open>Dsc_Int\<close>) and
  the same rat-image opening step @{thm [source] carried_init_child_left} uses.\<close>
lemma cdlr_Poly_carried_init_same_den_int:
  fixes d :: int
  assumes d0: "d \<noteq> 0"
  shows "map_poly rat_of_int (Poly (carried_init_same_den l d r xs))
       = smult ((rat_of_int d) ^ (length xs - 1))
           (pcompose (map_poly rat_of_int (Poly xs))
             [: rat_of_int l / rat_of_int d, (rat_of_int r - rat_of_int l) / rat_of_int d :])"
proof -
  have d0': "rat_of_int d \<noteq> 0" using d0 by simp
  have LIST: "map rat_of_int (carried_init_same_den l d r xs)
      = scale_poly_list (rat_of_int r - rat_of_int l)
          (taylor_shift_list (rat_of_int l)
            (rev (scale_poly_list (rat_of_int d) (rev (map rat_of_int xs)))))"
    by (simp add: carried_init_same_den_def
        scale_for_fractional_shift_eq_scale_poly_list rev_map[symmetric]
        map_rat_of_int_scale_poly_list map_rat_of_int_taylor_shift_list)
  have "map_poly rat_of_int (Poly (carried_init_same_den l d r xs))
      = Poly (map rat_of_int (carried_init_same_den l d r xs))"
    by (simp add: Poly_map_rat_of_int)
  also have "\<dots> = Poly (scale_poly_list (rat_of_int r - rat_of_int l)
          (taylor_shift_list (rat_of_int l)
            (rev (scale_poly_list (rat_of_int d) (rev (map rat_of_int xs))))))"
    by (simp only: LIST)
  also have "\<dots> = smult ((rat_of_int d) ^ (length (map rat_of_int xs) - 1))
        (pcompose (Poly (map rat_of_int xs))
          [: rat_of_int l / rat_of_int d, (rat_of_int r - rat_of_int l) / rat_of_int d :])"
    by (rule cdlr_Poly_carried_frame_rat[OF d0'])
  finally show ?thesis by (simp add: Poly_map_rat_of_int)
qed

lemma carried_init_same_den_eval:
  fixes d :: int
  assumes d0: "d \<noteq> 0"
  shows "poly (map_poly rat_of_int (Poly (carried_init_same_den l d r xs))) t
       = (rat_of_int d) ^ (length xs - 1)
         * poly (map_poly rat_of_int (Poly xs))
             ((rat_of_int l + (rat_of_int r - rat_of_int l) * t) / rat_of_int d)"
proof -
  have d0': "rat_of_int d \<noteq> 0" using d0 by simp
  show ?thesis
    unfolding cdlr_Poly_carried_init_same_den_int[OF d0]
    \<comment> \<open>\<open>ac_simps\<close> for the last step only: \<open>poly_pcompose\<close> leaves \<open>t * (r - l) / d\<close>
       where the statement says \<open>(r - l) * t / d\<close>.\<close>
    by (simp add: poly_pcompose add_divide_distrib ac_simps)
qed

text \<open>\<^bold>\<open>(c\<acute>): the node poly vanishes at a point iff the ROOT poly vanishes at that point's
  image under the node's own affine map.\<close> The \<open>d\<^sup>n\<^sup>-\<^sup>1\<close> factor is nonzero, so the iff is exact --
  which is the whole reason the \<open>accgrow\<close> branch condition can be transported at all.\<close>
lemma carried_init_same_den_eval_zero_iff:
  fixes d :: int
  assumes d0: "d \<noteq> 0"
  shows "(poly (map_poly rat_of_int (Poly (carried_init_same_den l d r xs))) t = 0)
       = (poly (map_poly rat_of_int (Poly xs))
            ((rat_of_int l + (rat_of_int r - rat_of_int l) * t) / rat_of_int d) = 0)"
  using carried_init_same_den_eval[OF d0, of l r xs t] d0 by simp



text \<open>\<^bold>\<open>(c\<acute>) part 1: the two midpoints coincide in ABSOLUTE coordinates.\<close> Pure
  arithmetic -- deliberately stated with no @{const poly} term in it, so the affine cancellation
  cannot be confounded by \<open>simp\<close> re-deriving inside a \<open>carried_init_same_den\<close>. Each step below
  was bisected standalone before assembly.\<close>
text \<open>\<^bold>\<open>Three tiny helpers, and the reason they exist.\<close> \<open>field_simps\<close> against this theory's
  AMBIENT SIMPSET (the whole Bail/Truncate/pipeline import chain) is very slow on a goal carrying
  \<open>dyadic_rat\<close> and \<open>rat_of_int (2\<^sup>k)\<close>, although the same tactic is fast standalone. Stated over
  plain \<open>rat\<close> variables the same facts are one \<open>rule\<close> each, and the ambient set never enters.\<close>
lemma dyadic_rat_div: "dyadic_rat x k = rat_of_int x / 2 ^ k"
  by (simp add: dyadic_rat_def)

text \<open>\<^bold>\<open>No \<open>field_simps\<close> in either\<close> -- even at FOUR plain variables it is slow against this
  theory's ambient simpset. \<open>rat_affine_over_den\<close> is pure rewriting (three named distribution
  laws, no arithmetic search); \<open>rat_mid_over_den\<close> is that plus one \<open>argo\<close> step, which is
  linear over the atoms \<open>A / D\<close> and \<open>B / D\<close> and never touches the simpset at all.\<close>
lemma rat_affine_over_den:
  fixes A B T D :: rat
  shows "(A + (B - A) * T) / D = A / D + (B / D - A / D) * T"
proof -
  have split: "(A + (B - A) * T) / D = A / D + ((B - A) * T) / D"
    by (rule add_divide_distrib)
  have shift: "((B - A) * T) / D = ((B - A) / D) * T"
    by (simp only: times_divide_eq_left)
  have dist: "(B - A) / D = B / D - A / D"
    by (rule diff_divide_distrib)
  show ?thesis by (simp only: split shift dist)
qed

lemma rat_half_mix:
  fixes X Y :: rat
  shows "X + (Y - X) * (1 / 2) = (X + Y) / 2"
  \<comment> \<open>safe to use \<open>field_simps\<close> HERE: no division by a variable, so none of the
     conditional division rules that made the ambient simpset expensive can fire.\<close>
  by (simp add: field_simps)

lemma rat_mid_over_den:
  fixes A B D :: rat
  shows "(A + (B - A) * (1 / 2)) / D = (A / D + B / D) / 2"
proof -
  have "(A + (B - A) * (1 / 2)) / D = A / D + (B / D - A / D) * (1 / 2)"
    by (rule rat_affine_over_den)
  also have "\<dots> = (A / D + B / D) / 2" by (rule rat_half_mix)
  finally show ?thesis .
qed

lemma hybrid_node_mid_abs:
  assumes lr0: "l0 < r0"
    and abv: "(a, b) = dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)"
  shows "(rat_of_int l0 + (rat_of_int r0 - rat_of_int l0) * ((a + b) / 2)) / rat_of_int (2 ^ k0)
       = (rat_of_int l + (rat_of_int r - rat_of_int l) * (1 / 2)) / rat_of_int (2 ^ k)"
proof -
  have lo_lt: "dyadic_rat l0 k0 < dyadic_rat r0 k0"
    using lr0 by (simp add: dyadic_rat_def divide_strict_right_mono)
  hence hne: "dyadic_rat r0 k0 - dyadic_rat l0 k0 \<noteq> 0" by simp
  have aval: "a = (dyadic_rat l k - dyadic_rat l0 k0) / (dyadic_rat r0 k0 - dyadic_rat l0 k0)"
    and bval: "b = (dyadic_rat r k - dyadic_rat l0 k0) / (dyadic_rat r0 k0 - dyadic_rat l0 k0)"
    using abv by (simp_all add: dyadic_iv_node_iv_of_def dyadic_iv_node_iv_def Let_def)
  \<comment> \<open>recover the endpoints first, then average: no division survives into the arithmetic.\<close>
  have ea: "(dyadic_rat r0 k0 - dyadic_rat l0 k0) * a = dyadic_rat l k - dyadic_rat l0 k0"
    unfolding aval using hne by simp
  have eb: "(dyadic_rat r0 k0 - dyadic_rat l0 k0) * b = dyadic_rat r k - dyadic_rat l0 k0"
    unfolding bval using hne by simp
  have Rmid: "dyadic_rat l0 k0 + (dyadic_rat r0 k0 - dyadic_rat l0 k0) * ((a + b) / 2)
            = (dyadic_rat l k + dyadic_rat r k) / 2"
  proof -
    have "(dyadic_rat r0 k0 - dyadic_rat l0 k0) * ((a + b) / 2)
        = ((dyadic_rat r0 k0 - dyadic_rat l0 k0) * a
           + (dyadic_rat r0 k0 - dyadic_rat l0 k0) * b) / 2"
      by (simp add: distrib_left add_divide_distrib)
    also have "\<dots> = ((dyadic_rat l k - dyadic_rat l0 k0)
                     + (dyadic_rat r k - dyadic_rat l0 k0)) / 2"
      by (simp only: ea eb)
    finally show ?thesis by (simp add: field_simps)
  qed
  \<comment> \<open>each of these is a \<open>rule\<close>, not a \<open>simp\<close>: see the helpers' note above.\<close>
  have p0: "(2::rat) ^ k \<noteq> 0" and p00: "(2::rat) ^ k0 \<noteq> 0" by simp_all
  have cvtk: "rat_of_int (2 ^ k) = (2::rat) ^ k"
    and cvtk0: "rat_of_int (2 ^ k0) = (2::rat) ^ k0" by simp_all
  have Lc: "(rat_of_int l + (rat_of_int r - rat_of_int l) * (1 / 2)) / rat_of_int (2 ^ k)
          = (dyadic_rat l k + dyadic_rat r k) / 2"
    unfolding cvtk dyadic_rat_div by (rule rat_mid_over_den)
  have Rc: "(rat_of_int l0 + (rat_of_int r0 - rat_of_int l0) * ((a + b) / 2)) / rat_of_int (2 ^ k0)
          = dyadic_rat l0 k0 + (dyadic_rat r0 k0 - dyadic_rat l0 k0) * ((a + b) / 2)"
    unfolding cvtk0 dyadic_rat_div by (rule rat_affine_over_den)
  show ?thesis by (simp only: Lc Rc Rmid)
qed

text \<open>\<^bold>\<open>(c\<acute>) part 2: the bridge \<open>accgrow\<close> needs.\<close> Two applications of
  @{thm [source] carried_init_same_den_eval_zero_iff} -- one at the NODE frame, one at the ROOT
  frame -- joined by part 1. The \<open>P_eq\<close> premise is the keystone's own, threaded down.\<close>
lemma hybrid_mid_zero_bridge:
  assumes lr0: "l0 < r0"
    and P_eq: "P = Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)"
    and X_eq: "X = carried_init_same_den l (2 ^ k) r rp"
    and abv: "(a, b) = dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)"
  shows "(poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)
       = (poly (map_poly rat_of_int P) ((a + b) / 2) = 0)"
proof -
  have d0: "(2::int) ^ k \<noteq> 0" and d00: "(2::int) ^ k0 \<noteq> 0" by simp_all
  have A: "(poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)
         = (poly (map_poly rat_of_int (Poly rp))
              ((rat_of_int l + (rat_of_int r - rat_of_int l) * (1 / 2))
               / rat_of_int (2 ^ k)) = 0)"
    unfolding X_eq by (rule carried_init_same_den_eval_zero_iff[OF d0])
  have B: "(poly (map_poly rat_of_int P) ((a + b) / 2) = 0)
         = (poly (map_poly rat_of_int (Poly rp))
              ((rat_of_int l0 + (rat_of_int r0 - rat_of_int l0) * ((a + b) / 2))
               / rat_of_int (2 ^ k0)) = 0)"
    unfolding P_eq by (rule carried_init_same_den_eval_zero_iff[OF d00])
  show ?thesis
    by (simp only: A B hybrid_node_mid_abs[OF lr0 abv])
qed


text \<open>\<^bold>\<open>Consistency check FIRST\<close>: at \<open>m = 0\<close>, \<open>w = 1\<close>, \<open>dd = 2\<close> the composite's outer factor
  is @{const carried_left} itself, so the general statement below must specialise to the ALREADY
  PROVEN @{thm [source] carried_init_child_left}. If this bridge fails the general shape is
  wrong and no effort should go into proving it.\<close>
lemma carried_init_same_den_zero_one: "carried_init_same_den 0 2 1 Q = carried_left Q"
  by (simp add: carried_init_same_den_def carried_left_def)

lemma carried_init_same_den_compose_agrees_with_child_left:
  fixes d :: int
  assumes d0: "d \<noteq> 0"
  shows "carried_init_same_den 0 2 (0 + 1) (carried_init_same_den l d r xs)
       = carried_init_same_den (l * 2 + 0 * (r - l)) (d * 2) (l * 2 + (0 + 1) * (r - l)) xs"
  using carried_init_child_left[OF d0, of l r xs]
  by (simp add: carried_init_same_den_zero_one mult.commute)

text \<open>\<^bold>\<open>The COMPOSITION identity.\<close> Two nested
  @{const carried_init_same_den} frames collapse to one, because composing two affine maps gives
  an affine map. The window arm's \<open>fw\<close>/\<open>lkw\<close>/\<open>okw\<close>
  all rest on it: @{const newton_wcand} builds its candidate from the NODE poly, while the
  invariant builds the node poly from the ROOT \<open>rp\<close>.

  \<^bold>\<open>Route\<close>: @{thm [source] cdlr_Poly_carried_init_same_den_int} twice at the \<open>Poly\<close> level,
  then back to LISTS by @{thm [source] poly_eq_same_length} (both sides have length \<open>length xs\<close>,
  by @{thm [source] truncate_length_carried_init_same_den}) and
  @{thm [source] map_rat_of_int_inj} -- the same closing pair
  @{thm [source] carried_init_child_left} uses for the bisection instance.

  \<^bold>\<open>Coefficient arithmetic is done by NAMED RULES, never \<open>field_simps\<close>\<close>: every one of these
  goals divides by a variable, which is precisely the shape that is slow against this theory's
  ambient simpset (see the helper note above \<open>rat_affine_over_den\<close>).\<close>

lemma rat_div_mul_div:
  fixes a b c e :: rat
  shows "(a / c) * (b / e) = (a * b) / (c * e)"
  by (simp only: times_divide_times_eq)

lemma rat_div_widen:
  fixes a c e :: rat
  assumes e0: "e \<noteq> 0"
  shows "a / c = (a * e) / (c * e)"
  by (rule mult_divide_mult_cancel_right[OF e0, symmetric])

text \<open>\<^bold>\<open>Stated at the form the rewrite chain actually REACHES\<close>, not the one the composition
  starts in: \<open>cdlr_compose_coeff1\<close> is general in its numerator, so it fires on the \<open>m\<close>-instance
  too and collapses \<open>((r - l) / d) * (m / dd)\<close> before any \<open>l / d + \<dots>\<close> law can match. Stated
  the other way round this lemma silently never applies.\<close>
lemma cdlr_compose_coeff0:
  fixes l r m d dd :: rat
  assumes dd0: "dd \<noteq> 0"
  shows "l / d + (m * (r - l)) / (d * dd) = (l * dd + m * (r - l)) / (d * dd)"
proof -
  have B: "l / d = (l * dd) / (d * dd)" by (rule rat_div_widen[OF dd0])
  show ?thesis by (simp only: B add_divide_distrib[symmetric])
qed

lemma cdlr_compose_coeff1:
  fixes l r w d dd :: rat
  shows "((r - l) / d) * (w / dd) = (w * (r - l)) / (d * dd)"
  by (simp only: rat_div_mul_div mult.commute)

lemma rat_num_diff:
  fixes l r m w dd :: rat
  shows "l * dd + (m + w) * (r - l) - (l * dd + m * (r - l)) = w * (r - l)"
  by (simp add: algebra_simps)

lemma rat_plus_minus:
  fixes m w :: rat
  shows "m + w - m = w"
  by simp

lemma rat_pow_swap:
  fixes d dd :: rat
  shows "dd ^ n * d ^ n = (d * dd) ^ n"
  by (simp add: power_mult_distrib mult.commute)

lemma pcompose_linear_linear:
  fixes A B C E :: rat
  shows "pcompose [:A, B:] [:C, E:] = [: A + B * C, B * E :]"
  by simp

lemma carried_init_same_den_compose:
  fixes d dd :: int
  assumes d0: "d \<noteq> 0" and dd0: "dd \<noteq> 0"
  shows "carried_init_same_den m dd (m + w) (carried_init_same_den l d r xs)
       = carried_init_same_den (l * dd + m * (r - l)) (d * dd)
           (l * dd + (m + w) * (r - l)) xs"
proof (rule map_rat_of_int_inj, rule poly_eq_same_length)
  show "length (map rat_of_int (carried_init_same_den m dd (m + w)
                  (carried_init_same_den l d r xs)))
      = length (map rat_of_int (carried_init_same_den (l * dd + m * (r - l)) (d * dd)
                  (l * dd + (m + w) * (r - l)) xs))"
    by (simp add: truncate_length_carried_init_same_den)
next
  have dr0: "rat_of_int d \<noteq> 0" and ddr0: "rat_of_int dd \<noteq> 0"
    using d0 dd0 by simp_all
  have ddne: "d * dd \<noteq> 0" using d0 dd0 by simp
  have ddd0: "rat_of_int (d * dd) \<noteq> 0" using dr0 ddr0 by simp
  have lenQ: "length (carried_init_same_den l d r xs) = length xs"
    by (rule truncate_length_carried_init_same_den)
  \<comment> \<open>the OUTER frame, then the inner one substituted into it.\<close>
  have outer: "map_poly rat_of_int (Poly (carried_init_same_den m dd (m + w)
                  (carried_init_same_den l d r xs)))
             = smult (rat_of_int dd ^ (length xs - 1))
                 (pcompose (map_poly rat_of_int (Poly (carried_init_same_den l d r xs)))
                   [: rat_of_int m / rat_of_int dd,
                      (rat_of_int (m + w) - rat_of_int m) / rat_of_int dd :])"
    using cdlr_Poly_carried_init_same_den_int[OF dd0,
            of m "m + w" "carried_init_same_den l d r xs"] lenQ by simp
  have inner: "map_poly rat_of_int (Poly (carried_init_same_den l d r xs))
             = smult (rat_of_int d ^ (length xs - 1))
                 (pcompose (map_poly rat_of_int (Poly xs))
                   [: rat_of_int l / rat_of_int d,
                      (rat_of_int r - rat_of_int l) / rat_of_int d :])"
    by (rule cdlr_Poly_carried_init_same_den_int[OF d0])
  have target: "map_poly rat_of_int (Poly (carried_init_same_den (l * dd + m * (r - l)) (d * dd)
                  (l * dd + (m + w) * (r - l)) xs))
             = smult (rat_of_int (d * dd) ^ (length xs - 1))
                 (pcompose (map_poly rat_of_int (Poly xs))
                   [: rat_of_int (l * dd + m * (r - l)) / rat_of_int (d * dd),
                      (rat_of_int (l * dd + (m + w) * (r - l))
                       - rat_of_int (l * dd + m * (r - l))) / rat_of_int (d * dd) :])"
    by (rule cdlr_Poly_carried_init_same_den_int[OF ddne])
  show "Poly (map rat_of_int (carried_init_same_den m dd (m + w)
                  (carried_init_same_den l d r xs)))
      = Poly (map rat_of_int (carried_init_same_den (l * dd + m * (r - l)) (d * dd)
                  (l * dd + (m + w) * (r - l)) xs))"
    \<comment> \<open>\<open>simp only\<close> throughout: every rewrite is named, and the ambient simpset -- which
       is slow on any goal dividing by a variable -- never enters.\<close>
    apply (simp only: Poly_map_rat_of_int outer inner target)
    apply (simp only: pcompose_smult smult_smult pcompose_assoc[symmetric])
    apply (simp only: pcompose_linear_linear)
    \<comment> \<open>push the int coercions in, settle the two numerators, then the two coefficient
       identities and the power. Every step named.\<close>
    apply (simp only: of_int_add of_int_mult of_int_diff)
    apply (simp only: rat_num_diff rat_plus_minus)
    apply (simp only: cdlr_compose_coeff0[OF ddr0] cdlr_compose_coeff1 rat_pow_swap)
    done
qed


text \<open>\<^bold>\<open>A frame at the SAME poly holds at any guard\<close> -- \<open>g = 0\<close> is the definitional case and
  any larger guard follows by @{thm [source] gframe_mono} from @{thm [source] gframe_exact}. This
  is what the window's \<open>fw\<close> needs once its candidate is identified with the recompute.\<close>
lemma node_frame_any: "node_frame X X g"
proof (cases "g = 0")
  case True thus ?thesis by (simp add: node_frame_def)
next
  case False
  have "gframe 0 g X X" by (rule gframe_mono[OF gframe_exact]) simp
  thus ?thesis using False by (auto simp: node_frame_def)
qed


section \<open>The arm-selection count bridge\<close>

text \<open>\<^bold>\<open>The gap this closes.\<close> Every one of the
  four assemblies demands the ABSTRACT face of the arm selection ---
  \<open>descartes_list_int (fst (dyadic_iv_node_iv_of \<dots>)) (snd (\<dots>)) (coeffs P) = 0 / = 1 / \<ge> 2\<close> ---
  stated over the ROOT poly \<open>P\<close> on the NORMALIZED node view. The concrete face the loop branches
  on is @{const carried_descartes_count} of the node's own carried list, over \<open>rp\<close> on the
  ABSOLUTE dyadic interval, and these lemmas identify the two.
  @{thm [source] hybrid_count_bridge} and @{thm [source] hybrid_count_bridge_dispatch} both
  TAKE @{const carried_repr_scalar} as a hypothesis, and the one site that establishes it
  (@{thm [source] carried_count_subinterval_mono}, via
  @{thm [source] window_child_formula_repr_scalar}) delivers the ABSOLUTE side.

  \<^bold>\<open>Why bail does not need this\<close>: bail carries the repr relation per node as an invariant conjunct
  (\<open>newton_gmp_node_inv\<close> in \<open>Bail_Loop_Refine.thy\<close>), because its
  node polys are truncated and not recomputable from the root. Hybrid's are: every node list is
  \<open>carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp\<close>, a function of the node
  coordinates and \<open>rp\<close> alone. So here the relation is a THEOREM, not an invariant obligation.\<close>

text \<open>\<^bold>\<open>Step 1: the local-poly composition\<close>, lifted out of the \<open>compose\<close> block inside
  @{thm [source] carried_repr_scalar_compose} (\<open>Newton_Spec.thy\<close>), which proves exactly this
  internally. Stating it separately is what lets the count argument run WITHOUT
  exhibiting a third list: \<open>compose\<close> itself is not invertible, so it cannot deliver the middle
  \<open>carried_repr_scalar Q0 u v X\<close> from the two absolute-interval facts we actually have.\<close>
lemma hybrid_local_poly_window:
  fixes c :: rat
  assumes Qrat: "map rat_of_int Q = smult_list c (local_poly_rat a b P)"
  shows "local_poly_rat u v Q
       = smult_list c (local_poly_rat (a + u * (b - a)) (a + v * (b - a)) P)"
proof -
  have "local_poly_rat u v Q
      = scale_poly_list (v - u) (taylor_shift_list u (smult_list c (local_poly_rat a b P)))"
    unfolding local_poly_rat_def Qrat by simp
  also have "\<dots> = smult_list c
                    (scale_poly_list (v - u) (taylor_shift_list u (local_poly_rat a b P)))"
    by (simp add: taylor_shift_list_smult scale_poly_list_smult_list)
  also have "\<dots> = smult_list c (scale_poly_list (v - u)
                     (taylor_shift_list u
                       (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int P)))))"
    by (simp add: local_poly_rat_def)
  also have "\<dots> = smult_list c (scale_poly_list ((b - a) * (v - u))
                     (taylor_shift_list (a + u * (b - a)) (map rat_of_int P)))"
    by (simp add: newton_scale_taylor_compose)
  also have "\<dots> = smult_list c (local_poly_rat (a + u * (b - a)) (a + v * (b - a)) P)"
    unfolding local_poly_rat_def by (simp add: algebra_simps)
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>Step 2: the count of a WINDOW of a scalar-repr node\<close>, in \<open>descartes_list_int\<close> form on
  both sides. This is the \<open>\<not>\<close>-inverse of @{thm [source] carried_repr_scalar_compose}: it says the
  abstract count taken on \<open>[u,v]\<close> of the REPRESENTATIVE equals the abstract count on the composed
  window of the REPRESENTED poly, with no third list in sight.\<close>
lemma hybrid_descartes_window:
  assumes repr: "carried_repr_scalar P a b Q"
    and lenP: "0 < length P"
    and ab: "a \<noteq> b" and uv: "u \<noteq> v"
  shows "descartes_list_int u v Q
       = descartes_list_int (a + u * (b - a)) (a + v * (b - a)) P"
proof -
  from repr obtain c where cpos: "0 < c"
    and Qeq: "map rat_of_int (rev Q) = smult_list c (rev (local_poly_rat a b P))"
    unfolding carried_repr_scalar_def by blast
  have Qrat: "map rat_of_int Q = smult_list c (local_poly_rat a b P)"
  proof -
    have "map rat_of_int Q = rev (map rat_of_int (rev Q))" by (simp add: rev_map)
    also have "\<dots> = rev (smult_list c (rev (local_poly_rat a b P)))" using Qeq by simp
    also have "\<dots> = smult_list c (local_poly_rat a b P)" by (simp add: rev_smult_list)
    finally show ?thesis .
  qed
  have lenQ: "0 < length Q"
  proof -
    have "length Q = length (map rat_of_int Q)" by simp
    also have "\<dots> = length (local_poly_rat a b P)" using Qrat by (simp add: local_poly_rat_def)
    also have "\<dots> = length P" by (simp add: local_poly_rat_def)
    finally show ?thesis using lenP by simp
  qed
  \<comment> \<open>the composed endpoints stay distinct: a named \<open>rule\<close>, not \<open>field_simps\<close> -- \<open>b - a\<close> is a
     variable and this leaf's ambient simpset fires conditional division rules against it.\<close>
  have uv': "a + u * (b - a) \<noteq> a + v * (b - a)"
  proof
    assume "a + u * (b - a) = a + v * (b - a)"
    hence "(u - v) * (b - a) = 0" by (simp add: algebra_simps)
    thus False using ab uv by simp
  qed
  have "descartes_list_int u v Q
      = sign_changes_fold (taylor_shift_list (1::rat) (rev (local_poly_rat u v Q)))"
    by (rule descartes_list_int_via_local[OF lenQ uv])
  also have "\<dots> = sign_changes_fold (taylor_shift_list (1::rat)
                    (rev (smult_list c
                       (local_poly_rat (a + u * (b - a)) (a + v * (b - a)) P))))"
    by (simp only: hybrid_local_poly_window[OF Qrat])
  also have "\<dots> = sign_changes_fold (smult_list c (taylor_shift_list (1::rat)
                    (rev (local_poly_rat (a + u * (b - a)) (a + v * (b - a)) P))))"
    by (simp add: rev_smult_list taylor_shift_list_smult)
  also have "\<dots> = sign_changes_fold (taylor_shift_list (1::rat)
                    (rev (local_poly_rat (a + u * (b - a)) (a + v * (b - a)) P)))"
    by (simp add: sign_changes_fold_smult_list_pos cpos)
  also have "\<dots> = descartes_list_int (a + u * (b - a)) (a + v * (b - a)) P"
    by (rule descartes_list_int_via_local[OF lenP uv', symmetric])
  finally show ?thesis .
qed

text \<open>\<^bold>\<open>Step 3: the node view's endpoints in ABSOLUTE coordinates\<close> -- the \<open>ea\<close>/\<open>eb\<close> pair already
  inlined inside @{thm [source] hybrid_node_mid_abs}, hoisted so the count bridge can use it.
  Recovering the endpoints by multiplying out (rather than dividing) is deliberate: no division
  by a variable survives into the arithmetic.\<close>
lemma hybrid_node_iv_endpoints_abs:
  assumes lr0: "l0 < r0"
    and abv: "(a, b) = dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)"
  shows "dyadic_rat l0 k0 + (dyadic_rat r0 k0 - dyadic_rat l0 k0) * a = dyadic_rat l k"
    and "dyadic_rat l0 k0 + (dyadic_rat r0 k0 - dyadic_rat l0 k0) * b = dyadic_rat r k"
proof -
  have lo_lt: "dyadic_rat l0 k0 < dyadic_rat r0 k0"
    using lr0 by (simp add: dyadic_rat_def divide_strict_right_mono)
  hence hne: "dyadic_rat r0 k0 - dyadic_rat l0 k0 \<noteq> 0" by simp
  have aval: "a = (dyadic_rat l k - dyadic_rat l0 k0) / (dyadic_rat r0 k0 - dyadic_rat l0 k0)"
    and bval: "b = (dyadic_rat r k - dyadic_rat l0 k0) / (dyadic_rat r0 k0 - dyadic_rat l0 k0)"
    using abv by (simp_all add: dyadic_iv_node_iv_of_def dyadic_iv_node_iv_def Let_def)
  show "dyadic_rat l0 k0 + (dyadic_rat r0 k0 - dyadic_rat l0 k0) * a = dyadic_rat l k"
    unfolding aval using hne by simp
  show "dyadic_rat l0 k0 + (dyadic_rat r0 k0 - dyadic_rat l0 k0) * b = dyadic_rat r k"
    unfolding bval using hne by simp
qed

text \<open>\<^bold>\<open>The concrete non-degeneracy, read back off the view.\<close>
  @{const hybrid_cap_invar} states its non-degeneracy on the node's normalised view, but
  @{thm [source] hybrid_split_child_count_mono}, and hence the payload bound's preservation on the split
  arm, needs it on the column values. The transport is
  @{thm [source] hybrid_node_iv_endpoints_abs}: the view map is affine with positive slope
  \<open>hi - lo\<close>, so \<open>a < b\<close> forces \<open>dyadic_rat l k < dyadic_rat r k\<close> and the common denominator
  cancels.\<close>
lemma hybrid_node_lr_of_view:
  assumes lr0: "l0 < r0"
    and abv: "(a, b) = dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)"
    and ab: "a < b"
  shows "l < r"
proof -
  have lo_lt: "dyadic_rat l0 k0 < dyadic_rat r0 k0"
    using lr0 by (simp add: dyadic_rat_def divide_strict_right_mono)
  have ea: "dyadic_rat l0 k0 + (dyadic_rat r0 k0 - dyadic_rat l0 k0) * a = dyadic_rat l k"
    and eb: "dyadic_rat l0 k0 + (dyadic_rat r0 k0 - dyadic_rat l0 k0) * b = dyadic_rat r k"
    using hybrid_node_iv_endpoints_abs[OF lr0 abv] by simp_all
  have slope: "0 < dyadic_rat r0 k0 - dyadic_rat l0 k0" using lo_lt by simp
  have lt: "dyadic_rat l k < dyadic_rat r k"
    using mult_strict_left_mono[OF ab slope] ea eb by simp
  \<comment> \<open>the last step CONTRAPOSITIVELY: \<open>divide_strict_right_mono\<close> proves the division
     inequality, it does not cancel one, and a \<open>simp\<close> on a variable-power denominator depends on
     the ambient simpset.\<close>
  show ?thesis
  proof (rule ccontr)
    assume "\<not> l < r"
    hence "dyadic_rat r k \<le> dyadic_rat l k"
      unfolding dyadic_rat_def by (simp add: divide_right_mono)
    with lt show False by simp
  qed
qed

text \<open>\<^bold>\<open>The bridge itself.\<close> Concrete node count \<open>=\<close> abstract root count on the node's view.
  Both sides are transported to \<open>rp\<close> on the ABSOLUTE interval, which is the one place both
  @{thm [source] window_child_formula_repr_scalar} instances live.\<close>
lemma hybrid_node_count_bridge:
  assumes lr0: "l0 < r0"
    and Pl_eq: "Pl = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and rp_len: "0 < length rp"
    and abv: "(a, b) = dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)"
    and view_ne: "a \<noteq> b"
  shows "carried_descartes_count (carried_init_same_den l (2 ^ k) r rp)
       = descartes_list_int a b Pl"
proof -
  have d0: "(0::int) < 2 ^ k0" and dk: "(0::int) < 2 ^ k" by simp_all
  have wcf0: "carried_init_same_den l0 (2 ^ k0) r0 rp = window_child_formula l0 (2 ^ k0) r0 rp"
    and wcfk: "carried_init_same_den l (2 ^ k) r rp = window_child_formula l (2 ^ k) r rp"
    by (simp_all add: carried_init_same_den_def window_child_formula_def)
  \<comment> \<open>@{thm [source] dyadic_rat_div} is oriented \<open>dyadic_rat x k = rat_of_int x / 2 ^ k\<close>, which is
     the direction the goal needs: the \<open>of_int (2 ^ kk)\<close> denominator
     @{thm [source] window_child_formula_repr_scalar} produces is already collapsed to
     \<open>2 ^ kk :: rat\<close> by the time it arrives.\<close>
  have repr0: "carried_repr_scalar rp (dyadic_rat l0 k0) (dyadic_rat r0 k0) Pl"
    unfolding Pl_eq wcf0
    using window_child_formula_repr_scalar[OF d0, of rp l0 r0] by (simp add: dyadic_rat_div)
  have reprk: "carried_repr_scalar rp (dyadic_rat l k) (dyadic_rat r k)
                 (carried_init_same_den l (2 ^ k) r rp)"
    unfolding wcfk
    using window_child_formula_repr_scalar[OF dk, of rp l r] by (simp add: dyadic_rat_div)
  have root_ne: "dyadic_rat l0 k0 \<noteq> dyadic_rat r0 k0"
    using lr0 by (simp add: dyadic_rat_def divide_strict_right_mono)
  note ends = hybrid_node_iv_endpoints_abs[OF lr0 abv]
  \<comment> \<open>\<open>node_ne\<close> is DERIVED, not assumed: the endpoint transport is an affine bijection with
     nonzero slope, so a non-degenerate node VIEW forces a non-degenerate node INTERVAL. Taking
     it as a premise would push an extra obligation onto all four assembly sites for nothing.\<close>
  have node_ne: "dyadic_rat l k \<noteq> dyadic_rat r k"
  proof
    assume eq: "dyadic_rat l k = dyadic_rat r k"
    have "(dyadic_rat r0 k0 - dyadic_rat l0 k0) * (a - b) = 0"
      using ends eq by (simp add: algebra_simps)
    thus False using view_ne root_ne by simp
  qed
  have "descartes_list_int a b Pl
      = descartes_list_int (dyadic_rat l0 k0 + a * (dyadic_rat r0 k0 - dyadic_rat l0 k0))
                           (dyadic_rat l0 k0 + b * (dyadic_rat r0 k0 - dyadic_rat l0 k0)) rp"
    by (rule hybrid_descartes_window[OF repr0 rp_len root_ne view_ne])
  also have "\<dots> = descartes_list_int (dyadic_rat l k) (dyadic_rat r k) rp"
    using ends by (simp add: mult.commute)
  also have "\<dots> = carried_descartes_count (carried_init_same_den l (2 ^ k) r rp)"
    by (rule hybrid_count_bridge[OF reprk rp_len node_ne, symmetric])
  finally show ?thesis by (rule sym)
qed

text \<open>\<^bold>\<open>The split arm's right half is root-free when the decide fires\<close>: the \<open>zeroR\<close>
  premise of @{thm [source] hybrid_body_step_split}, in the form its assembly discharges. The
  exact right child is the right half's node polynomial (@{thm [source]
  carried_left_right_reconstruct}), and the node bridge turns its count into the abstract one.\<close>
lemma hybrid_split_right_zero:
  assumes lr0: "l0 < r0"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and rp_len: "0 < length rp"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and abnode: "dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks) = (a, b)"
    and ab: "a < b"
    and rz0: "carried_descartes_count (carried_right X) = 0"
  shows "descartes_list_int ((a + b) / 2) b (coeffs P) = 0"
proof -
  have recR: "carried_right X
      = carried_init_same_den (last lns + last rns) (2 ^ (last ks + 1)) (2 * last rns) rp"
    unfolding X_eq mult_2 by (rule carried_left_right_reconstruct(2))
  have midlt: "(a + b) / 2 < b" using ab by (simp add: field_simps)
  have abv: "((a + b) / 2, b)
             = dyadic_iv_node_iv_of l0 r0 k0 ((last lns + last rns, 2 * last rns), Suc (last ks))"
    by (simp add: hybrid_node_iv_split_children(2)[OF lr0] abnode)
  have "carried_descartes_count
          (carried_init_same_den (last lns + last rns) (2 ^ Suc (last ks)) (2 * last rns) rp)
        = descartes_list_int ((a + b) / 2) b (coeffs P)"
    by (rule hybrid_node_count_bridge[OF lr0 Pcoeffs rp_len abv less_imp_neq[OF midlt]])
  thus ?thesis using rz0 recR by simp
qed

text \<open>\<^bold>\<open>The dispatch form the four arms cite\<close>: the classify trichotomy \<open>0 / 1 / \<ge> 2\<close>,
  matching @{thm [source] hybrid_count_bridge_dispatch}'s shape. Here the
  underlying bridge is an exact equality, so each face is one rewrite; stating them keeps
  the call sites free of an \<open>unfolding\<close> step and keeps the trichotomy the only spelling of an arm
  condition.\<close>
lemma hybrid_node_count_dispatch:
  assumes lr0: "l0 < r0"
    and Pl_eq: "Pl = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and rp_len: "0 < length rp"
    and abv: "(a, b) = dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)"
    and view_ne: "a \<noteq> b"
  shows "(carried_descartes_count (carried_init_same_den l (2 ^ k) r rp) = 0)
           = (descartes_list_int a b Pl = 0)"
    and "(carried_descartes_count (carried_init_same_den l (2 ^ k) r rp) = 1)
           = (descartes_list_int a b Pl = 1)"
    and "(2 \<le> carried_descartes_count (carried_init_same_den l (2 ^ k) r rp))
           = (2 \<le> descartes_list_int a b Pl)"
  using hybrid_node_count_bridge[OF lr0 Pl_eq rp_len abv view_ne] by simp_all


text \<open>\<^bold>\<open>The middle representation: the node polynomial represents the root-frame polynomial on the node view.\<close>
  This is the per-node conjunct bail carries as an invariant (\<open>newton_gmp_node_inv\<close>) and hybrid
  does not, and it is what @{thm [source] newton_window_pick_bail_abs} demands before it
  gives the window characterisation. @{thm [source] carried_repr_scalar_compose} is not
  invertible, so it cannot deliver it; instead the two absolute-interval scalars are divided. Both \<open>Pl\<close> and the node
  list are \<open>window_child_formula\<close> images of \<open>rp\<close>, so each carries its own positive scalar against
  \<open>local_poly_rat\<close> of \<open>rp\<close>; @{thm [source] hybrid_local_poly_window} moves \<open>Pl\<close>'s onto the node
  view window, the endpoint transport identifies that window with the node's own absolute interval,
  and the quotient \<open>ck / c0\<close> is the scalar the definition asks for.

  This generalises @{thm [source] hybrid_node_count_bridge}: that lemma is the
  count face of this one (compose with @{thm [source] hybrid_count_bridge}).\<close>
lemma hybrid_node_repr_scalar:
  assumes lr0: "l0 < r0"
    and Pl_eq: "Pl = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and abv: "(a, b) = dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)"
  shows "carried_repr_scalar Pl a b (carried_init_same_den l (2 ^ k) r rp)"
proof -
  have d0: "(0::int) < 2 ^ k0" and dk: "(0::int) < 2 ^ k" by simp_all
  have wcf0: "carried_init_same_den l0 (2 ^ k0) r0 rp = window_child_formula l0 (2 ^ k0) r0 rp"
    and wcfk: "carried_init_same_den l (2 ^ k) r rp = window_child_formula l (2 ^ k) r rp"
    by (simp_all add: carried_init_same_den_def window_child_formula_def)
  have repr0: "carried_repr_scalar rp (dyadic_rat l0 k0) (dyadic_rat r0 k0) Pl"
    unfolding Pl_eq wcf0
    using window_child_formula_repr_scalar[OF d0, of rp l0 r0] by (simp add: dyadic_rat_div)
  have reprk: "carried_repr_scalar rp (dyadic_rat l k) (dyadic_rat r k)
                 (carried_init_same_den l (2 ^ k) r rp)"
    unfolding wcfk
    using window_child_formula_repr_scalar[OF dk, of rp l r] by (simp add: dyadic_rat_div)
  from repr0 obtain c0 where c0pos: "0 < c0"
    and P0eq: "map rat_of_int (rev Pl)
             = smult_list c0 (rev (local_poly_rat (dyadic_rat l0 k0) (dyadic_rat r0 k0) rp))"
    unfolding carried_repr_scalar_def by blast
  from reprk obtain ck where ckpos: "0 < ck"
    and Xeq: "map rat_of_int (rev (carried_init_same_den l (2 ^ k) r rp))
            = smult_list ck (rev (local_poly_rat (dyadic_rat l k) (dyadic_rat r k) rp))"
    unfolding carried_repr_scalar_def by blast
  \<comment> \<open>un-\<open>rev\<close> \<open>Pl\<close>'s scalar equation, exactly as @{thm [source] hybrid_descartes_window} does,
     because @{thm [source] hybrid_local_poly_window} is stated on the un-reversed list.\<close>
  have Pl_rat: "map rat_of_int Pl
              = smult_list c0 (local_poly_rat (dyadic_rat l0 k0) (dyadic_rat r0 k0) rp)"
  proof -
    have "map rat_of_int Pl = rev (map rat_of_int (rev Pl))" by (simp add: rev_map)
    also have "\<dots> = rev (smult_list c0
                      (rev (local_poly_rat (dyadic_rat l0 k0) (dyadic_rat r0 k0) rp)))"
      using P0eq by simp
    also have "\<dots> = smult_list c0 (local_poly_rat (dyadic_rat l0 k0) (dyadic_rat r0 k0) rp)"
      by (simp add: rev_smult_list)
    finally show ?thesis .
  qed
  note ends = hybrid_node_iv_endpoints_abs[OF lr0 abv]
  have view_win: "local_poly_rat a b Pl
                = smult_list c0 (local_poly_rat (dyadic_rat l k) (dyadic_rat r k) rp)"
  proof -
    have "local_poly_rat a b Pl
        = smult_list c0 (local_poly_rat
              (dyadic_rat l0 k0 + a * (dyadic_rat r0 k0 - dyadic_rat l0 k0))
              (dyadic_rat l0 k0 + b * (dyadic_rat r0 k0 - dyadic_rat l0 k0)) rp)"
      by (rule hybrid_local_poly_window[OF Pl_rat])
    also have "\<dots> = smult_list c0 (local_poly_rat (dyadic_rat l k) (dyadic_rat r k) rp)"
      using ends by (simp add: mult.commute)
    finally show ?thesis .
  qed
  have quot: "map rat_of_int (rev (carried_init_same_den l (2 ^ k) r rp))
            = smult_list (ck / c0) (rev (local_poly_rat a b Pl))"
  proof -
    have "smult_list (ck / c0) (rev (local_poly_rat a b Pl))
        = smult_list (ck / c0) (smult_list c0
             (rev (local_poly_rat (dyadic_rat l k) (dyadic_rat r k) rp)))"
      using view_win by (simp add: rev_smult_list)
    also have "\<dots> = smult_list (ck / c0 * c0)
                      (rev (local_poly_rat (dyadic_rat l k) (dyadic_rat r k) rp))"
      by (simp add: smult_list_smult_list)
    also have "\<dots> = smult_list ck (rev (local_poly_rat (dyadic_rat l k) (dyadic_rat r k) rp))"
      using c0pos by simp
    finally show ?thesis using Xeq by simp
  qed
  have cpos: "0 < ck / c0" using ckpos c0pos by simp
  show ?thesis unfolding carried_repr_scalar_def using cpos quot by blast
qed


text \<open>\<^bold>\<open>\<open>win\<close> at the node\<close>: the concrete window pick projects onto
  @{const try_window_bail_int} on the node view. This is the window arm's \<open>win\<close> premise, and it
  is @{thm [source] newton_window_pick_bail_abs} instantiated through
  @{thm [source] hybrid_node_repr_scalar}: the representation was the only thing bail's lemma needs that
  the hybrid development did not already have.

  \<^bold>\<open>The window is a function of the pick index\<close>, and the function is forced: it is the node view
  of @{const newton_window_child}, i.e. verbatim the columns the arm pushes
  (\<open>l * 2\<^sup>2\<^sup>^\<^sup>e\<^sup>+\<^sup>2 + m * (r - l)\<close>, width \<open>4\<close>, depth \<open>k + 2\<^sup>e + 2\<close>). So the same \<open>Iw\<close> serves \<open>win\<close> and
  \<open>npush_w\<close>/\<open>vpush_w\<close>, which is what the \<open>\<And>m\<close> forms need.

  \<^bold>\<open>Stated at the actual count\<close>, not \<open>\<And>v\<close>: bail's projection holds for the \<open>v\<close> the pick was made
  with, and the abstract side is the count on the node view, so the two agree only at
  \<open>v = \<close>@{const carried_descartes_count}\<open> X\<close> (@{thm [source] hybrid_node_count_bridge}). A \<open>\<And>v\<close>
  form with a \<open>v\<close>-free right-hand side would be unsatisfiable, not stronger.\<close>
lemma hybrid_window_pick_abs_node:
  fixes P :: "int poly"
  assumes lr0: "l0 < r0"
    and Pl_eq: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and rp2: "Suc 0 < length rp"
    and abv: "(a, b) = dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k)"
    and ab: "a < b"
    and X_eq: "X = carried_init_same_den l (2 ^ k) r rp"
    and pk: "newton_window_pick_bail (carried_descartes_count X) e X = Some (m, cand)"
  shows "try_window_bail_int True a b (N_of e) P
           (descartes_list_int a b (coeffs P))
       = Some (dyadic_iv_node_iv_of l0 r0 k0
                 ((l * 2 ^ (2 ^ e + 2) + m * (r - l),
                   l * 2 ^ (2 ^ e + 2) + (m + 4) * (r - l)), k + (2 ^ e + 2)))"
proof -
  have rp_len: "0 < length rp" using rp2 by simp
  have Pl_len: "Suc 0 < length (coeffs P)"
    using rp2 by (simp add: Pl_eq truncate_length_carried_init_same_den)
  have canon: "coeffs (Poly (coeffs P)) = coeffs P" by simp
  have repr: "carried_repr_scalar (coeffs P) a b X"
    unfolding X_eq by (rule hybrid_node_repr_scalar[OF lr0 Pl_eq abv])
  have nodeiv: "dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k) = dyadic_iv_node_iv l0 r0 k0 l r k"
    by (simp add: dyadic_iv_node_iv_of_def)
  have av: "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)"
    and bv: "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
    using abv nodeiv by (metis fst_conv, metis snd_conv)
  have count: "descartes_list_int a b (coeffs P) = carried_descartes_count X"
    using hybrid_node_count_bridge[OF lr0 Pl_eq rp_len abv] ab X_eq by simp
  note abs = newton_window_pick_bail_abs[OF repr Pl_len ab lr0 canon av bv,
                where v = "carried_descartes_count X" and e = e]
  show ?thesis
    using abs pk
    \<comment> \<open>the residual after the \<open>OF\<close> is purely the \<open>_of\<close>/uncurried spelling of the CHILD's node
       view: \<open>nodeiv\<close> covers the popped node only, so the child's needs the definition itself.\<close>
    by (simp add: count newton_window_child_def Let_def dyadic_iv_node_iv_of_def)
qed


text \<open>\<^bold>\<open>The window's geometry\<close>: \<open>wsub\<close>, \<open>wprop\<close> and \<open>mu_w\<close>, all three from the single
  \<open>win\<close> fact. @{const try_window_bail_int} is the rational face of
  @{const try_window_bail}, and the real face already carries every property the invariant step
  wants: @{thm [source] try_window_bail_SomeD} (containment and the exact width quotient),
  @{thm [source] try_window_bail_Some_fst_lt_snd} (non-degeneracy) and
  @{thm [source] try_window_bail_Some_width_lt} (strictness). The \<open>\<mu>\<close> drop is then
  @{thm [source] mu_subinterval_factor_strict}, whose \<open>b' - a' = (b - a) / N\<close> premise is exactly
  @{thm [source] try_window_bail_SomeD}(3).

  \<^bold>\<open>Strictness comes from \<open>width_lt\<close>, not from dividing\<close>: \<open>(b - a) / N < b - a\<close> is true but the
  goal divides by \<open>real (N_of e)\<close>, and the ambient simpset fires conditional division
  rules against it. The named width lemma sidesteps that.\<close>
lemma hybrid_window_geometry_node:
  fixes P :: "int poly" and I :: "rat \<times> rat"
  assumes dpos: "0 < \<delta>"
    and ab: "a < b"
    and wide: "\<delta> < real_of_rat b - real_of_rat a"
    and P0: "P \<noteq> 0"
    and win: "try_window_bail_int gn a b (N_of e) P v = Some I"
  shows "alr_ivl_pss (fst I, snd I) (a, b)"
    and "fst I < snd I"
    and "dyadic_iv_interval_mu \<delta> I < dyadic_iv_interval_mu \<delta> (a, b)"
proof -
  have Npos: "0 < N_of e" using N_of_ge_2[of e] by simp
  have abr: "real_of_rat a < real_of_rat b" using ab by (simp add: of_rat_less)
  note real_win = try_window_bail_int_Some[OF ab P0 Npos refl win]
  have sub1: "real_of_rat a \<le> real_of_rat (fst I)"
    using try_window_bail_SomeD(1)[OF real_win abr Npos] by simp
  have sub2: "real_of_rat (snd I) \<le> real_of_rat b"
    using try_window_bail_SomeD(2)[OF real_win abr Npos] by simp
  have lt: "real_of_rat (fst I) < real_of_rat (snd I)"
    using try_window_bail_Some_fst_lt_snd[OF real_win abr Npos] by simp
  have wid: "real_of_rat (snd I) - real_of_rat (fst I)
           = (real_of_rat b - real_of_rat a) / real (N_of e)"
    using try_window_bail_SomeD(3)[OF real_win abr Npos] by simp
  have widlt: "real_of_rat (snd I) - real_of_rat (fst I) < real_of_rat b - real_of_rat a"
    using try_window_bail_Some_width_lt[OF real_win abr] by simp
  show "fst I < snd I" using lt by (simp add: of_rat_less)
  show "dyadic_iv_interval_mu \<delta> I < dyadic_iv_interval_mu \<delta> (a, b)"
    unfolding dyadic_iv_interval_mu_def
    using mu_subinterval_factor_strict[OF dpos abr wide N_of_ge_2 wid] by simp
  show "alr_ivl_pss (fst I, snd I) (a, b)"
  proof -
    have s1: "a \<le> fst I" using sub1 by (simp add: of_rat_less_eq)
    have s2: "snd I \<le> b" using sub2 by (simp add: of_rat_less_eq)
    have wne: "(fst I, snd I) \<noteq> (a, b)"
    proof
      assume "(fst I, snd I) = (a, b)"
      hence "fst I = a" and "snd I = b" by simp_all
      thus False using widlt by simp
    qed
    show ?thesis using s1 s2 wne by (simp add: alr_ivl_pss_def alr_ivl_subset_def)
  qed
qed


text \<open>\<^bold>\<open>The POPPED NODE's own facts, extracted once.\<close> All four assemblies want
  \<open>cache\<close>, \<open>locked_exact\<close> and the node frame at the LAST index; the couplings state them
  \<open>\<forall>i < length qtodo\<close>. This is that projection, done once instead of four times.

  \<open>last_conv_nth\<close> is the bridge: the couplings are indexed, \<open>step_pre\<close> and the arms speak of
  \<open>last\<close>.\<close>
lemma hybrid_node_facts_last:
  assumes inv: "hybrid_refine_invar P l0 r0 k0 seed (lns, rns, ks) qtodo es ss cs gs rp acc"
    and lne: "lns \<noteq> []"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
  shows "hybrid_cs_ok (last gs) (last cs) (carried_descartes_count X)"
    and "4398046511104 \<le> last gs \<longrightarrow> last qtodo = X"
    and "node_frame X (last qtodo) (last gs)"
    and "last gs \<le> (last ks + 1) * length rp \<or> 4398046511104 \<le> last gs"
proof -
  have tc: "hybrid_trunc_coupling (lns, rns, ks) qtodo gs rp"
    and cc: "hybrid_cs_coupling (lns, rns, ks) qtodo cs gs rp"
    using inv unfolding hybrid_refine_invar_def by simp_all
  have LEN: "length lns = length qtodo" "length rns = length qtodo"
     "length ks = length qtodo" "length gs = length qtodo"
    using tc unfolding hybrid_trunc_coupling_def by simp_all
  have LC: "length cs = length qtodo"
    using cc unfolding hybrid_cs_coupling_def by simp
  have qne: "qtodo \<noteq> []" using lne LEN(1) by auto
  have ne: "rns \<noteq> []" "ks \<noteq> []" "gs \<noteq> []" "cs \<noteq> []"
    using qne LEN LC by auto
  have i: "length qtodo - 1 < length qtodo" using qne by simp
  \<comment> \<open>every \<open>last\<close> as the same index, so one instantiation serves all four conclusions.\<close>
  have nth: "lns ! (length qtodo - 1) = last lns" "rns ! (length qtodo - 1) = last rns"
     "ks ! (length qtodo - 1) = last ks" "gs ! (length qtodo - 1) = last gs"
     "cs ! (length qtodo - 1) = last cs" "qtodo ! (length qtodo - 1) = last qtodo"
    using lne qne ne LEN LC by (simp_all add: last_conv_nth)
  have T: "node_frame (carried_init_same_den (lns ! (length qtodo - 1))
                         (2 ^ (ks ! (length qtodo - 1))) (rns ! (length qtodo - 1)) rp)
                      (qtodo ! (length qtodo - 1)) (gs ! (length qtodo - 1))
         \<and> (gs ! (length qtodo - 1)
              \<le> (ks ! (length qtodo - 1) + 1) * length rp
            \<or> 4398046511104 \<le> gs ! (length qtodo - 1))
         \<and> (4398046511104 \<le> gs ! (length qtodo - 1) \<longrightarrow>
              qtodo ! (length qtodo - 1)
                = carried_init_same_den (lns ! (length qtodo - 1))
                    (2 ^ (ks ! (length qtodo - 1))) (rns ! (length qtodo - 1)) rp)"
    using tc i unfolding hybrid_trunc_coupling_def by simp
  have C: "hybrid_cs_ok (gs ! (length qtodo - 1)) (cs ! (length qtodo - 1))
             (carried_descartes_count
                (carried_init_same_den (lns ! (length qtodo - 1))
                   (2 ^ (ks ! (length qtodo - 1))) (rns ! (length qtodo - 1)) rp))"
    using cc i unfolding hybrid_cs_coupling_def by simp
  show "hybrid_cs_ok (last gs) (last cs) (carried_descartes_count X)"
    using C unfolding nth X_eq .
  show "4398046511104 \<le> last gs \<longrightarrow> last qtodo = X"
    using T unfolding nth X_eq by simp
  show "node_frame X (last qtodo) (last gs)"
    using T unfolding nth X_eq by simp
  show "last gs \<le> (last ks + 1) * length rp \<or> 4398046511104 \<le> last gs"
    using T unfolding nth by simp
qed


section \<open>The arm assemblies -- every premise derived at an arbitrary loop state\<close>

text \<open>\<^bold>\<open>The discard arm, assembled.\<close> This is the shape @{thm [source] hybrid_loop_expol}'s
  \<open>step\<close> hypothesis needs, for the \<open>v = 0\<close> arm: from the loop invariants and the arm selection
  alone, with no premise mentioning an op output.

  \<^bold>\<open>Almost everything comes from @{const hybrid_loop_step_pre}\<close>, which the safety invariant
  carries under the loop condition: the column non-emptiness, both pushables, all five
  \<open>butlast\<close> caps, and the popped node's own \<open>k\<close>/\<open>\<sigma>\<close>/\<open>length\<close> bounds. The \<open>X\<close>-bounds are the
  root's, since @{const carried_init_same_den} preserves length; \<open>ab\<close> is the non-degeneracy
  conjunct of @{const hybrid_cap_invar}; \<open>safe'\<close> is
  @{thm [source] hybrid_loop_safe_invar_pop_all}; and \<open>nsplit\<close>/\<open>vsplit\<close> are the pop
  decomposition, which is what fixes \<open>(a, b, e, dk, s)\<close> to the popped node's own view.

  \<open>zero\<close> and \<open>count0\<close> are the two faces of the arm selection -- abstract and concrete -- and
  @{thm [source] hybrid_count_bridge} is what identifies them at the assembly site.\<close>
lemma hybrid_body_step_discard_assembled:
  assumes safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp acc"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) acc"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and count0: "carried_descartes_count X = 0"
    and zero: "descartes_list_int (fst (dyadic_iv_node_iv_of l0 r0 k0
                                          ((last lns, last rns), last ks)))
                                 (snd (dyadic_iv_node_iv_of l0 r0 k0
                                          ((last lns, last rns), last ks))) (coeffs P) = 0"
    and dpos: "0 < \<delta>"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>the popped node's cache and lock, which the couplings supply at the LAST index -- the
       same projection shape the other per-node facts take, done once at the assembly site.\<close>
    and cache: "hybrid_cs_ok (last gs) (last cs) (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> last gs \<Longrightarrow> last qtodo = X"
    \<comment> \<open>\<^bold>\<open>The payload bound\<close>, threaded exactly as \<open>budinv\<close> is. \<^bold>\<open>Last\<close>.\<close>
    and payinv: "hybrid_pay_invar (lns, rns, ks) gs rp"
    \<comment> \<open>\<^bold>\<open>The root relation\<close>, @{const hybrid_state_invar}'s fifth
       conjunct, \<^bold>\<open>last\<close>. It is the same proposition at the pushed state as at the popped one
       (no arm touches \<open>P\<close> or \<open>rp\<close>), so it passes straight through; it exists so that
       \<open>hybrid_loop_correct\<close>'s \<open>\<And>s\<close> step can reach \<open>s\<close>'s own \<open>rp\<close>.\<close>
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    \<comment> \<open>the pop's two word bounds (@{thm [source] small_len_b2}). \<^bold>\<open>Last\<close>.\<close>
    and Q_small: "length (last qtodo) < 1099511627776"
  shows "hybrid_loop_body_checked_monadic (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc))"
proof -
  have stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp_all
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have lne: "lns \<noteq> []" using cond by (simp add: hybrid_loop_cond_def)
  have ne: "qtodo \<noteq> []" "es \<noteq> []" "ss \<noteq> []" "cs \<noteq> []" "gs \<noteq> []" "ks \<noteq> []" "rns \<noteq> []"
    using lne SL VL by auto
  \<comment> \<open>\<^bold>\<open>No \<open>simplified\<close>\<close>: it normalises \<open>step_pre\<close>'s conjuncts away from the shapes the arm
     lemma states them in (\<open>0 < length rp\<close> becomes \<open>rp \<noteq> []\<close>, \<open>length rp + 1 <\<close> becomes
     \<open>Suc (length rp) <\<close>), and then nothing matches.\<close>
  note Pu = pre[unfolded hybrid_loop_step_pre_def]
  have CL: "length lns = length ks" "length rns = length ks" "length ss = length ks"
    using VL SL by simp_all
  have cpl: "hybrid_trunc_coupling (lns, rns, ks) qtodo gs rp"
    using inv unfolding hybrid_refine_invar_def by simp
  have lenX: "length X = length rp"
    by (simp add: X_eq truncate_length_carried_init_same_den)
  \<comment> \<open>the popped node's own view -- this is what pins \<open>(a, b, e, dk, s)\<close>.\<close>
  have nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
       = hybrid_alpha_nodes l0 r0 k0
           (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
         @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
             snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
             last es, last ks, last ss)]"
    by (rule hybrid_alpha_nodes_pop_decomp[OF lne VL(1) VL(2) SL(2) SL(3)])
  \<comment> \<open>stated with the pair SPLIT: the body step wants \<open>@ [(a, b)]\<close>, and against a bare node view
     the unifier would have to invent a tuple from \<open>(?a, ?b) \<equiv> X\<close> -- higher-order, and it reports
     \<open>OF: no unifiers\<close>. \<open>simp\<close> collapses the split form back, so the two are the same fact.\<close>
  have vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
       = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
         @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
             snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))]"
    using hybrid_alpha_views_pop_decomp[OF lne VL(1) VL(2)] by simp
  have ilast: "length ks - 1 < length ks" using ne(6) by simp
  have ab: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
            < snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using hybrid_cap_invar_nondeg[OF capinv ilast] lne ne VL
    by (simp add: last_conv_nth)
  have safe': "hybrid_loop_safe_invar
                 (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                   butlast es, butlast ss, butlast cs, butlast gs, rp), acc)"
    by (rule hybrid_loop_safe_invar_pop_all[OF stinv pre cpl capinv dpos _ _ kcap kdepth])
       (use Pu in simp_all)
  have arm: "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs acc rp
       \<le> SPEC (\<lambda>(wl, acc'). acc' = acc \<and>
             wl = ((butlast lns, butlast rns, butlast ks), butlast qtodo,
                   butlast es, butlast ss, butlast cs, butlast gs, rp))"
    by (rule hybrid_loop_step_args_discard[OF tinv lne VL(1) VL(2) ne(1) ne(2) ne(3) ne(4) ne(5)
              _ _ _ _ X_pbound X_gbound X_eq cache locked_exact count0])
    \<comment> \<open>\<^bold>\<open>\<open>insert\<close>, not a chained \<open>use\<close>\<close> -- this file's own arm lemmas say it: bounds go in by
       \<open>insert\<close>, which puts the conjunction into EVERY goal where \<open>simp\<close> splits it. Chained, the
       conjunction is not mined and exactly the column caps are left open.\<close>
       (insert Pu lenX lne ne Q_small, simp_all)
  \<comment> \<open>the payload bound: pop only, so @{thm [source] hybrid_pay_invar_pop} on the invariant's
     own conjunct.\<close>
  have paypop: "hybrid_pay_invar (butlast lns, butlast rns, butlast ks) (butlast gs) rp"
    by (rule hybrid_pay_invar_pop[OF payinv]) (use SL VL in simp_all)
  show ?thesis
    \<comment> \<open>premise ORDER matters and is not the reading order: \<open>capinv\<close>/\<open>clr\<close>/\<open>crr\<close>/\<open>csk\<close> sit
       AFTER \<open>safe'\<close>, where the k-potential block was inserted.\<close>
    by (rule hybrid_body_step_discard[OF stinv pre cond inv nsplit vsplit ab zero safe'
              capinv budinv CL(1) CL(2) CL(3) arm paypop Pcoeffs])
qed

text \<open>\<^bold>\<open>The DEGENERATE midpoint's node view.\<close> The split and window arms push the
  bisection midpoint into the ACCUMULATOR as the degenerate column entry \<open>(l + r, l + r, k + 1)\<close>.
  Its node view is the single point \<open>(a + b) / 2\<close>, and that is the last fact \<open>accgrow\<close> needs on
  those two arms -- \<open>dyadic_iv_acc_ivs_append1\<close> (below) supplies the append, this supplies
  the view.

  Same shape and same proof as @{thm [source] hybrid_node_iv_split_children}, of which it is the
  degenerate case: \<open>2 * l\<close> and \<open>2 * r\<close> both replaced by \<open>l + r\<close>, so both endpoints land on the
  midpoint the two children share.\<close>
lemma hybrid_node_iv_split_mid:
  assumes lr: "l0 < r0"
  shows "dyadic_iv_node_iv_of l0 r0 k0 ((l + r, l + r), Suc k)
       = ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))
           + snd (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))) / 2,
          (fst (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))
           + snd (dyadic_iv_node_iv_of l0 r0 k0 ((l, r), k))) / 2)"
proof -
  have lt: "dyadic_rat l0 k0 < dyadic_rat r0 k0"
    using lr by (simp add: dyadic_rat_def divide_strict_right_mono)
  hence hne: "dyadic_rat r0 k0 - dyadic_rat l0 k0 \<noteq> 0" by simp
  have hne2: "dyadic_rat r0 k0 * 2 - dyadic_rat l0 k0 * 2 \<noteq> 0"
    using hne by (simp add: algebra_simps)
  show ?thesis
    unfolding dyadic_iv_node_iv_of_def dyadic_iv_node_iv_def Let_def
    by (simp add: dyadic_rat_double dyadic_rat_double' dyadic_rat_mid hne hne2 field_simps
                  affine_half_sum[OF hne])
qed


text \<open>The accumulator's own append law -- the accept arm's \<open>accgrow\<close> is this plus the popped
  node's view, and nothing else.\<close>
lemma dyadic_iv_acc_ivs_append1:
  assumes lr: "length al = length ar" and rk: "length ar = length ak"
  shows "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al @ [x], ar @ [y], ak @ [p]))
       = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak))
         @ [dyadic_iv_node_iv_of l0 r0 k0 ((x, y), p)]"
  using assms
  by (simp add: dyadic_iv_acc_ivs_def dyadic_interval_vec_triples_def)

text \<open>\<^bold>\<open>The accept arm, assembled.\<close> The discard arm's skeleton, with one addition: the
  accumulator GROWS, so \<open>accgrow\<close> is discharged here from
  @{thm [source] dyadic_iv_acc_ivs_append1} at the popped node's view.

  \<^bold>\<open>\<open>safe'\<close> is a premise on this arm, and it is the one place the acc budget is needed\<close>: at the
  popped state the accumulator has already grown, so \<open>step_pre\<close> wants
  \<open>dyadic_interval_vec_pushable (al @ [last lns], \<dots>)\<close>, which is
  @{thm [source] hybrid_budget_invar_acc_grown} -- available because \<open>hybrid_budget_invar\<close>
  is conjoined into \<open>hybrid_state_invar\<close> and preserved by all four arms.\<close>
lemma hybrid_body_step_accept_assembled:
  assumes safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and count1: "carried_descartes_count X = 1"
    and one: "descartes_list_int (fst (dyadic_iv_node_iv_of l0 r0 k0
                                         ((last lns, last rns), last ks)))
                                (snd (dyadic_iv_node_iv_of l0 r0 k0
                                         ((last lns, last rns), last ks))) (coeffs P) = 1"
    and X_pbound: "length X * nat_bitlen (length X) < max_snat LENGTH(gmp_poly_len)"
    and X_gbound: "4398046511104 + length X < max_snat LENGTH(gmp_poly_len)"
    and cache: "hybrid_cs_ok (last gs) (last cs) (carried_descartes_count X)"
    and locked_exact: "4398046511104 \<le> last gs \<Longrightarrow> last qtodo = X"
    and safe': "hybrid_loop_safe_invar
                  (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                    butlast es, butlast ss, butlast cs, butlast gs, rp),
                   (al @ [last lns], ar @ [last rns], ak @ [last ks]))"
    \<comment> \<open>\<^bold>\<open>The payload bound\<close>, the fourth invariant conjunct, threaded exactly as \<open>budinv\<close> is.\<close>
    and payinv: "hybrid_pay_invar (lns, rns, ks) gs rp"
    \<comment> \<open>\<^bold>\<open>The root relation\<close>, @{const hybrid_state_invar}'s fifth
       conjunct, \<^bold>\<open>last\<close>. It is the same proposition at the pushed state as at the popped one
       (no arm touches \<open>P\<close> or \<open>rp\<close>), so it passes straight through; it exists so that
       \<open>hybrid_loop_correct\<close>'s \<open>\<And>s\<close> step can reach \<open>s\<close>'s own \<open>rp\<close>.\<close>
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    \<comment> \<open>the pop's two word bounds (@{thm [source] small_len_b2}). \<^bold>\<open>Last\<close>.\<close>
    and Q_small: "length (last qtodo) < 1099511627776"
  shows "hybrid_loop_body_checked_monadic
           (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp_all
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and ainv: "dyadic_interval_vec_invar (al, ar, ak)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have AL: "length al = length ar" "length ar = length ak"
    using ainv unfolding dyadic_interval_vec_invar_def by simp_all
  have lne: "lns \<noteq> []" using cond by (simp add: hybrid_loop_cond_def)
  have ne: "qtodo \<noteq> []" "es \<noteq> []" "ss \<noteq> []" "cs \<noteq> []" "gs \<noteq> []" "ks \<noteq> []" "rns \<noteq> []"
    using lne SL VL by auto
  note Pu = pre[unfolded hybrid_loop_step_pre_def]
  have CL: "length lns = length ks" "length rns = length ks" "length ss = length ks"
    using VL SL by simp_all
  have lenX: "length X = length rp"
    by (simp add: X_eq truncate_length_carried_init_same_den)
  have nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
       = hybrid_alpha_nodes l0 r0 k0
           (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
         @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
             snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
             last es, last ks, last ss)]"
    by (rule hybrid_alpha_nodes_pop_decomp[OF lne VL(1) VL(2) SL(2) SL(3)])
  have vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
       = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
         @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
             snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))]"
    using hybrid_alpha_views_pop_decomp[OF lne VL(1) VL(2)] by simp
  have ilast: "length ks - 1 < length ks" using ne(6) by simp
  have ab: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
            < snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using hybrid_cap_invar_nondeg[OF capinv ilast] lne ne VL
    by (simp add: last_conv_nth)
  have accgrow: "dyadic_iv_acc_ivs l0 r0 k0
                   (dyadic_interval_vec_triples (al @ [last lns], ar @ [last rns], ak @ [last ks]))
                 = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak))
                   @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
                       snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))]"
    using dyadic_iv_acc_ivs_append1[OF AL(1) AL(2)] by simp
  have arm: "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
       \<le> SPEC (\<lambda>(wl, acc').
             acc' = (al @ [last lns], ar @ [last rns], ak @ [last ks]) \<and>
             wl = ((butlast lns, butlast rns, butlast ks), butlast qtodo,
                   butlast es, butlast ss, butlast cs, butlast gs, rp))"
    \<comment> \<open>same premise order as the discard arm.\<close>
    by (rule hybrid_loop_step_args_accept[OF tinv lne VL(1) VL(2) ne(1) ne(2) ne(3) ne(4) ne(5)
              _ _ _ _ X_pbound X_gbound X_eq cache locked_exact count1])
       (insert Pu lenX lne ne Q_small, simp_all)
  \<comment> \<open>\<^bold>\<open>The payload bound at the popped state\<close>: the accept arm pushes nothing onto the worklist,
     so this is @{thm [source] hybrid_pay_invar_pop} on the invariant's own conjunct.\<close>
  have paypop: "hybrid_pay_invar (butlast lns, butlast rns, butlast ks) (butlast gs) rp"
    by (rule hybrid_pay_invar_pop[OF payinv]) (use SL VL in simp_all)
  show ?thesis
    by (rule hybrid_body_step_accept[OF cond inv nsplit vsplit ab one accgrow safe'
              capinv budinv CL(1) CL(2) CL(3) arm paypop Pcoeffs])
qed

text \<open>\<^bold>\<open>The split arm, assembled.\<close> The discard arm's skeleton, plus one new
  derivation: \<open>npush\<close>/\<open>vpush\<close>, the two pushed children's \<open>\<alpha>\<close>-images, from
  \<open>hybrid_npush_split_satisfiable\<close> with the geometry supplied by
  @{thm [source] hybrid_node_iv_split_children}.

  \<open>accgrow\<close> and \<open>safe'\<close> are premises of this lemma: \<open>accgrow\<close> needs the degenerate midpoint's
  node view, and \<open>safe'\<close> is \<open>\<And>\<close>-quantified over the pushed columns and over an accumulator that
  has grown on the midpoint-root branch. Both are discharged where the lemma is used (\<open>accgrow\<close> as a local \<open>have\<close>
  at each call site); neither is a premise of \<open>hybrid_main_list_correct\<close>.\<close>
lemma hybrid_body_step_split_assembled:
  fixes pol :: newton_pol
  assumes safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and lr0: "l0 < r0"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and v2: "2 \<le> descartes_list_int (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) (snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) (coeffs P)"
    and dpos: "0 < \<delta>"
    and wide: "\<delta> < real_of_rat (snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) - real_of_rat (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))"
    \<comment> \<open>\<^bold>\<open>\<open>P_eq\<close>, threaded from the keystone.\<close> \<open>accgrow\<close> is DERIVED below rather than
       assumed; deriving it needs to know how the abstract \<open>P\<close> relates to \<open>rp\<close>,
       because the arm branches on the NODE poly at \<open>1/2\<close> while
       @{thm [source] hybrid_refine_invar_split_step} states the condition on the ROOT poly at
       the node midpoint. Nothing else in this lemma connects the two.\<close>
    and P_eq: "P = Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)"
    \<comment> \<open>the ambient word caps, passed straight to the body step, which now DERIVES
       \<open>safe'\<close> rather than taking it. Same two premises the discard arm carries.\<close>
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and arm: "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
              \<le> SPEC (\<lambda>(wl, acc').
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                     acc' = (al @ [last lns + last rns], ar @ [last lns + last rns],
                             ak @ [last ks + 1])) \<and>
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
                  hybrid_split_wl X (butlast lns) (butlast rns) (butlast ks) (butlast qtodo) (butlast es) (butlast ss) (butlast cs) (butlast gs) rp (last lns) (last rns) (last ks) (last es) (last ss) wl)"
    \<comment> \<open>\<^bold>\<open>The payload bound.\<close> \<open>paypush\<close> is a premise here, as \<open>arm\<close> is; the assembly discharges it with
       @{thm [source] hybrid_pay_split_child} from the \<open>hybrid_child_gok\<close> / \<open>gl \<le> max g 2\<^sup>4\<^sup>2\<close> facts the
       split arm's SPEC exports. \<^bold>\<open>Last\<close>.\<close>
    \<comment> \<open>\<^bold>\<open>Conditioned on the arm's own exports.\<close> A \<open>\<And>gl gr\<close> form with a free right-hand side would claim the
       pushed state satisfies @{const hybrid_pay_invar} for arbitrary child guards, which is
       false. So it is conditioned, as \<open>safe\<close>\<open>'\<close> is, on the
       two atoms the arm's SPEC exports, and discharged with
       @{thm [source] hybrid_pay_invar_push2}.\<close>
    and paypush: "\<And>gl gr. hybrid_child_pay_ok (2 * last lns) (last ks + 1) (last lns + last rns) rp gl \<Longrightarrow>
                    hybrid_child_pay_ok (last lns + last rns) (last ks + 1) (2 * last rns) rp gr \<Longrightarrow> hybrid_pay_invar
                    (butlast lns @ [2 * last lns, last lns + last rns],
                     butlast rns @ [last lns + last rns, 2 * last rns],
                     butlast ks @ [last ks + 1, last ks + 1])
                    (butlast gs @ [gl, gr]) rp"
    \<comment> \<open>\<^bold>\<open>The root relation\<close>, @{const hybrid_state_invar}'s fifth
       conjunct, \<^bold>\<open>last\<close>. It is the same proposition at the pushed state as at the popped one
       (no arm touches \<open>P\<close> or \<open>rp\<close>), so it passes straight through; it exists so that
       \<open>hybrid_loop_correct\<close>'s \<open>\<And>s\<close> step can reach \<open>s\<close>'s own \<open>rp\<close>.\<close>
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
  shows "hybrid_loop_body_checked_monadic
           (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe unfolding hybrid_loop_safe_invar_def by simp
  have pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have lne: "lns \<noteq> []" using cond by (simp add: hybrid_loop_cond_def)
  have ne: "qtodo \<noteq> []" "es \<noteq> []" "ss \<noteq> []" "cs \<noteq> []" "gs \<noteq> []" "ks \<noteq> []" "rns \<noteq> []"
    using lne SL VL by auto
  have CL: "length lns = length ks" "length rns = length ks" "length ss = length ks"
    using VL SL by simp_all
  have BL: "length (butlast lns) = length (butlast rns)"
     "length (butlast rns) = length (butlast ks)"
     "length (butlast es) = length (butlast ks)"
     "length (butlast ss) = length (butlast ks)"
    using VL SL by simp_all
  have ACL: "length al = length ar" "length ar = length ak"
    using stinv unfolding hybrid_loop_state_invar_def dyadic_interval_vec_invar_def
    by (simp_all add: Let_def)
  \<comment> \<open>\<^bold>\<open>\<open>accgrow\<close>, DERIVED\<close> -- the append law at the popped node, the degenerate
     midpoint's node view, and (c\<acute>) to move the branch condition from the NODE poly at \<open>1/2\<close>
     onto the ROOT poly at the node midpoint. Those three are exactly what this arm was missing.\<close>
  have midzero: "(poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)
               = (poly (map_poly rat_of_int P)
                    ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
                      + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2) = 0)"
    by (rule hybrid_mid_zero_bridge[OF lr0 P_eq X_eq surjective_pairing[symmetric]])
  have midview: "dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns + last rns, last lns + last rns), last ks + 1)
               = ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
                   + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2,
                  (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
                   + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2)"
    using hybrid_node_iv_split_mid[OF lr0, where l = "last lns" and r = "last rns" and k = "last ks"] by simp
  have accgrow: "\<And>ag ah bb.
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                     ag = al @ [last lns + last rns] \<and> ah = ar @ [last lns + last rns] \<and>
                     bb = ak @ [last ks + 1]) \<Longrightarrow>
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
                     ag = al \<and> ah = ar \<and> bb = ak) \<Longrightarrow>
                  dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (ag, ah, bb))
                  = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak))
                    @ (if poly (map_poly of_int P :: rat poly)
                           ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2) = 0
                       then [((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2, (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2)]
                       else [])"
  proof -
    fix ag ah bb
    assume g1: "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                  ag = al @ [last lns + last rns] \<and> ah = ar @ [last lns + last rns] \<and>
                  bb = ak @ [last ks + 1]"
       and g0: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
                  ag = al \<and> ah = ar \<and> bb = ak"
    show "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (ag, ah, bb))
        = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak))
          @ (if poly (map_poly of_int P :: rat poly)
                 ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2) = 0
             then [((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2, (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2)]
             else [])"
    proof (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0")
      case True
      hence E: "ag = al @ [last lns + last rns]" "ah = ar @ [last lns + last rns]"
               "bb = ak @ [last ks + 1]" using g1 by auto
      \<comment> \<open>\<open>if_P\<close>/\<open>if_not_P\<close>, not \<open>if_True\<close>/\<open>if_False\<close>: the branch condition in the goal is the
         ROOT-poly one, and it is only KNOWN through (c\<acute>) -- it never becomes the literal
         \<open>True\<close> that \<open>if_True\<close> needs.\<close>
      have condT: "poly (map_poly of_int P :: rat poly)
                     ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
                       + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2) = 0"
        using True midzero by simp
      have app: "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (ag, ah, bb))
          = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak))
            @ [dyadic_iv_node_iv_of l0 r0 k0
                 ((last lns + last rns, last lns + last rns), last ks + 1)]"
        unfolding E by (rule dyadic_iv_acc_ivs_append1[OF ACL(1) ACL(2)])
      show ?thesis by (simp only: app midview if_P[OF condT])
    next
      case False
      hence E: "ag = al" "ah = ar" "bb = ak" using g0 by auto
      have condF: "\<not> (poly (map_poly of_int P :: rat poly)
                     ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
                       + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2) = 0)"
        using False midzero by simp
      show ?thesis unfolding E by (simp only: if_not_P[OF condF] append_Nil2)
    qed
  qed
  have nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
       = hybrid_alpha_nodes l0 r0 k0
           (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
         @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)), snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)), last es, last ks, last ss)]"
    by (rule hybrid_alpha_nodes_pop_decomp[OF lne VL(1) VL(2) SL(2) SL(3)])
  have vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
       = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
         @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)), snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))]"
    using hybrid_alpha_views_pop_decomp[OF lne VL(1) VL(2)] by simp
  have ilast: "length ks - 1 < length ks" using ne(6) by simp
  have ab: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) < snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using hybrid_cap_invar_nondeg[OF capinv ilast] lne ne VL
    by (simp add: last_conv_nth)
  have npush: "\<And>sv. hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [last ks + 1, last ks + 1])
                   (butlast es @ [newton_child_exp (last es), newton_child_exp (last es)])
                   (butlast ss @ [sv, sv])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)), (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2,
                       max 1 (last es - 1), last ks + 1, sv),
                      ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2, snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
                       max 1 (last es - 1), last ks + 1, sv)]"
    by (rule hybrid_npush_split_satisfiable[OF BL(1) BL(2) BL(3) BL(4)
              hybrid_node_iv_split_children(1)[OF lr0] hybrid_node_iv_split_children(2)[OF lr0]
              newton_child_exp_eq refl])
  have vpush: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [last ks + 1, last ks + 1])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)), (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2),
                      ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2, snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))]"
    using hybrid_alpha_views_append2[OF BL(1) BL(2),
            of l0 r0 k0 "2 * last lns" "last lns + last rns" "last lns + last rns"
               "2 * last rns" "last ks + 1" "last ks + 1"]
          hybrid_node_iv_split_children(1)[OF lr0] hybrid_node_iv_split_children(2)[OF lr0]
    by simp
  have ACL: "length al = length ar" "length ar = length ak"
    using stinv unfolding hybrid_loop_state_invar_def dyadic_interval_vec_invar_def
    by (simp_all add: Let_def)
  have rp_len_z: "0 < length rp" using pre unfolding hybrid_loop_step_pre_def by simp
  show ?thesis
    by (rule hybrid_body_step_split[OF cond stinv pre inv X_eq nsplit vsplit npush vpush accgrow ab
              P0 p0 sf v2 dpos wide capinv budinv CL(1) CL(2) CL(3) ne(6) lr0
              surjective_pairing kcap kdepth arm paypush Pcoeffs
              hybrid_split_right_zero[OF lr0 Pcoeffs rp_len_z X_eq surjective_pairing ab]])
qed

text \<open>\<^bold>\<open>The window arm, assembled\<close> -- the fourth and last. Its REJECT half IS the split arm,
  so \<open>nsplit\<close>/\<open>vsplit\<close>/\<open>ab\<close>/\<open>npush_s\<close>/\<open>vpush_s\<close> and the coupling facts derive exactly as there.
  Its ACCEPT half's window facts are premises here and are derived in
  \<open>hybrid_step_discharge_window\<close>; each is conditioned on the arm's own exported
  pick, so those premises are about the ONE window the run took rather than about every \<open>m\<close>.

  \<^bold>\<open>The node view is pinned by EQUATIONS, not by substitution\<close> (\<open>abnode\<close>/\<open>edef\<close>/\<open>dkdef\<close>/\<open>sdef\<close>):
  that lets every pass-through premise keep the body step's own wording verbatim, which is what
  makes this a transcription rather than a re-derivation.\<close>
lemma hybrid_body_step_window_assembled:
  fixes pol :: newton_pol
  assumes safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and lr0: "l0 < r0"
    and abnode: "dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks) = (a, b)"
    and edef: "e = last es" and dkdef: "dk = last ks" and sdef: "sv0 = last ss"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and v2: "2 \<le> descartes_list_int a b (coeffs P)"
    and dpos: "0 < \<delta>" and wide: "\<delta> < real_of_rat b - real_of_rat a"
    \<comment> \<open>the k-potential half: its input, the column lengths it needs, and the node view the
       geometry lemma turns into the children's halves.\<close>
    \<comment> \<open>\<^bold>\<open>\<open>P_eq\<close>, threaded from the keystone\<close>, as on the split arm: \<open>accgrow_s\<close>
       is DERIVED below, and deriving it needs the abstract \<open>P\<close> tied to \<open>rp\<close>.\<close>
    and P_eq: "P = Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)"
    \<comment> \<open>the ambient word caps, passed to the body step, which DERIVES \<open>safe_s\<close>.\<close>
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>The window interval is a function of the index, \<open>Iw m\<close>, and every window premise is
       conditioned on the arm's own pick.\<close> A fixed \<open>I\<close> under \<open>\<And>m\<close> would force every window child to
       be the same interval (\<open>hybrid_npush_w_forall_m_forces_one_window\<close>). The pick, which the arm exports, ties
       \<open>m\<close> to an abstract interval, so these are assumptions about the one window the run actually took.
       \<open>mu_w\<close> is stated at \<open>Iw m\<close>, not \<open>(fst (Iw m), snd (Iw m))\<close>: the same pair, but the
       measure goal carries the latter and \<open>simp\<close> collapses it, while \<open>wsub\<close>/\<open>wprop\<close> must be in
       the projected form the invariant step demands.

       \<^bold>\<open>Stated at the actual count, not \<open>\<And>v\<close>.\<close> None of these four right-hand
       sides mentions \<open>v\<close>, so a \<open>\<And>v\<close> form would demand that
       every \<open>v\<close> admitting a pick land on the same window, which together with \<open>npush_w\<close>'s \<open>\<And>m\<close>
       (forcing \<open>Iw m\<close> to be the \<open>m\<close>-th child's view) is not satisfiable in general. The
       arm's SPEC pins \<open>v = \<close>@{const carried_descartes_count}\<open> X\<close>; that is the only instance
       these are used at, and the only one \<open>hybrid_window_pick_abs_node\<close> and
       \<open>hybrid_window_geometry_node\<close> prove (both below; plain names, since at this point they are forward
       references).\<close>
    and win: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                 try_window_bail_int (snd (dec :: bool \<times> bool)) a b (N_of e) P
                   (descartes_list_int a b (coeffs P)) = Some (Iw m)"
    and wsub: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                 alr_ivl_pss (fst (Iw m), snd (Iw m)) (a, b)"
    and wprop: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow> fst (Iw m) < snd (Iw m)"
    and mu_w: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                 dyadic_iv_interval_mu \<delta> (Iw m) < dyadic_iv_interval_mu \<delta> (a, b)"
    and npush_w: "\<And>m. hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)], butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)], butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
                   (butlast es @ [last es + 1]) (butlast ss @ [last ss])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(fst (Iw m), snd (Iw m), e + 1, dk + (2 ^ e + 2), sv0)]"
    and vpush_w: "\<And>m. hybrid_alpha_views l0 r0 k0 (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)], butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)], butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(fst (Iw m), snd (Iw m))]"
    and gw: "\<And>v :: nat. 4398046511104 + v \<le> (Suc (Suc (last ks + 2 ^ last es)) + 1) * length rp
                 \<or> 4398046511104 \<le> 4398046511104 + v"
    \<comment> \<open>\<^bold>\<open>\<open>v :: nat\<close> is load-bearing.\<close> \<open>v\<close>'s only constraint here is
       \<open>2\<^sup>4\<^sup>2 \<le> 2\<^sup>4\<^sup>2 + v\<close> -- pure numerals -- so Isabelle generalises it to a FIXED type variable
       \<open>'a\<close>, and \<open>rule\<close> can then never match the \<open>nat\<close> goal. Diagnosed by inserting \<open>lkw\<close> beside
       the goal and reading the two forms: \<open>(4398046511104::'a)\<close> against \<open>nat\<close>.\<close>
    \<comment> \<open>\<^bold>\<open>the arm SELECTION fact\<close>, the window counterpart of the discard arm's \<open>count0\<close>.
       \<open>okw\<close> is DERIVED below and needs \<open>2 \<le> v\<close>: at \<open>v \<in> {0, 1}\<close> the cache class
       \<open>v + 2\<close> would violate @{const dyadic_iv_cs_invar}'s first two clauses. The gate only
       opens at \<open>cnt \<ge> 2\<close>, so this is exactly the branch condition.\<close>
    and count2: "2 \<le> carried_descartes_count X"
    \<comment> \<open>the k-potential's window inputs: the accepted child's \<open>\<mu>\<close>-drop at the NODE VIEW, and
       the gate's own exponent cap, which is what bounds the depth jump by \<open>C\<close>.\<close>
    and muW: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                     last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                    Suc (Suc (last ks + 2 ^ last es))))
                < dyadic_iv_interval_mu \<delta>
                    (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    and jw: "int (2 ^ last es + 2) \<le> int (2 ^ newton_pol_ecap + 2)"
    and ndW: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                fst (dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                     last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                    Suc (Suc (last ks + 2 ^ last es))))
                < snd (dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                     last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                    Suc (Suc (last ks + 2 ^ last es))))"
    \<comment> \<open>\<^bold>\<open>\<open>safe_w\<close> is also at the actual count.\<close> Unlike the six above, its right-hand side
       does mention \<open>v\<close> (in the pushed \<open>cs\<close>/\<open>gs\<close> entries), so a \<open>\<And>v\<close> form would not be vacuous,
       but it would be unprovable, because its cap-invariant input travels through \<open>muW\<close>/\<open>ndW\<close>,
       which hold only for the window the run actually picked.\<close>
    and safe_w: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                            = Some (m, cand) \<Longrightarrow> hybrid_loop_safe_invar
                  (((butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)], butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)], butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
                    butlast qtodo @ [cand], butlast es @ [last es + 1],
                    butlast ss @ [last ss], butlast cs @ [Suc (Suc (carried_descartes_count X))],
                    butlast gs @ [4398046511104 + carried_descartes_count X], rp),
                   (al, ar, ak))"
    and arm: "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
              \<le> SPEC (\<lambda>(wl, acc').
           ((poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                 acc' = (al @ [last lns + last rns], ar @ [last lns + last rns], ak @ [last ks + 1])) \<and>
              (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
                            hybrid_split_wl X (butlast lns) (butlast rns) (butlast ks) (butlast qtodo) (butlast es) (butlast ss) (butlast cs) (butlast gs) rp (last lns) (last rns) (last ks) (last es) (last ss) wl)
           \<or>
           (\<exists>m cand v. acc' = (al, ar, ak) \<and>
              v = carried_descartes_count X \<and>
              carried_descartes_count cand = v \<and>
              newton_window_pick_bail v (last es) X = Some (m, cand) \<and>
              wl = ((butlast lns @ [last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns)],
                     butlast rns @ [last lns * 2 ^ (2 ^ last es + 2) + (m + 4) * (last rns - last lns)],
                     butlast ks @ [last ks + (2 ^ last es + 2)]),
                    butlast qtodo @ [cand], butlast es @ [last es + 1], butlast ss @ [last ss],
                    butlast cs @ [v + 2], butlast gs @ [4398046511104 + v], rp)))"
    \<comment> \<open>\<^bold>\<open>The payload bound\<close>: the accept half is derived below (the window child's payload is its
       count); the reject half is the split arm's. \<^bold>\<open>Last\<close>.\<close>
    and payinv: "hybrid_pay_invar (lns, rns, ks) gs rp"
    \<comment> \<open>\<^bold>\<open>Conditioned on the arm's own exports.\<close> A \<open>\<And>gl gr\<close> form with a free right-hand side would claim the
       pushed state satisfies @{const hybrid_pay_invar} for arbitrary child guards, which is
       false. So it is conditioned, as \<open>safe\<close>\<open>'\<close> is, on the
       two atoms the arm's SPEC exports, and discharged with
       @{thm [source] hybrid_pay_invar_push2}.\<close>
    and paypush_s: "\<And>gl gr. hybrid_child_pay_ok (2 * last lns) (last ks + 1) (last lns + last rns) rp gl \<Longrightarrow>
                      hybrid_child_pay_ok (last lns + last rns) (last ks + 1) (2 * last rns) rp gr \<Longrightarrow> hybrid_pay_invar
                      (butlast lns @ [2 * last lns, last lns + last rns],
                       butlast rns @ [last lns + last rns, 2 * last rns],
                       butlast ks @ [last ks + 1, last ks + 1])
                      (butlast gs @ [gl, gr]) rp"
    \<comment> \<open>\<^bold>\<open>The root relation\<close>, @{const hybrid_state_invar}'s fifth
       conjunct, \<^bold>\<open>last\<close>. It is the same proposition at the pushed state as at the popped one
       (no arm touches \<open>P\<close> or \<open>rp\<close>), so it passes straight through; it exists so that
       \<open>hybrid_loop_correct\<close>'s \<open>\<And>s\<close> step can reach \<open>s\<close>'s own \<open>rp\<close>.\<close>
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
  shows "hybrid_loop_body_checked_monadic
           (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe unfolding hybrid_loop_safe_invar_def by simp
  have pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have lne: "lns \<noteq> []" using cond by (simp add: hybrid_loop_cond_def)
  have ne: "qtodo \<noteq> []" "es \<noteq> []" "ss \<noteq> []" "cs \<noteq> []" "gs \<noteq> []" "ks \<noteq> []" "rns \<noteq> []"
    using lne SL VL by auto
  have CL: "length lns = length ks" "length rns = length ks" "length ss = length ks"
    using VL SL by simp_all
  have BL: "length (butlast lns) = length (butlast rns)"
     "length (butlast rns) = length (butlast ks)"
     "length (butlast es) = length (butlast ks)"
     "length (butlast ss) = length (butlast ks)"
    using VL SL by simp_all
  have ACL: "length al = length ar" "length ar = length ak"
    using stinv unfolding hybrid_loop_state_invar_def dyadic_interval_vec_invar_def
    by (simp_all add: Let_def)
  \<comment> \<open>\<^bold>\<open>\<open>accgrow_s\<close>, DERIVED\<close> -- the split arm's derivation verbatim, except that this
     lemma NAMES the node view \<open>(a, b)\<close> via \<open>abnode\<close> instead of carrying its projections, so
     the bridge takes \<open>abnode[symmetric]\<close> where the split arm takes \<open>surjective_pairing\<close>.\<close>
  have midzero: "(poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0)
               = (poly (map_poly rat_of_int P) ((a + b) / 2) = 0)"
    by (rule hybrid_mid_zero_bridge[OF lr0 P_eq X_eq abnode[symmetric]])
  have midview: "dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns + last rns, last lns + last rns), last ks + 1)
               = ((a + b) / 2, (a + b) / 2)"
    using hybrid_node_iv_split_mid[OF lr0, where l = "last lns" and r = "last rns"
            and k = "last ks"] abnode by simp
  \<comment> \<open>\<^bold>\<open>The window candidate IS the recompute-from-root.\<close> The pick emits
     @{const newton_wcand} of the NODE poly; \<open>X_eq\<close> makes that node poly a
     @{const carried_init_same_den} of \<open>rp\<close>; and \<open>carried_init_same_den_compose\<close> collapses the
     two frames into the single one the pushed columns carry. \<open>4 * 2\<^sup>2\<^sup>^\<^sup>e = 2\<^sup>2\<^sup>^\<^sup>e\<^sup>+\<^sup>2\<close> and
     \<open>2\<^sup>k \<cdot> 2\<^sup>2\<^sup>^\<^sup>e\<^sup>+\<^sup>2 = 2\<^sup>S\<^sup>u\<^sup>c\<^sup>\<^sup>(\<^sup>S\<^sup>u\<^sup>c\<^sup>\<^sup>(\<^sup>k\<^sup>+\<^sup>2\<^sup>^\<^sup>e\<^sup>)\<^sup>)\<close> are the two exponent normalisations.\<close>
  have cand_eq: "\<And>m cand v. newton_window_pick_bail v (last es) X = Some (m, cand) \<Longrightarrow>
      cand = carried_init_same_den
               (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns))
               (2 ^ (Suc (Suc (last ks + 2 ^ last es))))
               (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp"
  proof -
    fix m cand v
    assume pk: "newton_window_pick_bail v (last es) X = Some (m, cand)"
    have c1: "cand = carried_init_same_den m (2 ^ (2 ^ last es + 2)) (m + 4) X"
      using newton_window_pick_bail_cand[OF pk] by (simp add: newton_wcand_def)
    have c2: "carried_init_same_den m (2 ^ (2 ^ last es + 2)) (m + 4)
                (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp)
            = carried_init_same_den
                (last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns))
                (2 ^ last ks * 2 ^ (2 ^ last es + 2))
                (last lns * 2 ^ (2 ^ last es + 2) + (m + 4) * (last rns - last lns)) rp"
      by (rule carried_init_same_den_compose) simp_all
    have e1: "(2::int) ^ (2 ^ last es + 2) = 4 * 2 ^ 2 ^ last es"
      by (simp add: power_add)
    have e2: "(2::int) ^ last ks * 2 ^ (2 ^ last es + 2)
            = 2 ^ (Suc (Suc (last ks + 2 ^ last es)))"
      by (simp add: power_add)
    show "cand = carried_init_same_den
               (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns))
               (2 ^ (Suc (Suc (last ks + 2 ^ last es))))
               (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp"
      unfolding c1 X_eq by (simp only: c2 e1[symmetric] e2)
  qed
  have fw: "\<And>m cand v. newton_window_pick_bail v (last es) X = Some (m, cand) \<Longrightarrow>
      node_frame (carried_init_same_den
                    (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns))
                    (2 ^ (Suc (Suc (last ks + 2 ^ last es))))
                    (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp)
                 cand (4398046511104 + v)"
  proof -
    fix m cand v
    assume pk: "newton_window_pick_bail v (last es) X = Some (m, cand)"
    show "node_frame (carried_init_same_den
                        (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns))
                        (2 ^ (Suc (Suc (last ks + 2 ^ last es))))
                        (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp)
                     cand (4398046511104 + v)"
      unfolding cand_eq[OF pk] by (rule node_frame_any)
  qed
  have lkw: "\<And>m cand (v :: nat). newton_window_pick_bail v (last es) X = Some (m, cand) \<Longrightarrow>
      4398046511104 \<le> 4398046511104 + v \<longrightarrow>
        cand = carried_init_same_den
                 (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns))
                 (2 ^ (Suc (Suc (last ks + 2 ^ last es))))
                 (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp"
    using cand_eq by blast
  \<comment> \<open>\<^bold>\<open>\<open>okw\<close>, DERIVED\<close>. The candidate's count IS \<open>v\<close>
     (@{thm [source] newton_window_pick_bail_count}), and \<open>cand\<close> is the recompute by \<open>cand_eq\<close>,
     so the goal is \<open>hybrid_cs_ok (2\<^sup>4\<^sup>2 + v) (v + 2) v\<close>. The locked guard rules out the
     sentinel disjunct, leaving @{const dyadic_iv_cs_invar} \<open>(v + 2) v\<close> -- which holds exactly
     because the gate only opens at \<open>2 \<le> v\<close>.\<close>
  have okw: "\<And>m cand v. newton_window_pick_bail v (last es) X = Some (m, cand) \<Longrightarrow>
      v = carried_descartes_count X \<Longrightarrow>
      hybrid_cs_ok (4398046511104 + v) (Suc (Suc v))
        (carried_descartes_count (carried_init_same_den
           (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns))
           (2 ^ (Suc (Suc (last ks + 2 ^ last es))))
           (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp))"
  proof -
    fix m cand v
    assume pk: "newton_window_pick_bail v (last es) X = Some (m, cand)"
       and vdef: "v = carried_descartes_count X"
    have cnt: "carried_descartes_count cand = v" by (rule newton_window_pick_bail_count[OF pk])
    have v2v: "2 \<le> v" using vdef count2 by simp
    have "hybrid_cs_ok (4398046511104 + v) (Suc (Suc v)) v"
      using v2v by (auto simp: hybrid_cs_ok_def dyadic_iv_cs_invar_def)
    thus "hybrid_cs_ok (4398046511104 + v) (Suc (Suc v))
        (carried_descartes_count (carried_init_same_den
           (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns))
           (2 ^ (Suc (Suc (last ks + 2 ^ last es))))
           (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp))"
      unfolding cand_eq[OF pk, symmetric] cnt .
  qed
  \<comment> \<open>\<^bold>\<open>The payload bound, accept half, derived.\<close> The window child's guard is \<open>2\<^sup>4\<^sup>2 + v\<close> and its count
     is \<open>v\<close>, so @{thm [source] hybrid_pay_window_child} gives the atom outright; the prefix comes
     from the pop and @{thm [source] hybrid_pay_invar_push1} appends. This is the only arm that
     creates a lock, and it pins the payload while doing so.\<close>
  have paypre: "hybrid_pay_invar (butlast lns, butlast rns, butlast ks) (butlast gs) rp"
    by (rule hybrid_pay_invar_pop[OF payinv]) (use SL VL in simp_all)
  \<comment> \<open>the ceiling half of the atom: the pushed guard is \<open>2\<^sup>4\<^sup>2 + v\<close> and \<open>v\<close> is the parent
     node's own count, which cannot exceed the list's length.\<close>
  have vlen: "carried_descartes_count X \<le> length rp"
    using carried_descartes_count_le_length_cn[of X]
    by (simp add: X_eq truncate_length_carried_init_same_den)
  have paypush_w: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                               = Some (m, cand) \<Longrightarrow> hybrid_pay_invar
                     (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)],
                      butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)],
                      butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
                     (butlast gs @ [4398046511104 + carried_descartes_count X]) rp"
  proof -
    fix m cand
    assume pk: "newton_window_pick_bail (carried_descartes_count X) (last es) X = Some (m, cand)"
    have pc: "hybrid_child_pay_ok
                (last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns))
                (Suc (Suc (last ks + 2 ^ last es)))
                (last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)) rp
                (4398046511104 + carried_descartes_count X)"
      by (rule hybrid_pay_window_child[OF pk cand_eq[OF pk] vlen])
    show "hybrid_pay_invar
            (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)],
             butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)],
             butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
            (butlast gs @ [4398046511104 + carried_descartes_count X]) rp"
      by (rule hybrid_pay_invar_push1[OF paypre _ _ _ pc]) (use SL VL in simp_all)
  qed
  have accgrow_s: "\<And>ag ah bb.
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                     ag = al @ [last lns + last rns] \<and> ah = ar @ [last lns + last rns] \<and>
                     bb = ak @ [last ks + 1]) \<Longrightarrow>
                  (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
                     ag = al \<and> ah = ar \<and> bb = ak) \<Longrightarrow>
                  dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (ag, ah, bb))
                  = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak))
                    @ (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                       then [((a + b) / 2, (a + b) / 2)] else [])"
  proof -
    fix ag ah bb
    assume g1: "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                  ag = al @ [last lns + last rns] \<and> ah = ar @ [last lns + last rns] \<and>
                  bb = ak @ [last ks + 1]"
       and g0: "poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow>
                  ag = al \<and> ah = ar \<and> bb = ak"
    show "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (ag, ah, bb))
        = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak))
          @ (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
             then [((a + b) / 2, (a + b) / 2)] else [])"
    proof (cases "poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0")
      case True
      hence E: "ag = al @ [last lns + last rns]" "ah = ar @ [last lns + last rns]"
               "bb = ak @ [last ks + 1]" using g1 by auto
      have condT: "poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0"
        using True midzero by simp
      have app: "dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (ag, ah, bb))
          = dyadic_iv_acc_ivs l0 r0 k0 (dyadic_interval_vec_triples (al, ar, ak))
            @ [dyadic_iv_node_iv_of l0 r0 k0
                 ((last lns + last rns, last lns + last rns), last ks + 1)]"
        unfolding E by (rule dyadic_iv_acc_ivs_append1[OF ACL(1) ACL(2)])
      show ?thesis by (simp only: app midview if_P[OF condT])
    next
      case False
      hence E: "ag = al" "ah = ar" "bb = ak" using g0 by auto
      have condF: "\<not> (poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0)"
        using False midzero by simp
      show ?thesis unfolding E by (simp only: if_not_P[OF condF] append_Nil2)
    qed
  qed
  have nsplit: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
       = hybrid_alpha_nodes l0 r0 k0
           (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
         @ [(a, b, e, dk, sv0)]"
    \<comment> \<open>\<open>rule\<close> FIRST, then rewrite: under a bare \<open>using\<close> the decomposition's \<open>l0\<close>/\<open>r0\<close>/\<open>k0\<close>
       stay schematic and \<open>abnode\<close>, which is at the specific frame, cannot fire.\<close>
  proof -
    have D: "hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
         = hybrid_alpha_nodes l0 r0 k0
             (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
           @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)), snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)), last es, last ks, last ss)]"
      by (rule hybrid_alpha_nodes_pop_decomp[OF lne VL(1) VL(2) SL(2) SL(3)])
    show ?thesis using D by (simp add: abnode edef dkdef sdef)
  qed
  have vsplit: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
       = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks) @ [(a, b)]"
  proof -
    have D: "hybrid_alpha_views l0 r0 k0 (lns, rns, ks)
         = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
           @ [dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)]"
      by (rule hybrid_alpha_views_pop_decomp[OF lne VL(1) VL(2)])
    show ?thesis using D by (simp add: abnode)
  qed
  have ilast: "length ks - 1 < length ks" using ne(6) by simp
  have ab: "a < b"
    using hybrid_cap_invar_nondeg[OF capinv ilast] lne ne VL abnode
    by (simp add: last_conv_nth)
  have npush_s: "\<And>sv. hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [last ks + 1, last ks + 1])
                   (butlast es @ [newton_child_exp (last es), newton_child_exp (last es)])
                   (butlast ss @ [sv, sv])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, sv),
                      ((a + b) / 2, b, max 1 (e - 1), dk + 1, sv)]"
  proof -
    fix sv
    have D: "hybrid_alpha_nodes l0 r0 k0
                 (butlast lns @ [2 * last lns, last lns + last rns],
                  butlast rns @ [last lns + last rns, 2 * last rns],
                  butlast ks @ [last ks + 1, last ks + 1])
                 (butlast es @ [newton_child_exp (last es), newton_child_exp (last es)])
                 (butlast ss @ [sv, sv])
               = hybrid_alpha_nodes l0 r0 k0
                   (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                 @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
                     (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2,
                     max 1 (last es - 1), last ks + 1, sv),
                    ((fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))) / 2,
                     snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)), max 1 (last es - 1), last ks + 1, sv)]"
      by (rule hybrid_npush_split_satisfiable[OF BL(1) BL(2) BL(3) BL(4)
                hybrid_node_iv_split_children(1)[OF lr0]
                hybrid_node_iv_split_children(2)[OF lr0] newton_child_exp_eq refl])
    show "hybrid_alpha_nodes l0 r0 k0
                 (butlast lns @ [2 * last lns, last lns + last rns],
                  butlast rns @ [last lns + last rns, 2 * last rns],
                  butlast ks @ [last ks + 1, last ks + 1])
                 (butlast es @ [newton_child_exp (last es), newton_child_exp (last es)])
                 (butlast ss @ [sv, sv])
               = hybrid_alpha_nodes l0 r0 k0
                   (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                 @ [(a, (a + b) / 2, max 1 (e - 1), dk + 1, sv),
                    ((a + b) / 2, b, max 1 (e - 1), dk + 1, sv)]"
      using D by (simp add: abnode edef dkdef)
  qed
  have vpush_s: "hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [2 * last lns, last lns + last rns],
                    butlast rns @ [last lns + last rns, 2 * last rns],
                    butlast ks @ [last ks + 1, last ks + 1])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(a, (a + b) / 2), ((a + b) / 2, b)]"
    using hybrid_alpha_views_append2[OF BL(1) BL(2),
            of l0 r0 k0 "2 * last lns" "last lns + last rns" "last lns + last rns"
               "2 * last rns" "last ks + 1" "last ks + 1"]
          hybrid_node_iv_split_children(1)[OF lr0] hybrid_node_iv_split_children(2)[OF lr0]
          abnode
    by simp
  have rp_len_z: "0 < length rp" using pre unfolding hybrid_loop_step_pre_def by simp
  show ?thesis
    \<comment> \<open>the FULL premise order -- \<open>p0\<close>/\<open>wide\<close>/\<open>crr\<close>/\<open>kne\<close>/\<open>lr0\<close> are declared on the same
       LINE as their neighbours, so a line-wise reading of the list silently drops them.\<close>
    by (rule hybrid_body_step_window[OF cond stinv pre inv X_eq nsplit vsplit ab P0 p0 sf v2 dpos wide
              capinv budinv CL(1) CL(2) CL(3) ne(6) lr0 abnode npush_s vpush_s accgrow_s kcap kdepth
              win wsub wprop mu_w npush_w vpush_w fw gw lkw okw muW jw ndW safe_w arm
              paypush_w paypush_s Pcoeffs
              hybrid_split_right_zero[OF lr0 Pcoeffs rp_len_z X_eq abnode ab]])
qed

text \<open>\<^bold>\<open>A vacuity tripwire for the pushing arms.\<close> If \<open>safe'\<close> were \<open>\<And>\<close>-quantified over the pushed
  polynomials \<open>ql\<close>/\<open>qr\<close>, it would contradict @{const hybrid_loop_step_pre}, which demands
  \<open>0 < length (last qtodo)\<close> of the pushed state, whose last entry is \<open>qr\<close>: instantiate at \<open>[]\<close>.

  A fact that holds only for the arm's own witnesses cannot be a premise quantified over all of
  them. The arm exports what pins them --- \<open>node_frame (carried_left X) ql gl\<close> gives
  \<open>length ql = length rp\<close> through @{thm [source] cdlr_node_frame_len} --- so \<open>safe'\<close> is
  conditioned on those exports instead of quantified over every possible child.\<close>
lemma hybrid_safe_push_forall_q_is_vacuous:
  assumes safe': "\<And>ql qr cl cr gl gr sv ag ah bb.
                  hybrid_loop_safe_invar
                    (((butlast lns @ [2 * last lns, last lns + last rns],
                       butlast rns @ [last lns + last rns, 2 * last rns],
                       butlast ks @ [last ks + 1, last ks + 1]),
                      butlast qtodo @ [ql, qr],
                      butlast es @ [newton_child_exp (last es), newton_child_exp (last es)],
                      butlast ss @ [sv, sv], butlast cs @ [cl, cr], butlast gs @ [gl, gr], rp),
                     (ag, ah, bb))"
  shows False
proof -
  have "hybrid_loop_safe_invar
          (((butlast lns @ [2 * last lns, last lns + last rns],
             butlast rns @ [last lns + last rns, 2 * last rns],
             butlast ks @ [last ks + 1, last ks + 1]),
            butlast qtodo @ [[], []],
            butlast es @ [newton_child_exp (last es), newton_child_exp (last es)],
            butlast ss @ [0, 0], butlast cs @ [0, 0], butlast gs @ [0, 0], rp),
           (al, ar, ak))"
    by (rule safe')
  thus False
    by (simp add: hybrid_loop_safe_invar_def hybrid_loop_step_pre_def hybrid_loop_cond_def)
qed

text \<open>\<^bold>\<open>The seed cache class.\<close> @{thm [source] hybrid_refine_invar_seed} wants
  \<open>hybrid_cs_ok 0 c0 (carried_descartes_count P)\<close> for the \<open>c0\<close> the wrapper computes with
  @{const carried_descartes_count_trunc_monadic}. At the seed \<open>g = 0\<close>, so
  @{thm [source] hybrid_cs_ok_def}'s first disjunct would need the "no cache" sentinel
  \<open>c0 = 4\<close> --- but the wrapper seeds \<open>cs\<close> with the real count. Hence the second disjunct,
  @{const dyadic_iv_cs_invar}.

  @{thm [source] carried_descartes_count_trunc_monadic_classify_le3} is exactly this contract:
  its \<open>cnt \<le> 3\<close> conjunct makes @{const dyadic_iv_cs_invar}'s remaining
  \<open>4 \<le> c \<longrightarrow> c = cnt + 2\<close> clause vacuous, and the other three are the classify trichotomy
  verbatim. So this is a SPEC weakening.\<close>
lemma hybrid_count_trunc_cs_ok:
  assumes len_bound: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "carried_descartes_count_trunc_monadic xs
       \<le> SPEC (\<lambda>c0. hybrid_cs_ok 0 c0 (carried_descartes_count xs))"
  using carried_descartes_count_trunc_monadic_classify_le3[OF len_bound]
  by (auto simp: hybrid_cs_ok_def dyadic_iv_cs_invar_def pw_le_iff refine_pw_simps)


text \<open>\<^bold>\<open>The \<open>carried_init_same_den\<close> COMPOSITION identity\<close>, the fact every window premise
  (\<open>fw\<close>/\<open>lkw\<close>/\<open>okw\<close>) rests on:
  @{const newton_wcand} builds its candidate from the NODE poly, while the invariant builds the
  node poly from the ROOT \<open>rp\<close>. Two affine maps compose to one, so the identity is true; the
  content is that the \<open>same_den\<close> normalisation of the composite is the canonical one.

  \<^bold>\<open>It is a GENERALISATION, not new mathematics\<close>: @{thm [source] carried_init_child_left} is
  the instance \<open>m = 0\<close>, \<open>w = 1\<close>, \<open>dd = 2\<close>, and the window needs \<open>w = 4\<close>,
  \<open>dd = 2 ^ (2 ^ e + 2)\<close>.\<close>
section \<open>The per-state step discharge, arm by arm\<close>

text \<open>\<^bold>\<open>Shape, and why it is stated at an already-destructured state.\<close> Each lemma below is
  @{thm [source] hybrid_loop_expol}'s \<open>step\<close> premise for one arm, with the state's columns
  named. The \<open>\<And>s\<close> wrapper is a separate step: \<open>rp\<close> is a component of \<open>s\<close>, so under that
  binder every \<open>rp\<close>-mentioning premise here would be about an arbitrary \<open>rp\<close>, and nothing in
  @{const hybrid_state_invar} pins it --- @{const hybrid_trunc_coupling} and
  @{const hybrid_cs_coupling} relate the worklist nodes to \<open>rp\<close>, but never \<open>P\<close> to \<open>rp\<close>.

  \<^bold>\<open>The word caps are premises, not derivations.\<close> \<open>rp_pb\<close>/\<open>rp_gb\<close> are the root-length caps the
  \<open>X\<close>-bounds reduce to (@{const carried_init_same_den} preserves length), and they are discharged
  once at the keystone from \<open>lenb\<close>/\<open>rp_small\<close> rather than four times here.

  \<^bold>\<open>\<open>Pcoeffs\<close> is stated on \<open>coeffs P\<close>, not \<open>P\<close>\<close>, because that is the form both consumers need:
  @{thm [source] hybrid_node_count_dispatch} wants the root list, and the assemblies' \<open>P_eq\<close>
  (\<open>P = Poly (\<dots>)\<close>) follows from it by @{thm [source] Poly_coeffs}. Going the other way would need
  canonicity as a side condition; the keystone already carries it as \<open>canon\<close>.\<close>

lemma hybrid_step_discharge_discard:
  fixes P :: "int poly"
  assumes dpos: "0 < \<delta>"
    and lr0: "l0 < r0"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and rp_len: "0 < length rp"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and rp_gb: "4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp acc"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) acc"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    and count0: "carried_descartes_count
                   (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp) = 0"
    \<comment> \<open>\<^bold>\<open>The payload invariant\<close>, the fourth invariant conjunct --- threaded exactly as \<open>budinv\<close> is,
       and last so no existing \<open>[OF \<dots>]\<close> position moves.\<close>
    and payinv: "hybrid_pay_invar (lns, rns, ks) gs rp"
    \<comment> \<open>Pays for the pop's \<open>Q_small\<close>, as on the split arm. \<^bold>\<open>Last\<close>.\<close>
    and rp_small: "length rp < 1099511627776"
  shows "hybrid_loop_body_checked_monadic (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc))"
proof -
  have lne: "lns \<noteq> []" using cond by (simp add: hybrid_loop_cond_def)
  have Xdef: "carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp
            = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp" ..
  note nf = hybrid_node_facts_last[OF inv lne Xdef]
  have lenX: "length (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp) = length rp"
    by (simp add: truncate_length_carried_init_same_den)
  have lenQ: "length (last qtodo) = length rp"
    using cdlr_node_frame_len[OF nf(3)] lenX by simp
  \<comment> \<open>the node view is non-degenerate: @{const hybrid_cap_invar}'s own conjunct at the LAST
     index, which is where @{thm [source] last_conv_nth} is the bridge -- same step the discard
     assembly takes for its \<open>ab\<close>.\<close>
  have stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), acc)"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have ne: "ks \<noteq> []" "rns \<noteq> []" using lne VL by auto
  have ilast: "length ks - 1 < length ks" using ne(1) by simp
  \<comment> \<open>\<open>rns \<noteq> []\<close> must be in scope too, not just \<open>ks \<noteq> []\<close>: @{thm [source] last_conv_nth} is
     conditional on non-emptiness PER LIST, so without it \<open>last rns\<close> survives while \<open>last lns\<close>
     and \<open>last ks\<close> are rewritten, and the two sides no longer match.\<close>
  have ab: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
            < snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using hybrid_cap_invar_nondeg[OF capinv ilast] lne ne VL
    by (simp add: last_conv_nth)
  have abv: "(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
              snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
           = dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)" by simp
  have view_ne: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
                 \<noteq> snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using ab by simp
  \<comment> \<open>Here the concrete arm selection becomes the abstract one.\<close>
  have zero: "descartes_list_int
                (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
                (snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
                (coeffs P) = 0"
    using hybrid_node_count_dispatch(1)[OF lr0 Pcoeffs rp_len abv view_ne] count0 by simp
  show ?thesis
    by (rule hybrid_body_step_discard_assembled
    \<comment> \<open>\<open>nf(2)\<close> is an OBJECT implication (\<open>\<longrightarrow>\<close>, as the couplings state it) while the assembly's
       \<open>locked_exact\<close> is a META one (\<open>\<Longrightarrow>\<close>); without \<open>rule_format\<close> the \<open>OF\<close> reports
       \<open>no unifiers\<close> and names none of the fifteen premises.\<close>
              [OF safe inv capinv budinv cond Xdef count0 zero dpos kcap kdepth _ _
                  nf(1) nf(2)[rule_format] payinv Pcoeffs])
       (use lenX rp_pb rp_gb lenQ rp_small in simp_all)
qed


text \<open>\<^bold>\<open>The accept arm.\<close> Same projection as discard. \<open>safe\<close>\<open>'\<close> is derived, from
  @{thm [source] hybrid_loop_safe_invar_pop_all} at the original accumulator plus
  @{thm [source] hybrid_loop_safe_invar_acc_swap}. The swap's \<open>pushable\<close> input is exactly what
  @{const hybrid_budget_invar}'s accumulator conjunct pays for
  (@{thm [source] hybrid_budget_invar_acc_grown}).\<close>

lemma hybrid_step_discharge_accept:
  fixes P :: "int poly"
  assumes lr0: "l0 < r0"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and rp_len: "0 < length rp"
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and rp_gb: "4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and count1: "carried_descartes_count
                   (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp) = 1"
    \<comment> \<open>\<^bold>\<open>The payload invariant\<close>, the fourth invariant conjunct --- threaded exactly as \<open>budinv\<close> is.\<close>
    and payinv: "hybrid_pay_invar (lns, rns, ks) gs rp"
    \<comment> \<open>\<^bold>\<open>The four \<open>safe\<close>\<open>'\<close> needs\<close>, \<^bold>\<open>last\<close> --- the same set the discard
       arm carries, since \<open>safe\<close>\<open>'\<close> is @{thm [source] hybrid_loop_safe_invar_pop_all}
       at a grown accumulator.\<close>
    and dpos: "0 < \<delta>"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>Pays for the pop's \<open>Q_small\<close>. \<^bold>\<open>Last\<close>.\<close>
    and rp_small: "length rp < 1099511627776"
  shows "hybrid_loop_body_checked_monadic
           (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have lne: "lns \<noteq> []" using cond by (simp add: hybrid_loop_cond_def)
  have Xdef: "carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp
            = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp" ..
  note nf = hybrid_node_facts_last[OF inv lne Xdef]
  have lenX: "length (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp) = length rp"
    by (simp add: truncate_length_carried_init_same_den)
  have lenQ: "length (last qtodo) = length rp"
    using cdlr_node_frame_len[OF nf(3)] lenX by simp
  have stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have ne: "ks \<noteq> []" "rns \<noteq> []" using lne VL by auto
  have ilast: "length ks - 1 < length ks" using ne(1) by simp
  have ab: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
            < snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using hybrid_cap_invar_nondeg[OF capinv ilast] lne ne VL
    by (simp add: last_conv_nth)
  have abv: "(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
              snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
           = dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)" by simp
  have view_ne: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
                 \<noteq> snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using ab by simp
  have one: "descartes_list_int
               (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
               (snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
               (coeffs P) = 1"
    using hybrid_node_count_dispatch(2)[OF lr0 Pcoeffs rp_len abv view_ne] count1 by simp
  \<comment> \<open>\<^bold>\<open>\<open>safe\<close>\<open>'\<close>, derived\<close>: pop at the original accumulator, then swap in the grown one.
     The swap's two inputs are the accumulator's own length alignment and the \<open>pushable\<close> that
     @{thm [source] hybrid_budget_invar_acc_grown} pays for --- which is why
     @{const hybrid_budget_invar} carries an accumulator conjunct at all.\<close>
  have pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  note Pu = pre[unfolded hybrid_loop_step_pre_def]
  have cpl: "hybrid_trunc_coupling (lns, rns, ks) qtodo gs rp"
    using inv unfolding hybrid_refine_invar_def by simp
  have popsafe: "hybrid_loop_safe_invar
                   (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                     butlast es, butlast ss, butlast cs, butlast gs, rp), (al, ar, ak))"
    by (rule hybrid_loop_safe_invar_pop_all[OF stinv pre cpl capinv dpos rp_len rp_bound
                                                 kcap kdepth])
  have ACL: "length al = length ar" "length ar = length ak"
    using stinv unfolding hybrid_loop_state_invar_def dyadic_interval_vec_invar_def
    by (simp_all add: Let_def)
  have accinv': "dyadic_interval_vec_invar
                   (al @ [last lns], ar @ [last rns], ak @ [last ks])"
    using ACL unfolding dyadic_interval_vec_invar_def by simp
  have accpush': "dyadic_interval_vec_pushable
                    (al @ [last lns], ar @ [last rns], ak @ [last ks])"
    using hybrid_budget_invar_acc_grown[OF budinv lne VL(1) VL(2)] ACL
    unfolding dyadic_interval_vec_pushable_def by simp
  have safe': "hybrid_loop_safe_invar
                 (((butlast lns, butlast rns, butlast ks), butlast qtodo,
                   butlast es, butlast ss, butlast cs, butlast gs, rp),
                  (al @ [last lns], ar @ [last rns], ak @ [last ks]))"
    by (rule hybrid_loop_safe_invar_acc_swap[OF popsafe accinv' accpush'])
  show ?thesis
    by (rule hybrid_body_step_accept_assembled
              [OF safe inv capinv budinv cond Xdef count1 one _ _
                  nf(1) nf(2)[rule_format] safe' payinv Pcoeffs])
       (use lenX rp_pb rp_gb lenQ rp_small in simp_all)
qed

text \<open>\<^bold>\<open>The two word caps a locked pop needs.\<close> Both are freestanding arithmetic, stated as
  lemmas so that the arm proofs discharge them by a rule rather than by a tactic inside a
  40-premise apply chain.\<close>
lemma v_guard_ceiling_cap:
  assumes pay: "hybrid_child_pay_ok l1 k1 r1 rp g"
    and small: "length rp < 1099511627776"
  shows "max g 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
proof -
  have ceil: "g \<le> 4398046511104 + length rp"
    using pay unfolding hybrid_child_pay_ok_def by simp
  have "max g 4398046511104 \<le> 4398046511104 + length rp"
    using ceil by (simp add: max.bounded_iff)
  thus ?thesis using small by (simp add: max_snat_def)
qed

lemma v_lock_payload_cap:
  assumes v: "v \<le> length rp" and small: "length rp < 1099511627776"
  shows "4398046511104 + v + length rp < max_snat LENGTH(gmp_poly_len)"
  using assms by (simp add: max_snat_def)

text \<open>\<^bold>\<open>The split arm.\<close> Everything except \<open>arm\<close> is projected from the invariant; \<open>arm\<close> ---
  the @{const hybrid_loop_step_args_monadic} refinement with its 42 premises --- is derived
  inside the proof from its residual goals. \<open>wide\<close> is the keystone's \<open>small_fast\<close> read
  contrapositively against \<open>v2\<close>: a node carrying two or more sign variations cannot be
  \<open>\<delta>\<close>-small.\<close>

lemma hybrid_step_discharge_split:
  fixes P :: "int poly"
  assumes dpos: "0 < \<delta>"
    and lr0: "l0 < r0"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> real_of_rat b - real_of_rat a \<le> \<delta> \<Longrightarrow>
                       descartes_list_int a b (coeffs P) \<le> 1"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and rp_len: "0 < length rp"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and count2: "2 \<le> carried_descartes_count
                       (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp)"
    \<comment> \<open>\<^bold>\<open>The arm SELECTOR's second half\<close> --- \<open>count2\<close> picks \<open>cnt \<ge> 2\<close>, this picks the gate-CLOSED
       fork. Both come from the case split in \<open>hybrid_step_all_cols\<close>, which is the
       only place that knows which arm ran.\<close>
    and gate_closed: "\<not> newton_pol_gate_len (length (last qtodo)) (last es) (last ks) (last ss)"
    \<comment> \<open>\<^bold>\<open>The root caps \<open>arm\<close> needs.\<close> \<open>rp_pb\<close>/\<open>rp_gb\<close>/\<open>rp_small\<close> are the discard
       arm's own three, and \<open>g_room\<close> is the keystone premise that makes the truncation layer's
       saturation band \<open>2\<^sup>4\<^sup>0 \<le> g < 2\<^sup>4\<^sup>2\<close> unreachable --- it is what turns
       @{const hybrid_trunc_coupling}'s depth disjunct into \<open>g_tri\<close>'s first one.\<close>
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and rp_gb: "4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and g_room: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   (kD + 1) * length rp < 1099511627776"
    \<comment> \<open>\<^bold>\<open>The payload invariant\<close>, the fourth invariant conjunct --- threaded exactly as \<open>budinv\<close> is,
       and last so no existing \<open>[OF \<dots>]\<close> position moves.\<close>
    and payinv: "hybrid_pay_invar (lns, rns, ks) gs rp"
  shows "hybrid_loop_body_checked_monadic
           (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have lne: "lns \<noteq> []" using cond by (simp add: hybrid_loop_cond_def)
  have Xdef: "carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp
            = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp" ..
  have stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have ne: "ks \<noteq> []" "rns \<noteq> []" using lne VL by auto
  have ilast: "length ks - 1 < length ks" using ne(1) by simp
  have ab: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
            < snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using hybrid_cap_invar_nondeg[OF capinv ilast] lne ne VL
    by (simp add: last_conv_nth)
  have abv: "(fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)),
              snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
           = dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)" by simp
  have view_ne: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
                 \<noteq> snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using ab by simp
  have v2: "2 \<le> descartes_list_int
                  (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
                  (snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
                  (coeffs P)"
    using hybrid_node_count_dispatch(3)[OF lr0 Pcoeffs rp_len abv view_ne] count2 by simp
  \<comment> \<open>\<open>wide\<close>: \<open>small_fast\<close> contrapositively. Stated as a \<open>rule\<close>-free \<open>linarith\<close> step because the
     only arithmetic involved is \<open>\<not> (w \<le> \<delta>) \<Longrightarrow> \<delta> < w\<close> on reals.\<close>
  have wide: "\<delta> < real_of_rat (snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
                - real_of_rat (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence le: "real_of_rat (snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
             - real_of_rat (fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
             \<le> \<delta>" by simp
    from small_fast[OF ab le] v2 show False by simp
  qed
  have P_eq: "P = Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)"
    using Pcoeffs by (metis Poly_coeffs)
  \<comment> \<open>\<^bold>\<open>From here down is the \<open>arm\<close> discharge\<close> --- the 41 residual goals the rule leaves.
     All but four are \<open>hybrid_loop_step_pre\<close> conjuncts or length bridges; the four that are
     not are \<open>g_tri\<close>, \<open>gcap_rp\<close>, \<open>gcap_lock\<close> and \<open>lrne\<close>, and each has its own named step below.\<close>
  note nf = hybrid_node_facts_last[OF inv lne Xdef]
  have pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  \<comment> \<open>\<^bold>\<open>No \<open>simplified\<close>\<close>: it normalises \<open>step_pre\<close>'s conjuncts away from the shapes the arm
     lemma states them in --- the discard assembly's note, and it applies verbatim here.\<close>
  note Pu = pre[unfolded hybrid_loop_step_pre_def]
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have ne5: "qtodo \<noteq> []" "es \<noteq> []" "ss \<noteq> []" "cs \<noteq> []" "gs \<noteq> []"
    using lne SL by auto
  have lenX: "length (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp) = length rp"
    by (simp add: truncate_length_carried_init_same_den)
  have lenQ: "length (last qtodo) = length rp"
    using cdlr_node_frame_len[OF nf(3)] lenX by simp
  \<comment> \<open>\<^bold>\<open>\<open>g_tri\<close>: the coupling's depth disjunct, closed by \<open>g_room\<close>.\<close> The k-potential bounds the
     popped node's depth, \<open>g_room\<close> turns that into \<open>(k+1)\<cdot>length rp < 2\<^sup>4\<^sup>0\<close>, and the coupling's
     first disjunct then lands strictly below \<open>2\<^sup>4\<^sup>0\<close>. The second disjunct is the lock sentinel
     and passes through --- which is exactly what makes the LOCKED pop admissible.\<close>
  have depthle: "int (last ks) \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_le[OF capinv ilast] lne ne VL by (simp add: last_conv_nth)
  have g_tri: "last gs < 1099511627776 \<or> 4398046511104 \<le> last gs"
    using nf(4) g_room[OF depthle] by linarith
  \<comment> \<open>The payload invariant's conjunct at the popped node, and the two caps it pays for.\<close>
  have ig: "length gs - 1 < length gs" using ne5(5) by simp
  have payg: "hybrid_child_pay_ok (last lns) (last ks) (last rns) rp (last gs)"
    using hybrid_pay_invarD[OF payinv ig] lne ne ne5 SL VL
    by (simp add: last_conv_nth)
  have vlen: "carried_descartes_count
                (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp) \<le> length rp"
    using carried_descartes_count_le_length_cn[of
            "carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"] lenX by simp
  \<comment> \<open>the node's non-degeneracy on the COLUMNS, which is what the payload invariant's \<open>mono\<close>
     needs; \<open>ab\<close> has it on the view and @{thm [source] hybrid_node_lr_of_view} is the transport.\<close>
  have lrne: "last lns < last rns"
    by (rule hybrid_node_lr_of_view[OF lr0 abv ab])
  have arm: "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
       \<le> SPEC (\<lambda>(wl, acc').
           (poly (map_poly rat_of_int (Poly (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp))) (1 / 2) = 0 \<longrightarrow>
              acc' = (al @ [last lns + last rns], ar @ [last lns + last rns],
                      ak @ [last ks + 1])) \<and>
           (poly (map_poly rat_of_int (Poly (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp))) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
           hybrid_split_wl (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp) (butlast lns) (butlast rns) (butlast ks) (butlast qtodo) (butlast es) (butlast ss) (butlast cs) (butlast gs) rp (last lns) (last rns) (last ks) (last es) (last ss) wl)"
    by (rule hybrid_loop_step_args_split
              [OF tinv lne VL(1) VL(2) ne5(1) ne5(2) ne5(3) ne5(4) ne5(5)
                  _ _ _ _ _ _ Xdef nf(1) nf(2)[rule_format] nf(3) g_tri count2 gate_closed
                  v_guard_ceiling_cap[OF payg rp_small]
                  v_lock_payload_cap[OF vlen rp_small]
                  _ _ _ _ _ _ _ _ _ rp_small rp_pb _ _ _ _ _ nf(4) payg lrne])
       (insert Pu lenX lenQ rp_pb rp_gb rp_small lne ne ne5, simp_all)
  \<comment> \<open>\<^bold>\<open>The payload invariant at the PUSHED state\<close> --- pop then two-child push, on the atoms the arm exports.\<close>
  have paypre: "hybrid_pay_invar (butlast lns, butlast rns, butlast ks) (butlast gs) rp"
    by (rule hybrid_pay_invar_pop[OF payinv]) (use SL VL in simp_all)
  have paypush: "\<And>gl gr.
        hybrid_child_pay_ok (2 * last lns) (last ks + 1) (last lns + last rns) rp gl \<Longrightarrow>
        hybrid_child_pay_ok (last lns + last rns) (last ks + 1) (2 * last rns) rp gr \<Longrightarrow>
        hybrid_pay_invar
          (butlast lns @ [2 * last lns, last lns + last rns],
           butlast rns @ [last lns + last rns, 2 * last rns],
           butlast ks @ [last ks + 1, last ks + 1])
          (butlast gs @ [gl, gr]) rp"
    by (rule hybrid_pay_invar_push2[OF paypre]) (use SL VL in simp_all)
  show ?thesis
    by (rule hybrid_body_step_split_assembled
              [OF safe inv capinv budinv cond Xdef lr0 P0 p0 sf v2 dpos wide P_eq kcap kdepth arm paypush Pcoeffs])
qed


text \<open>\<^bold>\<open>The window arm.\<close> \<open>v2\<close>, \<open>wide\<close> and \<open>P_eq\<close> are projected from the invariant as on the
  other arms; the window facts (\<open>win\<close>, \<open>wsub\<close>, \<open>wprop\<close>, \<open>mu_w\<close>), the guard facts \<open>gw\<close>/\<open>jw\<close> and
  \<open>arm\<close> are derived inside the proof. The premises specific to this arm are the selector
  \<open>gate_open\<close> and the two naming premises \<open>Iw_def\<close>/\<open>dec_def\<close>.

  \<open>Iw\<close> and \<open>dec\<close> are free variables: they are the abstract window data the pick determines.
  An existential over them here would hide the obligation rather than discharge it; the naming
  premises pin both to the arm's own pick instead.\<close>

lemma hybrid_step_discharge_window:
  \<comment> \<open>\<^bold>\<open>No type annotation on \<open>Iw\<close>.\<close> The pick index \<open>m\<close> is an \<open>int\<close> --- \<open>npush_w\<close> forms
     \<open>m * (last rns - last lns)\<close> over the \<open>int\<close> coordinate columns --- so \<open>Iw :: int \<Rightarrow> rat \<times> rat\<close>.
     Writing \<open>nat \<Rightarrow> rat \<times> rat\<close> makes \<open>win\<close> (the first premise mentioning \<open>Iw\<close>) unmatchable, and
     the \<open>OF\<close> then reports \<open>no unifiers\<close> for the whole rule without naming a premise.\<close>
  fixes P :: "int poly"
  assumes dpos: "0 < \<delta>"
    and lr0: "l0 < r0"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> real_of_rat b - real_of_rat a \<le> \<delta> \<Longrightarrow>
                       descartes_list_int a b (coeffs P) \<le> 1"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and rp_len: "0 < length rp"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and X_eq: "X = carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp"
    and abnode: "dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks) = (a, b)"
    and edef: "e = last es" and dkdef: "dk = last ks" and sdef: "sv0 = last ss"
    and count2: "2 \<le> carried_descartes_count X"
    \<comment> \<open>\<^bold>\<open>\<open>win\<close>/\<open>wsub\<close>/\<open>wprop\<close>/\<open>mu_w\<close> are derived below, not assumed.\<close> What replaces
       them is not a weaker assumption but a naming one: the window \<open>Iw\<close> and the gate pair \<open>dec\<close>
       are free variables of the assembly, and once the four facts are derived, something has to
       say which window and which gate they are derived for. Both are pinned to the arm's own
       pick, so both are discharged by \<open>refl\<close> at any call site.\<close>
    and Iw_def: "\<And>m. Iw m = dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                     last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                    Suc (Suc (last ks + 2 ^ last es)))"
    and dec_def: "dec = (True, True)"
    \<comment> \<open>\<^bold>\<open>\<open>npush_w\<close> and \<open>vpush_w\<close> are DISCHARGED below\<close> --- \<open>hybrid_npush_w_satisfiable\<close> and
       @{thm [source] hybrid_alpha_views_append1}, both of which want exactly \<open>Iw_def\<close> plus the
       column-length alignment the state invariant already carries.\<close>
    \<comment> \<open>\<^bold>\<open>\<open>gw\<close>, \<open>muW\<close> and \<open>ndW\<close> are DISCHARGED below too.\<close> \<open>gw\<close>'s second disjunct
       \<open>2\<^sup>4\<^sup>2 \<le> 2\<^sup>4\<^sup>2 + v\<close> is a tautology on \<open>nat\<close> --- it was never an obligation, only a premise
       that looked like one. \<open>muW\<close> and \<open>ndW\<close> are \<open>mu_w\<close> and \<open>wprop\<close> read through \<open>Iw_def\<close>: the
       node view they name IS \<open>Iw m\<close>, and the right-hand side of \<open>muW\<close> is \<open>(a, b)\<close> by \<open>abnode\<close>.
       They differed from \<open>mu_w\<close>/\<open>wprop\<close> only in being written out rather than projected.\<close>
    \<comment> \<open>\<^bold>\<open>The arm selector\<close> --- \<open>count2\<close> picks \<open>cnt \<ge> 2\<close>, this picks the gate-open fork.
       \<open>jw\<close> is derived from it: \<open>newton_pol_gate_len\<close> conjoins \<open>e \<le> newton_pol_ecap\<close>, and
       \<open>2 ^ \<cdot>\<close> is monotone.\<close>
    and gate_open: "newton_pol_gate_len (length (last qtodo)) (last es) (last ks) (last ss)"
    \<comment> \<open>\<^bold>\<open>The root caps \<open>arm\<close> needs\<close>, the split twin's four verbatim --- \<open>g_room\<close> is what
       replaces \<open>g_small\<close>, which is now DERIVED (and, being the unlocked-only form, was the
       premise that excluded the window arm's OWN children).\<close>
    and rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    and rp_gb: "4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    and rp_small: "length rp < 1099511627776"
    and g_room: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                   (kD + 1) * length rp < 1099511627776"
    \<comment> \<open>\<^bold>\<open>The payload invariant\<close>, the fourth invariant conjunct --- threaded exactly as \<open>budinv\<close> is,
       and last so no existing \<open>[OF \<dots>]\<close> position moves.\<close>
    and payinv: "hybrid_pay_invar (lns, rns, ks) gs rp"
  shows "hybrid_loop_body_checked_monadic
           (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have lne: "lns \<noteq> []" using cond by (simp add: hybrid_loop_cond_def)
  have stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have ne: "ks \<noteq> []" "rns \<noteq> []" using lne VL by auto
  have ilast: "length ks - 1 < length ks" using ne(1) by simp
  have ab: "a < b"
    using hybrid_cap_invar_nondeg[OF capinv ilast] lne ne VL abnode
    by (simp add: last_conv_nth)
  have abv: "(a, b) = dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)"
    using abnode by simp
  have v2: "2 \<le> descartes_list_int a b (coeffs P)"
    using hybrid_node_count_dispatch(3)[OF lr0 Pcoeffs rp_len abv] ab count2 X_eq by simp
  have wide: "\<delta> < real_of_rat b - real_of_rat a"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence le: "real_of_rat b - real_of_rat a \<le> \<delta>" by simp
    from small_fast[OF ab le] v2 show False by simp
  qed
  have P_eq: "P = Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)"
    using Pcoeffs by (metis Poly_coeffs)
  \<comment> \<open>\<^bold>\<open>The four window facts, derived.\<close> \<open>win\<close> is
     \<open>hybrid_window_pick_abs_node\<close> --- i.e. bail's own
     @{thm [source] newton_window_pick_bail_abs} instantiated through the middle repr --- and the
     other three are \<open>hybrid_window_geometry_node\<close> applied to it.
     \<^bold>\<open>The two spellings of the child's coordinates\<close> (\<open>2\<^sup>2\<^sup>^\<^sup>e\<^sup>+\<^sup>2\<close> vs \<open>4 \<cdot> 2\<^sup>2\<^sup>^\<^sup>e\<close>, \<open>k + (2\<^sup>e + 2)\<close> vs
     \<open>Suc (Suc (k + 2\<^sup>e))\<close>) are the same term post-\<open>simp\<close>; \<open>Iw_def\<close> is stated in the form the
     push premises use, so the normalisation happens once, here.\<close>
  have rp2: "Suc 0 < length rp"
  proof -
    have "length (coeffs P) = Suc (degree P)" using P0 by (simp add: length_coeffs_degree)
    moreover have "length (coeffs P) = length rp"
      by (simp add: Pcoeffs truncate_length_carried_init_same_den)
    ultimately show ?thesis using p0 by simp
  qed
  have win: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                        = Some (m, cand) \<Longrightarrow>
               try_window_bail_int (snd (dec :: bool \<times> bool)) a b (N_of e) P
                 (descartes_list_int a b (coeffs P)) = Some (Iw m)"
  proof -
    fix m cand
    assume pk: "newton_window_pick_bail (carried_descartes_count X) (last es) X = Some (m, cand)"
    show "try_window_bail_int (snd (dec :: bool \<times> bool)) a b (N_of e) P
            (descartes_list_int a b (coeffs P)) = Some (Iw m)"
      using hybrid_window_pick_abs_node[OF lr0 Pcoeffs rp2 abnode[symmetric] ab X_eq pk]
      by (simp add: dec_def edef Iw_def power_add)
  qed
  have wsub: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                         = Some (m, cand) \<Longrightarrow> alr_ivl_pss (fst (Iw m), snd (Iw m)) (a, b)"
    and wprop: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                           = Some (m, cand) \<Longrightarrow> fst (Iw m) < snd (Iw m)"
    and mu_w: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow>
                 dyadic_iv_interval_mu \<delta> (Iw m) < dyadic_iv_interval_mu \<delta> (a, b)"
    using hybrid_window_geometry_node[OF dpos ab wide P0 win] by blast+
  have gw: "\<And>v :: nat. 4398046511104 + v \<le> (Suc (Suc (last ks + 2 ^ last es)) + 1) * length rp
                 \<or> 4398046511104 \<le> 4398046511104 + v" by simp
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have ne5: "qtodo \<noteq> []" "es \<noteq> []" "ss \<noteq> []" "cs \<noteq> []" "gs \<noteq> []"
    using lne SL by auto
  have pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  note Pu = pre[unfolded hybrid_loop_step_pre_def]
  note NF = hybrid_node_facts_last[OF inv lne X_eq]
  \<comment> \<open>\<^bold>\<open>Four derivations\<close> --- \<open>jw\<close>, \<open>g_tri\<close>, \<open>exact0\<close> and (below) \<open>arm\<close>/\<open>paypush_s\<close>, each
     from a one-step source. There is no \<open>g_small\<close> premise, which is what admits a locked pop on
     this arm.\<close>
  have jw: "int (2 ^ last es + 2) \<le> int (2 ^ newton_pol_ecap + 2)"
    using gate_open unfolding newton_pol_gate_len_def by simp
  have depthle: "int (last ks) \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_le[OF capinv ilast] lne ne VL by (simp add: last_conv_nth)
  have g_tri: "last gs < 1099511627776 \<or> 4398046511104 \<le> last gs"
    using NF(4) g_room[OF depthle] by linarith
  \<comment> \<open>\<open>node_frame X Q 0\<close> IS \<open>X = Q\<close> by definition --- no lemma needed, only the unfolding.\<close>
  have exact0: "last gs = 0 \<longrightarrow> last qtodo = X"
    using NF(3) unfolding node_frame_def by auto
  have lenX: "length X = length rp"
    by (simp add: X_eq truncate_length_carried_init_same_den)
  have BL: "length (butlast lns) = length (butlast rns)"
     "length (butlast rns) = length (butlast ks)"
     "length (butlast es) = length (butlast ks)"
     "length (butlast ss) = length (butlast ks)"
    using VL SL by simp_all
  have npush_w: "\<And>m. hybrid_alpha_nodes l0 r0 k0
                   (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)],
                    butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)],
                    butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
                   (butlast es @ [last es + 1]) (butlast ss @ [last ss])
                 = hybrid_alpha_nodes l0 r0 k0
                     (butlast lns, butlast rns, butlast ks) (butlast es) (butlast ss)
                   @ [(fst (Iw m), snd (Iw m), e + 1, dk + (2 ^ e + 2), sv0)]"
    by (rule hybrid_npush_w_satisfiable[OF BL(1) BL(2) BL(3) BL(4) Iw_def edef dkdef sdef])
  have vpush_w: "\<And>m. hybrid_alpha_views l0 r0 k0
                   (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)],
                    butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)],
                    butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
                 = hybrid_alpha_views l0 r0 k0 (butlast lns, butlast rns, butlast ks)
                   @ [(fst (Iw m), snd (Iw m))]"
    by (simp add: hybrid_alpha_views_append1[OF BL(1) BL(2)] Iw_def)
  have muW: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                        = Some (m, cand) \<Longrightarrow>
               dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv_of l0 r0 k0
                  ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                    last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                   Suc (Suc (last ks + 2 ^ last es))))
               < dyadic_iv_interval_mu \<delta>
                   (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using mu_w by (simp add: Iw_def abnode)
  have ndW: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                        = Some (m, cand) \<Longrightarrow>
               fst (dyadic_iv_node_iv_of l0 r0 k0
                  ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                    last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                   Suc (Suc (last ks + 2 ^ last es))))
               < snd (dyadic_iv_node_iv_of l0 r0 k0
                  ((last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns),
                    last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)),
                   Suc (Suc (last ks + 2 ^ last es))))"
    using wprop by (simp add: Iw_def)
  \<comment> \<open>\<^bold>\<open>\<open>safe_w\<close>, DERIVED.\<close> @{thm [source] hybrid_loop_safe_invar_push1_all} at the window
     child. Its only non-bookkeeping input is the cap invariant at the PUSHED state, which is
     @{thm [source] hybrid_cap_invar_push1} on the \<open>muW\<close>/\<open>jw\<close>/\<open>ndW\<close> above --- so the k-potential
     survives the window's \<open>k' = k + 2\<^sup>e + 2\<close> jump for the same reason bail's does: one \<open>\<mu>\<close> level of
     budget is worth \<open>C\<close>. \<open>qlen\<close> is the candidate's length, and the candidate is a
     @{const carried_init_same_den} of \<open>rp\<close> (@{thm [source] newton_window_pick_bail_cand}), so it
     is \<open>length rp\<close> on the nose.\<close>
  have rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    using pre unfolding hybrid_loop_step_pre_def by simp
  \<comment> \<open>\<^bold>\<open>No \<open>\<And>m\<close> inside the \<open>for m\<close>.\<close> An inner binder shadows the one \<open>pk\<close> fixes, and then
     \<open>intro\<close> generalises the conclusion over a FRESH \<open>ma\<close> while the \<open>\<mu>\<close>/non-degeneracy hypotheses
     stay at the outer \<open>m\<close> --- two subgoals that look identical to their own premises.\<close>
  have capW: "hybrid_cap_invar \<delta> l0 r0 k0
                (butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)],
                 butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)],
                 butlast ks @ [Suc (Suc (last ks + 2 ^ last es))])
                (butlast ss @ [last ss])"
    if pk: "newton_window_pick_bail (carried_descartes_count X) (last es) X = Some (m, cand)"
    for m cand
    using ne VL SL muW[OF pk] ndW[OF pk] jw
    by (intro hybrid_cap_invar_push1[OF capinv _ _ _ _ _ _ jw]) simp_all
  have qlen: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                          = Some (m, cand) \<Longrightarrow> length cand = length rp"
  proof -
    fix m cand
    assume pk: "newton_window_pick_bail (carried_descartes_count X) (last es) X = Some (m, cand)"
    have "cand = carried_init_same_den m (2 ^ (2 ^ last es + 2)) (m + 4) X"
      using newton_window_pick_bail_cand[OF pk] by (simp add: newton_wcand_def)
    thus "length cand = length rp"
      by (simp add: X_eq truncate_length_carried_init_same_den)
  qed
  \<comment> \<open>The payload invariant's conjunct at the popped node, the ceiling it pays for, and the
     column-level non-degeneracy the split children's count monotonicity needs --- the split twin's three.\<close>
  have ig: "length gs - 1 < length gs" using ne5(5) by simp
  have payg: "hybrid_child_pay_ok (last lns) (last ks) (last rns) rp (last gs)"
    using hybrid_pay_invarD[OF payinv ig] lne ne ne5 SL VL
    by (simp add: last_conv_nth)
  have vlen: "carried_descartes_count X \<le> length rp"
    using carried_descartes_count_le_length_cn[of X] lenX by simp
  have lenQ: "length (last qtodo) = length rp"
    using cdlr_node_frame_len[OF NF(3)] lenX by simp
  have lrne: "last lns < last rns"
    by (rule hybrid_node_lr_of_view[OF lr0 abnode[symmetric] ab])
  \<comment> \<open>\<^bold>\<open>The nine window-specific caps\<close> --- everything the shared \<open>(insert Pu \<dots>)\<close> pass does NOT
     close. Seven are the gate's own exponent bounds (\<open>newton_pol_ecap = 8\<close>, so
     \<open>2\<^sup>e + 2 \<le> 258\<close> by @{thm [source] newton_pol_ecap_width}) and the k-potential read at the
     popped node; the other two are \<open>pushable2 \<Rightarrow> pushable\<close> and a \<open>ks\<close>-column cap.\<close>
  have X_ne1: "1 < length X"
    using count2 carried_descartes_count_le_length_cn[of X] by simp
  have eecap: "last es \<le> newton_pol_ecap"
    using gate_open unfolding newton_pol_gate_len_def by simp
  have ecapv: "last es < LENGTH(gmp_poly_len)"
    using eecap by (simp add: newton_pol_ecap_def)
  have ew: "(2::nat) ^ last es + 2 \<le> 258" by (rule newton_pol_ecap_width[OF eecap])
  have ecap2: "2 ^ last es + 2 < max_snat LENGTH(gmp_poly_len)"
    using ew by (simp add: max_snat_def)
  have ecap3: "last es + 1 < max_snat LENGTH(gmp_poly_len)"
    using eecap by (simp add: newton_pol_ecap_def max_snat_def)
  \<comment> \<open>the k-potential with the popped node's own \<open>\<mu>\<close> spent: a live node has \<open>\<mu> \<ge> 1\<close>, so the
     potential has \<open>C = 258\<close> of headroom above the node's depth. That is what pays
     for the window's \<open>k' = k + 2\<^sup>e + 2\<close> jump (\<open>\<le> 258\<close> under the gate) and for the degree
     product below --- exactly the gate's own bound.\<close>
  have bud2: "1 \<le> dyadic_iv_interval_mu \<delta>
                     (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    by (rule dyadic_iv_interval_mu_ge_1[OF dpos]) (use abnode ab in simp)
  have kbud: "int (last ks) + int (2 ^ newton_pol_ecap + 2)
                * int (dyadic_iv_interval_mu \<delta>
                    (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))
              \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_nth[OF capinv ilast] lne ne VL by (simp add: last_conv_nth)
  have k258: "int (last ks) + 258 \<le> hybrid_root_potential \<delta> k0"
  proof -
    have "(258::int) * 1 \<le> 258 * int (dyadic_iv_interval_mu \<delta>
                    (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks)))"
      using bud2 by (intro mult_left_mono) simp_all
    thus ?thesis using kbud by (simp add: newton_pol_ecap_def)
  qed
  have kcap2: "last ks + (2 ^ last es + 2) < max_snat LENGTH(gmp_poly_len)"
    using k258 kcap ew by simp
  have p258: "int (2 ^ newton_pol_ecap + 2) \<le> hybrid_root_potential \<delta> k0"
    using k258 by (simp add: newton_pol_ecap_def)
  have gate4: "(2 ^ last es + 2) * (length X - 1) < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "(2 ^ last es + 2) * (length X - 1) \<le> (2 ^ newton_pol_ecap + 2) * (length rp - 1)"
      using ew lenX by (simp add: newton_pol_ecap_def mult_le_mono1)
    thus ?thesis using kdepth[OF p258] by simp
  qed
  have vcap1: "int (carried_descartes_count X) < max_sint LENGTH(gmp_long_len)"
    using vlen rp_small by (simp add: max_sint_def)
  have push2b: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    using Pu by simp
  have push1b: "dyadic_interval_vec_pushable (butlast lns, butlast rns, butlast ks)"
    using push2b
    unfolding dyadic_interval_vec_pushable_def dyadic_interval_vec_pushable2_def
    by (simp add: Let_def)
  have kslen: "length (butlast ks) + 1 < max_snat LENGTH(gmp_poly_len)"
    using push2b unfolding dyadic_interval_vec_pushable2_def by (simp add: Let_def)
  have arm: "hybrid_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
              \<le> SPEC (\<lambda>(wl, acc').
           ((poly (map_poly rat_of_int (Poly X)) (1 / 2) = 0 \<longrightarrow>
                 acc' = (al @ [last lns + last rns], ar @ [last lns + last rns], ak @ [last ks + 1])) \<and>
              (poly (map_poly rat_of_int (Poly X)) (1 / 2) \<noteq> 0 \<longrightarrow> acc' = (al, ar, ak)) \<and>
                            hybrid_split_wl X (butlast lns) (butlast rns) (butlast ks) (butlast qtodo) (butlast es) (butlast ss) (butlast cs) (butlast gs) rp (last lns) (last rns) (last ks) (last es) (last ss) wl)
           \<or>
           (\<exists>m cand v. acc' = (al, ar, ak) \<and>
              v = carried_descartes_count X \<and>
              carried_descartes_count cand = v \<and>
              newton_window_pick_bail v (last es) X = Some (m, cand) \<and>
              wl = ((butlast lns @ [last lns * 2 ^ (2 ^ last es + 2) + m * (last rns - last lns)],
                     butlast rns @ [last lns * 2 ^ (2 ^ last es + 2) + (m + 4) * (last rns - last lns)],
                     butlast ks @ [last ks + (2 ^ last es + 2)]),
                    butlast qtodo @ [cand], butlast es @ [last es + 1], butlast ss @ [last ss],
                    butlast cs @ [v + 2], butlast gs @ [4398046511104 + v], rp)))"
    by (rule hybrid_loop_step_args_window
              [OF tinv lne VL(1) VL(2) ne5(1) ne5(2) ne5(3) ne5(4) ne5(5)
                  gate_open count2 g_tri NF(4) X_eq NF(1) NF(2)[rule_format] exact0 NF(3)
                  _ _ _ _ _ _ _ _ _ X_ne1 _ _ _ ecapv ecap2 ecap3 kcap2 gate4 vcap1 _
                  v_guard_ceiling_cap[OF payg rp_small]
                  v_lock_payload_cap[OF vlen rp_small]
                  _ _ rp_small rp_pb _ _ _ _ _ _ push1b kslen _ payg lrne])
       (insert Pu lenX lenQ rp_pb rp_gb rp_small lne ne ne5 vlen, simp_all)
  \<comment> \<open>\<^bold>\<open>The payload invariant at the REJECT half's pushed state\<close> --- the gate-open arm falls
     through to the split at the lock guard, so it pushes TWO children and needs the split twin's step.\<close>
  have paypre: "hybrid_pay_invar (butlast lns, butlast rns, butlast ks) (butlast gs) rp"
    by (rule hybrid_pay_invar_pop[OF payinv]) (use SL VL in simp_all)
  have paypush_s: "\<And>gl gr.
        hybrid_child_pay_ok (2 * last lns) (last ks + 1) (last lns + last rns) rp gl \<Longrightarrow>
        hybrid_child_pay_ok (last lns + last rns) (last ks + 1) (2 * last rns) rp gr \<Longrightarrow>
        hybrid_pay_invar
          (butlast lns @ [2 * last lns, last lns + last rns],
           butlast rns @ [last lns + last rns, 2 * last rns],
           butlast ks @ [last ks + 1, last ks + 1])
          (butlast gs @ [gl, gr]) rp"
    by (rule hybrid_pay_invar_push2[OF paypre]) (use SL VL in simp_all)
  have safe_w: "\<And>m cand. newton_window_pick_bail (carried_descartes_count X) (last es) X
                            = Some (m, cand) \<Longrightarrow>
                  hybrid_loop_safe_invar
                  (((butlast lns @ [last lns * (4 * 2 ^ 2 ^ last es) + m * (last rns - last lns)],
                     butlast rns @ [last lns * (4 * 2 ^ 2 ^ last es) + (m + 4) * (last rns - last lns)],
                     butlast ks @ [Suc (Suc (last ks + 2 ^ last es))]),
                    butlast qtodo @ [cand], butlast es @ [last es + 1],
                    butlast ss @ [last ss], butlast cs @ [Suc (Suc (carried_descartes_count X))],
                    butlast gs @ [4398046511104 + carried_descartes_count X], rp),
                   (al, ar, ak))"
    by (rule hybrid_loop_safe_invar_push1_all
              [OF stinv pre capW qlen dpos rp_len rp_bound kcap kdepth])
  show ?thesis
    \<comment> \<open>\<^bold>\<open>\<open>kdepth\<close> goes in as a HOLE, not as a fact.\<close> Supplying it positionally leaves the
       trivial residual \<open>\<And>kD. int kD \<le> \<kappa> \<Longrightarrow> int kD \<le> \<kappa>\<close> in its slot, which then swallows
       \<open>win\<close> and the \<open>OF\<close> reports \<open>no unifiers\<close> for all thirteen window facts at once --- a
       failure that names none of them. With \<open>_\<close> the alignment is preserved and the one real
       goal is discharged after.\<close>
    apply (rule hybrid_body_step_window_assembled
              [OF safe inv capinv budinv cond X_eq lr0 abnode edef dkdef sdef P0 p0 sf v2 dpos
                  wide P_eq kcap _ win wsub wprop mu_w npush_w vpush_w gw count2 muW jw
                  ndW safe_w arm payinv paypush_s Pcoeffs])
    using kdepth by blast
qed


section \<open>\<^bold>\<open>The arm case split, and the \<open>\<And>s\<close> step\<close>\<close>

text \<open>\<^bold>\<open>(e): every arm at ONE state.\<close> \<open>hybrid_loop_correct\<close>'s \<open>step\<close> is \<open>\<And>s\<close>, so this is the
  lemma that has to hold at an ARBITRARY loop state. Two things make it a case split rather
  than an assembly:

  \<^item> the arm selection is a PURE case distinction on \<open>carried_descartes_count X \<in> {0, 1, \<ge> 2}\<close>
    followed by the gate fork --- no op output is involved, which is why the four discharges
    can take \<open>count0\<close>/\<open>count1\<close>/\<open>count2\<close> + \<open>gate_closed\<close>/\<open>gate_open\<close> as ordinary premises;
  \<^item> \<^bold>\<open>every \<open>rp\<close>-shaped premise is stated at \<open>length (coeffs P)\<close>\<close>, not at \<open>rp\<close>. That is (e0)
    in action: \<open>rp\<close> is a COMPONENT of \<open>s\<close>, so a premise about "the" \<open>rp\<close> is meaningless here ---
    but @{const hybrid_state_invar}'s root relation pins \<open>coeffs P = carried_init_same_den \<dots> rp\<close>
    at THIS state's \<open>rp\<close>, and @{const carried_init_same_den} preserves length, so every length
    premise transfers.

  The window arm's six naming premises (\<open>X_eq\<close>, \<open>abnode\<close>, \<open>edef\<close>, \<open>dkdef\<close>, \<open>sdef\<close>, \<open>Iw_def\<close>,
  \<open>dec_def\<close>) are \<open>refl\<close>/@{thm [source] surjective_pairing} here, which is what "pinned at any call
  site" meant when they were introduced.\<close>
lemma hybrid_step_all_cols:
  fixes P :: "int poly"
  assumes dpos: "0 < \<delta>"
    and lr0: "l0 < r0"
    and P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> real_of_rat b - real_of_rat a \<le> \<delta> \<Longrightarrow>
                       descartes_list_int a b (coeffs P) \<le> 1"
    and lenP: "0 < length (coeffs P)"
    and pbP: "length (coeffs P) * nat_bitlen (length (coeffs P))
                < max_snat LENGTH(gmp_poly_len)"
    and gbP: "4398046511104 + length (coeffs P) < max_snat LENGTH(gmp_poly_len)"
    and smallP: "length (coeffs P) < 1099511627776"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepthP: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                    kD * (length (coeffs P) - 1) < max_snat LENGTH(gmp_poly_len)"
    and g_roomP: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                    (kD + 1) * length (coeffs P) < 1099511627776"
    and safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and sinv: "hybrid_state_invar \<delta> P l0 r0 k0 sd
                 (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
  shows "hybrid_loop_body_checked_monadic
           (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> hybrid_state_invar \<delta> P l0 r0 k0 sd s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have inv: "hybrid_refine_invar P l0 r0 k0 sd (lns, rns, ks) qtodo es ss cs gs rp (al, ar, ak)"
    and capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and budinv: "hybrid_budget_invar \<delta> l0 r0 k0 (lns, rns, ks) (al, ar, ak)"
    and payinv: "hybrid_pay_invar (lns, rns, ks) gs rp"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    using sinv by simp_all
  \<comment> \<open>\<^bold>\<open>(e0) discharging.\<close> Every length premise moves from \<open>coeffs P\<close> to THIS state's \<open>rp\<close>.\<close>
  have lenrp: "length rp = length (coeffs P)"
    using Pcoeffs by (simp add: truncate_length_carried_init_same_den)
  have rp_len: "0 < length rp" using lenP lenrp by simp
  have rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    using pbP lenrp by simp
  have rp_gb: "4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
    using gbP lenrp by simp
  have rp_small: "length rp < 1099511627776" using smallP lenrp by simp
  have rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)" using rp_gb by simp
  have kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                  kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    using kdepthP lenrp by simp
  have g_room: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                  (kD + 1) * length rp < 1099511627776"
    using g_roomP lenrp by simp
  show ?thesis
  proof (cases "carried_descartes_count
                  (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp)")
    case c0: 0
    show ?thesis
      by (rule hybrid_step_discharge_discard
                [OF dpos lr0 Pcoeffs rp_len rp_pb rp_gb kcap kdepth safe inv capinv budinv cond
                    c0 payinv rp_small])
  next
    case c1: (Suc n)
    show ?thesis
    proof (cases n)
      case 0
      with c1 have count1: "carried_descartes_count
                              (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp) = 1"
        by simp
      show ?thesis
        by (rule hybrid_step_discharge_accept
                  [OF lr0 Pcoeffs rp_len rp_pb rp_gb safe inv capinv budinv cond count1 payinv
                      dpos rp_bound kcap kdepth rp_small])
    next
      case (Suc m)
      with c1 have count2: "2 \<le> carried_descartes_count
                                  (carried_init_same_den (last lns) (2 ^ last ks) (last rns) rp)"
        by simp
      show ?thesis
      proof (cases "newton_pol_gate_len (length (last qtodo)) (last es) (last ks) (last ss)")
        case gopen: True
        \<comment> \<open>\<^bold>\<open>The seven naming premises go in as HOLES\<close>, not as \<open>refl\<close> in the \<open>OF\<close> list: \<open>Iw\<close> and
           \<open>dec\<close> are schematic there, so \<open>OF refl\<close> asks the unifier to decompose \<open>(?a, ?b)\<close> and
           reports a bare \<open>no unifiers\<close> for the whole 29-premise rule. Applied afterwards they
           are one \<open>rule\<close> each --- \<open>abnode\<close> is @{thm [source] surjective_pairing}, the rest \<open>refl\<close>.\<close>
        show ?thesis
          apply (rule hybrid_step_discharge_window
                    [OF dpos lr0 P0 p0 sf small_fast Pcoeffs rp_len kcap kdepth safe inv capinv
                        budinv cond _ _ _ _ _ count2 _ _ gopen rp_pb rp_gb rp_small g_room payinv])
          apply (all \<open>((rule refl | rule surjective_pairing | assumption); fail)?\<close>)
          done
      next
        case gclosed: False
        show ?thesis
          by (rule hybrid_step_discharge_split
                    [OF dpos lr0 P0 p0 sf small_fast Pcoeffs rp_len kcap kdepth safe inv capinv
                        budinv cond count2 gclosed rp_pb rp_gb rp_small g_room payinv])
      qed
    qed
  qed
qed

section \<open>\<^bold>\<open>VACUITY TRIPWIRES\<close> -- three premise shapes that must never be reintroduced\<close>

text \<open>\<^bold>\<open>Vacuity tripwires.\<close> Each lemma below proves that a premise shape is contradictory. A
  lemma with a contradictory premise set is accepted by the checker and proves nothing: it can
  never be applied, because discharging its premises is discharging \<open>False\<close>. Certification is
  not satisfiability, and nothing in the toolchain checks the latter.

  \<^bold>\<open>1. \<open>polrel\<close> quantified over \<open>pol2\<close>.\<close> \<open>\<And>pol2 \<dots>. polr \<dots> = pol2 \<dots>\<close> says ONE real policy
  \<open>polr\<close> agrees with EVERY rational policy; instantiating \<open>pol2\<close> at two constant policies refutes
  it. The shape arises because @{thm [source] hybrid_acc_invar_step}'s \<open>branch\<close> obligation is
  \<open>\<And>pol\<close>-quantified, so a \<open>polr\<close> fixed outside that binder cannot serve it. The sound form builds
  \<open>polr\<close> from \<open>pol2\<close> inside the binder (\<open>of_rat\<close> is injective, so \<open>inv of_rat\<close> is a left
  inverse).

  \<^bold>\<open>2. \<open>npush\<close> quantified over the pushed run length \<open>sv\<close>.\<close> The abstract split step pins the
  children's run length to \<open>split_run_len_int P a b s\<close>, but the arm leaves the pushed \<open>ss\<close> entry
  existential, so quantifying \<open>npush\<close> over \<open>sv\<close> with an \<open>sv\<close>-independent right-hand side is
  refuted by two instantiations (@{thm [source] hybrid_alpha_nodes_append2} copies \<open>sv\<close> into the
  node verbatim). The concrete \<open>\<sigma>\<close> genuinely diverges from the abstract one
  (@{const hybrid_split_run_len} reads cached classes, and the ambiguous sentinel \<open>c = 4\<close>
  carries no count information), so \<open>\<sigma>\<close> is a ghost column in @{const hybrid_abs_invar_g}
  rather than a projection of \<open>ss\<close>.

  \<^bold>\<open>3. \<open>npush_w\<close> quantified over the window index \<open>m\<close>.\<close> The same defect one component over: a
  right-hand side naming a fixed window \<open>I\<close> for every \<open>m\<close> forces all window children to be the
  same interval. The sound form threads the \<open>m \<leftrightarrow> I\<close> link
  (@{thm [source] hybrid_window_choice_abs} proves it at the op) through the arm chain.\<close>

lemma hybrid_polrel_forall_pol_is_vacuous:
  fixes polr :: newton_pol_real and P :: "int poly"
  assumes polrel: "\<And>pol2 a2 b2 e2 dk2 s2 v.
                    polr (degree P) (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = pol2 (degree P) a2 b2 e2 dk2 (s2, v)"
  shows False
  using polrel[of 0 1 0 0 0 0 "\<lambda>_ _ _ _ _ _. (True, True)"]
        polrel[of 0 1 0 0 0 0 "\<lambda>_ _ _ _ _ _. (False, False)"]
  by simp

lemma hybrid_npush_forall_sv_is_vacuous:
  assumes lr: "length lns = length rns" and rk: "length rns = length ks"
    and le: "length es = length ks" and ls: "length ss = length ks"
    and npush: "\<And>sv. hybrid_alpha_nodes l0 r0 k0
                   (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
                   (es @ [e1, e2]) (ss @ [sv, sv])
                 = hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                   @ [(av, cv, ee, dd, sv0), (cv, bv, ee, dd, sv0)]"
  shows False
proof -
  have push: "\<And>s1 s2. hybrid_alpha_nodes l0 r0 k0
                 (lns @ [l1, l2], rns @ [r1, r2], ks @ [k1, k2])
                 (es @ [e1, e2]) (ss @ [s1, s2])
             = hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
               @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((l1, r1), k1)),
                   snd (dyadic_iv_node_iv_of l0 r0 k0 ((l1, r1), k1)), e1, k1, s1),
                  (fst (dyadic_iv_node_iv_of l0 r0 k0 ((l2, r2), k2)),
                   snd (dyadic_iv_node_iv_of l0 r0 k0 ((l2, r2), k2)), e2, k2, s2)]"
    by (rule hybrid_alpha_nodes_append2[OF lr rk le ls])
  from npush[of sv0] npush[of "Suc sv0"] push[of sv0 sv0] push[of "Suc sv0" "Suc sv0"]
  show False by simp
qed

text \<open>\<^bold>\<open>4. \<open>gcap_rp\<close> quantified over the guard \<open>g1\<close>.\<close> \<open>\<And>g1. max g1 2\<^sup>4\<^sup>2 + length rp < max_snat\<close>
  must hold for every value of \<open>g1\<close>, so instantiating at \<open>g1 = max_snat\<close> refutes it. The bound is
  meant to say that the guard the op produces leaves room for one more coefficient list, which is
  a statement about the child guards the arm builds, not about all \<open>g1\<close>. It is therefore stated
  at the guards the arm emits (\<open>max g 2\<^sup>4\<^sup>2\<close> for the resolve, \<open>2\<^sup>4\<^sup>2 + v\<close> for the lock), which the
  caller discharges from \<open>g_dep\<close> and \<open>vcap2\<close>.\<close>
lemma hybrid_step_args_gcap_rp_forall_g_is_vacuous:
  assumes gcap_rp: "\<And>g1 :: nat. max g1 4398046511104 + length rp < max_snat LENGTH(gmp_poly_len)"
  shows False
proof -
  have "max (max_snat LENGTH(gmp_poly_len)) 4398046511104 + length rp
          < max_snat LENGTH(gmp_poly_len)"
    by (rule gcap_rp)
  thus False by simp
qed

lemma hybrid_npush_w_forall_m_forces_one_window:
  assumes lr: "length lns = length rns" and rk: "length rns = length ks"
    and le: "length es = length ks" and ls: "length ss = length ks"
    and npush_w: "\<And>m. hybrid_alpha_nodes l0 r0 k0
                   (lns @ [lw m], rns @ [rw m], ks @ [kw]) (es @ [ew]) (ss @ [sw])
                 = hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
                   @ [(fst I, snd I, ew, kw, sw)]"
  shows "dyadic_iv_node_iv_of l0 r0 k0 ((lw m1, rw m1), kw)
       = dyadic_iv_node_iv_of l0 r0 k0 ((lw m2, rw m2), kw)"
proof -
  have push: "\<And>m. hybrid_alpha_nodes l0 r0 k0
                 (lns @ [lw m], rns @ [rw m], ks @ [kw]) (es @ [ew]) (ss @ [sw])
             = hybrid_alpha_nodes l0 r0 k0 (lns, rns, ks) es ss
               @ [(fst (dyadic_iv_node_iv_of l0 r0 k0 ((lw m, rw m), kw)),
                   snd (dyadic_iv_node_iv_of l0 r0 k0 ((lw m, rw m), kw)), ew, kw, sw)]"
    using lr rk le ls
    by (simp add: hybrid_alpha_nodes_def dyadic_interval_vec_triples_def)
  from npush_w[of m1] npush_w[of m2] push[of m1] push[of m2]
  show ?thesis by (simp add: prod_eq_iff)
qed


text \<open>\<^bold>\<open>The seed node's view is \<open>(0, 1)\<close>\<close> --- the root node is the whole
  interval, so the normalisation is the identity on it. Everything the seed obligations want
  (the k-potential at equality, the append/acc budgets, the non-degeneracy) reads off this.\<close>
lemma hybrid_node_iv_of_seed:
  assumes lr: "l_num < r_num"
  shows "dyadic_iv_node_iv_of l_num r_num kk ((l_num, r_num), kk) = (0, 1)"
proof -
  have "dyadic_rat l_num kk < dyadic_rat r_num kk"
    using lr by (simp add: dyadic_rat_def divide_strict_right_mono)
  hence "dyadic_rat r_num kk - dyadic_rat l_num kk \<noteq> 0" by simp
  thus ?thesis by (simp add: dyadic_iv_node_iv_of_def dyadic_iv_node_iv_def Let_def)
qed

lemma hybrid_alpha_views_seed:
  assumes lr: "l_num < r_num"
  shows "hybrid_alpha_views l_num r_num kk ([l_num], [r_num], [kk]) = [(0, 1)]"
  by (simp add: hybrid_alpha_views_def dyadic_interval_vec_triples_def
                hybrid_node_iv_of_seed[OF lr])

text \<open>\<^bold>\<open>The k-potential at the seed holds with EQUALITY\<close>: @{const hybrid_root_potential} is
  \<open>int k0 + C \<cdot> \<mu> (0, 1)\<close> by definition and the seed node's view IS \<open>(0, 1)\<close>, so the
  invariant's inequality is \<open>\<kappa> \<le> \<kappa>\<close>. That is the whole reason \<open>k0\<close> is instantiated to the
  seed's own depth at the keystone.\<close>
lemma hybrid_cap_invar_seed:
  assumes lr: "l_num < r_num"
  shows "hybrid_cap_invar \<delta> l_num r_num kk ([l_num], [r_num], [kk]) [0]"
  unfolding hybrid_cap_invar_def
  by (simp add: hybrid_node_iv_of_seed[OF lr] hybrid_root_potential_def)

text \<open>\<^bold>\<open>The seed state's safety\<close> --- obligation (3) of the seeding chain.
  Every column is a singleton here, so each of @{const hybrid_loop_step_pre}'s eighteen
  conjuncts reduces to a keystone premise; the \<open>butlast\<close> caps are all at the empty list.\<close>
lemma hybrid_loop_safe_invar_seed:
  assumes lenP: "0 < length Ps"
    and lenb: "length Ps + 1 < max_snat LENGTH(gmp_poly_len)"
    and kk1: "kk + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_len: "0 < length rp"
    and rp_bound: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "kk * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
  shows "hybrid_loop_safe_invar
           ((([ll], [rr], [kk]), [Ps], [ee], [0], [xx], [0], rp), ([], [], []))"
  unfolding hybrid_loop_safe_invar_def hybrid_loop_state_invar_def
            hybrid_loop_step_pre_def hybrid_loop_cond_def
            dyadic_interval_vec_invar_def dyadic_interval_vec_pushable_def
            dyadic_interval_vec_pushable2_def
  using assms by (simp add: Let_def max_snat_def)

section \<open>KEYSTONE: \<open>\<exists>pol\<close> multiset correctness of the lazy hybrid\<close>

text \<open>Mirrors @{thm [source] bail_main_list_correct}'s premises (\<open>\<delta>\<close>-smallness witness,
  square-freeness, canonical coefficients, word caps, the \<open>k\<close>-potential cap) plus the
  dense side's seed premises: \<open>P\<close> is the carried init of the retained escalation root
  \<open>rp\<close> (the pipeline threads \<open>rp\<close> exactly as \<open>Split_Truncate\<close> does), the \<open>2^40\<close> trust
  window on the root length, and depth-safety of the escalation product bound at every
  reachable depth (bounded by bail's own \<open>k\<close>-potential).
  The conclusion is bail's keystone SPEC with \<open>pol_final\<close> generalized to \<open>\<exists>pol\<close> — which
  the \<forall>\<open>pol\<close> abstract theorems then consume in the FCOMP chain exactly as bail's
  \<open>pol_final\<close> instance does.\<close>
lemma hybrid_main_list_correct_strong:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and len2: "Suc 0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and sf: "square_free (map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
    and lenb: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
    and lr: "l_num < r_num"
    \<comment> \<open>\<^bold>\<open>At \<open>k\<close>, not at a free \<open>k0\<close>.\<close> A \<open>k0\<close> occurring in no other premise and in no
       conclusion would be the caller's choice, and nothing could be proved with it, because the
       wrapper's own SPEC (\<open>dyadic_iv_acc_ivs l_num r_num k\<close>) forces the loop's root depth to be
       \<open>k\<close>. \<open>k_depth_safe\<close> and \<open>g_room\<close> below are written against \<open>int k + C \<cdot> \<mu>\<close>, which is
       \<open>hybrid_root_potential \<delta> k\<close> unfolded. \<open>kcap\<close> is redundant --- it follows from
       \<open>k_depth_safe\<close> at \<open>kD = nat \<kappa>\<close>, since a degree-\<open>\<ge> 1\<close> root makes
       \<open>kD \<le> kD \<cdot> (length rp - 1)\<close> --- and is kept because it documents the intent at the ABI.

       \<^bold>\<open>The \<open>kD\<close> range is linear in \<open>\<mu>\<close>\<close>, \<open>C \<cdot> \<mu>\<close>, because that is what the cap invariant
       proves: every push strictly drops \<open>\<mu>\<close> and lifts \<open>k\<close> by at most \<open>C\<close>. What needs
       \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1\<close> is the worklist length bound (@{const hybrid_budget_invar}), not the depth, and
       \<open>mucap\<close> --- verbatim a clause of \<open>dsc_isolate_all_split_pre\<close> --- pays for it. With
       \<open>\<mu> \<le> 61\<close> from \<open>mucap\<close>, \<open>g_room\<close> reduces to a bound on \<open>length rp\<close> alone and no root
       separation term survives.\<close>
    and mucap: "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
                < int (max_snat LENGTH(gmp_poly_len))"
    and kcap: "int k + int (2 ^ newton_pol_ecap + 2) * int (dyadic_iv_interval_mu \<delta> (0, 1))
               \<le> hybrid_root_potential \<delta> k"
    and P_eq: "P = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rp_len: "0 < length rp"
    and rp_small: "length rp < 1099511627776"
    and k_depth_safe: "\<And>kD. int kD \<le> int k + int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<Longrightarrow>
        kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    \<comment> \<open>\<^bold>\<open>Guard headroom.\<close> Same depth-quantified shape as
       @{text k_depth_safe}, and discharged at the same site. \<^bold>\<open>Why it is needed\<close>:
       @{const truncate_child_guards_mop} saturates a child guard to the literal \<open>2\<^sup>4\<^sup>1\<close> once
       \<open>2\<^sup>4\<^sup>0 \<le> g\<close>, while the true child guard is \<open>g + len\<close>. Since @{const gframe} reads \<open>g\<close> as an
       error bound (\<open>err < 2^(s+g)\<close>), a saturated guard understates the error whenever
       \<open>g + len > 2\<^sup>4\<^sup>1\<close> --- so that branch is not merely unproven, it is unsound, and \<open>g_tri\<close> in
       @{thm [source] truncate_children_mid_agrees} exists precisely to exclude it. This premise
       makes the band unreachable.

       With the guard column bounded by \<open>gs ! i \<le> (ks ! i + 1) * length rp\<close>
       (@{const hybrid_trunc_coupling}), this premise gives \<open>g < 2\<^sup>4\<^sup>0\<close> at every popped node,
       hence \<open>g_tri\<close>'s first disjunct --- so the split arms discharge it at the call site and
       \<open>truncate_children_mid_agrees\<close> needs no change.

       \<^bold>\<open>Caller obligation\<close>: \<open>rp_small\<close> alone gives only \<open>length rp < 2\<^sup>4\<^sup>0\<close> and \<open>mucap\<close> bounds
       \<open>\<mu>\<close> at 61, so with \<open>C = 258\<close> this asks for \<open>(k + 258\<cdot>61 + 1) \<cdot> len < 2\<^sup>4\<^sup>0\<close> --- a bound on
       \<open>len\<close> alone that does not follow from \<open>rp_small\<close>. It is physically unreachable
       (\<open>g \<ge> 2\<^sup>4\<^sup>0\<close> needs a degree-\<open>~10\<^sup>1\<^sup>0\<close> polynomial), but it is a hypothesis of the exported
       entry and is not checked at runtime.\<close>
    and g_room: "\<And>kD. int kD \<le> int k + int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<Longrightarrow>
        (kD + 1) * length rp < 1099511627776"
  \<comment> \<open>\<^bold>\<open>\<open>_strong\<close>\<close>: the middle conjunct is the acc cap, i.e. the emitted-interval count bound.
     It is not new mathematics: @{const hybrid_budget_invar} carries it and the plain exit
     drops it. \<open>mucap\<close> pays for it, so the premises are those of \<open>hybrid_main_list_correct\<close>,
     which is kept below so the FCOMP chain and its use sites are unchanged.\<close>
  shows "hybrid_main_list_monadic e0 l_num r_num k P rp \<le> SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      length (dyadic_interval_vec_triples acc) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      (\<exists>pol. mset (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly P))))"
proof -
  \<comment> \<open>\<^bold>\<open>The instantiation is \<open>l0 := l_num\<close>, \<open>r0 := r_num\<close>, \<open>k0 := k\<close>\<close>, and at that choice
     @{const hybrid_root_potential} is \<^bold>\<open>literally\<close> the \<open>\<kappa>\<close> that \<open>k_depth_safe\<close> and \<open>g_room\<close>
     are stated against --- it IS \<open>int k + C \<cdot> \<mu> (0,1)\<close> by definition. That is why those two ABI
     premises need no re-statement here.\<close>
  have potK: "hybrid_root_potential \<delta> k
              = int k + int (2 ^ newton_pol_ecap + 2)
                  * int (dyadic_iv_interval_mu \<delta> (0, 1))"
    by (simp add: hybrid_root_potential_def)
  have lenrp: "length rp = length P"
    using P_eq by (simp add: truncate_length_carried_init_same_den)
  have rp2: "2 \<le> length rp" using len2 lenrp by simp
  \<comment> \<open>the seed node's view is \<open>(0, 1)\<close>, which is non-degenerate, so its \<open>\<mu>\<close> is \<open>\<ge> 1\<close> and the
     potential has \<open>C = 258\<close> of headroom above \<open>k\<close>. Everything word-shaped below is that plus
     \<open>k_depth_safe\<close>.\<close>
  have bud2: "1 \<le> dyadic_iv_interval_mu \<delta> (0, 1)"
    by (rule dyadic_iv_interval_mu_ge_1[OF \<delta>_pos]) simp
  have pot_ge: "int k + 258 \<le> hybrid_root_potential \<delta> k"
  proof -
    have "(258::int) * 1 \<le> 258 * int (dyadic_iv_interval_mu \<delta> (0, 1))"
      using bud2 by (intro mult_left_mono) simp_all
    thus ?thesis by (simp add: hybrid_root_potential_def newton_pol_ecap_def)
  qed
  have pot_nn: "0 \<le> hybrid_root_potential \<delta> k" using pot_ge by simp
  have kfit: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k \<Longrightarrow>
                 kD < max_snat LENGTH(gmp_poly_len)"
  proof -
    fix kD assume h: "int kD \<le> hybrid_root_potential \<delta> k"
    have A: "kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
      using k_depth_safe[of kD] h potK by simp
    \<comment> \<open>\<^bold>\<open>Destructure \<open>length rp\<close> FIRST.\<close> Left as \<open>length rp - 1\<close> the goal normalises to
       \<open>0 < kD \<longrightarrow> Suc 0 \<le> length rp - Suc 0\<close>, a truncated-subtraction shape \<open>simp\<close> does not
       close from \<open>2 \<le> length rp\<close>; as \<open>Suc m\<close> it is @{thm [source] mult_le_mono2} at \<open>1 \<le> m\<close>.\<close>
    obtain m where rpm: "length rp = Suc m" and m1: "1 \<le> m"
      using rp2 by (cases "length rp") auto
    have B: "kD \<le> kD * (length rp - 1)"
      using rpm m1 mult_le_mono2[of 1 m kD] by simp
    show "kD < max_snat LENGTH(gmp_poly_len)" using B A by (rule le_less_trans)
  qed
  have potcap: "hybrid_root_potential \<delta> k < int (max_snat LENGTH(gmp_poly_len))"
    using kfit[of "nat (hybrid_root_potential \<delta> k)"] pot_nn by simp
  have k1: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    using kfit[of "k + 1"] pot_ge by simp
  have kdepthK: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k \<Longrightarrow>
                   kD * (length P - 1) < max_snat LENGTH(gmp_poly_len)"
    using k_depth_safe potK lenrp by simp
  have g_roomK: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k \<Longrightarrow>
                   (kD + 1) * length P < 1099511627776"
    using g_room potK lenrp by simp
  \<comment> \<open>the six the seed's \<open>step_pre\<close> wants, at the singleton columns.\<close>
  \<comment> \<open>the two the keystone states over the LIST \<open>P\<close> and the step wants over \<open>coeffs (Poly P)\<close>;
     \<open>canon\<close> is exactly the bridge, and the degree is \<open>length P - 1 \<ge> 1\<close> by \<open>len2\<close>.\<close>
  have p0: "degree (Poly P) \<noteq> 0"
    using len2 canon by (simp add: degree_eq_length_coeffs)
  have small_fastP: "\<And>a b. a < b \<Longrightarrow> real_of_rat b - real_of_rat a \<le> \<delta> \<Longrightarrow>
                       descartes_list_int a b (coeffs (Poly P)) \<le> 1"
    using small_fast canon by simp
  \<comment> \<open>\<^bold>\<open>The one length premise the keystone does NOT state\<close>: \<open>length P \<cdot> nat_bitlen (length P)\<close>.
     It is not an ABI obligation, it is arithmetic --- @{const nat_bitlen} is a \<open>LEAST\<close>, so
     \<open>length P < 2\<^sup>4\<^sup>0\<close> caps it at 40 by @{thm [source] Least_le} and the product at \<open>40 \<cdot> 2\<^sup>4\<^sup>0\<close>.\<close>
  have bl40: "nat_bitlen (length P) \<le> 40"
    unfolding nat_bitlen_def by (rule Least_le) (use rp_small lenrp in simp)
  have pbP: "length P * nat_bitlen (length P) < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "length P * nat_bitlen (length P) \<le> length P * 40"
      using bl40 by (rule mult_le_mono2)
    also have "\<dots> < 1099511627776 * 40" using rp_small lenrp by simp
    finally show ?thesis by (simp add: max_snat_def)
  qed
  \<comment> \<open>the same six, restated over \<open>coeffs (Poly P)\<close> --- the shape the \<open>\<And>s\<close> step is phrased in,
     since \<open>rp\<close> is a component of \<open>s\<close> and \<open>P\<close> is not. \<open>canon\<close> is the whole bridge.\<close>
  \<comment> \<open>\<open>unfolding canon\<close>, not \<open>simp add: canon\<close>: as a simp RULE it competes with
     \<open>coeffs_eq_Nil\<close>/\<open>Poly_eq_0_iff\<close> and \<open>0 < length (coeffs (Poly P))\<close> normalises to
     \<open>\<exists>x\<in>set P. x \<noteq> 0\<close> instead. Unfolded first, every goal is literally over \<open>P\<close>.\<close>
  have lenC: "0 < length (coeffs (Poly P))" unfolding canon using len2 by simp
  have pbC: "length (coeffs (Poly P)) * nat_bitlen (length (coeffs (Poly P)))
               < max_snat LENGTH(gmp_poly_len)"
    unfolding canon by (rule pbP)
  have smallC: "length (coeffs (Poly P)) < 1099511627776"
    unfolding canon using rp_small lenrp by simp
  have gbC: "4398046511104 + length (coeffs (Poly P)) < max_snat LENGTH(gmp_poly_len)"
    unfolding canon using rp_small lenrp by (simp add: max_snat_def)
  have kdepthC: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k \<Longrightarrow>
                   kD * (length (coeffs (Poly P)) - 1) < max_snat LENGTH(gmp_poly_len)"
    unfolding canon by (rule kdepthK)
  have g_roomC: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k \<Longrightarrow>
                   (kD + 1) * length (coeffs (Poly P)) < 1099511627776"
    unfolding canon by (rule g_roomK)
  have lenP1: "0 < length P" using len2 by simp
  have lenP2: "length P + 1 < max_snat LENGTH(gmp_poly_len)" using lenb by simp
  have rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)" using lenb lenrp by simp
  have krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    using k_depth_safe[of k] pot_ge potK by simp
  \<comment> \<open>\<^bold>\<open>The \<open>\<And>s\<close> STEP\<close> --- @{thm [source] hybrid_step_all_cols} at a destructured state. The
     destructuring is @{thm [source] prod_cases7}/@{thm [source] prod_cases3}, not \<open>cases\<close>: the
     loop state is a nested 7-tuple over a 3-tuple and \<open>cases\<close> peels one pair at a time.\<close>
  have step: "\<And>s. \<lbrakk> hybrid_loop_safe_invar s
                     \<and> hybrid_state_invar \<delta> (Poly P) l_num r_num k (0, 1, e0, k, 0) s;
                     hybrid_loop_cond s \<rbrakk>
              \<Longrightarrow> hybrid_loop_body_checked_monadic s
                \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s'
                                \<and> hybrid_state_invar \<delta> (Poly P) l_num r_num k
                                    (0, 1, e0, k, 0) s')
                         \<and> hybrid_state_mu \<delta> l_num r_num k s'
                           < hybrid_state_mu \<delta> l_num r_num k s)"
  proof -
    fix s :: hybrid_state
    assume A: "hybrid_loop_safe_invar s
               \<and> hybrid_state_invar \<delta> (Poly P) l_num r_num k (0, 1, e0, k, 0) s"
      and C: "hybrid_loop_cond s"
    obtain stx accx where s1: "s = (stx, accx)" by (rule prod.exhaust)
    obtain todo qtx esx ssx csx gsx rpx
      where s2: "stx = (todo, qtx, esx, ssx, csx, gsx, rpx)" by (rule prod_cases7)
    obtain lnsx rnsx ksx where s3: "todo = (lnsx, rnsx, ksx)" by (rule prod_cases3)
    obtain alx arx akx where s4: "accx = (alx, arx, akx)" by (rule prod_cases3)
    show "hybrid_loop_body_checked_monadic s
        \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s'
                        \<and> hybrid_state_invar \<delta> (Poly P) l_num r_num k (0, 1, e0, k, 0) s')
                 \<and> hybrid_state_mu \<delta> l_num r_num k s'
                   < hybrid_state_mu \<delta> l_num r_num k s)"
      unfolding s1 s2 s3 s4
      by (rule hybrid_step_all_cols[OF \<delta>_pos lr P0 p0 sf small_fastP
                 lenC pbC gbC smallC potcap kdepthC g_roomC
                 conjunct1[OF A[unfolded s1 s2 s3 s4]]
                 conjunct2[OF A[unfolded s1 s2 s3 s4]]
                 C[unfolded s1 s2 s3 s4]])
  qed
  show ?thesis
  unfolding hybrid_main_list_monadic_def PR_CONST_def
      dyadic_interval_vec_empty_sz_monadic_def poly_empty_sz_monadic_def
      poly_push_coeff_monadic_def poly_vec_empty_sz_monadic_def poly_vec_push_monadic_def
    \<comment> \<open>\<^bold>\<open>The seeding chain.\<close> The unfolding above collapses the whole wrapper to \<^bold>\<open>5\<close>
       subgoals. Feeding @{thm [source] hybrid_count_trunc_cs_ok} to the vcg discharges the count
       bind and leaves \<^bold>\<open>4\<close>, of which only the last two are real work.
       (1) \<open>dyadic_interval_vec_pushable ([], [], op_al_empty)\<close> -- the empty seed vectors.
       (2) \<open>length P + 1 < max_snat\<close> -- immediate from the keystone's \<open>lenb\<close> (\<open>+ 2 <\<close>).
       (3) \<^bold>\<open>the seed \<open>hybrid_loop_safe_invar\<close>\<close>, the wrapper's ASSERT. It sits inside the
       count's continuation, and it is an 18-conjunct @{const hybrid_loop_step_pre} at the seed
       state; every column is a singleton there (\<open>last ks = k\<close>, \<open>butlast qtodo = []\<close>), so each
       conjunct reduces to a keystone premise (\<open>rp_len\<close>, \<open>rp_bound\<close>, \<open>lenb\<close>, \<open>kcap\<close>, \<open>k_depth_safe\<close>).
       (4) the loop itself -- @{thm [source] hybrid_loop_expol}, whose \<open>step\<close> premise is the
       body step discharged above. The \<open>cs\<close> hypothesis the seed needs
       (\<open>hybrid_cs_ok 0 x (carried_descartes_count P)\<close>) is already in scope by then.\<close>
    apply (refine_vcg hybrid_count_trunc_cs_ok[THEN order_trans])
    apply (all \<open>((insert lenb, clarsimp simp: dyadic_interval_vec_pushable_def max_snat_def); fail)?\<close>)
    \<comment> \<open>(3) the seed safety, and (4) the loop --- the two that are real work. \<open>rp2\<close> gives the
       degree bound the \<open>k\<close>-cap needs.\<close>
    apply (all \<open>((clarsimp,
                  rule hybrid_loop_safe_invar_seed[OF lenP1 lenP2 k1 rp_len rpb krp]); fail)?\<close>)
    apply clarsimp
    \<comment> \<open>\<^bold>\<open>The instantiation is forced by the wrapper's own SPEC\<close> --- \<open>dyadic_iv_acc_ivs l_num r_num k\<close>
       and \<open>newdsc_pol_bail_int pol 0 1 e0 k (Poly P)\<close> pin every one of the nine, and \<open>k0 := k\<close>
       is what makes @{const hybrid_root_potential} equal the keystone's \<open>\<kappa>\<close>.\<close>
    apply (rule SPEC_cons_rule[OF hybrid_loop_expol])
    \<comment> \<open>\<^bold>\<open>The WEAKENING goal first\<close>: \<open>l0\<close>/\<open>r0\<close>/\<open>k0\<close>/\<open>a\<close>/\<open>b\<close>/\<open>dk0\<close>/\<open>P\<close> are still schematic after
       the rule, and it is the wrapper's own SPEC --- not a \<open>where\<close> --- that pins them. A
       \<open>where\<close> here reports \<open>No such variable\<close> on the dotted-index names.\<close>
    prefer 3
    \<comment> \<open>the three frees are \<open>ASSERT\<close>-then-\<open>RETURN ()\<close> ops, so the tail collapses to \<open>RETURN acc\<close>
       and the postcondition IS the loop's, with the witness \<open>pol\<close> handed straight over. That
       \<open>assumption\<close> is also what instantiates \<open>l0\<close>/\<open>r0\<close>/\<open>k0\<close>/\<open>a\<close>/\<open>b\<close>/\<open>dk0\<close>/\<open>P\<close>.\<close>
    apply (clarsimp split: prod.splits
                    simp: poly_vec_free_empty_monadic_def dyadic_interval_vec_free_monadic_def
                          mop_free_def)
    \<comment> \<open>\<open>intro conjI exI\<close>, not \<open>rule exI\<close>: the postcondition now has the acc cap in front of
       the \<open>\<exists>pol\<close>, and both come straight from the loop's own post.\<close>
    apply (intro conjI exI; assumption)
    \<comment> \<open>\<^bold>\<open>and the STEP before the INIT\<close>: the weakening pins \<open>l0\<close>/\<open>r0\<close>/\<open>k0\<close>/\<open>a\<close>/\<open>b\<close>/\<open>dk0\<close>/\<open>P\<close> but
       not \<open>\<delta>\<close> (it does not occur there), so an \<open>init\<close> attempted next sees \<open>?\<delta> x\<close> --- a schematic
       under the \<open>\<And>x\<close> binder --- and every seed rule fails to unify. The step goal mentions \<open>\<delta>\<close>.\<close>
    prefer 2
     apply (rule step; assumption)
    subgoal for x
      apply (rule conjI, assumption)
      apply (simp only: hybrid_state_invar_simp)
      apply (intro conjI)
          apply (rule hybrid_refine_invar_seed[OF lr P_eq _ ], assumption)
           apply simp
         apply (rule hybrid_cap_invar_seed[OF lr])
        apply (rule hybrid_budget_invar_seed[OF mucap hybrid_alpha_views_seed[OF lr]])
        apply simp
       apply (rule hybrid_pay_invar_seed)
      \<comment> \<open>\<open>unfolding\<close>, not \<open>simp add:\<close> --- as rewrites, \<open>P_eq\<close> fires first and \<open>canon\<close> then has
         nothing to match.\<close>
      apply (unfold canon)
      apply (rule P_eq)
      done
    done
qed


text \<open>\<^bold>\<open>The original keystone statement\<close>, kept so the \<open>FCOMP\<close> chain
  (\<open>hybrid_expol_int_spec\<close>, hence \<open>hybrid_main_list_impl\<close> — both in \<open>Hybrid_Capstone\<close>,
  which imports this theory) and its use sites are unchanged. A strict weakening: it drops the
  acc cap.\<close>
lemma hybrid_main_list_correct:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and len2: "Suc 0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and sf: "square_free (map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
    and lenb: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
    and lr: "l_num < r_num"
    and mucap: "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
                < int (max_snat LENGTH(gmp_poly_len))"
    and kcap: "int k + int (2 ^ newton_pol_ecap + 2) * int (dyadic_iv_interval_mu \<delta> (0, 1))
               \<le> hybrid_root_potential \<delta> k"
    and P_eq: "P = carried_init_same_den l_num (2 ^ k) r_num rp"
    and rp_len: "0 < length rp"
    and rp_small: "length rp < 1099511627776"
    and k_depth_safe: "\<And>kD. int kD \<le> int k + int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<Longrightarrow>
        kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and g_room: "\<And>kD. int kD \<le> int k + int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<Longrightarrow>
        (kD + 1) * length rp < 1099511627776"
  shows "hybrid_main_list_monadic e0 l_num r_num k P rp \<le> SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      (\<exists>pol. mset (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol 0 1 e0 k (Poly P))))"
  by (rule weaken_SPEC[OF hybrid_main_list_correct_strong[OF assms]]) auto


end
