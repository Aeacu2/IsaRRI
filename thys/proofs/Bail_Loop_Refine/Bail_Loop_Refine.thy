theory Bail_Loop_Refine
  imports "IsaRRI_LLVM.Bail_Solver"
          "IsaRRI_LLVM.Bail_Spec"
          "IsaRRI_LLVM.Dyadic_IV_Refine"
begin

text \<open>Loop-refinement KEYSTONE for the carried cascade-bail Newton solver:
  the concrete GMP loop @{const bail_main_list_monadic} produces, in the
  count frame, EXACTLY the multiset the abstract algorithm @{const newdsc_pol_bail_int} at
  the concrete scheduling policy @{const pol_final} produces.

  \<^bold>\<open>Architecture\<close> — the clone of \<open>Bisection_Loop_Refine.thy\<close>
  (\<open>bisection_loop_monadic_seed_correct\<close> + \<open>bisection_main_list_spec\<close>), against
  @{const newdsc_pol_bail_int}\<open> pol_final\<close> instead of \<open>dsc_int\<close>:
  \<^enum> a pure LIFO model @{text newton_gmp_step_bail}/@{text newton_gmp_main_bail} mirroring
    @{const bail_after_pop_monadic} (with the window-accept branch);
  \<^enum> an order-agnostic multiset invariant \<open>mset acc + \<Sum>\<^sub>{node} tree(node)\<close>, where the
    abstract per-node tree is @{const newdsc_pol_bail}\<open> pol_final_real\<close> — supplied by the
    worklist simulation @{thm [source] newdsc_pol_bail_main_int_sim_aux}
    (one worklist node contributes exactly its @{const newdsc_pol_bail} subtree);
  \<^enum> the \<open>\<mu>\<close>-measure decrease (the ONE genuinely new case vs the bisection template: a
    window accept shrinks width by \<open>1/N_of e \<le> 1/4\<close>, pinned by @{thm [source]
    newdsc_pol_bail_domI_general}); and
  \<^enum> the \<open>\<alpha>\<close>-projection WHILEIT data refinement.

  \<^bold>\<open>Foundation\<close> — the node invariant rests on the relaxation
  @{const carried_repr_scalar} (a positive-scalar relaxation of the exact
  \<open>carried_repr\<close>; @{thm [source] carried_repr_scalar_count} gives the count bridge),
  built in \<open>Newton_Spec.thy\<close> so the Newton chain does not import the
  \<open>carried_repr\<close> / \<open>Bisection_Refine\<close> chain. The pure count-frame / bisection geometry is
  therefore restated below rather than imported.

  Layer: NRES REFINEMENT.\<close>

section \<open>Copied count-frame / bisection geometry\<close>

text \<open>Mirrors \<open>Bisection_Loop_Refine.thy\<close> / \<open>Solvers_Refine.thy\<close> verbatim; restated,
  not imported, so that this chain stays independent of the bisection refinement chain, whose
  node invariant is the exact \<open>carried_repr\<close> rather than @{const carried_repr_scalar}.
  All pure rational arithmetic over @{const dyadic_rat} / \<open>2^k\<close>.\<close>

(* dyadic_iv_unit_dyadic (as in Solvers_Refine.thy) *)


lemma dyadic_iv_unit_dyadic_less_bl:
  assumes "dyadic_iv_unit_dyadic (a, b)" shows "a < b"
proof -
  from assms obtain l k where "a = of_int l / 2 ^ k" "b = of_int (l + 1) / 2 ^ k"
    by (auto simp: dyadic_iv_unit_dyadic_def)
  thus ?thesis by (simp add: divide_strict_right_mono)
qed
lemma dyadic_iv_unit_dyadic_bisect_left_bl:
  assumes "dyadic_iv_unit_dyadic (a, b)" shows "dyadic_iv_unit_dyadic (a, (a + b) / 2)"
proof -
  from assms obtain l k where lk: "a = of_int l / 2 ^ k" "b = of_int (l + 1) / 2 ^ k"
    by (auto simp: dyadic_iv_unit_dyadic_def)
  show ?thesis unfolding dyadic_iv_unit_dyadic_def
  proof (intro exI conjI)
    show "fst (a, (a + b) / 2) = of_int (2 * l) / 2 ^ (k + 1)"
      using lk by (simp add: field_simps)
    show "snd (a, (a + b) / 2) = of_int (2 * l + 1) / 2 ^ (k + 1)"
      using lk by (simp add: field_simps)
  qed
qed

lemma dyadic_iv_unit_dyadic_bisect_right_bl:
  assumes "dyadic_iv_unit_dyadic (a, b)" shows "dyadic_iv_unit_dyadic ((a + b) / 2, b)"
proof -
  from assms obtain l k where lk: "a = of_int l / 2 ^ k" "b = of_int (l + 1) / 2 ^ k"
    by (auto simp: dyadic_iv_unit_dyadic_def)
  show ?thesis unfolding dyadic_iv_unit_dyadic_def
  proof (intro exI conjI)
    show "fst ((a + b) / 2, b) = of_int (2 * l + 1) / 2 ^ (k + 1)"
      using lk by (simp add: field_simps)
    show "snd ((a + b) / 2, b) = of_int (2 * l + 1 + 1) / 2 ^ (k + 1)"
      using lk by (simp add: field_simps)
  qed
qed

(* dyadic_rat bisection helpers (as in Bisection_Loop_Refine.thy) *)
text \<open>Arithmetic helpers. CRITICAL: never expose \<open>2^k\<close> to \<open>field_simps\<close> — its power simproc grinds
  for minutes on a symbolic exponent. Keep @{term "(2::rat) ^ k"} an OPAQUE atom and use only the
  distributive/cancel lemmas below (\<open>of_int_add\<close>, \<open>add_divide_distrib\<close>, \<open>divide_divide_eq_left\<close> are
  default simp; \<open>2^(k+1)\<close> is reduced once via \<open>power_add\<close>).\<close>

lemma blr_dr_step_bl:
  "dyadic_rat n (k + 1) = dyadic_rat n k / 2"
  by (simp add: dyadic_rat_def power_add)

lemma blr_dr_add_same_bl:
  "dyadic_rat (m + n) k = dyadic_rat m k + dyadic_rat n k"
  by (simp add: dyadic_rat_def add_divide_distrib)

lemma blr_dr_double_left_bl:
  "dyadic_rat (l + l) (k + 1) = dyadic_rat l k"
proof -
  have "dyadic_rat (l + l) (k + 1) = dyadic_rat (l + l) k / 2"
    by (rule blr_dr_step_bl)
  also have "\<dots> = (dyadic_rat l k + dyadic_rat l k) / 2"
    using blr_dr_add_same_bl[of l l k] by simp
  finally show ?thesis by (simp add: field_simps)
qed

lemma blr_dr_double_right_bl:
  "dyadic_rat (r + r) (k + 1) = dyadic_rat r k"
proof -
  have "dyadic_rat (r + r) (k + 1) = dyadic_rat (r + r) k / 2"
    by (rule blr_dr_step_bl)
  also have "\<dots> = (dyadic_rat r k + dyadic_rat r k) / 2"
    using blr_dr_add_same_bl[of r r k] by simp
  finally show ?thesis by (simp add: field_simps)
qed

lemma blr_dr_sum_mid_bl:
  "dyadic_rat (l + r) (k + 1)
     = (dyadic_rat l k + dyadic_rat r k) / 2"
proof -
  have "dyadic_rat (l + r) (k + 1) = dyadic_rat (l + r) k / 2"
    by (rule blr_dr_step_bl)
  also have "\<dots> = (dyadic_rat l k + dyadic_rat r k) / 2"
    by (simp only: blr_dr_add_same_bl)
  finally show ?thesis .
qed

text \<open>The single scalar identity behind the bisection (holds unconditionally, incl.\ \<open>D = 0\<close>);
  \<open>field_simps\<close> is used only here on four plain rationals.\<close>
lemma blr_half_diff_div_bl:
  fixes x y lo D :: rat
  shows "((x + y) / 2 - lo) / D = ((x - lo) / D + (y - lo) / D) / 2"
proof (cases "D = 0")
  case True thus ?thesis by simp
next
  case False thus ?thesis by (simp add: field_simps)
qed

(* dyadic_iv_phi / dyadic_iv_node_iv / dyadic_iv_rat_intervals_of (as in Bisection_Loop_Refine.thy) *)
subsection \<open>The affine count-frame \<open>\<leftrightarrow>\<close> output-frame map\<close>

text \<open>\<open>dyadic_iv_phi l0 r0 k0\<close> sends a count-frame @{text "[0,1]"} interval to the output frame
  \<open>[l0/2^k0, r0/2^k0]\<close>; \<open>dyadic_iv_node_iv\<close> is its inverse on a node's output triple.\<close>


text \<open>Cornerstone: \<open>dyadic_iv_phi\<close> applied to a node's count-frame interval recovers the node's output
  dyadic interval. Needs \<open>l0 < r0\<close> so the frame width is nonzero.\<close>
lemma dyadic_iv_phi_node_iv_bl:
  assumes "l0 < r0"
  shows "dyadic_iv_phi l0 r0 k0 (dyadic_iv_node_iv l0 r0 k0 l r k)
       = (dyadic_rat l k, dyadic_rat r k)"
proof -
  have "dyadic_rat l0 k0 < dyadic_rat r0 k0"
    using assms by (simp add: dyadic_rat_def divide_strict_right_mono)
  hence den_ne: "dyadic_rat r0 k0 - dyadic_rat l0 k0 \<noteq> 0" by simp
  show ?thesis
    unfolding dyadic_iv_phi_def dyadic_iv_node_iv_def Let_def fst_conv snd_conv
    using den_ne by (simp add: field_simps)
qed

text \<open>Hence the \<open>dyadic_iv_phi\<close>-image of the count-frame projection of an accumulator vector is exactly its
  output rational-interval list. This transports the multiset identity from count to output frame.\<close>
lemma dyadic_iv_phi_image_to_list_bl:
  assumes "l0 < r0"
  shows "map (dyadic_iv_phi l0 r0 k0)
           (map (\<lambda>((l, r), k). dyadic_iv_node_iv l0 r0 k0 l r k)
             (dyadic_interval_vec_triples acc))
       = dyadic_iv_rat_intervals_of acc"
  by (simp add: dyadic_iv_rat_intervals_of_def dyadic_interval_vec_to_list_def
      dyadic_interval_of_triple_def dyadic_iv_phi_node_iv_bl[OF assms] o_def split_def
      cong: map_cong)

(* dyadic_iv_node_iv_of (as in Bisection_Loop_Refine.thy) *)
text \<open>Count-frame projection of a stack node and of the whole todo / acc.\<close>


(* dyadic_iv_node_iv bisection (as in Bisection_Loop_Refine.thy) *)

text \<open>The output children @{text "((2l,l+r),k+1)"} and @{text "((l+r,2r),k+1)"} project, in the
  count frame, to the left and right halves of the parent's count-frame interval. No
  \<open>field_simps\<close>: only the targeted rewrites @{thm blr_dr_double_left_bl}/@{thm blr_dr_sum_mid_bl}/@{thm blr_half_diff_div_bl}.\<close>
lemma dyadic_iv_node_iv_bisect_left_bl:
  "dyadic_iv_node_iv l0 r0 k0 (l + l) (l + r) (k + 1)
     = (fst (dyadic_iv_node_iv l0 r0 k0 l r k),
        (fst (dyadic_iv_node_iv l0 r0 k0 l r k) + snd (dyadic_iv_node_iv l0 r0 k0 l r k)) / 2)"
proof -
  have e1: "dyadic_rat (l + l) (k + 1) = dyadic_rat l k"
    by (rule blr_dr_double_left_bl)
  have e2: "dyadic_rat (l + r) (k + 1)
      = (dyadic_rat l k + dyadic_rat r k) / 2"
    by (rule blr_dr_sum_mid_bl)
  show ?thesis
    unfolding dyadic_iv_node_iv_def Let_def fst_conv snd_conv e1 e2
    by (simp add: blr_half_diff_div_bl)
qed

lemma dyadic_iv_node_iv_bisect_right_bl:
  "dyadic_iv_node_iv l0 r0 k0 (l + r) (r + r) (k + 1)
     = ((fst (dyadic_iv_node_iv l0 r0 k0 l r k) + snd (dyadic_iv_node_iv l0 r0 k0 l r k)) / 2,
        snd (dyadic_iv_node_iv l0 r0 k0 l r k))"
proof -
  have e1: "dyadic_rat (l + r) (k + 1)
      = (dyadic_rat l k + dyadic_rat r k) / 2"
    by (rule blr_dr_sum_mid_bl)
  have e2: "dyadic_rat (r + r) (k + 1) = dyadic_rat r k"
    by (rule blr_dr_double_right_bl)
  show ?thesis
    unfolding dyadic_iv_node_iv_def Let_def fst_conv snd_conv e1 e2
    by (simp add: blr_half_diff_div_bl)
qed

lemma dyadic_iv_node_iv_bisect_mid_bl:
  "dyadic_iv_node_iv l0 r0 k0 (l + r) (l + r) (k + 1)
     = ((fst (dyadic_iv_node_iv l0 r0 k0 l r k) + snd (dyadic_iv_node_iv l0 r0 k0 l r k)) / 2,
        (fst (dyadic_iv_node_iv l0 r0 k0 l r k) + snd (dyadic_iv_node_iv l0 r0 k0 l r k)) / 2)"
proof -
  have e: "dyadic_rat (l + r) (k + 1)
      = (dyadic_rat l k + dyadic_rat r k) / 2"
    by (rule blr_dr_sum_mid_bl)
  show ?thesis
    unfolding dyadic_iv_node_iv_def Let_def fst_conv snd_conv e
    by (simp add: blr_half_diff_div_bl)
qed

(* dyadic_iv_todo_ivs / dyadic_iv_acc_ivs (as in Bisection_Loop_Refine.thy) *)
text \<open>Count-frame interval projections of the stack todo and of the accepted list.\<close>


lemma dyadic_iv_todo_ivs_Nil_bl[simp]: "dyadic_iv_todo_ivs l0 r0 k0 [] = []" by (simp add: dyadic_iv_todo_ivs_def)
lemma dyadic_iv_todo_ivs_append_bl[simp]:
  "dyadic_iv_todo_ivs l0 r0 k0 (xs @ ys) = dyadic_iv_todo_ivs l0 r0 k0 xs @ dyadic_iv_todo_ivs l0 r0 k0 ys"
  by (simp add: dyadic_iv_todo_ivs_def)
lemma dyadic_iv_acc_ivs_append_bl[simp]:
  "dyadic_iv_acc_ivs l0 r0 k0 (xs @ ys) = dyadic_iv_acc_ivs l0 r0 k0 xs @ dyadic_iv_acc_ivs l0 r0 k0 ys"
  by (simp add: dyadic_iv_acc_ivs_def)

section \<open>The pure LIFO model of the carried Newton GMP loop\<close>

text \<open>A pure node is an output triple @{text "((l,r),k)"} with its NewDsc scheduling
  exponent @{text e} and its carried polynomial @{term Q}; the pure state is a stack of
  such nodes (the todo) and a list of accepted output triples (the acc). This mirrors
  \<open>newton_loop_state\<close> under the @{const dyadic_interval_vec_triples}
  projection with the parallel @{text es} column folded into the node.\<close>

type_synonym newton_gmp_node = "(((int \<times> int) \<times> nat) \<times> nat \<times> nat \<times> gmp_poly)"
type_synonym newton_gmp_state = "newton_gmp_node list \<times> ((int \<times> int) \<times> nat) list"

text \<open>Count-frame projection of a pure node (drops @{text e} and @{term Q}).\<close>
definition newton_node_iv_of ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> newton_gmp_node \<Rightarrow> (rat \<times> rat)" where
"newton_node_iv_of l0 r0 k0 nd = dyadic_iv_node_iv_of l0 r0 k0 (fst nd)"

text \<open>The carried midpoint-root test the GMP body computes (= @{const bisection_mid_zero_monadic}):
  the carried polynomial vanishes at the count-frame midpoint @{text "1/2"}.\<close>
definition newton_mid_is_root :: "gmp_poly \<Rightarrow> bool" where
"newton_mid_is_root Q \<longleftrightarrow> poly (map_poly rat_of_int (Poly Q)) (1 / 2) = 0"

text \<open>The window candidate poly for grid cell @{text "m..m+4"} of @{text "s = 2^(2^e+2)"}: the
  in-place op's proven target @{const carried_init_same_den} on the node poly (the window-algebra
  spine, @{thm [source] carried_try_window_monadic_correct}). It is ACCEPTED iff its exact carried
  Descartes count still equals the parent count @{text v}.\<close>
definition newton_wcand :: "nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> gmp_poly" where
"newton_wcand e m Q = carried_init_same_den m (2 ^ (2 ^ e + 2)) (m + 4) Q"

definition newton_wok :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> gmp_poly \<Rightarrow> bool" where
"newton_wok v e m Q \<longleftrightarrow> carried_descartes_count (newton_wcand e m Q) = v"

text \<open>One Newton snap side (loc0 = left endpoint, loc1 = right): if the local derivative is
  nonzero, snap to grid cell @{text "kn-2"} and accept iff the window count matches.\<close>
definition newton_try_side ::
  "(nat \<Rightarrow> gmp_poly \<Rightarrow> bool \<times> int \<times> int) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option" where
"newton_try_side loc v e Q =
  (let (ok, num, den) = loc v Q
   in if ok then
        (let kn = newton_snap_kn e num den; m = kn - 2
         in if newton_wok v e m Q then Some (m, newton_wcand e m Q) else None)
      else None)"

text \<open>\<^bold>\<open>The cascade is two unconditional tries\<close>: Newton at the left location, then Newton at the right,
  as in @{const newdsc_pol_bail_main_int}, which has no block arm.\<close>
text \<open>The block fallback: try \<open>m=0\<close>, then \<open>m=s-4\<close>. \<open>newton_window_pick_bail\<close> does not call it; it and its
  projection lemmas below are statements about @{const try_blocks_int}, which the plain Newton route
  uses.\<close>
definition newton_blocks_pick :: "int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option" where
"newton_blocks_pick s v e Q =
  (if newton_wok v e 0 Q then Some (0, newton_wcand e 0 Q)
   else if newton_wok v e (s - 4) Q then Some (s - 4, newton_wcand e (s - 4) Q)
   else None)"

text \<open>\<^bold>\<open>The CASCADE-BAIL window pick\<close> (pure model of @{const newton_window_choice_bail_monadic}):
  loc0 probe — if it is ISSUED (\<open>fst (newton_lambda_loc0 v Q)\<close>), its verdict is FINAL, accept or
  bail; only if it MISSED do we try loc1. Written as a direct \<open>if\<close> on the issued flag to match the
  impl's \<open>if t0 then RETURN res0 else side1 v e Q\<close> shape term for term.

  Equal to the old four-arm cascade with the gate forced open and the blocks dropped: when
  \<open>t0\<close> holds, the old \<open>Some res \<Rightarrow> Some res | None \<Rightarrow> if t0 then None\<close> yields exactly
  @{const newton_try_side}'s value; when \<open>\<not> t0\<close> that value is \<open>None\<close> (a try_side accept forces
  \<open>ok\<close>), so the old cascade fell through to loc1, whose own \<open>\<not> t1\<close> tail is now \<open>None\<close> either way.\<close>
definition newton_window_pick_bail :: "nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> (int \<times> gmp_poly) option" where
"newton_window_pick_bail v e Q =
  (if fst (newton_lambda_loc0 v Q)
   then newton_try_side newton_lambda_loc0 v e Q
   else newton_try_side newton_lambda_loc1 v e Q)"

text \<open>Both cascade sources — a @{const newton_try_side} accept and a @{const newton_blocks_pick}
  hit — emit a candidate of the canonical form @{term "newton_wcand e m Q"}. Isolated (fast) so the
  window-choice candidate identity avoids unfolding the \<open>loc\<close>-triple internals in one giant
  @{method auto}.\<close>
lemma newton_try_side_cand_bl:
  "newton_try_side loc v e Q = Some (m, cand) \<Longrightarrow> cand = newton_wcand e m Q"
  by (cases "loc v Q") (auto simp: newton_try_side_def Let_def split: if_splits)

lemma newton_blocks_pick_cand_bl:
  "newton_blocks_pick s v e Q = Some (m, cand) \<Longrightarrow> cand = newton_wcand e m Q"
  by (auto simp: newton_blocks_pick_def split: if_splits)

text \<open>The split branch (@{const newton_branch_split_monadic}): two bisection children
  carrying @{const carried_left}/@{const carried_right}, exponent @{term "max 1 (e - 1)"}, plus
  the midpoint point-interval appended to acc iff @{const newton_mid_is_root} fires.\<close>
definition newton_split ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> newton_gmp_state \<Rightarrow> newton_gmp_state" where
"newton_split l r k e s Q st =
  (case st of (todo', acc) \<Rightarrow>
    (let s' = newton_split_run_len (newton_mid_is_root Q)
                (carried_descartes_count (carried_left Q))
                (carried_descartes_count (carried_right Q)) s
     in (todo' @ [(((l + l, l + r), k + 1), max 1 (e - 1), s', carried_left Q),
                  (((l + r, r + r), k + 1), max 1 (e - 1), s', carried_right Q)],
         if newton_mid_is_root Q then acc @ [((l + r, l + r), k + 1)] else acc)))"

text \<open>One pure loop step, mirroring @{const bail_after_pop_monadic}: pop the LAST node
  (LIFO), classify by the exact carried count @{term v}, then discard (@{text "v=0"}) / accept
  (@{text "v=1"}) / — for @{text "v \<ge> 2"} — either window-accept (gate open and some window try
  fires: push the ONE window child @{const newton_window_child} with exponent @{text "e+1"}) or
  split (gate closed, or every window try rejected).\<close>
definition newton_gmp_step_bail :: "newton_gmp_state \<Rightarrow> newton_gmp_state" where
"newton_gmp_step_bail st =
  (case st of (todo, acc) \<Rightarrow>
    if todo = [] then st
    else
      (let (((l, r), k), e, s, Q) = last todo;
           todo' = butlast todo;
           v = carried_descartes_count Q
       in if v = 0 then (todo', acc)
          else if v = 1 then (todo', acc @ [((l, r), k)])
          else
            (let deg = length Q - 1
             in if \<not> newton_pol_gate deg e k s then newton_split l r k e s Q (todo', acc)
                else
                  (case newton_window_pick_bail v e Q of
                     Some (m, cand) \<Rightarrow>
                       (let (l', r', k') = newton_window_child l r k e m
                        in (todo' @ [(((l', r'), k'), e + 1, s, cand)], acc))
                   | None \<Rightarrow> newton_split l r k e s Q (todo', acc)))))"

text \<open>The pure LIFO driver: iterate @{const newton_gmp_step_bail} until the stack empties.\<close>
partial_function (tailrec) newton_gmp_main_bail ::
  "newton_gmp_state \<Rightarrow> newton_gmp_state" where
"newton_gmp_main_bail st =
  (case st of (todo, acc) \<Rightarrow>
    (case todo of [] \<Rightarrow> st | _ \<Rightarrow> newton_gmp_main_bail (newton_gmp_step_bail st)))"

section \<open>The abstract per-node tree and its order-agnostic worklist decomposition\<close>

text \<open>The abstract subtree of ONE count-frame node @{text "(a,b,e,dk)"}: the int worklist
  @{const newdsc_pol_bail_main_int} at the concrete policy run on that node alone. Under the
  squarefree domain, @{thm [source] newdsc_pol_bail_main_int_sim_aux} makes it the real
  @{const newdsc_pol_bail} subtree (finite), and — the key fact below — one worklist step peels
  exactly this subtree onto the accumulator.\<close>
definition newton_tree1 :: "int poly \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (rat \<times> rat) list" where
"newton_tree1 P a b e dk s = newdsc_pol_bail_main_int (pol_final (degree P)) P [(a, b, e, dk, s)] []"

text \<open>The abstract tree multiset over a whole todo of count-frame nodes.\<close>
definition newton_tree_mset ::
  "int poly \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> (rat \<times> rat) multiset" where
"newton_tree_mset P nodes =
  sum_list (map (\<lambda>(a, b, e, dk, s). mset (newton_tree1 P a b e dk s)) nodes)"

lemma newton_tree_mset_Nil_bl[simp]: "newton_tree_mset P [] = {#}"
  by (simp add: newton_tree_mset_def)

lemma newton_tree_mset_append_bl[simp]:
  "newton_tree_mset P (xs @ ys) = newton_tree_mset P xs + newton_tree_mset P ys"
  by (simp add: newton_tree_mset_def)

lemma newton_tree_mset_Cons_bl:
  "newton_tree_mset P ((a, b, e, dk, s) # xs)
     = mset (newton_tree1 P a b e dk s) + newton_tree_mset P xs"
  by (simp add: newton_tree_mset_def)

text \<open>Bail analog of \<open>newdsc_pol_pol_final_dom\<close> (Newton.thy): the concrete policy's
  domain, from the proven @{thm [source] newdsc_pol_bail_terminates_squarefree}.\<close>
lemma newdsc_pol_bail_pol_final_dom:
  fixes P :: "int poly"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "newdsc_pol_bail_dom (pol_final_real, degree P, a, b, e, dk, s, map_poly of_int P)"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  show ?thesis by (rule newdsc_pol_bail_terminates_squarefree[OF dne dle p0 sf ab])
qed

text \<open>The domain fact for the concrete policy, packaged for the count-frame rational nodes
  this proof uses (real endpoints @{term "of_rat a"}, @{term "of_rat b"}).\<close>
lemma newton_pol_final_dom_rat_bl:
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "newdsc_pol_bail_dom
           (pol_final_real, degree P, of_rat a, of_rat b, e, dk, s, map_poly of_int P)"
  using newdsc_pol_bail_pol_final_dom[OF P0 p0 sf, of "of_rat a" "of_rat b" e dk s] ab
  by (simp add: of_rat_less)

text \<open>\<^bold>\<open>The keystone of the abstract side\<close>: processing the FRONT node of a worklist peels
  exactly that node's subtree onto the accumulator — from two applications of
  @{thm [source] newdsc_pol_bail_main_int_sim_aux} (once with the tail, once alone).\<close>
lemma newton_worklist_cons_bl:
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "newdsc_pol_bail_main_int (pol_final (degree P)) P ((a, b, e, dk, s) # todo) acc
       = newdsc_pol_bail_main_int (pol_final (degree P)) P todo (newton_tree1 P a b e dk s @ acc)"
proof -
  have dom: "newdsc_pol_bail_dom (pol_final_real, degree P, of_rat a, of_rat b, e, dk, s, map_poly of_int P)"
    by (rule newton_pol_final_dom_rat_bl[OF P0 p0 sf ab])
  let ?sub = "map real_to_rat_pair
                (rev (newdsc_pol_bail pol_final_real (degree P) (of_rat a) (of_rat b) e dk s
                        (map_poly of_int P)))"
  have gen: "\<And>td ac. newdsc_pol_bail_main_int (pol_final (degree P)) P ((a, b, e, dk, s) # td) ac
               = newdsc_pol_bail_main_int (pol_final (degree P)) P td (?sub @ ac)"
    by (rule newdsc_pol_bail_main_int_sim_aux[OF dom refl refl refl refl P0 ab pol_final_real_rel])
  have tree1: "newton_tree1 P a b e dk s = ?sub"
    unfolding newton_tree1_def by (subst gen) (simp add: newdsc_pol_bail_main_int.simps)
  show ?thesis by (subst gen) (simp add: tree1)
qed

text \<open>Hence the order-agnostic multiset decomposition: the result multiset of the whole
  worklist is the accumulator plus the sum of the per-node subtrees.\<close>
lemma newton_worklist_decomp_bl:
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)"
    and nodes: "\<forall>(a, b, e, dk, s) \<in> set todo. a < b"
  shows "mset (newdsc_pol_bail_main_int (pol_final (degree P)) P todo acc)
       = mset acc + newton_tree_mset P todo"
  using nodes
proof (induction todo arbitrary: acc)
  case Nil
  show ?case by (simp add: newdsc_pol_bail_main_int.simps)
next
  case (Cons nd todo)
  obtain a b e dk s where nd: "nd = (a, b, e, dk, s)" by (cases nd) auto
  have ab: "a < b" using Cons.prems nd by auto
  have "mset (newdsc_pol_bail_main_int (pol_final (degree P)) P (nd # todo) acc)
      = mset (newdsc_pol_bail_main_int (pol_final (degree P)) P todo (newton_tree1 P a b e dk s @ acc))"
    unfolding nd by (subst newton_worklist_cons_bl[OF P0 p0 sf ab]) (rule refl)
  also have "\<dots> = mset (newton_tree1 P a b e dk s @ acc) + newton_tree_mset P todo"
    using Cons.prems nd by (subst Cons.IH) auto
  also have "\<dots> = mset acc + newton_tree_mset P (nd # todo)"
    unfolding nd by (simp add: newton_tree_mset_Cons_bl)
  finally show ?case .
qed

section \<open>The pure-node invariant (over \<open>carried_repr_scalar\<close>)\<close>

text \<open>The per-node stack invariant: the carried polynomial scalar-represents the node's
  count-frame interval, which is unit-dyadic. Order-agnostic.\<close>
definition newton_gmp_node_inv ::
  "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> newton_gmp_node \<Rightarrow> bool" where
"newton_gmp_node_inv P l0 r0 k0 nd =
  (let iv = newton_node_iv_of l0 r0 k0 nd
   in carried_repr_scalar P (fst iv) (snd iv) (snd (snd (snd nd))) \<and> fst iv < snd iv)"
  \<comment> \<open>ordered (not unit-dyadic): a Newton window child of width \<open>(b-a)/N_of e\<close> is generally
      NOT unit-dyadic (a Newton snap start index \<open>m = kn-2\<close> need not be 4-aligned), so
      @{const dyadic_iv_unit_dyadic} cannot be preserved; downstream only \<open>fst iv < snd iv\<close> is used.\<close>

text \<open>The count bridge (@{thm [source] carried_repr_scalar_count} + the definition of
  @{const carried_descartes_count}): a scalar-repr node's carried Descartes count equals the
  abstract @{const descartes_list_int} count on its count-frame interval.\<close>
lemma carried_descartes_count_scalar_bl:
  assumes "carried_repr_scalar P a b Q" and "0 < length P" and "a \<noteq> b"
  shows "carried_descartes_count Q = descartes_list_int a b P"
  using carried_repr_scalar_count[OF assms]
  by (simp add: carried_descartes_count_def)

lemma newton_gmp_node_inv_ordered_bl:
  assumes "newton_gmp_node_inv P l0 r0 k0 nd"
  shows "fst (newton_node_iv_of l0 r0 k0 nd) < snd (newton_node_iv_of l0 r0 k0 nd)"
  using assms by (simp add: newton_gmp_node_inv_def Let_def)

lemma newton_gmp_node_inv_count_bl:
  assumes "newton_gmp_node_inv P l0 r0 k0 nd" and "0 < length P"
  shows "carried_descartes_count (snd (snd (snd nd)))
       = descartes_list_int (fst (newton_node_iv_of l0 r0 k0 nd))
                            (snd (newton_node_iv_of l0 r0 k0 nd)) P"
proof -
  have repr: "carried_repr_scalar P (fst (newton_node_iv_of l0 r0 k0 nd))
                (snd (newton_node_iv_of l0 r0 k0 nd)) (snd (snd (snd nd)))"
    using assms(1) by (simp add: newton_gmp_node_inv_def Let_def)
  have ne: "fst (newton_node_iv_of l0 r0 k0 nd) \<noteq> snd (newton_node_iv_of l0 r0 k0 nd)"
    using newton_gmp_node_inv_ordered_bl[OF assms(1)] by simp
  show ?thesis by (rule carried_descartes_count_scalar_bl[OF repr assms(2) ne])
qed

section \<open>Window-child count correspondence (the block windows = abstract B1/B2)\<close>

text \<open>The GMP window candidate is @{const carried_init_same_den}, which is definitionally
  @{const window_child_formula} (both in @{const scale_poly_list}/
  @{const taylor_shift_list} form).\<close>
lemma newton_wcand_eq_window_child_formula_bl:
  "newton_wcand e m Q = window_child_formula (m) (2 ^ (2 ^ e + 2)) (m + 4) Q"
  by (simp add: newton_wcand_def carried_init_same_den_def window_child_formula_def)

text \<open>A window candidate scalar-represents its global grid cell
  \<open>[a + (m/s)(b-a), a + ((m+4)/s)(b-a)]\<close> of the node's interval \<open>[a,b]\<close>, where
  \<open>s = 2^(2^e+2) = 4 N_of e\<close> (@{thm [source] four_N_of_pow2}): compose the node's
  @{const carried_repr_scalar} with @{thm [source] window_child_formula_repr_scalar}.\<close>
lemma newton_wcand_repr_scalar_bl:
  assumes repr: "carried_repr_scalar P a b Q"
  shows "carried_repr_scalar P
           (a + (of_int (m)     / of_int (2 ^ (2 ^ e + 2))) * (b - a))
           (a + (of_int (m + 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a))
           (newton_wcand e m Q)"
proof -
  have dpos: "(0 :: int) < 2 ^ (2 ^ e + 2)" by simp
  have w: "carried_repr_scalar Q
             (of_int (m) / of_int (2 ^ (2 ^ e + 2)))
             (of_int (m + 4) / of_int (2 ^ (2 ^ e + 2)))
             (newton_wcand e m Q)"
    unfolding newton_wcand_eq_window_child_formula_bl
    by (rule window_child_formula_repr_scalar[OF dpos])
  show ?thesis
    using carried_repr_scalar_compose[OF repr w] by simp
qed

text \<open>Hence the count of a window candidate equals the abstract @{const descartes_list_int}
  count on its global grid cell — the fact the tree-preservation window case needs.\<close>
lemma newton_wcand_count_bl:
  assumes repr: "carried_repr_scalar P a b Q" and lenP: "0 < length P"
    and ne: "a + (of_int (m)     / of_int (2 ^ (2 ^ e + 2))) * (b - a)
           \<noteq> a + (of_int (m + 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a)"
  shows "carried_descartes_count (newton_wcand e m Q)
       = descartes_list_int
           (a + (of_int (m)     / of_int (2 ^ (2 ^ e + 2))) * (b - a))
           (a + (of_int (m + 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a)) P"
  by (rule carried_descartes_count_scalar_bl[OF newton_wcand_repr_scalar_bl[OF repr] lenP ne])

section \<open>Block windows = abstract \<open>try_blocks_int\<close> B1/B2\<close>

text \<open>The grid divisor coercion: @{term "s = 2^(2^e+2)"} is @{term "4 * N_of e"}
  (@{thm [source] four_N_of_pow2}) as a rational.\<close>
lemma of_int_pow2_eq_4N_bl: "(of_int (2 ^ (2 ^ e + 2)) :: rat) = 4 * of_nat (N_of e)"
proof -
  have "(of_int (2 ^ (2 ^ e + 2)) :: rat) = (2 :: rat) ^ (2 ^ e + 2)"
    by (simp add: of_int_power)
  also have "\<dots> = of_nat ((2 :: nat) ^ (2 ^ e + 2))"
    by (simp add: of_nat_power)
  also have "\<dots> = of_nat (4 * N_of e)"
    by (simp add: four_N_of_pow2)
  finally show ?thesis by simp
qed

text \<open>The GMP block window @{term "m = 0"} is the abstract left block
  @{term "B1 = (a, a + w / N)"}; block @{term "m = s - 4"} is the right block
  @{term "B2 = (b - w / N, b)"}. Their carried counts thus equal the abstract
  @{const descartes_list_int} counts @{const try_blocks_int} tests.\<close>
lemma newton_block_left_count_bl:
  assumes repr: "carried_repr_scalar P a b Q" and lenP: "0 < length P" and ab: "a < b"
  shows "carried_descartes_count (newton_wcand e 0 Q)
       = descartes_list_int a (a + (b - a) / of_nat (N_of e)) P"
proof -
  have Npos: "(0 :: rat) < of_nat (N_of e)" using N_of_ge_2[of e] by simp
  have lo: "a + (of_int (0) / of_int (2 ^ (2 ^ e + 2))) * (b - a) = a" by simp
  have hi: "a + (of_int (0 + 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a)
          = a + (b - a) / of_nat (N_of e)"
  proof -
    have "of_int (0 + 4) / of_int (2 ^ (2 ^ e + 2)) = (1 :: rat) / of_nat (N_of e)"
      by (subst of_int_pow2_eq_4N_bl) simp
    thus ?thesis by simp
  qed
  have ne: "a + (of_int (0) / of_int (2 ^ (2 ^ e + 2))) * (b - a)
          \<noteq> a + (of_int (0 + 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a)"
    using ab Npos unfolding lo hi by simp
  show ?thesis
    using newton_wcand_count_bl[OF repr lenP ne] unfolding lo hi .
qed

lemma newton_block_right_count_bl:
  assumes repr: "carried_repr_scalar P a b Q" and lenP: "0 < length P" and ab: "a < b"
  shows "carried_descartes_count (newton_wcand e (2 ^ (2 ^ e + 2) - 4) Q)
       = descartes_list_int (b - (b - a) / of_nat (N_of e)) b P"
proof -
  have Npos: "(0 :: rat) < of_nat (N_of e)" using N_of_ge_2[of e] by simp
  have hi: "a + (of_int (((2::int) ^ (2 ^ e + 2) - 4) + 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a) = b"
  proof -
    have "((2 :: int) ^ (2 ^ e + 2) - 4) + 4 = (2 :: int) ^ (2 ^ e + 2)" by simp
    thus ?thesis using ab by simp
  qed
  have lo: "a + (of_int ((2::int) ^ (2 ^ e + 2) - 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a)
          = b - (b - a) / of_nat (N_of e)"
  proof -
    have A: "(of_int ((2 :: int) ^ (2 ^ e + 2) - 4) :: rat) = (4 :: rat) * of_nat (N_of e) - 4"
    proof -
      have "(of_int ((2 :: int) ^ (2 ^ e + 2) - 4) :: rat) = (of_int (2 ^ (2 ^ e + 2) :: int) :: rat) - 4"
        by simp
      also have "\<dots> = 4 * of_nat (N_of e) - 4" by (subst of_int_pow2_eq_4N_bl) simp
      finally show ?thesis .
    qed
    have B: "(of_int (2 ^ (2 ^ e + 2) :: int) :: rat) = 4 * of_nat (N_of e)"
      by (rule of_int_pow2_eq_4N_bl)
    have generic: "\<And>c :: rat. 0 < c \<Longrightarrow> (4 * c - 4) / (4 * c) = 1 - 1 / c"
      by (simp add: field_simps)
    have loc: "of_int ((2::int) ^ (2 ^ e + 2) - 4) / of_int (2 ^ (2 ^ e + 2) :: int)
             = (1 :: rat) - 1 / of_nat (N_of e)"
    proof -
      have "(of_int ((2::int) ^ (2 ^ e + 2) - 4) / of_int (2 ^ (2 ^ e + 2) :: int) :: rat)
          = (4 * of_nat (N_of e) - 4) / (4 * of_nat (N_of e))"
        by (simp only: A B)
      also have "\<dots> = 1 - 1 / of_nat (N_of e)" by (rule generic[OF Npos])
      finally show ?thesis .
    qed
    have lo_gen: "\<And>c :: rat. a + (1 - 1 / c) * (b - a) = b - (b - a) / c"
      by (simp add: field_simps)
    show ?thesis by (simp only: loc) (rule lo_gen)
  qed
  have ne: "a + (of_int ((2::int) ^ (2 ^ e + 2) - 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a)
          \<noteq> a + (of_int (((2::int) ^ (2 ^ e + 2) - 4) + 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a)"
    unfolding lo hi using ab Npos by simp
  show ?thesis
    using newton_wcand_count_bl[OF repr lenP ne] unfolding lo hi .
qed

text \<open>The block-window acceptance tests, in @{const descartes_list_int} form: the concrete
  @{const newton_wok} fires exactly when the abstract @{const try_blocks_int} block count hits
  @{term v}.\<close>
lemma newton_wok_block_left_bl:
  assumes "carried_repr_scalar P a b Q" and "0 < length P" and "a < b"
  shows "newton_wok v e 0 Q = (descartes_list_int a (a + (b - a) / of_nat (N_of e)) P = v)"
  by (simp add: newton_wok_def newton_block_left_count_bl[OF assms])

lemma newton_wok_block_right_bl:
  assumes "carried_repr_scalar P a b Q" and "0 < length P" and "a < b"
  shows "newton_wok v e (2 ^ (2 ^ e + 2) - 4) Q
       = (descartes_list_int (b - (b - a) / of_nat (N_of e)) b P = v)"
  by (simp only: newton_wok_def newton_block_right_count_bl[OF assms])

section \<open>List-op identities (\<open>taylor_shift 0\<close>, \<open>scale 1\<close>)\<close>

lemma blr_ruffini_step_zero_bl [simp]: "ruffini_step 0 a xs = a # xs"
  by (induction xs arbitrary: a) auto

lemma blr_taylor_shift_list_zero_bl [simp]: "taylor_shift_list 0 xs = xs"
  by (induction xs) simp_all

lemma blr_scale_poly_list_one_bl [simp]: "scale_poly_list 1 xs = xs"
  by (intro nth_equalityI) simp_all

section \<open>Split children scalar-repr the bisection halves\<close>

text \<open>@{const carried_left}/@{const carried_right} are themselves @{const window_child_formula}
  instances (grid @{term "d = 2"}: left @{term "[0/2, 1/2]"}, right @{term "[1/2, 2/2]"}), so the
  same window-algebra spine gives: the left child scalar-reps @{term "[a, (a+b)/2]"}, the right child
  @{term "[(a+b)/2, b]"}.\<close>
lemma carried_left_repr_scalar_bl:
  assumes repr: "carried_repr_scalar P a b Q"
  shows "carried_repr_scalar P a ((a + b) / 2) (carried_left Q)"
proof -
  have cl: "carried_left Q = window_child_formula 0 2 1 Q"
    by (simp add: carried_left_def window_child_formula_def)
  have w: "carried_repr_scalar Q (of_int (0 :: int) / of_int (2 :: int))
             (of_int (1 :: int) / of_int (2 :: int)) (carried_left Q)"
    unfolding cl by (rule window_child_formula_repr_scalar) simp
  have main: "carried_repr_scalar P (a + (of_int (0 :: int) / of_int (2 :: int)) * (b - a))
          (a + (of_int (1 :: int) / of_int (2 :: int)) * (b - a)) (carried_left Q)"
    by (rule carried_repr_scalar_compose[OF repr w])
  have e0: "a + (of_int (0 :: int) / of_int (2 :: int)) * (b - a) = a" by simp
  have e1: "a + (of_int (1 :: int) / of_int (2 :: int)) * (b - a) = (a + b) / 2"
    by (simp add: field_simps)
  show ?thesis by (rule main[unfolded e0 e1])
qed

lemma carried_right_repr_scalar_bl:
  assumes repr: "carried_repr_scalar P a b Q"
  shows "carried_repr_scalar P ((a + b) / 2) b (carried_right Q)"
proof -
  have cr: "carried_right Q = window_child_formula 1 2 2 Q"
    by (simp add: carried_right_def carried_left_def window_child_formula_def)
  have w: "carried_repr_scalar Q (of_int (1 :: int) / of_int (2 :: int))
             (of_int (2 :: int) / of_int (2 :: int)) (carried_right Q)"
    unfolding cr by (rule window_child_formula_repr_scalar) simp
  have main: "carried_repr_scalar P (a + (of_int (1 :: int) / of_int (2 :: int)) * (b - a))
          (a + (of_int (2 :: int) / of_int (2 :: int)) * (b - a)) (carried_right Q)"
    by (rule carried_repr_scalar_compose[OF repr w])
  have e1: "a + (of_int (1 :: int) / of_int (2 :: int)) * (b - a) = (a + b) / 2"
    by (simp add: field_simps)
  have e2: "a + (of_int (2 :: int) / of_int (2 :: int)) * (b - a) = b" by simp
  show ?thesis by (rule main[unfolded e1 e2])
qed

section \<open>Newton probe correspondence\<close>

text \<open>The local (count-frame) polynomial is the global polynomial pre-composed with the affine
  map @{term "\<lambda>x. a + (b - a) * x"}.\<close>
lemma Poly_local_poly_rat_bl:
  "Poly (local_poly_rat a b P) = pcompose (map_poly rat_of_int (Poly P)) [:a, b - a:]"
proof (rule poly_ext)
  fix x :: rat
  have "poly (Poly (local_poly_rat a b P)) x
      = poly (map_poly rat_of_int (Poly P)) (a + (b - a) * x)"
    by (simp add: local_poly_rat_def Poly_scale_poly_list Poly_taylor_shift_list
        Poly_map_rat_of_int poly_pcompose ac_simps)
  also have "\<dots> = poly (pcompose (map_poly rat_of_int (Poly P)) [:a, b - a:]) x"
    by (simp add: poly_pcompose ac_simps)
  finally show "poly (Poly (local_poly_rat a b P)) x
      = poly (pcompose (map_poly rat_of_int (Poly P)) [:a, b - a:]) x" .
qed

text \<open>Chain rule: the pderiv of the local poly picks up the affine factor @{term "b - a"}.\<close>
lemma poly_pderiv_local_poly_rat_bl:
  "poly (pderiv (Poly (local_poly_rat a b P))) x
     = (b - a) * poly (pderiv (map_poly rat_of_int (Poly P))) (a + (b - a) * x)"
proof -
  let ?R = "map_poly rat_of_int (Poly P)"
  have "pderiv (Poly (local_poly_rat a b P))
      = pcompose (pderiv ?R) [:a, b - a:] * pderiv [:a, b - a:]"
    by (simp add: Poly_local_poly_rat_bl pderiv_pcompose)
  also have "pderiv [:a, b - a :: rat:] = [:b - a:]" by (simp add: pderiv_pCons)
  finally have "poly (pderiv (Poly (local_poly_rat a b P))) x
      = poly (pcompose (pderiv ?R) [:a, b - a:]) x * (b - a)"
    by simp
  also have "\<dots> = (b - a) * poly (pderiv ?R) (a + (b - a) * x)"
    by (simp add: poly_pcompose ac_simps)
  finally show ?thesis .
qed

text \<open>Real \<open>\<leftrightarrow>\<close> rat poly-evaluation bridges (copied from the certified rational-newton
  route, cnl_-prefixed; general HOL facts).\<close>
lemma blr_poly_eval_of_rat_bl:
  fixes p :: "rat poly"
  shows "poly (map_poly of_rat p :: real poly) (of_rat x) = of_rat (poly p x)"
  by (induction p) (auto simp: of_rat_add of_rat_mult)

lemma blr_pderiv_map_poly_of_rat_bl:
  fixes p :: "rat poly"
  shows "pderiv (map_poly of_rat p :: real poly) = map_poly of_rat (pderiv p)"
  by (rule poly_eqI) (simp add: coeff_map_poly coeff_pderiv of_rat_add of_rat_mult)

lemma blr_dsc_pderiv_eval_of_rat_bl:
  fixes p :: "rat poly"
  shows "poly (pderiv (map_poly of_rat p :: real poly)) (of_rat x) = of_rat (poly (pderiv p) x)"
  by (simp add: blr_pderiv_map_poly_of_rat_bl blr_poly_eval_of_rat_bl)

lemma blr_poly_eval_real_of_rat_bl:
  "poly (map_poly of_int (Poly Pl) :: real poly) (of_rat x)
     = of_rat (poly (map_poly rat_of_int (Poly Pl)) x)"
proof -
  have real_eq: "(map_poly of_int (Poly Pl) :: real poly)
      = map_poly of_rat (map_poly rat_of_int (Poly Pl))"
    by (simp add: map_poly_map_poly o_def)
  show ?thesis unfolding real_eq by (simp add: blr_poly_eval_of_rat_bl)
qed

lemma blr_pderiv_eval_real_of_rat_bl:
  "poly (pderiv (map_poly of_int (Poly Pl) :: real poly)) (of_rat x)
     = of_rat (poly (pderiv (map_poly rat_of_int (Poly Pl))) x)"
proof -
  have real_eq: "(map_poly of_int (Poly Pl) :: real poly)
      = map_poly of_rat (map_poly rat_of_int (Poly Pl))"
    by (simp add: map_poly_map_poly o_def)
  show ?thesis unfolding real_eq by (simp add: blr_dsc_pderiv_eval_of_rat_bl)
qed

text \<open>Evaluation at 1: @{term "poly (Poly ys) 1"} is the coefficient sum; the pderiv at 1 is
  @{term "\<Sum>i<length ys. of_nat i * ys ! i"} (needed for the right-endpoint probe
  @{const poly_eval1_pair}).\<close>
lemma poly_Poly_1_bl: "poly (Poly ys) (1 :: 'a :: comm_semiring_1) = sum_list ys"
  by (induction ys) (simp_all add: mult_1_left)

lemma poly_pderiv_Poly_1_bl:
  "poly (pderiv (Poly ys)) 1 = (\<Sum>i<length ys. of_nat i * ys ! i)"
proof (induction ys)
  case Nil show ?case by simp
next
  case (Cons y ys)
  have rhs_split: "(\<Sum>i<length (y # ys). of_nat i * (y # ys) ! i)
      = (\<Sum>i<length ys. ys ! i) + (\<Sum>i<length ys. of_nat i * ys ! i)"
  proof -
    have "(\<Sum>i<Suc (length ys). of_nat i * (y # ys) ! i)
        = of_nat 0 * (y # ys) ! 0
          + (\<Sum>i<length ys. of_nat (Suc i) * (y # ys) ! Suc i)"
      by (rule sum.lessThan_Suc_shift)
    also have "\<dots> = (\<Sum>i<length ys. (ys ! i + of_nat i * ys ! i))"
      by (simp add: distrib_right add.commute)
    also have "\<dots> = (\<Sum>i<length ys. ys ! i) + (\<Sum>i<length ys. of_nat i * ys ! i)"
      by (rule sum.distrib)
    finally show ?thesis by simp
  qed
  show ?case
    unfolding rhs_split
    by (simp add: pderiv_pCons poly_Poly_1_bl Cons.IH sum_list_sum_nth atLeast0LessThan)
qed

text \<open>The non-reversed form of the scalar representation.\<close>
lemma carried_repr_scalar_map_bl:
  assumes "carried_repr_scalar P a b Q"
  shows "\<exists>c>0. map rat_of_int Q = smult_list c (local_poly_rat a b P)"
proof -
  from assms obtain c where c: "c > 0"
    and eq: "map rat_of_int (rev Q) = smult_list c (rev (local_poly_rat a b P))"
    unfolding carried_repr_scalar_def by blast
  have "map rat_of_int Q = rev (map rat_of_int (rev Q))" by (simp add: rev_map)
  also have "\<dots> = rev (smult_list c (rev (local_poly_rat a b P)))" using eq by simp
  also have "\<dots> = smult_list c (local_poly_rat a b P)" by (simp add: rev_smult_list)
  finally show ?thesis using c by blast
qed

lemma length_local_poly_rat_bl [simp]: "length (local_poly_rat a b P) = length P"
  by (simp add: local_poly_rat_def)

text \<open>The 0th/1st coefficients of the local poly are \<open>P(a)\<close> and \<open>(b-a) P'(a)\<close>.\<close>
lemma local_poly_rat_nth0_bl:
  assumes "0 < length P"
  shows "local_poly_rat a b P ! 0 = poly (map_poly rat_of_int (Poly P)) a"
proof -
  have "local_poly_rat a b P ! 0 = coeff (Poly (local_poly_rat a b P)) 0"
    using assms by (simp add: nth_default_coeffs_eq[symmetric] nth_default_nth)
  also have "\<dots> = poly (Poly (local_poly_rat a b P)) 0" by (simp add: poly_0_coeff_0)
  also have "\<dots> = poly (map_poly rat_of_int (Poly P)) a"
    by (simp add: Poly_local_poly_rat_bl poly_pcompose)
  finally show ?thesis .
qed

lemma local_poly_rat_nth1_bl:
  assumes "Suc 0 < length P"
  shows "local_poly_rat a b P ! Suc 0
       = (b - a) * poly (pderiv (map_poly rat_of_int (Poly P))) a"
proof -
  have "local_poly_rat a b P ! Suc 0 = coeff (Poly (local_poly_rat a b P)) (Suc 0)"
    using assms by (simp add: nth_default_coeffs_eq[symmetric] nth_default_nth)
  also have "\<dots> = poly (pderiv (Poly (local_poly_rat a b P))) 0"
    by (simp add: poly_0_coeff_0 coeff_pderiv)
  also have "\<dots> = (b - a) * poly (pderiv (map_poly rat_of_int (Poly P))) a"
    by (simp add: poly_pderiv_local_poly_rat_bl)
  finally show ?thesis .
qed

text \<open>Hence @{term "Q!0"} and @{term "Q!1"} equal the local coeffs scaled by the positive
  carried scalar @{term c} — which cancels in the @{text "\<lambda>_loc"} quotient.\<close>
lemma Q_nth01_scalar_bl:
  assumes repr: "carried_repr_scalar P a b Q" and len2: "Suc 0 < length P"
  obtains c where "c > 0"
    and "rat_of_int (Q ! 0) = c * poly (map_poly rat_of_int (Poly P)) a"
    and "rat_of_int (Q ! Suc 0) = c * ((b - a) * poly (pderiv (map_poly rat_of_int (Poly P))) a)"
proof -
  from carried_repr_scalar_map_bl[OF repr] obtain c where c: "c > 0"
    and meq: "map rat_of_int Q = smult_list c (local_poly_rat a b P)" by blast
  have lenQ: "length Q = length P"
    using meq by (metis length_local_poly_rat_bl length_map length_smult_list)
  have n0: "rat_of_int (Q ! 0) = c * (local_poly_rat a b P ! 0)"
    using meq len2 lenQ by (metis len2 lenQ length_local_poly_rat_bl nth_map nth_smult_list
        zero_less_Suc less_trans)
  have n1: "rat_of_int (Q ! Suc 0) = c * (local_poly_rat a b P ! Suc 0)"
    using meq len2 lenQ by (metis length_local_poly_rat_bl nth_map nth_smult_list)
  show ?thesis
    using that[OF c] n0 n1 local_poly_rat_nth0_bl[of P a b] local_poly_rat_nth1_bl[of P a b] len2
    by simp
qed

text \<open>\<^bold>\<open>The left-endpoint Newton probe correspondence\<close>: @{const newton_lambda_loc0} fires
  exactly when @{const newton_at} is defined at the left endpoint, and its rational
  \<open>\<lambda>_loc\<close> equals the count-frame image \<open>(newton_at - a) / (b - a)\<close> of the
  Newton point — the positive carried scalar cancels in the quotient.\<close>
lemma newton_lambda_loc0_newton_at_bl:
  assumes repr: "carried_repr_scalar P a b Q" and len2: "Suc 0 < length P" and ab: "a < b"
  shows "fst (newton_lambda_loc0 v Q)
           = (newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat a) \<noteq> None)"
    and "newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat a) \<noteq> None \<Longrightarrow>
         (the (newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat a)) - of_rat a)
           / of_rat (b - a)
         = of_rat (rat_of_int (fst (snd (newton_lambda_loc0 v Q)))
                   / rat_of_int (snd (snd (newton_lambda_loc0 v Q))))"
proof -
  let ?R = "map_poly of_int (Poly P) :: real poly"
  let ?Pa = "poly (map_poly rat_of_int (Poly P)) a"
  let ?Pa' = "poly (pderiv (map_poly rat_of_int (Poly P))) a"
  obtain c where cpos: "c > 0"
    and q0: "rat_of_int (Q ! 0) = c * ?Pa"
    and q1: "rat_of_int (Q ! Suc 0) = c * ((b - a) * ?Pa')"
    using Q_nth01_scalar_bl[OF repr len2] by blast
  have wne: "b - a \<noteq> 0" using ab by simp
  have Rval: "poly ?R (of_rat a) = of_rat ?Pa" by (rule blr_poly_eval_real_of_rat_bl)
  have Rder: "poly (pderiv ?R) (of_rat a) = of_rat ?Pa'" by (rule blr_pderiv_eval_real_of_rat_bl)
  \<comment> \<open>the derivative-zero test agrees on all three levels\<close>
  have q1_zero: "(Q ! Suc 0 = 0) = (?Pa' = 0)"
  proof -
    have "(Q ! Suc 0 = 0) = (rat_of_int (Q ! Suc 0) = 0)" by simp
    also have "\<dots> = (c * ((b - a) * ?Pa') = 0)" using q1 by simp
    also have "\<dots> = (?Pa' = 0)" using cpos wne by simp
    finally show ?thesis .
  qed
  have na_none: "(newton_at (int v) ?R (of_rat a) = None) = (?Pa' = 0)"
    by (simp add: newton_at_def Rder)
  \<comment> \<open>part 1: definedness\<close>
  have loc0_fst: "fst (newton_lambda_loc0 v Q) = (Q ! Suc 0 \<noteq> 0)"
    by (simp add: newton_lambda_loc0_def)
  show fst_eq: "fst (newton_lambda_loc0 v Q)
      = (newton_at (int v) ?R (of_rat a) \<noteq> None)"
    by (simp add: loc0_fst q1_zero na_none)
  \<comment> \<open>part 2: value\<close>
  assume defd: "newton_at (int v) ?R (of_rat a) \<noteq> None"
  have Pa'0: "?Pa' \<noteq> 0" using defd na_none by auto
  have Rder0: "poly (pderiv ?R) (of_rat a) \<noteq> 0" using Pa'0 Rder by simp
  have the_eq: "the (newton_at (int v) ?R (of_rat a))
      = of_rat a - of_rat (rat_of_int (int v)) * of_rat ?Pa / of_rat ?Pa'"
    using Rder0 by (simp add: newton_at_def Rval Rder)
  have lam_val: "(the (newton_at (int v) ?R (of_rat a)) - of_rat a) / of_rat (b - a)
      = of_rat ((- rat_of_int (int v) * ?Pa) / ((b - a) * ?Pa'))"
    using Pa'0 wne
    by (simp add: the_eq of_rat_divide of_rat_mult of_rat_diff of_rat_minus field_simps)
  have loc0_snd: "newton_lambda_loc0 v Q = (True, - int v * (Q ! 0), Q ! Suc 0)"
    using Pa'0 q1_zero by (simp add: newton_lambda_loc0_def)
  have rhs: "of_rat (rat_of_int (fst (snd (newton_lambda_loc0 v Q)))
             / rat_of_int (snd (snd (newton_lambda_loc0 v Q))))
      = of_rat ((- rat_of_int (int v) * ?Pa) / ((b - a) * ?Pa'))"
  proof -
    have num_eq: "rat_of_int (fst (snd (newton_lambda_loc0 v Q))) = - rat_of_int (int v) * (c * ?Pa)"
      using loc0_snd q0 by simp
    have den_eq: "rat_of_int (snd (snd (newton_lambda_loc0 v Q))) = c * ((b - a) * ?Pa')"
      using loc0_snd q1 by simp
    have "rat_of_int (fst (snd (newton_lambda_loc0 v Q)))
          / rat_of_int (snd (snd (newton_lambda_loc0 v Q)))
        = (- rat_of_int (int v) * ?Pa) / ((b - a) * ?Pa')"
      unfolding num_eq den_eq using cpos wne Pa'0 by (simp add: field_simps)
    thus ?thesis by simp
  qed
  show "(the (newton_at (int v) ?R (of_rat a)) - of_rat a) / of_rat (b - a)
      = of_rat (rat_of_int (fst (snd (newton_lambda_loc0 v Q)))
                / rat_of_int (snd (snd (newton_lambda_loc0 v Q))))"
    by (simp only: lam_val rhs)
qed

text \<open>@{const poly_eval1_pair} computes @{term "(Q(1), Q'(1))"}, which via the scalar repr are
  @{term "c * P(b)"} and @{term "c * (b-a) * P'(b)"} — the right-endpoint analogues of the loc0
  facts (evaluation at @{term 1} lands at the global right endpoint @{term b}).\<close>
lemma rat_of_int_sum_list_bl: "rat_of_int (sum_list xs) = sum_list (map rat_of_int xs)"
  by (induction xs) simp_all

lemma poly_eval1_pair_scalar_bl:
  assumes repr: "carried_repr_scalar P a b Q"
  obtains c where "c > 0"
    and "rat_of_int (fst (poly_eval1_pair Q)) = c * poly (map_poly rat_of_int (Poly P)) b"
    and "rat_of_int (snd (poly_eval1_pair Q))
           = c * ((b - a) * poly (pderiv (map_poly rat_of_int (Poly P))) b)"
proof -
  let ?R = "map_poly rat_of_int (Poly P)"
  from carried_repr_scalar_map_bl[OF repr] obtain c where c: "c > 0"
    and meq: "map rat_of_int Q = smult_list c (local_poly_rat a b P)" by blast
  have s: "rat_of_int (fst (poly_eval1_pair Q)) = c * poly ?R b"
  proof -
    have "rat_of_int (fst (poly_eval1_pair Q)) = sum_list (map rat_of_int Q)"
      by (simp only: poly_eval1_pair_def fst_conv rat_of_int_sum_list_bl)
    also have "\<dots> = poly (Poly (map rat_of_int Q)) 1" by (simp only: poly_Poly_1_bl)
    also have "\<dots> = c * poly (Poly (local_poly_rat a b P)) 1"
    proof -
      have "Poly (map rat_of_int Q) = smult c (Poly (local_poly_rat a b P))"
        by (simp only: meq Poly_smult_list)
      thus ?thesis by (simp only: poly_smult)
    qed
    also have "\<dots> = c * poly ?R b" by (simp add: Poly_local_poly_rat_bl poly_pcompose)
    finally show ?thesis .
  qed
  have ds: "rat_of_int (snd (poly_eval1_pair Q)) = c * ((b - a) * poly (pderiv ?R) b)"
  proof -
    have "rat_of_int (snd (poly_eval1_pair Q))
        = (\<Sum>i<length Q. of_nat i * rat_of_int (Q ! i))"
      by (simp add: poly_eval1_pair_def of_int_sum)
    also have "\<dots> = (\<Sum>i<length (map rat_of_int Q). of_nat i * (map rat_of_int Q) ! i)"
      by simp
    also have "\<dots> = poly (pderiv (Poly (map rat_of_int Q))) 1"
      by (simp only: poly_pderiv_Poly_1_bl)
    also have "\<dots> = c * poly (pderiv (Poly (local_poly_rat a b P))) 1"
    proof -
      have "pderiv (Poly (map rat_of_int Q)) = smult c (pderiv (Poly (local_poly_rat a b P)))"
        by (simp only: meq Poly_smult_list pderiv_smult)
      thus ?thesis by (simp only: poly_smult)
    qed
    also have "\<dots> = c * ((b - a) * poly (pderiv ?R) b)"
      by (simp add: poly_pderiv_local_poly_rat_bl)
    finally show ?thesis .
  qed
  show ?thesis using that[OF c s ds] .
qed

text \<open>\<^bold>\<open>The right-endpoint Newton probe correspondence\<close> — the analogue of
  @{thm [source] newton_lambda_loc0_newton_at_bl} at @{term b} (\<open>\<lambda>_loc = 1 - v Q(1)/Q'(1)\<close>).\<close>
lemma newton_lambda_loc1_newton_at_bl:
  assumes repr: "carried_repr_scalar P a b Q" and ab: "a < b"
  shows "fst (newton_lambda_loc1 v Q)
           = (newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat b) \<noteq> None)"
    and "newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat b) \<noteq> None \<Longrightarrow>
         (the (newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat b)) - of_rat a)
           / of_rat (b - a)
         = of_rat (rat_of_int (fst (snd (newton_lambda_loc1 v Q)))
                   / rat_of_int (snd (snd (newton_lambda_loc1 v Q))))"
proof -
  let ?R = "map_poly of_int (Poly P) :: real poly"
  let ?Pb = "poly (map_poly rat_of_int (Poly P)) b"
  let ?Pb' = "poly (pderiv (map_poly rat_of_int (Poly P))) b"
  obtain c where cpos: "c > 0"
    and s0: "rat_of_int (fst (poly_eval1_pair Q)) = c * ?Pb"
    and ds0: "rat_of_int (snd (poly_eval1_pair Q)) = c * ((b - a) * ?Pb')"
    using poly_eval1_pair_scalar_bl[OF repr] by blast
  have wne: "b - a \<noteq> 0" using ab by simp
  obtain sQ dsQ where pe: "poly_eval1_pair Q = (sQ, dsQ)" by (cases "poly_eval1_pair Q")
  have s0': "rat_of_int sQ = c * ?Pb" and ds0': "rat_of_int dsQ = c * ((b - a) * ?Pb')"
    using s0 ds0 pe by simp_all
  have Rval: "poly ?R (of_rat b) = of_rat ?Pb" by (rule blr_poly_eval_real_of_rat_bl)
  have Rder: "poly (pderiv ?R) (of_rat b) = of_rat ?Pb'" by (rule blr_pderiv_eval_real_of_rat_bl)
  have ds_zero: "(dsQ = 0) = (?Pb' = 0)"
  proof -
    have "(dsQ = 0) = (rat_of_int dsQ = 0)" by simp
    also have "\<dots> = (?Pb' = 0)" using ds0' cpos wne by simp
    finally show ?thesis .
  qed
  have na_none: "(newton_at (int v) ?R (of_rat b) = None) = (?Pb' = 0)"
    by (simp add: newton_at_def Rder)
  have loc1_fst: "fst (newton_lambda_loc1 v Q) = (dsQ \<noteq> 0)"
    by (simp add: newton_lambda_loc1_def pe)
  show "fst (newton_lambda_loc1 v Q) = (newton_at (int v) ?R (of_rat b) \<noteq> None)"
    by (simp add: loc1_fst ds_zero na_none)
  assume defd: "newton_at (int v) ?R (of_rat b) \<noteq> None"
  have Pb'0: "?Pb' \<noteq> 0" using defd na_none by auto
  have Rder0: "poly (pderiv ?R) (of_rat b) \<noteq> 0" using Pb'0 Rder by simp
  have the_eq: "the (newton_at (int v) ?R (of_rat b))
      = of_rat b - of_rat (rat_of_int (int v)) * of_rat ?Pb / of_rat ?Pb'"
    using Rder0 by (simp add: newton_at_def Rval Rder)
  have lam_val: "(the (newton_at (int v) ?R (of_rat b)) - of_rat a) / of_rat (b - a)
      = of_rat ((?Pb' * (b - a) - rat_of_int (int v) * ?Pb) / ((b - a) * ?Pb'))"
    using Pb'0 wne
    by (simp add: the_eq of_rat_divide of_rat_mult of_rat_diff of_rat_add
        of_rat_of_nat_eq field_simps)
  have loc1_snd: "newton_lambda_loc1 v Q = (True, dsQ - int v * sQ, dsQ)"
    using Pb'0 ds_zero by (simp add: newton_lambda_loc1_def pe)
  have rhs: "of_rat (rat_of_int (fst (snd (newton_lambda_loc1 v Q)))
             / rat_of_int (snd (snd (newton_lambda_loc1 v Q))))
      = of_rat ((?Pb' * (b - a) - rat_of_int (int v) * ?Pb) / ((b - a) * ?Pb'))"
  proof -
    have num_eq: "rat_of_int (fst (snd (newton_lambda_loc1 v Q)))
        = c * ((b - a) * ?Pb') - rat_of_int (int v) * (c * ?Pb)"
      using loc1_snd s0' ds0' by simp
    have den_eq: "rat_of_int (snd (snd (newton_lambda_loc1 v Q))) = c * ((b - a) * ?Pb')"
      using loc1_snd ds0' by simp
    have "rat_of_int (fst (snd (newton_lambda_loc1 v Q)))
          / rat_of_int (snd (snd (newton_lambda_loc1 v Q)))
        = (?Pb' * (b - a) - rat_of_int (int v) * ?Pb) / ((b - a) * ?Pb')"
      unfolding num_eq den_eq using cpos wne Pb'0 by (simp add: field_simps)
    thus ?thesis by simp
  qed
  show "(the (newton_at (int v) ?R (of_rat b)) - of_rat a) / of_rat (b - a)
      = of_rat (rat_of_int (fst (snd (newton_lambda_loc1 v Q)))
                / rat_of_int (snd (snd (newton_lambda_loc1 v Q))))"
    by (simp only: lam_val rhs)
qed

text \<open>The snap floor equality (HOL \<open>div\<close> IS floor division = GMP \<open>fdiv\<close>): the concrete
  @{const newton_snap_kn}'s integer division equals the abstract @{const snap_window_rat}'s
  real floor of \<open>s * lambda_loc\<close>, once \<open>lambda_loc = (lam - a)/(b - a)\<close> is supplied by the
  probe correspondence.\<close>
lemma newton_snap_floor_eq_bl:
  fixes lam :: real
  assumes val: "(lam - of_rat a) / of_rat (b - a) = of_rat (rat_of_int num / rat_of_int den)"
  shows "\<lfloor>of_nat (4 * N_of e) * ((lam - of_rat a) / of_rat (b - a))\<rfloor>
       = (num * 2 ^ (2 ^ e + 2)) div den"
proof -
  have s: "int (4 * N_of e) = (2 :: int) ^ (2 ^ e + 2)"
    by (simp add: four_N_of_pow2)
  have nat_real: "(of_nat (4 * N_of e) :: real) = of_rat (rat_of_int (2 ^ (2 ^ e + 2)))"
  proof -
    have "(of_nat (4 * N_of e) :: real) = of_int (int (4 * N_of e))" by simp
    also have "\<dots> = of_int (2 ^ (2 ^ e + 2))" using s by simp
    also have "\<dots> = of_rat (rat_of_int (2 ^ (2 ^ e + 2)))" by (metis of_rat_of_int_eq)
    finally show ?thesis .
  qed
  have "(of_nat (4 * N_of e) :: real) * ((lam - of_rat a) / of_rat (b - a))
      = of_rat (rat_of_int (2 ^ (2 ^ e + 2))) * of_rat (rat_of_int num / rat_of_int den)"
    by (simp only: nat_real val)
  also have "\<dots> = (of_int (2 ^ (2 ^ e + 2) * num) :: real) / of_int den"
    by (simp add: of_rat_mult of_rat_divide of_rat_of_int_eq of_rat_power of_rat_numeral_eq)
  finally have "\<lfloor>of_nat (4 * N_of e) * ((lam - of_rat a) / of_rat (b - a))\<rfloor>
      = \<lfloor>(of_int (2 ^ (2 ^ e + 2) * num) :: real) / of_int den\<rfloor>" by simp
  also have "\<dots> = (2 ^ (2 ^ e + 2) * num) div den"
    by (rule floor_divide_of_int_eq)
  finally show ?thesis by (simp add: mult.commute)
qed

text \<open>The concrete @{const newton_snap_kn} equals @{const snap_window_rat}'s grid index @{text kn}:
  the integer grid divisor @{text "2^(2^e+2)"} is @{text "int (4 N)"}, and the @{text div} is the
  abstract @{text floor} (@{thm [source] newton_snap_floor_eq_bl}), so the two @{text "nat(max 2 (min
  \<dots>))"} computations coincide once the probe supplies @{text "lambda_loc = (lam - a)/(b - a)"}.\<close>
lemma spow_int_bl: "(2 :: int) ^ (2 ^ e + 2) = int (4 * N_of e)"
proof -
  have "(2 :: int) ^ (2 ^ e + 2) = int ((2 :: nat) ^ (2 ^ e + 2))" by simp
  thus ?thesis by (simp add: four_N_of_pow2)
qed

lemma newton_snap_kn_eq_bl:
  fixes lam :: real
  assumes val: "(lam - of_rat a) / of_rat (b - a) = of_rat (rat_of_int num / rat_of_int den)"
  shows "newton_snap_kn e num den
       = max 2 (min (int (4 * N_of e) - 2)
                (\<lfloor>of_nat (4 * N_of e) * ((lam - of_rat a) / of_rat (b - a))\<rfloor>))"
proof -
  have fl: "(num * 2 ^ (2 ^ e + 2)) div den
          = \<lfloor>of_nat (4 * N_of e) * ((lam - of_rat a) / of_rat (b - a))\<rfloor>"
    using newton_snap_floor_eq_bl[OF val] by simp
  have "newton_snap_kn e num den
      = max 2 (min ((2 :: int) ^ (2 ^ e + 2) - 2) ((num * 2 ^ (2 ^ e + 2)) div den))"
    by (simp only: newton_snap_kn_def Let_def)
  also have "\<dots> = max 2 (min (int (4 * N_of e) - 2)
                     (\<lfloor>of_nat (4 * N_of e) * ((lam - of_rat a) / of_rat (b - a))\<rfloor>))"
    unfolding fl by (simp only: spow_int_bl)
  finally show ?thesis .
qed

text \<open>The snap index is clipped to \<open>[2, 4N-2]\<close> — so \<open>kn - 2\<close> is a valid grid cell start
  and \<open>(kn-2)+4 = kn+2 \<le> 4N\<close> (the \<open>node_iv_window_child_bl\<close> precondition).\<close>
lemma newton_snap_kn_ge2_bl: "2 \<le> newton_snap_kn e num den"
  by (simp add: newton_snap_kn_def Let_def)

lemma newton_snap_kn_le_bl: "newton_snap_kn e num den + 2 \<le> int (4 * N_of e)"
proof -
  have s4: "(4 :: int) \<le> 2 ^ (2 ^ e + 2)"
  proof -
    have "(4 :: int) = 2 ^ 2" by simp
    also have "\<dots> \<le> 2 ^ (2 ^ e + 2)" by (intro power_increasing) auto
    finally show ?thesis .
  qed
  have "newton_snap_kn e num den
      = max 2 (min ((2 :: int) ^ (2 ^ e + 2) - 2) ((num * 2 ^ (2 ^ e + 2)) div den))"
    unfolding newton_snap_kn_def Let_def by simp
  also have "\<dots> \<le> (2 :: int) ^ (2 ^ e + 2) - 2"
    using s4 by (simp add: min.coboundedI1)
  also have "\<dots> = int (4 * N_of e) - 2" by (simp only: spow_int_bl)
  finally have "newton_snap_kn e num den \<le> int (4 * N_of e) - 2" .
  thus ?thesis by simp
qed

text \<open>Int-normalised form of @{thm [source] newton_snap_kn_le_bl} — matches the window
  call sites' goal shape directly (\<open>int (4 * N_of e)\<close> pushed to \<open>4 * 2^2^e\<close>),
  so the window try's \<open>m + 4 \<le> 2^(2^e+2)\<close> side goal closes by simp.\<close>
lemma newton_snap_kn_le_bl'[simp]: "2 + newton_snap_kn e num den \<le> 4 * 2 ^ 2 ^ e"
  using newton_snap_kn_le_bl[of e num den] by (simp add: N_of_def)

section \<open>Mid-root scalar bridge (for the split branch)\<close>

text \<open>Evaluating the local (count-frame) polynomial at @{term x} is evaluating the global
  polynomial at the affine image @{term "a + (b - a) * x"} — from the pcompose forms of
  @{const scale_poly_list}/@{const taylor_shift_list}.\<close>
lemma poly_Poly_local_poly_rat_bl:
  "poly (Poly (local_poly_rat a b P)) x
     = poly (map_poly rat_of_int (Poly P)) (a + (b - a) * x)"
  by (simp add: local_poly_rat_def Poly_scale_poly_list Poly_taylor_shift_list
      Poly_map_rat_of_int poly_pcompose ac_simps)

text \<open>Hence the carried midpoint-root test on a scalar-repr node fires exactly when the
  GLOBAL polynomial vanishes at the node's count-frame midpoint @{term "(a + b) / 2"} — the
  scalar-relaxation analog of the ET \<open>carried_mid_zero_iff_poly\<close>.\<close>
lemma newton_mid_is_root_scalar_bl:
  assumes repr: "carried_repr_scalar P a b Q"
  shows "newton_mid_is_root Q \<longleftrightarrow> poly (map_poly rat_of_int (Poly P)) ((a + b) / 2) = 0"
proof -
  from repr obtain c where cpos: "c > 0"
    and Qeq: "map rat_of_int (rev Q) = smult_list c (rev (local_poly_rat a b P))"
    unfolding carried_repr_scalar_def by blast
  have Qrat: "map rat_of_int Q = smult_list c (local_poly_rat a b P)"
  proof -
    have "map rat_of_int Q = rev (map rat_of_int (rev Q))" by (simp add: rev_map)
    also have "\<dots> = rev (smult_list c (rev (local_poly_rat a b P)))" using Qeq by simp
    also have "\<dots> = smult_list c (local_poly_rat a b P)" by (simp add: rev_smult_list)
    finally show ?thesis .
  qed
  have mid: "a + (b - a) / 2 = (a + b) / 2" by (simp add: field_simps)
  have "poly (map_poly rat_of_int (Poly Q)) (1 / 2)
      = poly (Poly (map rat_of_int Q)) (1 / 2)"
    by (simp add: Poly_map_rat_of_int)
  also have "\<dots> = c * poly (Poly (local_poly_rat a b P)) (1 / 2)"
    using Qrat by (simp add: Poly_smult_list)
  also have "\<dots> = c * poly (map_poly rat_of_int (Poly P)) ((a + b) / 2)"
    by (simp add: poly_Poly_local_poly_rat_bl mid)
  finally have "poly (map_poly rat_of_int (Poly Q)) (1 / 2)
      = c * poly (map_poly rat_of_int (Poly P)) ((a + b) / 2)" .
  thus ?thesis unfolding newton_mid_is_root_def using cpos by auto
qed

section \<open>Window-child count-frame geometry (the window analog of \<open>node_iv_bisect_*\<close>)\<close>

text \<open>The count-frame interval of a window child @{const newton_window_child}\<open> l r k e m\<close> is the
  grid cell \<open>[a + (m/4N)(b-a), a + ((m+4)/4N)(b-a)]\<close> of the parent's count-frame interval
  \<open>(a,b)\<close> — proven from the output-frame endpoints @{thm [source] dyadic_window_child_eval}
  by dividing through by the (nonzero, since \<open>l0<r0\<close>) frame width.\<close>
text \<open>The scalar identity behind it (atoms only — keeps \<open>field_simps\<close> from exploding on the
  compound \<open>dyadic_rat\<close> denominators): shifting the left endpoint by @{text "c/N"} of the
  width, then projecting to the count frame, is projecting then shifting by the SAME fraction.\<close>
lemma window_frame_identity_bl:
  fixes drl drr lo dd :: rat and c :: int and nn :: nat
  assumes "dd \<noteq> 0"
  shows "(drl + of_int c * (drr - drl) / of_nat nn - lo) / dd
       = (drl - lo) / dd + of_int c * ((drr - lo) / dd - (drl - lo) / dd) / of_nat nn"
proof (cases "nn = 0")
  case True thus ?thesis by simp
next
  case False thus ?thesis using assms by (simp add: field_simps)
qed

lemma node_iv_window_child_bl:
  fixes l r :: int and k e :: nat and m :: int
  assumes l0r0: "l0 < r0" and mb: "m + 4 \<le> int (4 * N_of e)"
  shows "dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
             (fst (snd (newton_window_child l r k e m)))
             (snd (snd (newton_window_child l r k e m)))
       = (fst (dyadic_iv_node_iv l0 r0 k0 l r k)
            + of_int m * (snd (dyadic_iv_node_iv l0 r0 k0 l r k) - fst (dyadic_iv_node_iv l0 r0 k0 l r k))
              / of_nat (4 * N_of e),
          fst (dyadic_iv_node_iv l0 r0 k0 l r k)
            + of_int (m + 4) * (snd (dyadic_iv_node_iv l0 r0 k0 l r k) - fst (dyadic_iv_node_iv l0 r0 k0 l r k))
              / of_nat (4 * N_of e))"
proof -
  have D: "dyadic_rat r0 k0 - dyadic_rat l0 k0 \<noteq> 0"
    using l0r0 by (simp add: dyadic_rat_def divide_strict_right_mono)
  have el: "dyadic_rat (fst (newton_window_child l r k e m))
              (snd (snd (newton_window_child l r k e m)))
          = dyadic_rat l k + of_int m * (dyadic_rat r k - dyadic_rat l k) / of_nat (4 * N_of e)"
    using dyadic_window_child_eval(1)[OF mb]
    by (simp add: dyadic_rat_def diff_divide_distrib)
  have er: "dyadic_rat (fst (snd (newton_window_child l r k e m)))
              (snd (snd (newton_window_child l r k e m)))
          = dyadic_rat l k + of_int (m + 4) * (dyadic_rat r k - dyadic_rat l k) / of_nat (4 * N_of e)"
    using dyadic_window_child_eval(2)[OF mb]
    by (simp add: dyadic_rat_def diff_divide_distrib)
  show ?thesis
    unfolding dyadic_iv_node_iv_def Let_def fst_conv snd_conv el er
    by (rule prod_eqI)
       (simp_all only: fst_conv snd_conv window_frame_identity_bl[OF D])
qed

section \<open>Abstract one-step unfold of the per-node tree\<close>

text \<open>The per-node abstract tree @{const newton_tree1} unfolds one @{const newdsc_pol_bail_main_int} step
  into its branch cases: discard (v=0), accept (v=1), a single window child (Newton accept), or the
  midpoint and two bisection subtrees (split). The two split subtrees are separated with
  @{thm [source] newton_worklist_decomp_bl}. The guards are @{const pol_final}'s; both components are
  the gate, and @{const try_window_bail_int} reads only \<open>snd\<close>.\<close>
lemma newton_tree1_mset_unfold_bl:
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "mset (newton_tree1 P a b e dk s)
       = (let v = descartes_list_int a b (coeffs P) in
          if v = 0 then {#}
          else if v = 1 then {# (a, b) #}
          else (case try_window_bail_int (newton_pol_gate (degree P) e dk s)
                        a b (N_of e) P v of
                  Some I \<Rightarrow> mset (newton_tree1 P (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s)
                | None \<Rightarrow>
                     (if poly (map_poly of_int P :: rat poly) ((a + b) / 2) = 0
                        then {# ((a + b) / 2, (a + b) / 2) #} else {#})
                     + mset (newton_tree1 P a ((a + b) / 2) (max 1 (e - 1)) (dk + 1)
                               (split_run_len_int P a b s))
                     + mset (newton_tree1 P ((a + b) / 2) b (max 1 (e - 1)) (dk + 1)
                               (split_run_len_int P a b s))))"
proof -
  let ?v = "descartes_list_int a b (coeffs P)"
  let ?m = "(a + b) / 2"
  let ?e' = "max 1 (e - 1)"
  let ?s' = "split_run_len_int P a b s"
  let ?g = "newton_pol_gate (degree P) e dk s"
  let ?acc' = "if poly (map_poly of_int P :: rat poly) ?m = 0 then [(?m, ?m)] else []"
  have am: "a < ?m" and mb: "?m < b" using ab by simp_all
  have pf: "pol_final (degree P) a b e dk (s, ?v) = (?g, ?g)"
    by (simp add: pol_final_def)
  have split_mset:
    "\<And>acc0. mset (newdsc_pol_bail_main_int (pol_final (degree P)) P
                    [(a, ?m, ?e', dk + 1, ?s'), (?m, b, ?e', dk + 1, ?s')] acc0)
     = mset acc0 + mset (newton_tree1 P a ?m ?e' (dk + 1) ?s') + mset (newton_tree1 P ?m b ?e' (dk + 1) ?s')"
  proof -
    fix acc0
    have "mset (newdsc_pol_bail_main_int (pol_final (degree P)) P
                 [(a, ?m, ?e', dk + 1, ?s'), (?m, b, ?e', dk + 1, ?s')] acc0)
        = mset acc0 + newton_tree_mset P [(a, ?m, ?e', dk + 1, ?s'), (?m, b, ?e', dk + 1, ?s')]"
      using am mb by (intro newton_worklist_decomp_bl[OF P0 p0 sf]) auto
    thus "mset (newdsc_pol_bail_main_int (pol_final (degree P)) P
                 [(a, ?m, ?e', dk + 1, ?s'), (?m, b, ?e', dk + 1, ?s')] acc0)
        = mset acc0 + mset (newton_tree1 P a ?m ?e' (dk + 1) ?s') + mset (newton_tree1 P ?m b ?e' (dk + 1) ?s')"
      by (simp add: newton_tree_mset_Cons_bl newton_tree1_def add.assoc)
  qed
  have nil: "\<And>X. newdsc_pol_bail_main_int (pol_final (degree P)) P [] X = X"
    by (subst newdsc_pol_bail_main_int.simps) simp
  show ?thesis
    unfolding newton_tree1_def
    apply (subst newdsc_pol_bail_main_int.simps)
    apply (simp only: list.case prod.case Let_def)
    apply (subst pf)+
    apply (simp only: fst_conv snd_conv)
    apply (simp only: accept_child_int_def bisect_children_int_def Let_def)
    apply (auto simp del: One_nat_def simp: nil newton_tree1_def[symmetric] split: option.split)
    apply (all \<open>subst split_mset, simp\<close>)
    done
qed

section \<open>Block-window cells = abstract \<open>try_blocks_int\<close> B1/B2 (count-frame)\<close>

text \<open>The count-frame cell of the left block window @{term "m = 0"} is @{const try_blocks_int}'s
  B1 = @{term "(a, a + (b-a)/N)"}; the right block @{term "m = s-4"} (\<open>s = 2^(2^e+2) = 4N\<close>) is
  B2 = @{term "(b - (b-a)/N, b)"}. Instances of @{thm [source] node_iv_window_child_bl} + the
  \<open>4/(4N) = 1/N\<close> arithmetic.\<close>
lemma node_iv_window_left_cell_bl:
  fixes l r :: int and k e :: nat
  assumes l0r0: "l0 < r0"
  shows "dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e 0))
             (fst (snd (newton_window_child l r k e 0)))
             (snd (snd (newton_window_child l r k e 0)))
       = (fst (dyadic_iv_node_iv l0 r0 k0 l r k),
          fst (dyadic_iv_node_iv l0 r0 k0 l r k)
            + (snd (dyadic_iv_node_iv l0 r0 k0 l r k) - fst (dyadic_iv_node_iv l0 r0 k0 l r k)) / of_nat (N_of e))"
proof -
  have m4: "0 + 4 \<le> int (4 * N_of e)" using N_of_ge_2[of e] by simp
  have Nne: "of_nat (N_of e) \<noteq> (0 :: rat)" using N_of_ge_2[of e] by simp
  show ?thesis
    using node_iv_window_child_bl[OF l0r0 m4] Nne by (simp add: field_simps)
qed

lemma node_iv_window_right_cell_bl:
  fixes l r :: int and k e :: nat
  assumes l0r0: "l0 < r0"
  shows "dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e (2 ^ (2 ^ e + 2) - 4)))
             (fst (snd (newton_window_child l r k e (2 ^ (2 ^ e + 2) - 4))))
             (snd (snd (newton_window_child l r k e (2 ^ (2 ^ e + 2) - 4))))
       = (snd (dyadic_iv_node_iv l0 r0 k0 l r k)
            - (snd (dyadic_iv_node_iv l0 r0 k0 l r k) - fst (dyadic_iv_node_iv l0 r0 k0 l r k)) / of_nat (N_of e),
          snd (dyadic_iv_node_iv l0 r0 k0 l r k))"
proof -
  have seq: "(2 :: int) ^ (2 ^ e + 2) = int (4 * N_of e)"
    by (simp add: four_N_of_pow2)
  have m4: "((2::int) ^ (2 ^ e + 2) - 4) + 4 \<le> int (4 * N_of e)"
    using seq by simp
  let ?a = "fst (dyadic_iv_node_iv l0 r0 k0 l r k)"
  let ?b = "snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  let ?w = "(2::int) ^ (2 ^ e + 2) - 4"
  have win: "dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e ?w))
               (fst (snd (newton_window_child l r k e ?w)))
               (snd (snd (newton_window_child l r k e ?w)))
           = (?a + of_int ?w * (?b - ?a) / of_nat (4 * N_of e),
              ?a + of_int (?w + 4) * (?b - ?a) / of_nat (4 * N_of e))"
    by (rule node_iv_window_child_bl[OF l0r0 m4])
  have Npos: "(0 :: rat) < of_nat (N_of e)" using N_of_ge_2[of e] by simp
  have d4N: "(of_nat (4 * N_of e) :: rat) = 4 * of_nat (N_of e)" by simp
  have seqr: "(of_int ((2::int) ^ (2 ^ e + 2)) :: rat) = 4 * of_nat (N_of e)"
    using seq d4N by simp
  have wr: "(of_int ?w :: rat) = 4 * of_nat (N_of e) - 4"
    using seqr by simp
  have w4r: "(of_int (?w + 4) :: rat) = 4 * of_nat (N_of e)"
    using seqr by simp
  have gL: "\<And>x y n :: rat. 0 < n \<Longrightarrow> x + (4 * n - 4) * (y - x) / (4 * n) = y - (y - x) / n"
    by (simp add: field_simps)
  have gR: "\<And>x y n :: rat. 0 < n \<Longrightarrow> x + (4 * n) * (y - x) / (4 * n) = y"
    by (simp add: field_simps)
  have fst_eq: "?a + of_int ?w * (?b - ?a) / of_nat (4 * N_of e)
              = ?b - (?b - ?a) / of_nat (N_of e)"
    unfolding wr d4N by (rule gL[OF Npos])
  have snd_eq: "?a + of_int (?w + 4) * (?b - ?a) / of_nat (4 * N_of e) = ?b"
    unfolding w4r d4N by (rule gR[OF Npos])
  show ?thesis unfolding win fst_eq snd_eq by (rule refl)
qed

text \<open>\<^bold>\<open>The Newton snap cell = the abstract @{const snap_window_rat}\<close>: at grid position
  @{term "kn - 2"} (\<open>kn = newton_snap_kn\<close>), the window child's count-frame interval is exactly
  the abstract snapped window — since @{thm [source] newton_snap_kn_eq_bl} identifies the two grid
  indices and the step @{term "(b-a)/(4N)"} matches.\<close>
lemma newton_snap_cell_eq_bl:
  fixes lam :: real
  assumes l0r0: "l0 < r0"
    and val: "(lam - of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l r k)))
                / of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l r k) - fst (dyadic_iv_node_iv l0 r0 k0 l r k))
              = of_rat (rat_of_int num / rat_of_int den)"
  shows "dyadic_iv_node_iv l0 r0 k0
             (fst (newton_window_child l r k e (newton_snap_kn e num den - 2)))
             (fst (snd (newton_window_child l r k e (newton_snap_kn e num den - 2))))
             (snd (snd (newton_window_child l r k e (newton_snap_kn e num den - 2))))
       = snap_window_rat (fst (dyadic_iv_node_iv l0 r0 k0 l r k))
                         (snd (dyadic_iv_node_iv l0 r0 k0 l r k)) (N_of e) lam"
proof -
  let ?a = "fst (dyadic_iv_node_iv l0 r0 k0 l r k)"
  let ?b = "snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  let ?kn = "newton_snap_kn e num den"
  have kn2: "2 \<le> ?kn" by (rule newton_snap_kn_ge2_bl)
  have knle: "?kn + 2 \<le> int (4 * N_of e)" by (rule newton_snap_kn_le_bl)
  have mb: "(?kn - 2) + 4 \<le> int (4 * N_of e)" using kn2 knle by simp
  have m4id: "(?kn - 2) + 4 = ?kn + 2" using kn2 by simp
  \<comment> \<open>the window-child cell at m = kn-2\<close>
  have cell: "dyadic_iv_node_iv l0 r0 k0
                (fst (newton_window_child l r k e (?kn - 2)))
                (fst (snd (newton_window_child l r k e (?kn - 2))))
                (snd (snd (newton_window_child l r k e (?kn - 2))))
            = (?a + of_int (?kn - 2) * (?b - ?a) / of_nat (4 * N_of e),
               ?a + of_int (?kn + 2) * (?b - ?a) / of_nat (4 * N_of e))"
    using node_iv_window_child_bl[OF l0r0 mb] by (simp only: m4id)
  \<comment> \<open>the abstract snap, with kn' = kn via newton_snap_kn_eq_bl\<close>
  have kneq: "?kn = max 2 (min (int (4 * N_of e) - 2)
                (\<lfloor>of_nat (4 * N_of e) * ((lam - of_rat ?a) / of_rat (?b - ?a))\<rfloor>))"
    by (rule newton_snap_kn_eq_bl[OF val])
  \<comment> \<open>the abstract @{const snap_window_rat} snaps to \<open>nat ?kn\<close> (its index is \<open>nat\<close>-typed);
     bridge to the int \<open>?kn\<close> using \<open>?kn \<ge> 2\<close>.\<close>
  have b1: "(of_nat (nat ?kn - 2) :: rat) = of_int (?kn - 2)" using kn2 by (simp add: of_nat_diff)
  have b2: "(of_nat (nat ?kn + 2) :: rat) = of_int (?kn + 2)" using kn2 by simp
  have snap: "snap_window_rat ?a ?b (N_of e) lam
            = (?a + of_int (?kn - 2) * ((?b - ?a) / of_nat (4 * N_of e)),
               ?a + of_int (?kn + 2) * ((?b - ?a) / of_nat (4 * N_of e)))"
    unfolding snap_window_rat_def Let_def
    by (simp only: kneq[symmetric] b1 b2)
  show ?thesis
    unfolding cell snap by (simp add: mult.assoc)
qed

text \<open>Unifier: the concrete window acceptance @{const newton_wok}\<open> v e m\<close> holds iff the abstract
  @{const descartes_list_int} count on the window child's count-frame cell equals @{term v} — one
  fact serving BOTH the block phase (cell = B1/B2) and the Newton phase (cell = snap). Combines
  @{thm [source] newton_wcand_count_bl} with the identity that its grid interval \<open>[m/s, (m+4)/s]\<close> IS
  @{thm [source] node_iv_window_child_bl}'s cell (\<open>of_int m / of_int s = of_int m / of_nat (4N)\<close>).\<close>
lemma newton_wok_cell_bl:
  fixes m :: int
  assumes repr: "carried_repr_scalar P a b Q" and lenP: "0 < length P"
    and ab: "a < b" and l0r0: "l0 < r0"
    and mb: "m + 4 \<le> int (4 * N_of e)"
    and abdef: "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)" "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  shows "newton_wok v e m Q
       = (descartes_list_int
            (fst (dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                    (fst (snd (newton_window_child l r k e m)))
                    (snd (snd (newton_window_child l r k e m)))))
            (snd (dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                    (fst (snd (newton_window_child l r k e m)))
                    (snd (snd (newton_window_child l r k e m))))) P = v)"
proof -
  have grid: "\<And>j :: int. (of_int j / of_int (2 ^ (2 ^ e + 2)) :: rat)
                        = of_int j / of_nat (4 * N_of e)"
    using of_int_pow2_eq_4N_bl by simp
  have cellval: "dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                    (fst (snd (newton_window_child l r k e m)))
                    (snd (snd (newton_window_child l r k e m)))
              = (a + of_int m * (b - a) / of_nat (4 * N_of e),
                 a + of_int (m + 4) * (b - a) / of_nat (4 * N_of e))"
    unfolding node_iv_window_child_bl[OF l0r0 mb] abdef[symmetric] by simp
  have fst_eq: "fst (dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                    (fst (snd (newton_window_child l r k e m)))
                    (snd (snd (newton_window_child l r k e m))))
              = a + (of_int (m) / of_int (2 ^ (2 ^ e + 2))) * (b - a)"
    unfolding cellval fst_conv by (simp only: grid[of m] times_divide_eq_left)
  have snd_eq: "snd (dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                    (fst (snd (newton_window_child l r k e m)))
                    (snd (snd (newton_window_child l r k e m))))
              = a + (of_int (m + 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a)"
    unfolding cellval snd_conv
    by (simp only: grid[of "m + 4"] times_divide_eq_left)
  have ne: "a + (of_int (m) / of_int (2 ^ (2 ^ e + 2))) * (b - a)
          \<noteq> a + (of_int (m + 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a)"
    using ab by (simp add: of_int_pow2_eq_4N_bl N_of_ge_2[of e] field_simps)
  show ?thesis
    unfolding fst_eq snd_eq
    using newton_wcand_count_bl[OF repr lenP ne] by (simp add: newton_wok_def)
qed

text \<open>\<^bold>\<open>The Newton phase of \<open>newton_window_pick_bail\<close> matches \<open>try_newton_int\<close>'s per-endpoint test.\<close>
  Generic in the probe side (loc0 @ a / loc1 @ b): given that the probe fires iff @{const newton_at}
  is defined at the endpoint and its rational \<open>\<lambda>_loc\<close> is the count-frame image, @{const newton_try_side}
  returns the snapped window iff its abstract Descartes count hits @{term v} — exactly the abstract
  test.\<close>
lemma newton_try_side_generic_bl:
  fixes t :: rat
  assumes repr: "carried_repr_scalar P a b Q" and lenP: "0 < length P"
    and ab: "a < b" and l0r0: "l0 < r0"
    and abdef: "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)" "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
    and defd: "fst (loc v Q)
             = (newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat t) \<noteq> None)"
    and valc: "newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat t) \<noteq> None \<Longrightarrow>
        (the (newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat t)) - of_rat a)
          / of_rat (b - a)
        = of_rat (rat_of_int (fst (snd (loc v Q))) / rat_of_int (snd (snd (loc v Q))))"
  shows "map_option (\<lambda>(m, _). dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                        (fst (snd (newton_window_child l r k e m)))
                        (snd (snd (newton_window_child l r k e m))))
                    (newton_try_side loc v e Q)
       = (case newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat t) of
            None \<Rightarrow> None
          | Some lam \<Rightarrow> (let I = snap_window_rat a b (N_of e) lam
                         in if descartes_list_int (fst I) (snd I) P = v then Some I else None))"
proof (cases "newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat t)")
  case None
  hence "\<not> fst (loc v Q)" using defd by simp
  hence "newton_try_side loc v e Q = None"
    by (cases "loc v Q") (simp add: newton_try_side_def)
  thus ?thesis using None by simp
next
  case (Some lam)
  hence okT: "fst (loc v Q)" using defd by simp
  obtain num den where lnd: "loc v Q = (True, num, den)"
    using okT by (cases "loc v Q") auto
  have ndN: "newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat t) \<noteq> None"
    using Some by simp
  have val: "(lam - of_rat a) / of_rat (b - a) = of_rat (rat_of_int num / rat_of_int den)"
    using valc[OF ndN] Some lnd by simp
  let ?kn = "newton_snap_kn e num den"
  let ?m = "?kn - 2"
  have valn: "(lam - of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l r k)))
                / of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l r k) - fst (dyadic_iv_node_iv l0 r0 k0 l r k))
              = of_rat (rat_of_int num / rat_of_int den)"
    using val abdef by simp
  have snapcell: "dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e ?m))
                    (fst (snd (newton_window_child l r k e ?m)))
                    (snd (snd (newton_window_child l r k e ?m)))
                = snap_window_rat a b (N_of e) lam"
    using newton_snap_cell_eq_bl[OF l0r0 valn] abdef by simp
  have mb: "?m + 4 \<le> int (4 * N_of e)"
    using newton_snap_kn_le_bl[of e num den] newton_snap_kn_ge2_bl[of e num den] by linarith
  have wok_iff: "newton_wok v e ?m Q
               = (descartes_list_int (fst (snap_window_rat a b (N_of e) lam))
                    (snd (snap_window_rat a b (N_of e) lam)) P = v)"
    using newton_wok_cell_bl[OF repr lenP ab l0r0 mb abdef] snapcell by simp
  have side: "newton_try_side loc v e Q
            = (if newton_wok v e ?m Q then Some (?m, newton_wcand e ?m Q) else None)"
    using lnd by (simp add: newton_try_side_def Let_def)
  show ?thesis
    using Some snapcell wok_iff by (simp add: side Let_def)
qed

text \<open>The two instances: left endpoint (loc0 @ a) and right endpoint (loc1 @ b), discharging the
  generic's probe hypotheses from @{thm [source] newton_lambda_loc0_newton_at_bl} /
  @{thm [source] newton_lambda_loc1_newton_at_bl}.\<close>
lemma newton_try_side_loc0_bl:
  assumes repr: "carried_repr_scalar P a b Q" and len2: "Suc 0 < length P"
    and ab: "a < b" and l0r0: "l0 < r0"
    and abdef: "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)" "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  shows "map_option (\<lambda>(m, _). dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                        (fst (snd (newton_window_child l r k e m)))
                        (snd (snd (newton_window_child l r k e m))))
                    (newton_try_side newton_lambda_loc0 v e Q)
       = (case newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat a) of
            None \<Rightarrow> None
          | Some lam \<Rightarrow> (let I = snap_window_rat a b (N_of e) lam
                         in if descartes_list_int (fst I) (snd I) P = v then Some I else None))"
proof -
  have lenP: "0 < length P" using len2 by simp
  show ?thesis
    using repr lenP ab l0r0 abdef(1) abdef(2)
          newton_lambda_loc0_newton_at_bl(1)[OF repr len2 ab]
          newton_lambda_loc0_newton_at_bl(2)[OF repr len2 ab]
    by (rule newton_try_side_generic_bl)
qed

lemma newton_try_side_loc1_bl:
  assumes repr: "carried_repr_scalar P a b Q" and len2: "Suc 0 < length P"
    and ab: "a < b" and l0r0: "l0 < r0"
    and abdef: "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)" "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  shows "map_option (\<lambda>(m, _). dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                        (fst (snd (newton_window_child l r k e m)))
                        (snd (snd (newton_window_child l r k e m))))
                    (newton_try_side newton_lambda_loc1 v e Q)
       = (case newton_at (int v) (map_poly of_int (Poly P) :: real poly) (of_rat b) of
            None \<Rightarrow> None
          | Some lam \<Rightarrow> (let I = snap_window_rat a b (N_of e) lam
                         in if descartes_list_int (fst I) (snd I) P = v then Some I else None))"
proof -
  have lenP: "0 < length P" using len2 by simp
  show ?thesis
    using repr lenP ab l0r0 abdef(1) abdef(2)
          newton_lambda_loc1_newton_at_bl(1)[OF repr ab]
          newton_lambda_loc1_newton_at_bl(2)[OF repr ab]
    by (rule newton_try_side_generic_bl)
qed

text \<open>The Newton part of @{const newton_window_pick_bail} (try location 0, fall back to location 1) equals
  the abstract @{const try_newton_int} (try L1 at a, fall back to L2 at b): the fall-through structure
  lines up because @{const newton_try_side}\<open> loc0 = None\<close> is exactly ``L1 undefined or its snapped window
  misses''.\<close>
text \<open>Window-pick characterisation for a four-try policy (block \<open>m=0\<close>, block \<open>m=s-4\<close>, Newton \<open>loc0\<close>,
  Newton \<open>loc1\<close>): it projects onto the abstract @{const try_blocks_int} (\<open>B1,B2\<close>) followed, when \<open>v\<close> is
  within the Newton gate, by @{const try_newton_int} (\<open>L1,L2\<close>). The block phase goes via
  @{thm [source] newton_wok_block_left_bl}/@{thm [source] newton_wok_block_right_bl} and
  @{thm [source] node_iv_window_left_cell_bl}/@{thm [source] node_iv_window_right_cell_bl}; the Newton
  phase via the arm lemmas and a case split on whether the probe is issued.\<close>
lemma newton_window_pick_bail_abs:
  assumes repr: "carried_repr_scalar P a b Q" and len2: "Suc 0 < length P"
    and ab: "a < b" and l0r0: "l0 < r0" and canon: "coeffs (Poly P) = P"
    and abdef: "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)" "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  shows "map_option (\<lambda>(m, _). dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                        (fst (snd (newton_window_child l r k e m)))
                        (snd (snd (newton_window_child l r k e m))))
                    (newton_window_pick_bail v e Q)
       = try_window_bail_int True a b (N_of e) (Poly P) v"
proof -
  let ?R = "map_poly of_int (Poly P) :: real poly"
  let ?cell = "\<lambda>(m, _::gmp_poly). dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                     (fst (snd (newton_window_child l r k e m)))
                     (snd (snd (newton_window_child l r k e m)))"
  have lenP: "0 < length P" using len2 by simp
  have cP: "coeffs (Poly P) = P" using canon .
  have sw: "strip_while ((=) 0) P = P" using canon by (simp add: coeffs_Poly)
  \<comment> \<open>arm projections (one endpoint each) + the issued bridges\<close>
  have L1: "map_option ?cell (newton_try_side newton_lambda_loc0 v e Q)
          = (case newton_at (int v) ?R (of_rat a) of None \<Rightarrow> None
             | Some lam \<Rightarrow> (let I = snap_window_rat a b (N_of e) lam
                            in if descartes_list_int (fst I) (snd I) P = v then Some I else None))"
    by (rule newton_try_side_loc0_bl[OF repr len2 ab l0r0 abdef])
  have L2: "map_option ?cell (newton_try_side newton_lambda_loc1 v e Q)
          = (case newton_at (int v) ?R (of_rat b) of None \<Rightarrow> None
             | Some lam \<Rightarrow> (let I = snap_window_rat a b (N_of e) lam
                            in if descartes_list_int (fst I) (snd I) P = v then Some I else None))"
    by (rule newton_try_side_loc1_bl[OF repr len2 ab l0r0 abdef])
  have iss0: "fst (newton_lambda_loc0 v Q) = (newton_at (int v) ?R (of_rat a) \<noteq> None)"
    by (rule newton_lambda_loc0_newton_at_bl(1)[OF repr len2 ab])
  have iss1: "fst (newton_lambda_loc1 v Q) = (newton_at (int v) ?R (of_rat b) \<noteq> None)"
    by (rule newton_lambda_loc1_newton_at_bl(1)[OF repr ab])
  \<comment> \<open>blocks projection (the both-probes-missed / gate-closed fallback)\<close>
  have wok0: "newton_wok v e 0 Q = (descartes_list_int a (a + (b - a) / of_nat (N_of e)) P = v)"
    by (rule newton_wok_block_left_bl[OF repr lenP ab])
  have woks4: "newton_wok v e (2 ^ (2 ^ e + 2) - 4) Q
             = (descartes_list_int (b - (b - a) / of_nat (N_of e)) b P = v)"
    by (rule newton_wok_block_right_bl[OF repr lenP ab])
  have tb: "try_blocks_int a b (N_of e) (Poly P) v
    = (if descartes_list_int a (a + (b - a) / of_nat (N_of e)) P = v
       then Some (a, a + (b - a) / of_nat (N_of e))
       else if descartes_list_int (b - (b - a) / of_nat (N_of e)) b P = v
            then Some (b - (b - a) / of_nat (N_of e), b) else None)"
    by (simp add: try_blocks_int_def Let_def sw coeffs_Poly)
  have blk_proj: "map_option ?cell (newton_blocks_pick (2 ^ (2 ^ e + 2)) v e Q)
                = try_blocks_int a b (N_of e) (Poly P) v"
  proof (cases "descartes_list_int a (a + (b - a) / of_nat (N_of e)) P = v")
    case b1: True
    have wok: "newton_wok v e 0 Q" using b1 wok0 by simp
    show ?thesis
      unfolding newton_blocks_pick_def
      using wok node_iv_window_left_cell_bl[OF l0r0] abdef b1 tb by simp
  next
    case f1: False
    show ?thesis
    proof (cases "descartes_list_int (b - (b - a) / of_nat (N_of e)) b P = v")
      case b2: True
      have n0: "\<not> newton_wok v e 0 Q" using f1 wok0 by simp
      have wok: "newton_wok v e (2 ^ (2 ^ e + 2) - 4) Q" using b2 woks4 by simp
      show ?thesis
        unfolding newton_blocks_pick_def
        using n0 wok node_iv_window_right_cell_bl[OF l0r0] abdef f1 b2 tb by simp
    next
      case f2: False
      have n0: "\<not> newton_wok v e 0 Q" using f1 wok0 by simp
      have ns4: "\<not> newton_wok v e (2 ^ (2 ^ e + 2) - 4) Q" using f2 woks4 by simp
      show ?thesis unfolding newton_blocks_pick_def using n0 ns4 f1 f2 tb by simp
    qed
  qed
  \<comment> \<open>the two \<open>Some\<close> arms of @{const try_window_bail_int} are exactly \<open>L1\<close>/\<open>L2\<close>'s \<open>Some\<close> bodies\<close>
  have s0none: "newton_at (int v) ?R (of_rat a) = None \<Longrightarrow> newton_try_side newton_lambda_loc0 v e Q = None"
    using L1 by (cases "newton_try_side newton_lambda_loc0 v e Q") auto
  have s1none: "newton_at (int v) ?R (of_rat b) = None \<Longrightarrow> newton_try_side newton_lambda_loc1 v e Q = None"
    using L2 by (cases "newton_try_side newton_lambda_loc1 v e Q") auto
  \<comment> \<open>The Newton gate inside the choice op is \<open>True\<close>, and both cascades bottom out at \<open>None\<close>, so only the
     case analysis on whether location 0 or location 1 is issued remains.\<close>
  have pick: "newton_window_pick_bail v e Q
      = (if fst (newton_lambda_loc0 v Q)
         then newton_try_side newton_lambda_loc0 v e Q
         else newton_try_side newton_lambda_loc1 v e Q)"
    unfolding newton_window_pick_bail_def by simp
  have rhs: "try_window_bail_int True a b (N_of e) (Poly P) v
      = (case newton_at (int v) ?R (of_rat a) of
           Some lam1 \<Rightarrow> (let I1 = snap_window_rat a b (N_of e) lam1
                         in if descartes_list_int (fst I1) (snd I1) P = v then Some I1 else None)
         | None \<Rightarrow> (case newton_at (int v) ?R (of_rat b) of
                      Some lam2 \<Rightarrow> (let I2 = snap_window_rat a b (N_of e) lam2
                                    in if descartes_list_int (fst I2) (snd I2) P = v then Some I2 else None)
                    | None \<Rightarrow> None))"
    unfolding try_window_bail_int_def Let_def by (simp add: sw coeffs_Poly cong: option.case_cong)
  show ?thesis
  proof (cases "newton_at (int v) ?R (of_rat a)")
    case A0: (Some lam1)
    \<comment> \<open>loc0 issued: its verdict is final — accept or bail, never loc1\<close>
    have issT: "fst (newton_lambda_loc0 v Q)" using iss0 A0 by simp
    show ?thesis
      apply (simp only: pick rhs A0 option.case issT if_True)
      using L1 A0 by (auto simp: map_option_case split: option.splits)
  next
    case A0none: None
    have s0n: "newton_try_side newton_lambda_loc0 v e Q = None" using s0none A0none by simp
    have issF: "\<not> fst (newton_lambda_loc0 v Q)" using iss0 A0none by simp
    show ?thesis
    proof (cases "newton_at (int v) ?R (of_rat b)")
      case B0: (Some lam2)
      show ?thesis
        apply (simp only: pick rhs A0none B0 issF option.case if_False)
        using L2 B0 by (auto simp: map_option_case split: option.splits)
    next
      case B0none: None
      \<comment> \<open>both probes missed: bail bisects on both sides (was: the blocks fallback)\<close>
      have s1n: "newton_try_side newton_lambda_loc1 v e Q = None" using s1none B0none by simp
      show ?thesis
        by (simp only: pick rhs A0none B0none s1n issF option.case if_False option.map_disc_iff)
    qed
  qed
qed

text \<open>A scalar-repr node has the same length as the underlying poly-list — so its degree
  proxy @{term "length Q - 1"} equals @{term "degree (Poly P)"} under the canonical-coeffs
  assumption, making the concrete and abstract @{const newton_pol_gate} agree.\<close>
lemma carried_repr_scalar_length_bl:
  assumes "carried_repr_scalar P a b Q"
  shows "length Q = length P"
  using carried_repr_scalar_map_bl[OF assms]
  by (metis length_local_poly_rat_bl length_map length_smult_list)

section \<open>The abstract tree-multiset over a GMP worklist\<close>

text \<open>The abstract node a GMP node projects to: its count-frame interval @{term "(a,b)"} (via
  @{const newton_node_iv_of}), its scheduling exponent @{text e}, and its dyadic exponent
  @{text k} as the abstract depth tag @{text dk} (they track identically — both start at the
  input @{text k}, both @{text "+1"} on split, both @{text "+(2^e+2)"} on window-accept, see
  @{const newton_window_child}).\<close>
definition newton_absnode :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> newton_gmp_node \<Rightarrow> rat \<times> rat \<times> nat \<times> nat \<times> nat" where
"newton_absnode l0 r0 k0 nd =
  (fst (newton_node_iv_of l0 r0 k0 nd), snd (newton_node_iv_of l0 r0 k0 nd),
   fst (snd nd), snd (fst nd), fst (snd (snd nd)))"

definition newton_gmp_tree_mset ::
  "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> newton_gmp_node list \<Rightarrow> (rat \<times> rat) multiset" where
"newton_gmp_tree_mset P l0 r0 k0 todo = newton_tree_mset (Poly P) (map (newton_absnode l0 r0 k0) todo)"

lemma newton_gmp_tree_mset_Nil_bl[simp]: "newton_gmp_tree_mset P l0 r0 k0 [] = {#}"
  by (simp add: newton_gmp_tree_mset_def)

lemma newton_gmp_tree_mset_append_bl[simp]:
  "newton_gmp_tree_mset P l0 r0 k0 (xs @ ys)
     = newton_gmp_tree_mset P l0 r0 k0 xs + newton_gmp_tree_mset P l0 r0 k0 ys"
  by (simp add: newton_gmp_tree_mset_def)

lemma newton_gmp_tree_mset_Cons_bl:
  "newton_gmp_tree_mset P l0 r0 k0 (nd # xs)
     = mset (newton_tree1 (Poly P) (fst (newton_node_iv_of l0 r0 k0 nd))
                          (snd (newton_node_iv_of l0 r0 k0 nd)) (fst (snd nd)) (snd (fst nd))
                          (fst (snd (snd nd))))
       + newton_gmp_tree_mset P l0 r0 k0 xs"
  by (simp add: newton_gmp_tree_mset_def newton_absnode_def newton_tree_mset_Cons_bl)

section \<open>Tree-preservation: one pure step preserves the acc+tree multiset\<close>

text \<open>The count-frame invariant of the pure LIFO driver: one @{const newton_gmp_step_bail}
  leaves \<open>mset (dyadic_iv_acc_ivs \<dots>) + newton_gmp_tree_mset \<dots>\<close> unchanged. Mirrors the
  ET keystone's \<open>bisection_gmp_step_tree_preservation\<close>, with the extra Newton
  cases (gate-closed / window-accept / window-reject) all collapsed onto the abstract
  @{thm [source] newton_tree1_mset_unfold_bl} branches via @{thm [source] newton_window_pick_bail_abs}.\<close>
lemma newton_gmp_step_bail_tree_preservation:
  assumes P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
    and len2: "Suc 0 < length P"
    and sf: "square_free (map_poly of_int (Poly P) :: real poly)"
    and l0r0: "l0 < r0"
    and ne: "fst st \<noteq> []"
    and inv: "\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd"
  shows "mset (dyadic_iv_acc_ivs l0 r0 k0 (snd (newton_gmp_step_bail st)))
       + newton_gmp_tree_mset P l0 r0 k0 (fst (newton_gmp_step_bail st))
     = mset (dyadic_iv_acc_ivs l0 r0 k0 (snd st))
       + newton_gmp_tree_mset P l0 r0 k0 (fst st)"
proof -
  have lenP: "0 < length P" using len2 by simp
  have degP: "degree (Poly P) = length P - 1"
    using canon by (metis degree_eq_length_coeffs)
  have p0: "degree (Poly P) \<noteq> 0" using degP len2 by simp
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with ne have todo_ne: "todo \<noteq> []" by simp
  obtain lr k e s Q where last_eq0: "last todo = ((lr, k), e, s, Q)"
    by (cases "last todo") auto
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), e, s, Q)" using last_eq0 lr_eq by simp
  have inv': "\<forall>nd \<in> set todo. newton_gmp_node_inv P l0 r0 k0 nd" using inv by (simp add: st)
  have ninv: "newton_gmp_node_inv P l0 r0 k0 (((l, r), k), e, s, Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)"
  define b where "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  have headrepr: "carried_repr_scalar P a b Q"
    using ninv by (simp add: newton_gmp_node_inv_def newton_node_iv_of_def
                              dyadic_iv_node_iv_of_def Let_def a_def b_def)
  have ab: "a < b"
    using newton_gmp_node_inv_ordered_bl[OF ninv]
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using carried_descartes_count_scalar_bl[OF headrepr lenP] ab by simp
  have sw: "strip_while ((=) 0) P = P" using canon by (simp add: coeffs_Poly)
  have vP: "descartes_list_int a b (coeffs (Poly P)) = descartes_list_int a b P"
    by (simp add: sw coeffs_Poly)
  have lenQ: "length Q = length P" using carried_repr_scalar_length_bl[OF headrepr] .
  have deg_eq: "length Q - Suc 0 = degree (Poly P)" using lenQ degP by simp
  \<comment> \<open>peel the popped node's abstract subtree off the tree-multiset\<close>
  have todo_split: "todo = butlast todo @ [(((l, r), k), e, s, Q)]"
    using todo_ne last_eq by (metis append_butlast_last_id)
  have tree_todo: "newton_gmp_tree_mset P l0 r0 k0 todo
      = newton_gmp_tree_mset P l0 r0 k0 (butlast todo)
        + mset (newton_tree1 (Poly P) a b e k s)"
    by (subst todo_split)
       (simp add: newton_gmp_tree_mset_Cons_bl newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  let ?m = "(a + b) / 2"
  let ?accb = "mset (dyadic_iv_acc_ivs l0 r0 k0 acc)"
  let ?treeb = "newton_gmp_tree_mset P l0 r0 k0 (butlast todo)"
  let ?v = "descartes_list_int a b P"
  let ?g = "newton_pol_gate (degree (Poly P)) e k s"
  let ?e' = "max 1 (e - 1)"
  let ?rootm = "poly (map_poly of_int (Poly P) :: rat poly) ?m = 0"
  have isroot: "newton_mid_is_root Q \<longleftrightarrow> ?rootm"
    using newton_mid_is_root_scalar_bl[OF headrepr] by simp
  show ?thesis
  proof (cases "?v = 0")
    case v0: True
    have step: "newton_gmp_step_bail st = (butlast todo, acc)"
      using todo_ne last_eq count v0 by (simp add: st newton_gmp_step_bail_def Let_def)
    have HU: "mset (newton_tree1 (Poly P) a b e k s) = {#}"
      using newton_tree1_mset_unfold_bl[OF P0 p0 sf ab] v0 by (simp add: vP sw)
    show ?thesis using step tree_todo HU by (simp add: st)
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have step: "newton_gmp_step_bail st = (butlast todo, acc @ [((l, r), k)])"
        using todo_ne last_eq count v0 v1 by (simp add: st newton_gmp_step_bail_def Let_def)
      have HU: "mset (newton_tree1 (Poly P) a b e k s) = {# (a, b) #}"
        using newton_tree1_mset_unfold_bl[OF P0 p0 sf ab] v0 v1 by (simp add: vP sw)
      show ?thesis using step tree_todo HU
        by (simp add: st dyadic_iv_acc_ivs_def dyadic_iv_node_iv_of_def a_def b_def)
    next
      case v1: False
      \<comment> \<open>the split branch mset — shared by gate-closed and window-reject\<close>
      let ?s' = "split_run_len_int (Poly P) a b s"
      have am: "a < ?m" and mb: "?m < b" using ab by simp_all
      \<comment> \<open>obligation 3, the srl-bridge: the model's decay from the EXACT child counts equals the
         abstract int-level \<open>split_run_len_int\<close> — the carried children scalar-rep the halves, so
         their exact carried counts ARE the abstract per-half \<open>descartes_list_int\<close> counts, and
         the midpoint-root test bridges via @{thm [source] newton_mid_is_root_scalar_bl}.\<close>
      have cl_repr: "carried_repr_scalar P a ?m (carried_left Q)"
        using carried_left_repr_scalar_bl[OF headrepr] by simp
      have cr_repr: "carried_repr_scalar P ?m b (carried_right Q)"
        using carried_right_repr_scalar_bl[OF headrepr] by simp
      have cl_count: "carried_descartes_count (carried_left Q) = descartes_list_int a ?m P"
        using carried_descartes_count_scalar_bl[OF cl_repr lenP] am by simp
      have cr_count: "carried_descartes_count (carried_right Q) = descartes_list_int ?m b P"
        using carried_descartes_count_scalar_bl[OF cr_repr lenP] mb by simp
      have srl_bridge:
        "newton_split_run_len ?rootm (carried_descartes_count (carried_left Q))
           (carried_descartes_count (carried_right Q)) s = ?s'"
        by (simp add: newton_split_run_len_def split_run_len_int_def Let_def
                      cl_count cr_count sw)
      have split_tp: "mset (dyadic_iv_acc_ivs l0 r0 k0 (snd (newton_split l r k e s Q (butlast todo, acc))))
          + newton_gmp_tree_mset P l0 r0 k0 (fst (newton_split l r k e s Q (butlast todo, acc)))
        = ?accb + ?treeb
          + ((if ?rootm then {# (?m, ?m) #} else {#})
             + mset (newton_tree1 (Poly P) a ?m ?e' (k + 1) ?s')
             + mset (newton_tree1 (Poly P) ?m b ?e' (k + 1) ?s'))"
      proof -
        have tl: "dyadic_iv_node_iv l0 r0 k0 (2 * l) (l + r) (Suc k) = (a, ?m)"
          unfolding mult_2 using dyadic_iv_node_iv_bisect_left_bl[of l0 r0 k0 l r k]
          by (simp add: a_def b_def)
        have tr: "dyadic_iv_node_iv l0 r0 k0 (l + r) (2 * r) (Suc k) = (?m, b)"
          unfolding mult_2 using dyadic_iv_node_iv_bisect_right_bl[of l0 r0 k0 l r k]
          by (simp add: a_def b_def)
        have tm: "dyadic_iv_node_iv l0 r0 k0 (l + r) (l + r) (Suc k) = (?m, ?m)"
          using dyadic_iv_node_iv_bisect_mid_bl[of l0 r0 k0 l r k] by (simp add: a_def b_def)
        have treec: "newton_gmp_tree_mset P l0 r0 k0
              [(((l + l, l + r), k + 1), ?e', ?s', carried_left Q),
               (((l + r, r + r), k + 1), ?e', ?s', carried_right Q)]
            = mset (newton_tree1 (Poly P) a ?m ?e' (k + 1) ?s')
              + mset (newton_tree1 (Poly P) ?m b ?e' (k + 1) ?s')"
          by (simp add: newton_gmp_tree_mset_Cons_bl newton_node_iv_of_def dyadic_iv_node_iv_of_def tl tr)
        have accc: "mset (dyadic_iv_acc_ivs l0 r0 k0
              (if ?rootm then acc @ [((l + r, l + r), k + 1)] else acc))
            = ?accb + (if ?rootm then {# (?m, ?m) #} else {#})"
          by (simp add: dyadic_iv_acc_ivs_def dyadic_iv_node_iv_of_def tm)
        show ?thesis
          unfolding newton_split_def Let_def
          by (simp only: prod.case fst_conv snd_conv newton_gmp_tree_mset_append_bl
                         isroot srl_bridge accc treec)
             (simp add: ac_simps)
      qed
      show ?thesis
      proof (cases ?g)
        case gF: False
        have step: "newton_gmp_step_bail st = newton_split l r k e s Q (butlast todo, acc)"
          using todo_ne last_eq count v0 v1 gF
          by (simp add: st newton_gmp_step_bail_def Let_def deg_eq)
        have HU: "mset (newton_tree1 (Poly P) a b e k s)
            = (if ?rootm then {# (?m, ?m) #} else {#})
              + mset (newton_tree1 (Poly P) a ?m ?e' (k + 1) ?s')
              + mset (newton_tree1 (Poly P) ?m b ?e' (k + 1) ?s')"
          using newton_tree1_mset_unfold_bl[OF P0 p0 sf ab] v0 v1 gF
          by (simp add: vP sw try_window_bail_int_def)
        show ?thesis using step split_tp tree_todo HU by (simp add: st add.assoc)
      next
        case gT: True
        \<comment> \<open>window-pick projection to the abstract block/Newton dispatch\<close>
        let ?cell = "\<lambda>(m, _::gmp_poly). dyadic_iv_node_iv l0 r0 k0 (fst (newton_window_child l r k e m))
                         (fst (snd (newton_window_child l r k e m)))
                         (snd (snd (newton_window_child l r k e m)))"
        let ?WI = "try_window_bail_int True a b (N_of e) (Poly P) ?v"
        have WP: "map_option ?cell (newton_window_pick_bail ?v e Q) = ?WI"
          by (rule newton_window_pick_bail_abs[OF headrepr len2 ab l0r0 canon])
             (simp_all add: a_def b_def)
        \<comment> \<open>the abstract v\<ge>2 branch under an open gate = dispatch on \<open>?WI\<close> (the bail cascade)\<close>
        have abs_gT: "mset (newton_tree1 (Poly P) a b e k s)
            = (case ?WI of
                 Some I \<Rightarrow> mset (newton_tree1 (Poly P) (fst I) (snd I) (e + 1) (k + (2 ^ e + 2)) s)
               | None \<Rightarrow> (if ?rootm then {# (?m, ?m) #} else {#})
                         + mset (newton_tree1 (Poly P) a ?m ?e' (k + 1) ?s')
                         + mset (newton_tree1 (Poly P) ?m b ?e' (k + 1) ?s'))"
          using newton_tree1_mset_unfold_bl[OF P0 p0 sf ab] v0 v1 gT
          by (simp add: vP sw Let_def)
        show ?thesis
        proof (cases "newton_window_pick_bail ?v e Q")
          case None
          have WInone: "?WI = None" using WP None by simp
          have step: "newton_gmp_step_bail st = newton_split l r k e s Q (butlast todo, acc)"
            using todo_ne last_eq count v0 v1 gT None
            by (simp add: st newton_gmp_step_bail_def Let_def deg_eq)
          have HU: "mset (newton_tree1 (Poly P) a b e k s)
              = (if ?rootm then {# (?m, ?m) #} else {#})
                + mset (newton_tree1 (Poly P) a ?m ?e' (k + 1) ?s')
                + mset (newton_tree1 (Poly P) ?m b ?e' (k + 1) ?s')"
            using abs_gT WInone by simp
          show ?thesis using step split_tp tree_todo HU by (simp add: st add.assoc)
        next
          case (Some mc)
          obtain m cand where mc_eq: "mc = (m, cand)" by (cases mc)
          obtain l' r' k' where dwc: "newton_window_child l r k e m = (l', r', k')"
            by (cases "newton_window_child l r k e m") auto
          have k'_eq: "k' = k + (2 ^ e + 2)"
            using dwc by (simp add: newton_window_child_def Let_def)
          have Icell: "?WI = Some (dyadic_iv_node_iv l0 r0 k0 l' r' k')"
            using WP Some mc_eq dwc by simp
          have step: "newton_gmp_step_bail st
              = (butlast todo @ [(((l', r'), k'), e + 1, s, cand)], acc)"
            using todo_ne last_eq count v0 v1 gT Some mc_eq dwc
            by (simp add: st newton_gmp_step_bail_def Let_def deg_eq)
          have treec: "newton_gmp_tree_mset P l0 r0 k0 [(((l', r'), k'), e + 1, s, cand)]
              = mset (newton_tree1 (Poly P)
                        (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                        (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k')) (e + 1) k' s)"
            by (simp add: newton_gmp_tree_mset_Cons_bl newton_node_iv_of_def dyadic_iv_node_iv_of_def)
          have HU: "mset (newton_tree1 (Poly P) a b e k s)
              = mset (newton_tree1 (Poly P)
                        (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                        (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k')) (e + 1) k' s)"
            using abs_gT Icell by (simp add: k'_eq)
          show ?thesis using step tree_todo treec HU by (simp add: st add.assoc)
        qed
      qed
    qed
  qed
qed

section \<open>The count-frame \<open>\<mu>\<close>-measure (LIFO termination)\<close>

text \<open>Copied \<open>cnl_\<close>-prefixed from @{text Rational_Solver}/@{text Rational_Refine}
  (the ET route's termination measure; not importable — see the session ROOT). The base
  \<open>mu\<close>/@{thm [source] mu_halve_strict}/@{thm [source] mu_subinterval_factor_strict} live in
  @{text Dsc_Misc} (frozen base), reused directly.\<close>


definition newton_todo_ivs ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> newton_gmp_node list \<Rightarrow> (rat \<times> rat) list" where
"newton_todo_ivs l0 r0 k0 todo = map (newton_node_iv_of l0 r0 k0) todo"

lemma newton_todo_ivs_Nil_bl[simp]: "newton_todo_ivs l0 r0 k0 [] = []"
  by (simp add: newton_todo_ivs_def)

lemma newton_todo_ivs_append_bl[simp]:
  "newton_todo_ivs l0 r0 k0 (xs @ ys)
     = newton_todo_ivs l0 r0 k0 xs @ newton_todo_ivs l0 r0 k0 ys"
  by (simp add: newton_todo_ivs_def)

lemma dyadic_iv_todo_mu_mset_one_smaller_bl:
  assumes "x < z"
  shows "mset rest + {# x #} < add_mset z (mset rest)"
proof -
  have "multp (<) (mset rest + {# x #}) (mset rest + {# z #})"
    by (rule one_step_implies_multp[where I = "mset rest" and J = "{# z #}" and K = "{# x #}"])
       (use assms in auto)
  thus ?thesis by (simp add: less_multiset_def)
qed

lemma dyadic_iv_todo_mu_mset_two_smaller_bl:
  assumes "x < z" and "y < z"
  shows "mset rest + {# x, y #} < add_mset z (mset rest)"
proof -
  have "multp (<) (mset rest + {# x, y #}) (mset rest + {# z #})"
    by (rule one_step_implies_multp[where I = "mset rest" and J = "{# z #}" and K = "{# x, y #}"])
       (use assms in auto)
  thus ?thesis by (simp add: less_multiset_def)
qed

lemma dyadic_iv_todo_mu_mset_list_rel_wf_bl:
  "wf {(todo', todo). dyadic_iv_todo_mu_mset \<delta> todo' < dyadic_iv_todo_mu_mset \<delta> todo}"
proof -
  have wf_ms_pred: "wfp ((<) :: nat multiset \<Rightarrow> nat multiset \<Rightarrow> bool)" by simp
  have wf_ms: "wf ({(x, y). x < y} :: (nat multiset \<times> nat multiset) set)"
    using wf_ms_pred by (simp add: wfp_def)
  show ?thesis
    using wf_inv_image[OF wf_ms, of "\<lambda>todo. dyadic_iv_todo_mu_mset \<delta> todo"]
    by (simp add: inv_image_def)
qed

text \<open>Every window child chosen by @{const newton_window_pick_bail} sits within the grid: its start
  index @{term m} satisfies @{term "m + 4 \<le> int (4 * N_of e)"} (block \<open>m=0\<close>: trivial; block
  \<open>m=s-4\<close>: @{term "s = 4 * N_of e"}; Newton \<open>m = kn-2\<close>: @{thm [source] newton_snap_kn_le_bl}).\<close>
lemma newton_window_pick_bail_m_bound:
  assumes "newton_window_pick_bail v e Q = Some (m, cand)"
  shows "m + 4 \<le> int (4 * N_of e)"
proof -
  have s4N: "(2 :: nat) ^ (2 ^ e + 2) = 4 * N_of e" using four_N_of_pow2 by simp
  have s4Ni: "(2::int) ^ (2 ^ e + 2) = int (4 * N_of e)" using s4N by simp
  have N1: "1 \<le> N_of e" using N_of_ge_2[of e] by simp
  \<comment> \<open>Newton branch: @{term m} comes from @{const newton_try_side} (loc0 or loc1)\<close>
  have side: "\<And>loc. newton_try_side loc v e Q = Some (m, cand)
              \<Longrightarrow> m + 4 \<le> int (4 * N_of e)"
  proof -
    fix loc :: "nat \<Rightarrow> gmp_poly \<Rightarrow> bool \<times> int \<times> int"
    assume "newton_try_side loc v e Q = Some (m, cand)"
    then obtain num den where
      "(let kn = newton_snap_kn e num den in
          if newton_wok v e (kn - 2) Q then Some (kn - 2, newton_wcand e (kn - 2) Q) else None)
         = Some (m, cand)"
      by (cases "loc v Q") (auto simp: newton_try_side_def Let_def split: if_splits)
    hence m_eq: "m = newton_snap_kn e num den - 2"
      by (simp add: Let_def split: if_splits)
    have "newton_snap_kn e num den + 2 \<le> 4 * N_of e" by (rule newton_snap_kn_le_bl)
    moreover have "2 \<le> newton_snap_kn e num den" by (rule newton_snap_kn_ge2_bl)
    ultimately show "m + 4 \<le> int (4 * N_of e)" using m_eq by simp
  qed
  \<comment> \<open>Every pick is a @{const newton_try_side} accept: @{const newton_window_pick_bail} is an \<open>if\<close>
     choosing which side to try, and \<open>side\<close> bounds either one.\<close>
  show ?thesis
    using assms side
    by (auto simp: newton_window_pick_bail_def split: if_splits)
qed

text \<open>Measure decrease: one @{const newton_gmp_step_bail} strictly decreases the count-frame
  \<open>\<mu>\<close>-multiset. The pop removes \<open>\<mu>(a,b)\<close>; \<open>v=0/1\<close> just removes it; \<open>v\<ge>2\<close> replaces it either by two
  bisection halves (both strictly smaller, @{thm [source] mu_halve_strict}) or by one window child of
  width \<open>(b-a)/N_of e\<close> with \<open>N_of e \<ge> 2\<close> (strictly smaller, @{thm [source] mu_subinterval_factor_strict});
  for \<open>v\<ge>2\<close> the width \<open>> \<delta>\<close> is forced by @{term small_fast}.\<close>
lemma newton_gmp_step_bail_mu_decreases:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and l0r0: "l0 < r0"
    and ne: "fst st \<noteq> []"
    and inv: "\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd"
  shows "dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst (newton_gmp_step_bail st)))
       < dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st))"
proof -
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with ne have todo_ne: "todo \<noteq> []" by simp
  obtain lr k e s Q where last_eq0: "last todo = ((lr, k), e, s, Q)"
    by (cases "last todo") auto
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), e, s, Q)" using last_eq0 lr_eq by simp
  have inv': "\<forall>nd \<in> set todo. newton_gmp_node_inv P l0 r0 k0 nd" using inv by (simp add: st)
  have ninv: "newton_gmp_node_inv P l0 r0 k0 (((l, r), k), e, s, Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)"
  define b where "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  have headrepr: "carried_repr_scalar P a b Q"
    using ninv by (simp add: newton_gmp_node_inv_def newton_node_iv_of_def
                              dyadic_iv_node_iv_of_def Let_def a_def b_def)
  have ab: "a < b"
    using newton_gmp_node_inv_ordered_bl[OF ninv]
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using carried_descartes_count_scalar_bl[OF headrepr len] ab by simp
  \<comment> \<open>pop peels the head interval \<open>(a,b)\<close> off the measure multiset\<close>
  have todo_split: "todo = butlast todo @ [(((l, r), k), e, s, Q)]"
    using todo_ne last_eq by (metis append_butlast_last_id)
  let ?rank = "dyadic_iv_interval_mu \<delta>"
  let ?m = "(a + b) / 2"
  let ?e' = "max 1 (e - 1)"
  let ?R = "mset (map ?rank (newton_todo_ivs l0 r0 k0 (butlast todo)))"
  have niv: "newton_node_iv_of l0 r0 k0 (((l, r), k), e, s, Q) = (a, b)"
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  have old: "dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st)) = add_mset (?rank (a, b)) ?R"
    unfolding st fst_conv
    by (subst todo_split)
       (simp add: dyadic_iv_todo_mu_mset_def newton_todo_ivs_def niv)
  \<comment> \<open>the two split-child intervals and the shared width\<close>
  have tl: "dyadic_iv_node_iv l0 r0 k0 (2 * l) (l + r) (Suc k) = (a, ?m)"
    unfolding mult_2 using dyadic_iv_node_iv_bisect_left_bl[of l0 r0 k0 l r k]
    by (simp add: a_def b_def)
  have tr: "dyadic_iv_node_iv l0 r0 k0 (l + r) (2 * r) (Suc k) = (?m, b)"
    unfolding mult_2 using dyadic_iv_node_iv_bisect_right_bl[of l0 r0 k0 l r k]
    by (simp add: a_def b_def)
  show ?thesis
  proof (cases "descartes_list_int a b P = 0 \<or> descartes_list_int a b P = 1")
    case True
    have stf: "fst (newton_gmp_step_bail st) = butlast todo"
      using todo_ne last_eq True count by (auto simp: st newton_gmp_step_bail_def Let_def)
    show ?thesis unfolding stf old
      by (simp add: dyadic_iv_todo_mu_mset_def newton_todo_ivs_def
                    subset_implies_multp less_multiset_def)
  next
    case False
    have v0: "descartes_list_int a b P \<noteq> 0" and v1: "descartes_list_int a b P \<noteq> 1"
      using False by auto
    have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
    proof (rule ccontr)
      assume "\<not> \<delta> < of_rat b - of_rat a"
      then have "of_rat b - of_rat a \<le> \<delta>" by linarith
      then have "descartes_list_int a b P \<le> 1" using small_fast[OF ab] by simp
      with v0 v1 show False by simp
    qed
    have half_lt1: "?rank (a, ?m) < ?rank (a, b)"
      using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      by (simp add: dyadic_iv_interval_mu_def of_rat_add of_rat_divide)
    have half_lt2: "?rank (?m, b) < ?rank (a, b)"
      using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      by (simp add: dyadic_iv_interval_mu_def of_rat_add of_rat_divide)
    \<comment> \<open>the split step and its measure (shared by gate-closed and window-reject)\<close>
    have split_mu: "dyadic_iv_todo_mu_mset \<delta>
            (newton_todo_ivs l0 r0 k0 (fst (newton_split l r k e s Q (butlast todo, acc))))
          < dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st))"
    proof -
      have "dyadic_iv_todo_mu_mset \<delta>
              (newton_todo_ivs l0 r0 k0 (fst (newton_split l r k e s Q (butlast todo, acc))))
          = ?R + {# ?rank (a, ?m), ?rank (?m, b) #}"
        by (simp add: newton_split_def Let_def dyadic_iv_todo_mu_mset_def newton_todo_ivs_def
                      newton_node_iv_of_def dyadic_iv_node_iv_of_def tl tr)
      also have "\<dots> < add_mset (?rank (a, b)) ?R"
        by (rule dyadic_iv_todo_mu_mset_two_smaller_bl[OF half_lt1 half_lt2])
      finally show ?thesis using old by simp
    qed
    show ?thesis
    proof (cases "newton_pol_gate (length Q - Suc 0) e k s")
      case gF: False
      have "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
        using todo_ne last_eq count v0 v1 gF
        by (simp add: st newton_gmp_step_bail_def Let_def)
      thus ?thesis using split_mu by simp
    next
      case gT: True
      show ?thesis
      proof (cases "newton_window_pick_bail (descartes_list_int a b P) e Q")
        case None
        have "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
          using todo_ne last_eq count v0 v1 gT None
          by (simp add: st newton_gmp_step_bail_def Let_def)
        thus ?thesis using split_mu by simp
      next
        case (Some mc)
        obtain m cand where mc_eq: "mc = (m, cand)" by (cases mc)
        obtain l' r' k' where dwc: "newton_window_child l r k e m = (l', r', k')"
          by (cases "newton_window_child l r k e m") auto
        have mb: "m + 4 \<le> int (4 * N_of e)"
          using newton_window_pick_bail_m_bound[OF Some[unfolded mc_eq]] .
        have cellw: "?rank (dyadic_iv_node_iv l0 r0 k0 l' r' k') < ?rank (a, b)"
        proof -
          have cell: "dyadic_iv_node_iv l0 r0 k0 l' r' k'
              = (a + of_int m * (b - a) / of_nat (4 * N_of e),
                 a + of_int (m + 4) * (b - a) / of_nat (4 * N_of e))"
            using node_iv_window_child_bl[OF l0r0 mb, where l = l and r = r and k = k] dwc
            by (simp add: a_def b_def)
          have Npos: "(0::rat) < of_nat (4 * N_of e)" using N_of_ge_2[of e] by simp
          have wid: "snd (dyadic_iv_node_iv l0 r0 k0 l' r' k') - fst (dyadic_iv_node_iv l0 r0 k0 l' r' k')
              = (b - a) / of_nat (N_of e)"
            unfolding cell fst_conv snd_conv
            using Npos by (simp add: field_simps of_nat_mult)
          have widr: "of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                      - of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                    = (of_rat b - of_rat a) / of_nat (N_of e)"
          proof -
            have "of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                  - of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                = of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k')
                          - fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))"
              by (simp add: of_rat_diff)
            also have "\<dots> = of_rat ((b - a) / of_nat (N_of e))" using wid by simp
            also have "\<dots> = (of_rat b - of_rat a) / of_nat (N_of e)"
              by (simp add: of_rat_divide of_rat_diff of_rat_of_nat_eq)
            finally show ?thesis .
          qed
          show ?thesis
            unfolding dyadic_iv_interval_mu_def prod.sel
            by (rule mu_subinterval_factor_strict[OF \<delta>_pos _ _ _ widr])
               (use ab \<delta>_lt N_of_ge_2[of e] in \<open>simp_all add: of_rat_less\<close>)
        qed
        have stf: "fst (newton_gmp_step_bail st) = butlast todo @ [(((l', r'), k'), e + 1, s, cand)]"
          using todo_ne last_eq count v0 v1 gT Some mc_eq dwc
          by (simp add: st newton_gmp_step_bail_def Let_def)
        have "dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst (newton_gmp_step_bail st)))
            = ?R + {# ?rank (dyadic_iv_node_iv l0 r0 k0 l' r' k') #}"
          by (simp add: stf dyadic_iv_todo_mu_mset_def newton_todo_ivs_def
                        newton_node_iv_of_def dyadic_iv_node_iv_of_def)
        also have "\<dots> < add_mset (?rank (a, b)) ?R"
          by (rule dyadic_iv_todo_mu_mset_one_smaller_bl[OF cellw])
        finally show ?thesis using old by simp
      qed
    qed
  qed
qed

section \<open>Window-child representation and node-invariant preservation\<close>

text \<open>The window child's count-frame node carries @{const newton_wcand}: its interval
  (@{thm [source] node_iv_window_child_bl}, the \<open>4N\<close>-form) matches @{const newton_wcand}'s
  representation interval (@{thm [source] newton_wcand_repr_scalar_bl}, the \<open>s = 2^(2^e+2)\<close>-form)
  because \<open>2^(2^e+2) = 4 * N_of e\<close>.\<close>
lemma newton_window_child_repr_bl:
  assumes repr: "carried_repr_scalar P a b Q" and mb: "m + 4 \<le> int (4 * N_of e)" and l0r0: "l0 < r0"
    and abdef: "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)" "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
    and dwc: "newton_window_child l r k e m = (l', r', k')"
  shows "carried_repr_scalar P (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                               (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k')) (newton_wcand e m Q)"
proof -
  have s4N: "(of_int (2 ^ (2 ^ e + 2)) :: rat) = of_nat (4 * N_of e)"
    by (metis spow_int_bl of_int_of_nat_eq)
  have iveq: "dyadic_iv_node_iv l0 r0 k0 l' r' k'
      = (a + of_int m * (b - a) / of_nat (4 * N_of e),
         a + of_int (m + 4) * (b - a) / of_nat (4 * N_of e))"
    using node_iv_window_child_bl[OF l0r0 mb, where l = l and r = r and k = k] dwc
    by (simp add: abdef)
  \<comment> \<open>bridge the \<open>4N\<close>-form (node) to the \<open>s = 2^(2^e+2)\<close>-form (@{const newton_wcand})\<close>
  have e1: "a + of_int m * (b - a) / of_nat (4 * N_of e)
          = a + (of_int (m) / of_int (2 ^ (2 ^ e + 2))) * (b - a)"
    by (simp add: s4N of_int_of_nat_eq mult.commute N_of_def)
  have e2: "a + of_int (m + 4) * (b - a) / of_nat (4 * N_of e)
          = a + (of_int (m + 4) / of_int (2 ^ (2 ^ e + 2))) * (b - a)"
    by (simp add: s4N of_int_of_nat_eq mult.commute N_of_def)
  show ?thesis
    unfolding iveq fst_conv snd_conv e1 e2
    using newton_wcand_repr_scalar_bl[OF repr] by simp
qed


text \<open>Invariant preservation: one @{const newton_gmp_step_bail} preserves the per-node invariant on the
  whole worklist. Split children carry @{const carried_left}/@{const carried_right}; the window child
  carries @{const newton_wcand} (@{thm [source] newton_window_child_repr_bl}); ordering follows from
  positive width.\<close>
lemma newton_gmp_node_inv_preserved_bl:
  assumes lenP: "0 < length P" and l0r0: "l0 < r0"
    and inv: "\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd"
  shows "\<forall>nd \<in> set (fst (newton_gmp_step_bail st)). newton_gmp_node_inv P l0 r0 k0 nd"
proof (cases "fst st = []")
  case True
  thus ?thesis by (cases st) (simp add: newton_gmp_step_bail_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain lr k e s Q where last_eq0: "last todo = ((lr, k), e, s, Q)"
    by (cases "last todo") auto
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), e, s, Q)" using last_eq0 lr_eq by simp
  have inv': "\<forall>nd \<in> set todo. newton_gmp_node_inv P l0 r0 k0 nd" using inv by (simp add: st)
  have ninv: "newton_gmp_node_inv P l0 r0 k0 (((l, r), k), e, s, Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)"
  define b where "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  have headrepr: "carried_repr_scalar P a b Q"
    using ninv by (simp add: newton_gmp_node_inv_def newton_node_iv_of_def
                              dyadic_iv_node_iv_of_def Let_def a_def b_def)
  have ab: "a < b"
    using newton_gmp_node_inv_ordered_bl[OF ninv]
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using carried_descartes_count_scalar_bl[OF headrepr lenP] ab by simp
  have rest_inv: "\<forall>nd \<in> set (butlast todo). newton_gmp_node_inv P l0 r0 k0 nd"
    using inv' by (auto dest: in_set_butlastD)
  let ?m = "(a + b) / 2"
  let ?e' = "max 1 (e - 1)"
  have cl: "newton_gmp_node_inv P l0 r0 k0 (((l + l, l + r), k + 1), ?e', s', carried_left Q)" for s'
    unfolding newton_gmp_node_inv_def Let_def newton_node_iv_of_def dyadic_iv_node_iv_of_def prod.sel mult_2
    using carried_left_repr_scalar_bl[OF headrepr] dyadic_iv_node_iv_bisect_left_bl[of l0 r0 k0 l r k] ab
    by (simp add: a_def b_def)
  have cr: "newton_gmp_node_inv P l0 r0 k0 (((l + r, r + r), k + 1), ?e', s', carried_right Q)" for s'
    unfolding newton_gmp_node_inv_def Let_def newton_node_iv_of_def dyadic_iv_node_iv_of_def prod.sel mult_2
    using carried_right_repr_scalar_bl[OF headrepr] dyadic_iv_node_iv_bisect_right_bl[of l0 r0 k0 l r k] ab
    by (simp add: a_def b_def)
  have split_inv: "\<forall>nd \<in> set (fst (newton_split l r k e s Q (butlast todo, acc))).
                     newton_gmp_node_inv P l0 r0 k0 nd"
    using rest_inv cl cr by (auto simp: newton_split_def Let_def)
  show ?thesis
  proof (cases "descartes_list_int a b P = 0 \<or> descartes_list_int a b P = 1")
    case True
    have "fst (newton_gmp_step_bail st) = butlast todo"
      using todo_ne last_eq True count by (auto simp: st newton_gmp_step_bail_def Let_def)
    thus ?thesis using rest_inv by simp
  next
    case False
    have v0: "descartes_list_int a b P \<noteq> 0" and v1: "descartes_list_int a b P \<noteq> 1"
      using False by auto
    show ?thesis
    proof (cases "newton_pol_gate (length Q - Suc 0) e k s")
      case gF: False
      have "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
        using todo_ne last_eq count v0 v1 gF by (simp add: st newton_gmp_step_bail_def Let_def)
      thus ?thesis using split_inv by simp
    next
      case gT: True
      show ?thesis
      proof (cases "newton_window_pick_bail (descartes_list_int a b P) e Q")
        case None
        have "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
          using todo_ne last_eq count v0 v1 gT None by (simp add: st newton_gmp_step_bail_def Let_def)
        thus ?thesis using split_inv by simp
      next
        case (Some mc)
        obtain m cand where mc_eq: "mc = (m, cand)" by (cases mc)
        obtain l' r' k' where dwc: "newton_window_child l r k e m = (l', r', k')"
          by (cases "newton_window_child l r k e m") auto
        have mb: "m + 4 \<le> int (4 * N_of e)"
          using newton_window_pick_bail_m_bound[OF Some[unfolded mc_eq]] .
        have cand_eq: "cand = newton_wcand e m Q"
        proof -
          from Some[unfolded mc_eq]
          have pk: "newton_window_pick_bail (descartes_list_int a b P) e Q = Some (m, cand)" .
          \<comment> \<open>every pick is a @{const newton_try_side} accept at one of the two probe sides\<close>
          from pk obtain loc where
            "newton_try_side loc (descartes_list_int a b P) e Q = Some (m, cand)"
            by (auto simp: newton_window_pick_bail_def split: if_splits)
          thus ?thesis by (rule newton_try_side_cand_bl)
        qed
        have childrepr: "carried_repr_scalar P (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                           (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k')) cand"
          unfolding cand_eq
          by (rule newton_window_child_repr_bl[OF headrepr mb l0r0 a_def b_def dwc])
        have childord: "fst (dyadic_iv_node_iv l0 r0 k0 l' r' k') < snd (dyadic_iv_node_iv l0 r0 k0 l' r' k')"
        proof -
          have "dyadic_iv_node_iv l0 r0 k0 l' r' k'
              = (a + of_int m * (b - a) / of_nat (4 * N_of e),
                 a + of_int (m + 4) * (b - a) / of_nat (4 * N_of e))"
            using node_iv_window_child_bl[OF l0r0 mb, where l = l and r = r and k = k] dwc
            by (simp add: a_def b_def)
          moreover have "(0::rat) < of_nat (4 * N_of e)" using N_of_ge_2[of e] by simp
          ultimately show ?thesis using ab by (simp add: divide_strict_right_mono)
        qed
        have childinv: "newton_gmp_node_inv P l0 r0 k0 (((l', r'), k'), e + 1, s, cand)"
          using childrepr childord
          by (simp add: newton_gmp_node_inv_def Let_def newton_node_iv_of_def dyadic_iv_node_iv_of_def)
        have "fst (newton_gmp_step_bail st) = butlast todo @ [(((l', r'), k'), e + 1, s, cand)]"
          using todo_ne last_eq count v0 v1 gT Some mc_eq dwc
          by (simp add: st newton_gmp_step_bail_def Let_def)
        thus ?thesis using rest_inv childinv by auto
      qed
    qed
  qed
qed

text \<open>The order-agnostic multiset invariant of the pure LIFO driver: well-founded induction on the
  count-frame \<open>\<mu>\<close>-measure (@{thm [source] newton_gmp_step_bail_mu_decreases}), combining the one-step
  preservation @{thm [source] newton_gmp_step_bail_tree_preservation} with the node-invariant
  preservation @{thm [source] newton_gmp_node_inv_preserved_bl}.\<close>
lemma newton_gmp_main_bail_mset:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len2: "Suc 0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and sf: "square_free (map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P" and l0r0: "l0 < r0"
    and inv: "\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd"
  shows "mset (dyadic_iv_acc_ivs l0 r0 k0 (snd (newton_gmp_main_bail st)))
       = mset (dyadic_iv_acc_ivs l0 r0 k0 (snd st)) + newton_gmp_tree_mset P l0 r0 k0 (fst st)"
  using inv
proof (induction st rule: wf_induct_rule[OF wf_inv_image[OF dyadic_iv_todo_mu_mset_list_rel_wf_bl[where \<delta> = \<delta>],
    where f = "\<lambda>st. newton_todo_ivs l0 r0 k0 (fst st)"]])
  case (1 st)
  have len: "0 < length P" using len2 by simp
  show ?case
  proof (cases "fst st = []")
    case True
    have "newton_gmp_main_bail st = st"
      using True by (cases st) (simp add: newton_gmp_main_bail.simps)
    thus ?thesis using True by simp
  next
    case False
    have unfold: "newton_gmp_main_bail st = newton_gmp_main_bail (newton_gmp_step_bail st)"
    proof -
      obtain todo acc where st: "st = (todo, acc)" by (cases st)
      with False have tne: "todo \<noteq> []" by simp
      show ?thesis by (subst newton_gmp_main_bail.simps) (simp add: st tne split: list.splits)
    qed
    have dec: "(newton_gmp_step_bail st, st)
        \<in> inv_image {(todo', todo). dyadic_iv_todo_mu_mset \<delta> todo' < dyadic_iv_todo_mu_mset \<delta> todo}
            (\<lambda>st. newton_todo_ivs l0 r0 k0 (fst st))"
      using newton_gmp_step_bail_mu_decreases[OF \<delta>_pos len small_fast l0r0 False "1.prems"]
      by (simp add: inv_image_def)
    have step_inv: "\<forall>nd \<in> set (fst (newton_gmp_step_bail st)). newton_gmp_node_inv P l0 r0 k0 nd"
      using newton_gmp_node_inv_preserved_bl[OF len l0r0 "1.prems"] .
    show ?thesis
      unfolding unfold
      using "1.IH"[OF dec step_inv]
        newton_gmp_step_bail_tree_preservation[OF P0 canon len2 sf l0r0 False "1.prems"]
      by simp
  qed
qed

text \<open>Pure-model seed capstone. From the single seed node @{term "(((l_num,r_num),k),e0,P)"} (count-frame
  interval \<open>(0,1)\<close>, carried polynomial @{term P}, empty acc), the pure driver's accepted intervals equal
  @{term "newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P)"} as multisets. The seed carries the identity
  representation @{term "carried_repr_scalar P 0 1 P"} (\<open>c=1\<close>), and @{const newton_tree1} at the seed is
  @{const newdsc_pol_bail_int} by definition.\<close>
lemma newton_gmp_main_bail_seed_mset:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len2: "Suc 0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and sf: "square_free (map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P" and lr: "l_num < r_num"
  shows "mset (dyadic_iv_acc_ivs l_num r_num k
            (snd (newton_gmp_main_bail ([(((l_num, r_num), k), e0, 0, P)], []))))
       = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))"
proof -
  have node01: "dyadic_iv_node_iv l_num r_num k l_num r_num k = (0, 1)"
  proof -
    have "dyadic_rat l_num k < dyadic_rat r_num k"
      using lr by (simp add: dyadic_rat_def divide_strict_right_mono)
    hence "dyadic_rat r_num k - dyadic_rat l_num k \<noteq> 0" by simp
    thus ?thesis by (simp add: dyadic_iv_node_iv_def Let_def)
  qed
  have seedrepr: "carried_repr_scalar P 0 1 P"
    unfolding carried_repr_scalar_def
    by (rule exI[of _ 1]) (simp add: local_poly_rat_def smult_list_def rev_map)
  have seed_inv: "\<forall>nd \<in> set (fst ([(((l_num, r_num), k), e0, 0, P)],
                                  [] :: ((int \<times> int) \<times> nat) list)).
      newton_gmp_node_inv P l_num r_num k nd"
    by (simp add: newton_gmp_node_inv_def newton_node_iv_of_def dyadic_iv_node_iv_of_def Let_def
                  node01 seedrepr)
  have l6: "mset (dyadic_iv_acc_ivs l_num r_num k
              (snd (newton_gmp_main_bail ([(((l_num, r_num), k), e0, 0, P)], []))))
      = mset (dyadic_iv_acc_ivs l_num r_num k (snd ([(((l_num, r_num), k), e0, 0, P)], [])))
        + newton_gmp_tree_mset P l_num r_num k (fst ([(((l_num, r_num), k), e0, 0, P)], []))"
    using newton_gmp_main_bail_mset[OF \<delta>_pos len2 small_fast sf P0 canon lr seed_inv] by simp
  have seedtree: "newton_gmp_tree_mset P l_num r_num k [(((l_num, r_num), k), e0, 0, P)]
      = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))"
    by (simp add: newton_gmp_tree_mset_Cons_bl newton_node_iv_of_def dyadic_iv_node_iv_of_def node01
                  newton_tree1_def newdsc_pol_bail_int_def)
  show ?thesis using l6 by (simp add: dyadic_iv_acc_ivs_def seedtree)
qed

subsection \<open>Budget infrastructure\<close>

text \<open>Per-node worklist/accept append budgets: a node whose count-frame width takes \<open>\<mu>\<close>
  bisections to fall below \<open>\<delta>\<close> can spawn at most \<open>2^(\<mu>+1)-2\<close> further worklist nodes and
  \<open>2^(\<mu>+1)-1\<close> accepted intervals. Copied from @{text Rational_Solver}; the Newton window branch
  reuses them via the SINGLE-child variants (window child \<open>\<mu>\<close> strictly below the parent's).\<close>


lemma dyadic_iv_interval_todo_budget_nonneg_bl[simp]: "0 \<le> dyadic_iv_interval_todo_budget \<delta> I"
  unfolding dyadic_iv_interval_todo_budget_def by simp

lemma dyadic_iv_todo_append_budget_nonneg_bl[simp]: "0 \<le> dyadic_iv_todo_append_budget \<delta> todo"
  unfolding dyadic_iv_todo_append_budget_def by (induction todo) auto

lemma dyadic_iv_interval_acc_budget_pos_bl[simp]: "0 < dyadic_iv_interval_acc_budget \<delta> I"
proof -
  have "(1::nat) < 2 ^ Suc (dyadic_iv_interval_mu \<delta> I)" by (rule one_less_power) simp_all
  thus ?thesis unfolding dyadic_iv_interval_acc_budget_def by linarith
qed

lemma dyadic_iv_todo_acc_budget_nonneg_bl[simp]: "0 \<le> dyadic_iv_todo_acc_budget \<delta> todo"
  unfolding dyadic_iv_todo_acc_budget_def
  by (induction todo) (auto simp: dyadic_iv_interval_acc_budget_pos_bl[THEN order_less_imp_le])

lemma blr_budget_power_children_le_bl:
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

lemma blr_todo_budget_children_le_bl:
  assumes "x < z" and "y < z"
  shows "2 + (int ((2::nat) ^ Suc x) - 2) + (int ((2::nat) ^ Suc y) - 2)
       \<le> int ((2::nat) ^ Suc z) - 2"
  using blr_budget_power_children_le_bl[OF assms] by linarith

lemma blr_acc_budget_children_le_bl:
  assumes "x < z" and "y < z"
  shows "1 + (int ((2::nat) ^ Suc x) - 1) + (int ((2::nat) ^ Suc y) - 1)
       \<le> int ((2::nat) ^ Suc z) - 1"
  using blr_budget_power_children_le_bl[OF assms] by linarith

text \<open>Window branch (ONE child, strictly smaller \<open>\<mu>\<close>): the child's budget alone is covered by
  the parent's, net worklist size unchanged, no accepted interval added.\<close>
lemma blr_budget_power_single_le_bl:
  assumes "x < z" shows "int ((2::nat) ^ Suc x) \<le> int ((2::nat) ^ Suc z)"
  using assms by (simp add: power_increasing)

lemma blr_todo_budget_single_le_bl:
  assumes "x < z" shows "(int ((2::nat) ^ Suc x) - 2) \<le> int ((2::nat) ^ Suc z) - 2"
  using blr_budget_power_single_le_bl[OF assms] by linarith

lemma blr_acc_budget_single_le_bl:
  assumes "x < z" shows "(int ((2::nat) ^ Suc x) - 1) \<le> int ((2::nat) ^ Suc z) - 1"
  using blr_budget_power_single_le_bl[OF assms] by linarith

text \<open>The NewDsc per-node budget (copied \<open>cnl_\<close>-prefixed from @{text Rational_Newton_Endpoint_Refine};
  this is the CORRECT shape for a window solver, NOT the ET \<open>k + \<mu> + 1\<close> dyadic-depth bound which
  is bisection-only). The potential is \<open>e + \<mu>(a,b)\<close> (scheduling exponent + interval \<open>\<mu>\<close>): it
  bounds the worst-case exponent reachable, hence the window grid \<open>4 * N_of (e+\<mu>)\<close> (hence the
  dyadic-\<open>k\<close> jumps \<open>2^e+2\<close>), and it is NON-INCREASING parent\<rightarrow>child (window: \<open>+1\<close> exponent offset by
  the strict \<open>\<mu>\<close>-drop; split: \<open>e' \<le> e\<close> and \<open>\<mu>\<close> drops).\<close>
lemma blr_N_of_mono_bl:
  assumes "e \<le> f" shows "N_of e \<le> N_of f"
proof -
  have "(2::nat) ^ e \<le> 2 ^ f" by (rule power_increasing[OF assms]) simp
  thus ?thesis unfolding N_of_def by (rule power_increasing) simp
qed


subsection \<open>The projection \<open>\<alpha>\<close> from the concrete loop state to the pure @{const newton_gmp_main_bail} state\<close>

text \<open>The concrete @{typ newton_loop_state} is @{term "((todo, qtodo, es, ss, cs), acc)"} with the
  interval vector @{term todo}, the carried-poly stack @{term qtodo}, the exponent list @{term es}
  (all parallel), and the accepted vector @{term acc}. It projects to the pure @{const newton_gmp_main_bail}
  state: each todo node pairs its interval triple with its exponent and carried poly
  (@{typ newton_gmp_node} \<open>= (((int\<times>int)\<times>nat) \<times> nat \<times> gmp_poly)\<close>); acc drops the poly/exponent.
  This mirrors the ET \<open>bilr_alpha\<close> with the extra \<open>es\<close> column woven in.\<close>

definition blr_alpha_todo :: "newton_loop_state \<Rightarrow> newton_gmp_node list" where
"blr_alpha_todo st = (case st of ((todo, qtodo, es, ss, cs), _) \<Rightarrow>
   zip (dyadic_interval_vec_triples todo) (zip es (zip ss qtodo)))"

definition blr_alpha_acc :: "newton_loop_state \<Rightarrow> ((int \<times> int) \<times> nat) list" where
"blr_alpha_acc st = dyadic_interval_vec_triples (snd st)"

definition blr_alpha :: "newton_loop_state \<Rightarrow> newton_gmp_state" where
"blr_alpha st = (blr_alpha_todo st, blr_alpha_acc st)"

lemma blr_alpha_todo_length_bl:
  assumes "newton_loop_state_invar st"
  shows "length (blr_alpha_todo st) = (case st of (((lns, _, _), _, _), _) \<Rightarrow> length lns)"
proof -
  obtain todo qtodo es ss cs acc where st: "st = ((todo, qtodo, es, ss, cs), acc)" by (cases st) auto
  obtain lns rns ks where todo: "todo = (lns, rns, ks)" by (cases todo) auto
  from assms have "length lns = length rns" and "length lns = length ks"
    and "length qtodo = length lns" and "length es = length lns"
    and "length ss = length lns"
    by (auto simp: st todo newton_loop_state_invar_def Let_def
             dyadic_interval_vec_invar_def)
  thus ?thesis
    by (simp add: st todo blr_alpha_todo_def dyadic_interval_vec_triples_def)
qed

lemma blr_alpha_cond_bl:
  assumes "newton_loop_state_invar st"
  shows "newton_loop_cond st \<longleftrightarrow> blr_alpha_todo st \<noteq> []"
proof -
  obtain todo qtodo es ss cs acc where st: "st = ((todo, qtodo, es, ss, cs), acc)" by (cases st) auto
  obtain lns rns ks where todo: "todo = (lns, rns, ks)" by (cases todo) auto
  have "newton_loop_cond st \<longleftrightarrow> lns \<noteq> []"
    by (simp add: st todo newton_loop_cond_def Let_def)
  also have "\<dots> \<longleftrightarrow> length (blr_alpha_todo st) \<noteq> 0"
    using blr_alpha_todo_length_bl[OF assms] by (simp add: st todo)
  finally show ?thesis by simp
qed

lemma newton_gmp_main_bail_Nil: "newton_gmp_main_bail ([], acc) = ([], acc)"
  by (simp add: newton_gmp_main_bail.simps)

subsection \<open>Body: \<open>\<alpha>\<close>-relation list helpers (\<open>butlast\<close>/\<open>last\<close> of the zipped columns)\<close>

lemma blr_butlast_zip_bl':
  "length xs = length ys \<Longrightarrow> butlast (zip xs ys) = zip (butlast xs) (butlast ys)"
  by (induction xs ys rule: list_induct2) auto

lemma blr_last_zip_bl':
  "length xs = length ys \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> last (zip xs ys) = (last xs, last ys)"
proof (induction xs ys rule: list_induct2)
  case (Cons x xs y ys)
  show ?case by (cases "xs = []") (use Cons in auto)
qed simp

lemma blr_triples_butlast_bl:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)
       = butlast (dyadic_interval_vec_triples (lns, rns, ks))"
  using assms
  by (simp add: dyadic_interval_vec_triples_simps
      dyadic_interval_vec_invar_def blr_butlast_zip_bl'[symmetric] length_zip)

lemma blr_triples_append_bl:
  assumes "dyadic_interval_vec_invar (alns, arns, aks)"
  shows "dyadic_interval_vec_triples (alns @ [x], arns @ [y], aks @ [z])
       = dyadic_interval_vec_triples (alns, arns, aks) @ [((x, y), z)]"
  using assms
  by (simp add: dyadic_interval_vec_triples_simps dyadic_interval_vec_invar_def zip_append)

lemma blr_triples_last_bl:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)" and "lns \<noteq> []"
  shows "last (dyadic_interval_vec_triples (lns, rns, ks)) = ((last lns, last rns), last ks)"
proof -
  from assms have l: "length lns = length rns" "length lns = length ks" "lns \<noteq> []"
    by (auto simp: dyadic_interval_vec_invar_def)
  hence ne: "zip lns rns \<noteq> []" by (cases lns) auto
  have "last (zip (zip lns rns) ks) = (last (zip lns rns), last ks)"
    using l ne by (simp add: blr_last_zip_bl' length_zip)
  also have "last (zip lns rns) = (last lns, last rns)" using l by (simp add: blr_last_zip_bl')
  finally show ?thesis by (simp add: dyadic_interval_vec_triples_simps)
qed

text \<open>Popping the last node corresponds to @{term butlast} on the abstract todo (and the popped
  node is its @{term last}), threading the extra \<open>es\<close> column through the double zip.\<close>
lemma blr_alpha_todo_butlast_bl:
  assumes "newton_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs), acc)"
  shows "blr_alpha_todo (((butlast lns, butlast rns, butlast ks),
              butlast qtodo, butlast es, butlast ss, butlast cs), acc')
       = butlast (blr_alpha_todo (((lns, rns, ks), qtodo, es, ss, cs), acc))"
proof -
  from assms have inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lq: "length qtodo = length lns" and le: "length es = length lns"
    and lss: "length ss = length lns"
    by (auto simp: newton_loop_state_invar_def Let_def)
  from inv have lr: "length lns = length rns" "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  have lt: "length (dyadic_interval_vec_triples (lns, rns, ks)) = length (zip es (zip ss qtodo))"
    using lq le lr lss by (simp add: dyadic_interval_vec_triples_simps length_zip)
  have leq: "length es = length (zip ss qtodo)" using lq le lss by (simp add: length_zip)
  have lsq: "length ss = length qtodo" using lq lss by simp
  show ?thesis
    by (simp add: blr_alpha_todo_def blr_triples_butlast_bl[OF inv]
        blr_butlast_zip_bl'[OF lt, symmetric] blr_butlast_zip_bl'[OF leq, symmetric]
        blr_butlast_zip_bl'[OF lsq, symmetric])
qed

lemma blr_alpha_todo_last_bl:
  assumes "newton_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs), acc)" and "lns \<noteq> []"
  shows "last (blr_alpha_todo (((lns, rns, ks), qtodo, es, ss, cs), acc))
       = (((last lns, last rns), last ks), last es, last ss, last qtodo)"
proof -
  from assms have inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lq: "length qtodo = length lns" and le: "length es = length lns"
    and lss: "length ss = length lns"
    by (auto simp: newton_loop_state_invar_def Let_def)
  from inv have lr: "length lns = length rns" "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  have lt: "length (dyadic_interval_vec_triples (lns, rns, ks)) = length (zip es (zip ss qtodo))"
    using lq le lr lss by (simp add: dyadic_interval_vec_triples_simps length_zip)
  have leq: "length es = length (zip ss qtodo)" using lq le lss by (simp add: length_zip)
  have lsq: "length ss = length qtodo" using lq lss by simp
  have rk_ne: "rns \<noteq> []" "ks \<noteq> []" and esne: "es \<noteq> []" and ssne: "ss \<noteq> []"
    using \<open>lns \<noteq> []\<close> lr le lss by auto
  have ne: "dyadic_interval_vec_triples (lns, rns, ks) \<noteq> []"
    using \<open>lns \<noteq> []\<close> rk_ne by (simp add: dyadic_interval_vec_triples_simps)
  show ?thesis
    by (simp add: blr_alpha_todo_def blr_last_zip_bl'[OF lt ne]
        blr_last_zip_bl'[OF leq esne] blr_last_zip_bl'[OF lsq ssne]
        blr_triples_last_bl[OF inv \<open>lns \<noteq> []\<close>])
qed

subsection \<open>The refinement invariant and the two easy WHILEIT subgoals\<close>

text \<open>W1 cached-classify invariant: a cached window/split classify count \<open>c\<close> (in a \<open>cs\<close> column
  entry) aligns with the true carried Descartes count \<open>cnt\<close> of the sibling poly — trichotomy
  \<open>0/1/\<ge>2\<close> plus, when \<open>4 \<le> c\<close> (a window classify, disjoint from a truncated split count \<open>\<le> 3\<close>),
  the exact reuse \<open>c = cnt + 2\<close>. Lets @{const bail_after_pop_monadic} reuse a cached count
  instead of recomputing it.\<close>


lemma dyadic_iv_cs_invar_reuse_bl:
  assumes "dyadic_iv_cs_invar c cnt"
  shows "(if 4 \<le> c then c - 2 else cnt) = cnt"
  using assms by (auto simp: dyadic_iv_cs_invar_def)

text \<open>A truncated split classify (trichotomy \<open>0/1/\<ge>2\<close> plus \<open>c \<le> 3\<close>) satisfies @{const dyadic_iv_cs_invar}:
  the \<open>4 \<le> c\<close> reuse conjunct is vacuous below 4. Bridges \<open>blr_after_pop_refine_bl\<close>'s split_sc.\<close>
lemma dyadic_iv_cs_invar_from_classify_bl:
  assumes "(c = 0) = (cnt = 0)" "(c = 1) = (cnt = 1)" "(2 \<le> c) = (2 \<le> cnt)" "c \<le> 3"
  shows "dyadic_iv_cs_invar c cnt"
  using assms by (auto simp: dyadic_iv_cs_invar_def)

text \<open>The driver-fixpoint refinement invariant for the @{const bail_loop_monadic}
  WHILEIT (modelled on ET \<open>bilr_refine_invar\<close>, es woven in): the concrete state is data-safe, every
  abstract todo node satisfies @{const newton_gmp_node_inv} (for the \<open>\<mu>\<close>-measure and preserved by
  @{thm [source] newton_gmp_node_inv_preserved_bl}), the pure driver from the projected state agrees
  with the seed run, the snat-bound budgets stay under \<open>max_snat\<close> (worklist size + future
  appends; per-node depth \<open>k + \<mu> + 1\<close>; carried degree \<open>= degree P\<close>), and every cached classify
  in the \<open>cs\<close> column satisfies @{const dyadic_iv_cs_invar} against its sibling poly's count (W1).\<close>
definition blr_refine_invar ::
  "real \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> newton_gmp_state \<Rightarrow>
    newton_loop_state \<Rightarrow> bool" where
"blr_refine_invar \<delta> P l0 r0 k0 st0 st \<equiv>
  newton_loop_safe_invar st \<and>
  (\<forall>nd \<in> set (blr_alpha_todo st). newton_gmp_node_inv P l0 r0 k0 nd) \<and>
  newton_gmp_main_bail (blr_alpha st) = newton_gmp_main_bail st0 \<and>
  int (length (blr_alpha_todo st))
    + dyadic_iv_todo_append_budget \<delta> (map (newton_node_iv_of l0 r0 k0) (blr_alpha_todo st)) + 2
    < int (max_snat LENGTH(gmp_poly_len)) \<and>
  int (length (blr_alpha_acc st))
    + dyadic_iv_todo_acc_budget \<delta> (map (newton_node_iv_of l0 r0 k0) (blr_alpha_todo st)) + 1
    < int (max_snat LENGTH(gmp_poly_len)) \<and>
  \<comment> \<open>the popped node's dyadic exponent \<open>k\<close> stays word-bounded (carried-specific: the count-frame
     accumulates a dyadic \<open>k\<close> the endpoint-newdsc route has none of). PLAIN \<open>k+1 < max_snat\<close> is NOT
     preserved (the window jump \<open>k' = k + 2^e+2\<close> defeats it); the fix is the per-node POTENTIAL
     \<open>k + C\<cdot>(2^(\<mu>+1)-2)\<close> with \<open>C = 2^ecap+2\<close>: the window's exponential budget drop
     (\<open>\<ge> 2^\<mu> \<ge> 2\<close>) pays the gate-bounded jump (\<open>2^e+2 \<le> C\<close>), and it implies \<open>k+1 < max_snat\<close>
     since \<open>a<b \<Longrightarrow> \<mu>\<ge>1 \<Longrightarrow> budget \<ge> 2\<close>.\<close>
  (\<forall>nd \<in> set (blr_alpha_todo st).
     int (snd (fst nd))
       + int (2 ^ newton_pol_ecap + 2)
           * dyadic_iv_interval_todo_budget \<delta> (newton_node_iv_of l0 r0 k0 nd)
       < int (max_snat LENGTH(gmp_poly_len))) \<and>
  (\<forall>nd \<in> set (blr_alpha_todo st). length (snd (snd (snd nd))) = length P) \<and>
  \<comment> \<open>W1: the run-length counter \<open>s\<close> never exceeds the dyadic depth \<open>k\<close> (\<open>s' \<le> s + 1 \<le> k + 1 = k'\<close>
     on a split; \<open>s\<close> unchanged \<open>\<le> k \<le> k'\<close> on a window). With the \<open>k\<close>-potential (\<open>k + 1 < max_snat\<close>)
     this gives the \<open>s + 1 < max_snat\<close> word-bound the \<open>\<sigma>+1\<close> store needs.\<close>
  (\<forall>nd \<in> set (blr_alpha_todo st). fst (snd (snd nd)) \<le> snd (fst nd)) \<and>
  (case st of ((todo, qtodo, es, ss, cs), acc) \<Rightarrow>
     \<forall>i < length cs. dyadic_iv_cs_invar (cs ! i) (carried_descartes_count (qtodo ! i)))"

text \<open>Subgoal 3 of the WHILEIT rule: when the loop condition fails the abstract todo is empty.\<close>
lemma blr_not_cond_todo_empty_bl:
  assumes inv: "blr_refine_invar \<delta> P l0 r0 k0 st0 st"
    and not_cond: "\<not> newton_loop_cond st"
  shows "blr_alpha_todo st = []"
proof -
  from inv have "newton_loop_state_invar st"
    by (simp add: blr_refine_invar_def newton_loop_safe_invar_def)
  with not_cond blr_alpha_cond_bl show ?thesis by blast
qed

text \<open>Exit fact: once the abstract todo is empty, the projected acc is exactly the pure driver's final
  acc from the seed, which connects to the pure capstone.\<close>
lemma blr_invar_exit_bl:
  assumes inv: "blr_refine_invar \<delta> P l0 r0 k0 st0 st"
    and empty: "blr_alpha_todo st = []"
  shows "blr_alpha_acc st = snd (newton_gmp_main_bail st0)"
proof -
  from inv have main_eq: "newton_gmp_main_bail (blr_alpha st) = newton_gmp_main_bail st0"
    by (simp add: blr_refine_invar_def)
  have "blr_alpha st = ([], blr_alpha_acc st)"
    using empty by (simp add: blr_alpha_def)
  with main_eq have "newton_gmp_main_bail st0 = ([], blr_alpha_acc st)"
    by (simp add: newton_gmp_main_bail_Nil)
  thus ?thesis by simp
qed

subsection \<open>Body refinement: branch building blocks\<close>

text \<open>The count-0 branch (drop the popped node) frees the popped GMP data and returns the
  already-popped state unchanged. Clone of ET \<open>bilr_branch_zero_refine\<close> with the \<open>es\<close> column.\<close>
lemma blr_branch_zero_refine_bl:
  "newton_branch_zero_monadic todo qtodo es ss cs acc l_num r_num k Q
     \<le> RETURN ((todo, qtodo, es, ss, cs), acc)"
  unfolding newton_branch_zero_monadic_def mpzb_discard_monadic_def PR_CONST_def
  by refine_vcg simp

text \<open>The count-1 branch (accept the popped interval) pushes @{term "(l_num, r_num, k)"} onto acc
  and frees @{term Q}. Clone of ET \<open>bilr_branch_one_refine\<close> with \<open>es\<close>.\<close>
lemma blr_branch_one_refine_bl:
  assumes "dyadic_interval_vec_pushable (lns, rns, ks)"
  shows "newton_branch_one_monadic todo qtodo es ss cs (lns, rns, ks) l_num r_num k Q \<le>
    RETURN ((todo, qtodo, es, ss, cs), (lns @ [l_num], rns @ [r_num], ks @ [k]))"
  using assms
  unfolding newton_branch_one_monadic_def poly_push_coeff_monadic_def PR_CONST_def
    dyadic_interval_vec_pushable_def
  by refine_vcg auto

text \<open>Split helper: pushing the two carried children of @{term Q} appends
  @{term "carried_left Q"}/@{term "carried_right Q"}. Clone of ET \<open>bilr_carried_push_children_refine\<close>.\<close>
lemma blr_carried_push_children_refine_bl:
  assumes "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and "0 < length Q"
  shows "bisection_push_children_monadic qtodo Q \<le> RETURN (qtodo @ [carried_left Q, carried_right Q])"
  using assms
  unfolding bisection_push_children_monadic_def PR_CONST_def
  apply (refine_vcg carried_left_right_monadic_correct[THEN order_trans]
      poly_vec_push2_monadic_correct[THEN order_trans])
  apply auto
  done

text \<open>Split helper: pushing the midpoint appends @{term "((l_num+r_num,l_num+r_num),k+1)"} onto acc.
  Clone of ET \<open>bilr_push_mid_refine\<close>.\<close>
lemma blr_push_mid_refine_bl:
  assumes "dyadic_interval_vec_pushable (lns, rns, ks)"
  shows "carried_push_mid_monadic (lns, rns, ks) l_num r_num k \<le>
    RETURN (lns @ [l_num + r_num], rns @ [l_num + r_num], ks @ [k + 1])"
  using assms
  unfolding carried_push_mid_monadic_def poly_push_coeff_monadic_def PR_CONST_def
    dyadic_interval_vec_pushable_def mpz_add.amop_r1_def mpz_add.aop_r1_def COPY_def
  by refine_vcg auto

text \<open>The carried midpoint-root test refines @{const newton_mid_is_root}, as \<open>bilr_carried_mid_zero_refine\<close>
  does for bisection. \<open>bisection_mid_zero_monadic\<close> calls the specialised \<open>half_eval_zero_monadic\<close>, so this
  is a direct application of \<open>half_eval_zero_monadic_correct\<close>.\<close>
lemma blr_carried_mid_zero_refine_bl:
  assumes len0: "0 < length Q" and bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_mid_zero_monadic Q \<le> RETURN (newton_mid_is_root Q)"
  using half_eval_zero_monadic_correct[OF len0 bound]
  unfolding bisection_mid_zero_monadic_def PR_CONST_def newton_mid_is_root_def
  by (simp add: pw_le_iff refine_pw_simps)

text \<open>\<^bold>\<open>Establishing the class cache.\<close> The push-children-classify op splits @{term Q} in place, pushes
  the two carried children onto \<open>qtodo\<close>, and returns each child's truncated classification \<open>cl\<close>/\<open>cr\<close>. By
  @{thm [source] carried_descartes_count_trunc_monadic_classify_le3} each classification is in
  \<open>{0,1,2,3}\<close> and matches the exact carried count trichotomy, which is the \<open>cs\<close> invariant for the two new
  bisection entries. These \<open>cl\<close>/\<open>cr\<close> feed the decay @{const newton_split_run_len} and become the two \<open>cs\<close>
  entries.\<close>
lemma blr_push_children_classify_refine_bl:
  assumes q0: "0 < length Q" and qb: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and qtb: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "newton_push_children_classify_monadic qtodo Q \<le>
    SPEC (\<lambda>(qtodo', cl, cr).
      qtodo' = qtodo @ [carried_left Q, carried_right Q] \<and>
      cl \<le> 3
      \<and> (cl = 0) = (carried_descartes_count (carried_left Q) = 0)
      \<and> (cl = 1) = (carried_descartes_count (carried_left Q) = 1)
      \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left Q)) \<and>
      cr \<le> 3
      \<and> (cr = 0) = (carried_descartes_count (carried_right Q) = 0)
      \<and> (cr = 1) = (carried_descartes_count (carried_right Q) = 1)
      \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right Q)))"
  unfolding newton_push_children_classify_monadic_def newton_pcc_result_monadic_def PR_CONST_def
  apply (refine_vcg
      carried_left_right_monadic_correct[OF q0 qb, THEN order_trans]
      carried_descartes_count_trunc_monadic_classify_le3[THEN order_trans]
      poly_vec_push2_monadic_correct[THEN order_trans])
  using qb qtb q0 by (auto simp: length_carried_left carried_right_def)

text \<open>The split pair-state pushes the two child intervals + carried child polys + \<open>e' = max 1 (e-1)\<close>
  twice onto \<open>es\<close>, the decay \<open>s' = newton_split_run_len mid cl cr s\<close> twice onto \<open>ss\<close>, and each
  child's classify \<open>cl\<close>/\<open>cr\<close> onto \<open>cs\<close> (W1). The SPEC exposes \<open>cl\<close>/\<open>cr\<close> and their trichotomy so
  the caller can discharge the cs-invariant and the srl-bridge.\<close>
lemma blr_split_pair_state_refine_bl:
  assumes inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and p2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kb: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and qb: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and qtb: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and eb: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and ssb: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and csb: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and sb: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and q0: "0 < length Q"
  shows "newton_split_pair_state_monadic ((lns, rns, ks), qtodo, es, ss, cs) l_num r_num k e s mid Q \<le>
    SPEC (\<lambda>(todo', qtodo', es', ss', cs').
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num + l_num, l_num + r_num), k + 1),
           ((l_num + r_num, r_num + r_num), k + 1)] \<and>
      qtodo' = qtodo @ [carried_left Q, carried_right Q] \<and>
      es' = es @ [max 1 (e - 1), max 1 (e - 1)] \<and>
      (\<exists>cl cr.
         ss' = ss @ [newton_split_run_len mid cl cr s, newton_split_run_len mid cl cr s]
         \<and> cs' = cs @ [cl, cr]
         \<and> (cl = 0) = (carried_descartes_count (carried_left Q) = 0)
         \<and> (cl = 1) = (carried_descartes_count (carried_left Q) = 1)
         \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left Q))
         \<and> (cr = 0) = (carried_descartes_count (carried_right Q) = 0)
         \<and> (cr = 1) = (carried_descartes_count (carried_right Q) = 1)
         \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right Q))
         \<and> cl \<le> 3 \<and> cr \<le> 3))"
  unfolding newton_split_pair_state_monadic_def PR_CONST_def newton_child_exp_eq
  apply (simp only: Let_def prod.case)
  apply (refine_vcg
      dyadic_interval_vec_push_children_monadic_spec[OF inv p2 kb, THEN order_trans]
      blr_push_children_classify_refine_bl[OF q0 qb qtb, THEN order_trans]
      dyadic_exp_push2_monadic_spec[OF eb, THEN order_trans]
      dyadic_exp_push2_monadic_spec[OF ssb, THEN order_trans])
  apply (use assms in \<open>auto simp: dyadic_interval_vec_triples_simps\<close>)
  done

text \<open>Non-root split branch (\<open>mid = False\<close>): acc unchanged, two children pushed with ss/cs.\<close>
lemma blr_branch_split_nonroot_refine_bl:
  assumes inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and p2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kb: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and qb: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and qtb: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and eb: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and ssb: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and csb: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and sb: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and q0: "0 < length Q"
  shows "newton_branch_split_nonroot_monadic (lns, rns, ks) qtodo es ss cs acc l_num r_num k e s Q \<le>
    SPEC (\<lambda>((todo', qtodo', es', ss', cs'), acc').
      acc' = acc \<and>
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num + l_num, l_num + r_num), k + 1),
           ((l_num + r_num, r_num + r_num), k + 1)] \<and>
      qtodo' = qtodo @ [carried_left Q, carried_right Q] \<and>
      es' = es @ [max 1 (e - 1), max 1 (e - 1)] \<and>
      (\<exists>cl cr.
         ss' = ss @ [newton_split_run_len False cl cr s, newton_split_run_len False cl cr s]
         \<and> cs' = cs @ [cl, cr]
         \<and> (cl = 0) = (carried_descartes_count (carried_left Q) = 0)
         \<and> (cl = 1) = (carried_descartes_count (carried_left Q) = 1)
         \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left Q))
         \<and> (cr = 0) = (carried_descartes_count (carried_right Q) = 0)
         \<and> (cr = 1) = (carried_descartes_count (carried_right Q) = 1)
         \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right Q))
         \<and> cl \<le> 3 \<and> cr \<le> 3))"
  unfolding newton_branch_split_nonroot_monadic_def PR_CONST_def
  apply (refine_vcg
      blr_split_pair_state_refine_bl[OF inv p2 kb qb qtb eb ssb csb sb q0, THEN order_trans])
  using assms apply auto
  done

text \<open>Root split branch (\<open>mid = True\<close>): additionally pushes the midpoint onto acc.\<close>
lemma blr_branch_split_root_refine_bl:
  assumes inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and p2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kb: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and qb: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and qtb: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and eb: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and ssb: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and csb: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and sb: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and pa: "dyadic_interval_vec_pushable (alns, arns, aks)"
    and q0: "0 < length Q"
  shows "newton_branch_split_root_monadic (lns, rns, ks) qtodo es ss cs (alns, arns, aks) l_num r_num k e s Q \<le>
    SPEC (\<lambda>((todo', qtodo', es', ss', cs'), acc').
      acc' = (alns @ [l_num + r_num], arns @ [l_num + r_num], aks @ [k + 1]) \<and>
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num + l_num, l_num + r_num), k + 1),
           ((l_num + r_num, r_num + r_num), k + 1)] \<and>
      qtodo' = qtodo @ [carried_left Q, carried_right Q] \<and>
      es' = es @ [max 1 (e - 1), max 1 (e - 1)] \<and>
      (\<exists>cl cr.
         ss' = ss @ [newton_split_run_len True cl cr s, newton_split_run_len True cl cr s]
         \<and> cs' = cs @ [cl, cr]
         \<and> (cl = 0) = (carried_descartes_count (carried_left Q) = 0)
         \<and> (cl = 1) = (carried_descartes_count (carried_left Q) = 1)
         \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left Q))
         \<and> (cr = 0) = (carried_descartes_count (carried_right Q) = 0)
         \<and> (cr = 1) = (carried_descartes_count (carried_right Q) = 1)
         \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right Q))
         \<and> cl \<le> 3 \<and> cr \<le> 3))"
  unfolding newton_branch_split_root_monadic_def PR_CONST_def
  apply (refine_vcg blr_push_mid_refine_bl[OF pa, THEN order_trans]
      blr_split_pair_state_refine_bl[OF inv p2 kb qb qtb eb ssb csb sb q0, THEN order_trans])
  using assms apply auto
  done

text \<open>Full split branch: dispatch on the midpoint-root test; \<open>mid = newton_mid_is_root Q\<close>.\<close>
lemma blr_branch_split_refine_bl:
  assumes inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and p2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kb: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and q0: "0 < length Q"
    and qb: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and qtb: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and eb: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and ssb: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and csb: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and sb: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and pa: "dyadic_interval_vec_pushable (alns, arns, aks)"
  shows "newton_branch_split_monadic (lns, rns, ks) qtodo es ss cs (alns, arns, aks) l_num r_num k e s Q \<le>
    SPEC (\<lambda>((todo', qtodo', es', ss', cs'), acc').
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num + l_num, l_num + r_num), k + 1),
           ((l_num + r_num, r_num + r_num), k + 1)] \<and>
      qtodo' = qtodo @ [carried_left Q, carried_right Q] \<and>
      es' = es @ [max 1 (e - 1), max 1 (e - 1)] \<and>
      acc' = (if newton_mid_is_root Q
              then (alns @ [l_num + r_num], arns @ [l_num + r_num], aks @ [k + 1])
              else (alns, arns, aks)) \<and>
      (\<exists>cl cr.
         ss' = ss @ [newton_split_run_len (newton_mid_is_root Q) cl cr s,
                     newton_split_run_len (newton_mid_is_root Q) cl cr s]
         \<and> cs' = cs @ [cl, cr]
         \<and> (cl = 0) = (carried_descartes_count (carried_left Q) = 0)
         \<and> (cl = 1) = (carried_descartes_count (carried_left Q) = 1)
         \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left Q))
         \<and> (cr = 0) = (carried_descartes_count (carried_right Q) = 0)
         \<and> (cr = 1) = (carried_descartes_count (carried_right Q) = 1)
         \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right Q))
         \<and> cl \<le> 3 \<and> cr \<le> 3))"
  unfolding newton_branch_split_monadic_def PR_CONST_def
  apply (refine_vcg blr_carried_mid_zero_refine_bl[OF q0 qb, THEN order_trans]
      blr_branch_split_root_refine_bl[OF inv p2 kb qb qtb eb ssb csb sb pa q0]
      blr_branch_split_nonroot_refine_bl[OF inv p2 kb qb qtb eb ssb csb sb q0])
  using assms apply (auto split: if_splits)
  done

(*FASTLOOP_FREEZE_ABOVE*)
subsection \<open>Body refinement: the window dispatch\<close>

text \<open>Clean restatement of @{thm [source] carried_try_window_monadic_correct} in the
  @{const newton_wok}/@{const newton_wcand} vocabulary: the guarded try returns
  @{term "Some (newton_wcand e m Q)"} exactly when the grid cell's exact count matches @{term v}
  (@{const newton_wok}), else @{term None} — the shape @{const newton_window_pick_bail} dispatches on.\<close>
lemma blr_try_window_refine_bl:
  assumes "0 < length Q" and "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and "(2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and "0 \<le> m" and "m + 4 \<le> 2 ^ (2 ^ e + 2)"
    and "2 \<le> v" and "carried_descartes_count Q \<le> v"
  shows "newton_try_window_monadic v e m Q
       \<le> SPEC (\<lambda>res. res = (if newton_wok v e m Q then Some (m, newton_wcand e m Q) else None))"
proof -
  have "newton_try_window_monadic v e m Q \<le> SPEC (\<lambda>res.
    (case res of
       Some (m', cand) \<Rightarrow>
         m' = m
         \<and> cand = carried_init_same_den (m) (2 ^ (2 ^ e + 2)) (m + 4) Q
         \<and> carried_descartes_count cand = v
     | None \<Rightarrow>
         carried_descartes_count
           (carried_init_same_den (m) (2 ^ (2 ^ e + 2)) (m + 4) Q) \<noteq> v))"
    by (rule carried_try_window_monadic_correct[OF assms])
  thus ?thesis
    by (auto simp: pw_le_iff refine_pw_simps newton_wok_def newton_wcand_def
             split: option.splits prod.splits)
qed

text \<open>A Descartes count is bounded by the polynomial length (each fold step adds at most one
  sign change), so \<open>v \<ge> 2\<close> forces @{term "1 < length Q"} — the precondition the Newton
  probe ops (@{const newton_lambda_loc0}/\<open>_loc1\<close>) need.\<close>
lemma blr_sign_step_snd_le_bl: "snd (sign_step x (s, n)) \<le> Suc n"
  by (auto split: if_splits)

lemma blr_fold_sign_step_snd_le_bl: "snd (fold sign_step xs (s, n)) \<le> n + length xs"
proof (induction xs arbitrary: s n)
  case (Cons x xs)
  obtain s' n' where sn': "sign_step x (s, n) = (s', n')" by (cases "sign_step x (s, n)")
  have "n' \<le> Suc n" using blr_sign_step_snd_le_bl[of x s n] sn' by simp
  hence "snd (fold sign_step xs (s', n')) \<le> n' + length xs" using Cons.IH by (simp add: add.commute)
  thus ?case using \<open>n' \<le> Suc n\<close> sn' by simp
qed simp

lemma blr_carried_descartes_count_le_length_bl: "carried_descartes_count Q \<le> length Q"
  using blr_fold_sign_step_snd_le_bl[of "taylor_shift_list 1 (rev Q)" 0 0]
  by (simp add: carried_descartes_count_def sign_changes_fold_def)

text \<open>Newton probe endpoints: when the probe fires (@{term ok}), its denominator is nonzero
  (the guard @{term "xs!1 = 0"} / @{term "ds = 0"} is exactly the reject case) — the snap op's
  @{term "den \<noteq> 0"} precondition.\<close>
lemma newton_lambda_loc0_den_nz_bl:
  "fst (newton_lambda_loc0 v Q) \<Longrightarrow> snd (snd (newton_lambda_loc0 v Q)) \<noteq> 0"
  by (simp add: newton_lambda_loc0_def split: if_splits)

lemma newton_lambda_loc1_den_nz_bl:
  "fst (newton_lambda_loc1 v Q) \<Longrightarrow> snd (snd (newton_lambda_loc1 v Q)) \<noteq> 0"
  by (simp add: newton_lambda_loc1_def split: prod.splits if_splits)

text \<open>The two Newton-probe branches (location 0 at the left endpoint, location 1 at the right) each
  refine the abstract @{const newton_try_side}: probe, snap, guarded try. They are factored out so that
  @{text blr_window_choice_refine_bl}'s \<open>refine_vcg\<close> sees them atomically.

  \<^bold>\<open>Where the word bound on \<open>v\<close> comes from.\<close> Both lemmas assume \<open>int v < max_sint LENGTH(gmp_long_len)\<close>,
  and it is discharged at the single call site (@{text blr_after_pop_refine_bl}), where \<open>v\<close> is
  @{const carried_descartes_count} of the node: \<open>v = carried_descartes_count Q \<le> length Q\<close>
  (@{thm [source] blr_carried_descartes_count_le_length_bl}) and \<open>length Q + 1 < max_snat LENGTH(gmp_poly_len)\<close>,
  both widths 64. So the bound is the degree bound, and no tuned constant is involved. \<open>cQv\<close> bounds the
  count by \<open>v\<close>, the wrong direction for this, which is why the premise is passed in rather than derived
  locally.\<close>
lemma blr_loc0_branch_refine_bl:
  assumes lenQ0: "0 < length Q" and lenQ: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and lenQ1: "1 < length Q" and ecap: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and vb: "int v < max_sint LENGTH(gmp_long_len)"
    and v2: "2 \<le> v" and cQv: "carried_descartes_count Q \<le> v"
  shows "newton_window_side0_bail_monadic v e Q
       \<le> SPEC (\<lambda>(res, t). res = newton_try_side newton_lambda_loc0 v e Q
                            \<and> t = fst (newton_lambda_loc0 v Q))"
proof -
  show ?thesis
    unfolding newton_window_side0_bail_monadic_def PR_CONST_def
      mpzb_discard_monadic_def
    apply (refine_vcg newton_lambda_loc0_monadic_correct[OF lenQ1 vb, THEN order_trans]
        newton_snap_kn_monadic_correct[THEN order_trans]
        mpz_sub_ui_snat_monadic_spec[THEN order_trans]
        blr_try_window_refine_bl[OF lenQ0 lenQ gate4, THEN order_trans])
    apply (auto simp: newton_try_side_def newton_lambda_loc0_def Let_def
             newton_snap_kn_ge2_bl newton_snap_kn_le_bl slong_bounds_def max_sint_def min_sint_def max_snat_def
             split: if_splits prod.splits)
    using ecap v2 cQv by (simp_all add: max_snat_def N_of_def)
qed

lemma blr_loc1_branch_refine_bl:
  assumes lenQ0: "0 < length Q" and lenQ: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and ecap: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and lenQ2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and vb: "int v < max_sint LENGTH(gmp_long_len)"
    and v2: "2 \<le> v" and cQv: "carried_descartes_count Q \<le> v"
  shows "newton_window_side1_bail_monadic v e Q
       \<le> SPEC (\<lambda>res. res = newton_try_side newton_lambda_loc1 v e Q)"
proof -
  show ?thesis
    unfolding newton_window_side1_bail_monadic_def PR_CONST_def
      mpzb_discard_monadic_def
    apply (refine_vcg newton_lambda_loc1_monadic_correct[OF lenQ2 lenQ0 vb, THEN order_trans]
        newton_snap_kn_monadic_correct[THEN order_trans]
        mpz_sub_ui_snat_monadic_spec[THEN order_trans]
        blr_try_window_refine_bl[OF lenQ0 lenQ gate4, THEN order_trans])
    apply (auto simp: newton_try_side_def newton_lambda_loc1_def Let_def
             newton_snap_kn_ge2_bl newton_snap_kn_le_bl slong_bounds_def max_sint_def min_sint_def max_snat_def
             split: if_splits prod.splits)
    using ecap lenQ v2 cQv by (simp_all add: max_snat_def N_of_def)
qed

text \<open>The factored window-choice op refines the abstract @{const newton_window_pick_bail}. The op is
  \<open>(res0, t0) \<leftarrow> side0; if t0 then RETURN res0 else side1\<close>, so the proof is one bind and one boolean branch;
  the two window tries are inside \<open>side0\<close>/\<open>side1\<close> and discharged by the branch lemmas.\<close>
lemma blr_window_choice_refine_bl:
  assumes lenQ0: "0 < length Q" and lenQ: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and gate4: "(2 ^ e + 2) * (length Q - 1) < max_snat LENGTH(gmp_poly_len)"
    and lenQ1: "1 < length Q" and ecap: "2 ^ e + 2 < max_snat LENGTH(gmp_poly_len)"
    and lenQ2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and vb: "int v < max_sint LENGTH(gmp_long_len)"
    and v2: "2 \<le> v" and cQv: "carried_descartes_count Q \<le> v"
  shows "newton_window_choice_bail_monadic v e Q
       \<le> SPEC (\<lambda>wc. wc = newton_window_pick_bail v e Q)"
proof -
  show ?thesis
    unfolding newton_window_choice_bail_monadic_def PR_CONST_def
    apply (refine_vcg
        blr_loc0_branch_refine_bl[OF lenQ0 lenQ gate4 lenQ1 ecap vb v2 cQv, THEN order_trans]
        blr_loc1_branch_refine_bl[OF lenQ0 lenQ gate4 ecap lenQ2 vb v2 cQv, THEN order_trans])
    apply (all \<open>(auto simp: newton_window_pick_bail_def
                    split: if_splits option.splits prod.splits)?\<close>)
    done
qed

text \<open>Every window child @{const newton_window_pick_bail} returns carries @{const newton_wcand} as its
  candidate polynomial (both try branches do); the after-pop's window push needs this to identify the
  pushed polynomial with the abstract window child.\<close>
lemma newton_window_pick_bail_cand:
  "newton_window_pick_bail v e Q = Some (m, cand) \<Longrightarrow> cand = newton_wcand e m Q"
  by (auto simp: newton_window_pick_bail_def newton_try_side_def Let_def
           split: if_splits option.splits prod.splits)

text \<open>W1: an accepted window child carries exactly the popped node's count \<open>v\<close> (every \<open>Some\<close>
  branch of @{const newton_window_pick_bail} is gated by @{const newton_wok}, i.e. \<open>count = v\<close>). Lets the
  cached classify \<open>v + 2\<close> satisfy @{const dyadic_iv_cs_invar} against the child's true count.\<close>
lemma newton_window_pick_bail_count:
  "newton_window_pick_bail v e Q = Some (m, cand) \<Longrightarrow> carried_descartes_count cand = v"
  by (auto simp: newton_window_pick_bail_def newton_try_side_def newton_wok_def Let_def
           split: if_splits option.splits prod.splits)

text \<open>\<^bold>\<open>The W1 cs-invariant (obligation 2).\<close> A cached classify \<open>c\<close> and the exact carried count
  \<open>cnt\<close> agree on the 0/1/\<open>\<ge>2\<close> trichotomy the driver branches on, AND — for a WINDOW child, whose
  cache is \<open>cnt + 2 \<ge> 4\<close> (\<open>cnt \<ge> 2\<close>) — the reuse \<open>c - 2\<close> recovers \<open>cnt\<close> exactly. A
  bisection/initial classify is in \<open>{0,1,2,3}\<close> (@{thm [source]
  carried_descartes_count_trunc_monadic_classify_le3}), so its \<open>4 \<le> c\<close> conjunct is vacuous;
  a window classify is \<open>\<ge> 4\<close>, DISJOINT, so \<open>c = 0/1\<close>/\<open>2 \<le> c\<close> read the trichotomy and \<open>c - 2\<close>
  the count. (@{const dyadic_iv_cs_invar} + @{thm [source] dyadic_iv_cs_invar_reuse_bl} are defined above, next to
  @{const blr_refine_invar} which carries the cs-column invariant.)\<close>

text \<open>The after-pop dispatch refines @{const newton_gmp_step_bail}'s branch structure on the
  already-popped state: count 0/1 (read off the cached classify \<open>c\<close> via the cs-invariant), and for
  \<open>v \<ge> 2\<close> either the bisection split (gate closed / all window tries reject) or the single window
  child (some try fires), the window choice matching @{const newton_window_pick_bail} exactly. The reuse
  \<open>v = if 4 \<le> c then c - 2 else exact-count\<close> equals the true count by @{thm [source]
  dyadic_iv_cs_invar_reuse_bl} / the exact kernel. This is the ONE genuinely new refinement (no ET analog).\<close>
lemma blr_after_pop_refine_bl:
  assumes inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and p2: "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and kb: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and lenQ0: "0 < length Q"
    and lenQ: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and lenQ2: "length Q + 2 < max_snat LENGTH(gmp_poly_len)"
    and qb: "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and eb: "length es + 2 < max_snat LENGTH(gmp_poly_len)"
    and ssb: "length ss + 2 < max_snat LENGTH(gmp_poly_len)"
    and csb: "length cs + 2 < max_snat LENGTH(gmp_poly_len)"
    and sb: "s + 1 < max_snat LENGTH(gmp_poly_len)"
    and accp: "dyadic_interval_vec_pushable (alns, arns, aks)"
    and csinv: "dyadic_iv_cs_invar c (carried_descartes_count Q)"
  shows "bail_after_pop_monadic (lns, rns, ks) qtodo es ss cs (alns, arns, aks)
            l_num r_num k e s c Q
    \<le> SPEC (\<lambda>((todo', qtodo', es', ss', cs'), acc').
      dyadic_interval_vec_invar todo' \<and>
      (let v = carried_descartes_count Q;
           base_t = dyadic_interval_vec_triples (lns, rns, ks);
           split_t = base_t @ [((l_num + l_num, l_num + r_num), k + 1),
                               ((l_num + r_num, r_num + r_num), k + 1)];
           split_q = qtodo @ [carried_left Q, carried_right Q];
           split_es = es @ [max 1 (e - 1), max 1 (e - 1)];
           split_acc = (if newton_mid_is_root Q
                        then (alns @ [l_num + r_num], arns @ [l_num + r_num], aks @ [k + 1])
                        else (alns, arns, aks));
           split_sc = (\<lambda>ss' cs'. \<exists>cl cr.
                ss' = ss @ [newton_split_run_len (newton_mid_is_root Q) cl cr s,
                            newton_split_run_len (newton_mid_is_root Q) cl cr s]
              \<and> cs' = cs @ [cl, cr]
              \<and> (cl = 0) = (carried_descartes_count (carried_left Q) = 0)
              \<and> (cl = 1) = (carried_descartes_count (carried_left Q) = 1)
              \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left Q))
              \<and> (cr = 0) = (carried_descartes_count (carried_right Q) = 0)
              \<and> (cr = 1) = (carried_descartes_count (carried_right Q) = 1)
              \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right Q))
              \<and> cl \<le> 3 \<and> cr \<le> 3)
       in
       if v = 0 then dyadic_interval_vec_triples todo' = base_t \<and> qtodo' = qtodo
                     \<and> es' = es \<and> ss' = ss \<and> cs' = cs \<and> acc' = (alns, arns, aks)
       else if v = 1 then dyadic_interval_vec_triples todo' = base_t \<and> qtodo' = qtodo
                          \<and> es' = es \<and> ss' = ss \<and> cs' = cs
                          \<and> acc' = (alns @ [l_num], arns @ [r_num], aks @ [k])
       else if \<not> newton_pol_gate (length Q - 1) e k s
            then dyadic_interval_vec_triples todo' = split_t \<and> qtodo' = split_q
                 \<and> es' = split_es \<and> acc' = split_acc \<and> split_sc ss' cs'
       else (case newton_window_pick_bail v e Q of
               Some (m, cand) \<Rightarrow>
                 (let (l', r', k') = newton_window_child l_num r_num k e m in
                  dyadic_interval_vec_triples todo' = base_t @ [((l', r'), k')]
                  \<and> qtodo' = qtodo @ [cand] \<and> es' = es @ [e + 1]
                  \<and> ss' = ss @ [s] \<and> cs' = cs @ [v + 2]
                  \<and> acc' = (alns, arns, aks) \<and> cand = newton_wcand e m Q)
             | None \<Rightarrow> dyadic_interval_vec_triples todo' = split_t \<and> qtodo' = split_q
                        \<and> es' = split_es \<and> acc' = split_acc \<and> split_sc ss' cs')))"
proof -
  have lenQ1: "2 \<le> carried_descartes_count Q \<Longrightarrow> 1 < length Q"
    using blr_carried_descartes_count_le_length_bl[of Q] by linarith
  \<comment> \<open>cs-invariant: the impl branches on the cached \<open>c\<close>; align it with the exact count \<open>v\<close>.\<close>
  have c0: "(c = 0) = (carried_descartes_count Q = 0)"
    and c1: "(c = 1) = (carried_descartes_count Q = 1)"
    and c2: "(2 \<le> c) = (2 \<le> carried_descartes_count Q)"
    using csinv by (auto simp: dyadic_iv_cs_invar_def)
  have vreuse: "(if 4 \<le> c then c - 2 else carried_descartes_count Q) = carried_descartes_count Q"
    using dyadic_iv_cs_invar_reuse_bl[OF csinv] .
  have creuse: "4 \<le> c \<Longrightarrow> c - 2 = carried_descartes_count Q"
    using csinv by (auto simp: dyadic_iv_cs_invar_def)
  have creuse2: "4 \<le> c \<Longrightarrow> c = carried_descartes_count Q + 2"
    using csinv by (auto simp: dyadic_iv_cs_invar_def)
  have push: "dyadic_interval_vec_pushable (lns, rns, ks)"
    using p2 by (simp add: dyadic_interval_vec_pushable_def dyadic_interval_vec_pushable2_def)
  show ?thesis
    unfolding bail_after_pop_monadic_def PR_CONST_def
    apply (refine_vcg
        blr_branch_zero_refine_bl[THEN order_trans]
        blr_branch_one_refine_bl[OF accp, THEN order_trans]
        blr_branch_split_refine_bl[OF inv p2 kb lenQ0 lenQ qb eb ssb csb sb accp, THEN order_trans]
        newton_pol_gate_mop_correct[OF lenQ0, THEN order_trans]
        carried_descartes_count_exact_monadic_correct[OF lenQ, THEN order_trans]
        blr_window_choice_refine_bl[THEN order_trans]
        newton_window_push_monadic_correct[OF push, THEN order_trans])
    \<comment> \<open>The window try's two capped-count preconditions. At this dispatch \<open>v\<close> IS the exact
       count (\<open>vreuse\<close>), so \<open>carried_descartes_count Q \<le> v\<close> is reflexivity; the window arm
       is guarded by \<open>2 \<le> c\<close>, which \<open>c2\<close> transports to \<open>2 \<le> carried_descartes_count Q\<close>.\<close>
    apply (all \<open>(simp only: vreuse c2)?\<close>)
    \<comment> \<open>structural (invar/triples/zip/window-cand) + cs-invariant alignment (\<open>c\<close> vs count \<open>v\<close>,
       and the reuse \<open>v = c-2\<close> for \<open>4 \<le> c\<close>) — NO gate_def (avoids the double-exp arith blowup)\<close>
    apply (all \<open>(simp only: c0 c1 c2 vreuse)?\<close>)
    \<comment> \<open>\<open>int v < max_sint LENGTH(gmp_long_len)\<close> is a goal here: it is a premise of
       @{thm [source] blr_window_choice_refine_bl}, discharged by the \<open>int v < max_sint\<close> step further down
       this tactic tail, from the degree: \<open>v = carried_descartes_count Q \<le> length Q\<close> and
       \<open>length Q + 1 < max_snat LENGTH(gmp_poly_len)\<close>, both widths 64.\<close>
    apply (all \<open>(use inv in \<open>clarsimp simp: dyadic_interval_vec_triples_simps
              dyadic_interval_vec_invar_def zip_append Let_def
              dest: newton_window_pick_bail_cand[OF sym] split: option.splits\<close>)?\<close>)
    \<comment> \<open>W1 reuse: rewrite the impl-internal \<open>c - 2\<close> (the \<open>4 \<le> c\<close> cache reuse) back to the exact
       count so the existing count-based word-bound tail applies unchanged.\<close>
    apply (all \<open>(simp add: creuse)?\<close>)
    \<comment> \<open>gate-DERIVED word bounds: the caps gate implies each \<open>max_snat\<close>/shift-amount fact\<close>
    apply (all \<open>(simp add: newton_pol_gate_eL newton_pol_gate_wcap newton_pol_gate_kjump
              newton_pol_gate_mul newton_pol_gate_len1 newton_pol_gate_len2)?\<close>)
    \<comment> \<open>gate conjuncts proper (\<open>e \<le> ecap\<close> and friends): unfold once. Deliberately NOT
       \<open>max_snat_def\<close> — numeralising the goal here would strand the \<open>linarith\<close> pass below,
       whose facts (\<open>eb\<close>, \<open>qb\<close>, ...) stay in \<open>max_snat LENGTH(64)\<close> form.\<close>
    apply (all \<open>(simp add: newton_pol_gate_def newton_pol_ecap_def)?\<close>)
    \<comment> \<open>remaining machine-word arithmetic (facts reduced to the goal's \<open>max_snat 64\<close> form)\<close>
    apply (all \<open>(use qb[simplified] eb[simplified] kb[simplified] lenQ0[simplified] lenQ[simplified]
              lenQ2[simplified] blr_carried_descartes_count_le_length_bl[of Q] in linarith)?\<close>)
    \<comment> \<open>\<open>int v < max_sint\<close>: the count never exceeds the coefficient count\<close>
    apply (all \<open>(use lenQ[simplified] blr_carried_descartes_count_le_length_bl[of Q]
              in \<open>simp add: max_sint_def max_snat_def\<close>)?\<close>)
    \<comment> \<open>the folded pushable side-condition of the window push\<close>
    apply (all \<open>(rule push)?\<close>)
    \<comment> \<open>gate-derived word bounds in NUMERAL form: \<open>clarsimp\<close> has already evaluated \<open>max_snat\<close> and
       distributed \<open>(2\<^sup>e + 2) \<cdot> deg\<close>, so feed \<open>linarith\<close> the two non-linear facts explicitly\<close>
    apply (all \<open>(insert newton_pol_ecap_pow[of e]
              newton_pol_dcap_mul[of e "length Q - Suc 0"])?\<close>)
    apply (all \<open>(simp only: newton_pol_ecap_def newton_pol_kcap_def newton_pol_dcap_def)?\<close>)
    apply (all \<open>linarith?\<close>)
    \<comment> \<open>window-Some matching: Some-injectivity + @{const newton_window_child} determinism + cand\<close>
    apply (all \<open>(auto dest: newton_window_pick_bail_cand newton_window_pick_bail_cand[OF sym])?\<close>)
    apply (all \<open>(metis (full_types))?\<close>)
    \<comment> \<open>residual W1 cache bounds: \<open>ss\<close>/\<open>cs\<close> lengths and the window's \<open>c = v + 2\<close> (\<open>4 \<le> c\<close>).\<close>
    apply (all \<open>(use creuse2 ssb[simplified] csb[simplified] sb[simplified] lenQ2[simplified]
              lenQ[simplified] blr_carried_descartes_count_le_length_bl[of Q]
              in \<open>auto simp: max_snat_def max_sint_def\<close>)?\<close>)
    done
qed


subsection \<open>Body: the \<open>\<alpha>\<close>-bridge \<open>blr_alpha (step result) = newton_gmp_step_bail (blr_alpha st)\<close>\<close>

text \<open>The data-refinement crux: a concrete result satisfying the @{thm [source] blr_after_pop_refine_bl}
  characterisation (at the popped components) projects via @{const blr_alpha} to exactly
  @{const newton_gmp_step_bail} of the projected input. Case split on popped count / gate /
  @{const newton_window_pick_bail}, matching via the \<open>\<alpha>\<close>-pop connectors, @{thm [source] blr_triples_append_bl}
  (acc side), and @{const newton_split}. Mirrors ET \<open>bilr_step_alpha_eq\<close> with the window branch.\<close>
text \<open>Split the 3-level \<open>\<alpha>\<close>-projection zip over a two-element append, as a CONTROLLED rewrite
  (the general \<open>zip_append\<close> loops on the nested \<open>zip es (zip ss qtodo)\<close> shape).\<close>
lemma blr_zip4_append2_bl:
  assumes "length A = length B" "length A = length C" "length A = length D"
  shows "zip (A @ [a1, a2]) (zip (B @ [b1, b2]) (zip (C @ [c1, c2]) (D @ [d1, d2])))
       = zip A (zip B (zip C D)) @ [(a1, b1, c1, d1), (a2, b2, c2, d2)]"
  using assms by (simp add: zip_append)

lemma blr_zip4_append1_bl:
  assumes "length A = length B" "length A = length C" "length A = length D"
  shows "zip (A @ [a1]) (zip (B @ [b1]) (zip (C @ [c1]) (D @ [d1])))
       = zip A (zip B (zip C D)) @ [(a1, b1, c1, d1)]"
  using assms by (simp add: zip_append)

text \<open>@{const newton_split_run_len} tests only whether each child count is zero, so a classify
  agreeing with the exact count on the \<open>= 0\<close> predicate yields the same decay — the last piece of
  the srl-bridge (obligation 3) at the \<open>\<alpha>\<close> level.\<close>
lemma newton_split_run_len_cong_bl:
  assumes "(cl = 0) = (cl' = 0)" and "(cr = 0) = (cr' = 0)"
  shows "newton_split_run_len mid cl cr s = newton_split_run_len mid cl' cr' s"
  using assms by (auto simp: newton_split_run_len_def)

lemma blr_step_alpha_eq_bl:
  assumes si: "newton_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs), (alns, arns, aks))"
    and ne: "lns \<noteq> []"
    and char: "let v = carried_descartes_count (last qtodo);
                   base_t = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks);
                   split_t = base_t @ [((last lns + last lns, last lns + last rns), last ks + 1),
                                       ((last lns + last rns, last rns + last rns), last ks + 1)];
                   split_q = butlast qtodo @ [carried_left (last qtodo), carried_right (last qtodo)];
                   split_es = butlast es @ [max 1 (last es - 1), max 1 (last es - 1)];
                   split_acc = (if newton_mid_is_root (last qtodo)
                                then (alns @ [last lns + last rns], arns @ [last lns + last rns],
                                      aks @ [last ks + 1])
                                else (alns, arns, aks));
                   split_sc = (\<lambda>ss'' cs''. \<exists>cl cr.
                        ss'' = butlast ss
                          @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                             newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]
                        \<and> cs'' = butlast cs @ [cl, cr]
                        \<and> (cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)
                        \<and> (cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)
                        \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))
                        \<and> (cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)
                        \<and> (cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)
                        \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))
                        \<and> cl \<le> 3 \<and> cr \<le> 3)
               in
               if v = 0 then dyadic_interval_vec_triples todo' = base_t \<and> qtodo' = butlast qtodo
                             \<and> es' = butlast es \<and> ss' = butlast ss \<and> cs' = butlast cs
                             \<and> acc' = (alns, arns, aks)
               else if v = 1 then dyadic_interval_vec_triples todo' = base_t \<and> qtodo' = butlast qtodo
                                  \<and> es' = butlast es \<and> ss' = butlast ss \<and> cs' = butlast cs
                                  \<and> acc' = (alns @ [last lns], arns @ [last rns], aks @ [last ks])
               else if \<not> newton_pol_gate (length (last qtodo) - 1) (last es) (last ks) (last ss)
                    then dyadic_interval_vec_triples todo' = split_t \<and> qtodo' = split_q
                         \<and> es' = split_es \<and> acc' = split_acc \<and> split_sc ss' cs'
               else (case newton_window_pick_bail v (last es) (last qtodo) of
                       Some (m, cand) \<Rightarrow>
                         (let (l', r', k') = newton_window_child (last lns) (last rns) (last ks) (last es) m in
                          dyadic_interval_vec_triples todo' = base_t @ [((l', r'), k')]
                          \<and> qtodo' = butlast qtodo @ [cand] \<and> es' = butlast es @ [last es + 1]
                          \<and> ss' = butlast ss @ [last ss] \<and> cs' = butlast cs @ [v + 2]
                          \<and> acc' = (alns, arns, aks) \<and> cand = newton_wcand (last es) m (last qtodo))
                     | None \<Rightarrow> dyadic_interval_vec_triples todo' = split_t \<and> qtodo' = split_q
                                \<and> es' = split_es \<and> acc' = split_acc \<and> split_sc ss' cs')"
  shows "blr_alpha ((todo', qtodo', es', ss', cs'), acc')
       = newton_gmp_step_bail (blr_alpha (((lns, rns, ks), qtodo, es, ss, cs), (alns, arns, aks)))"
proof -
  let ?st = "(((lns, rns, ks), qtodo, es, ss, cs), (alns, arns, aks))"
  from si have inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and ia: "dyadic_interval_vec_invar (alns, arns, aks)"
    and lq: "length qtodo = length lns" and le: "length es = length lns"
    and lss: "length ss = length lns"
    by (auto simp: newton_loop_state_invar_def Let_def)
  from inv have ll: "length lns = length rns" "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  have A_ne: "blr_alpha_todo ?st \<noteq> []"
    using ne lq le ll lss unfolding blr_alpha_todo_def
    by (cases lns; cases qtodo; cases es; cases ss) (auto simp: dyadic_interval_vec_triples_simps)
  have lastA: "last (blr_alpha_todo ?st)
             = (((last lns, last rns), last ks), last es, last ss, last qtodo)"
    by (rule blr_alpha_todo_last_bl[OF si ne])
  have BL: "butlast (zip (dyadic_interval_vec_triples (lns, rns, ks)) (zip es (zip ss qtodo)))
          = zip (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
                (zip (butlast es) (zip (butlast ss) (butlast qtodo)))"
    using blr_alpha_todo_butlast_bl[OF si, of "(alns, arns, aks)"]
    by (simp add: blr_alpha_todo_def)
  have lenbl: "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
             = length (zip (butlast es) (zip (butlast ss) (butlast qtodo)))"
    using ll lq le lss by (simp add: dyadic_interval_vec_triples_simps length_zip)
  have lebq: "length (butlast es) = length (zip (butlast ss) (butlast qtodo))"
    using le lq lss by (simp add: length_zip)
  have lebss: "length (butlast es) = length (butlast ss)" using le lss by simp
  have lssq: "length (butlast ss) = length (butlast qtodo)" using lss lq by simp
  have lA: "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)) = length (butlast es)"
     "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)) = length (butlast ss)"
     "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)) = length (butlast qtodo)"
    using ll le lq lss by (simp_all add: dyadic_interval_vec_triples_simps length_zip)
  have accst: "blr_alpha_acc ?st = dyadic_interval_vec_triples (alns, arns, aks)"
    unfolding blr_alpha_acc_def by simp
  have lhs_t: "blr_alpha_todo ((todo', qtodo', es', ss', cs'), acc')
             = zip (dyadic_interval_vec_triples todo') (zip es' (zip ss' qtodo'))"
    by (simp add: blr_alpha_todo_def)
  have lhs_a: "blr_alpha_acc ((todo', qtodo', es', ss', cs'), acc') = dyadic_interval_vec_triples acc'"
    by (simp add: blr_alpha_acc_def)
  have step_red: "newton_gmp_step_bail (blr_alpha ?st)
    = (let v = carried_descartes_count (last qtodo)
       in if v = 0 then (butlast (blr_alpha_todo ?st), blr_alpha_acc ?st)
          else if v = 1 then (butlast (blr_alpha_todo ?st),
                              blr_alpha_acc ?st @ [((last lns, last rns), last ks)])
          else if \<not> newton_pol_gate (length (last qtodo) - 1) (last es) (last ks) (last ss)
               then newton_split (last lns) (last rns) (last ks) (last es) (last ss) (last qtodo)
                      (butlast (blr_alpha_todo ?st), blr_alpha_acc ?st)
               else (case newton_window_pick_bail v (last es) (last qtodo) of
                       Some (m, cand) \<Rightarrow>
                         (let (l', r', k') = newton_window_child (last lns) (last rns) (last ks) (last es) m
                          in (butlast (blr_alpha_todo ?st) @ [(((l', r'), k'), last es + 1, last ss, cand)],
                              blr_alpha_acc ?st))
                     | None \<Rightarrow> newton_split (last lns) (last rns) (last ks) (last es) (last ss) (last qtodo)
                                 (butlast (blr_alpha_todo ?st), blr_alpha_acc ?st)))"
    unfolding newton_gmp_step_bail_def blr_alpha_def
    using A_ne by (simp add: lastA Let_def)
  let ?srl = "newton_split_run_len (newton_mid_is_root (last qtodo))
                (carried_descartes_count (carried_left (last qtodo)))
                (carried_descartes_count (carried_right (last qtodo))) (last ss)"
  have split_red: "newton_split (last lns) (last rns) (last ks) (last es) (last ss) (last qtodo)
        (zip (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
             (zip (butlast es) (zip (butlast ss) (butlast qtodo))),
         dyadic_interval_vec_triples (alns, arns, aks))
      = (zip (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
             (zip (butlast es) (zip (butlast ss) (butlast qtodo)))
           @ [(((last lns + last lns, last lns + last rns), last ks + 1),
               max 1 (last es - 1), ?srl, carried_left (last qtodo)),
              (((last lns + last rns, last rns + last rns), last ks + 1),
               max 1 (last es - 1), ?srl, carried_right (last qtodo))],
         if newton_mid_is_root (last qtodo)
         then dyadic_interval_vec_triples (alns, arns, aks)
                @ [((last lns + last rns, last lns + last rns), last ks + 1)]
         else dyadic_interval_vec_triples (alns, arns, aks))"
    by (simp add: newton_split_def Let_def)
  note base = blr_alpha_def blr_alpha_todo_def blr_alpha_acc_def BL accst Let_def
  show ?thesis
  proof (cases "carried_descartes_count (last qtodo) = 0")
    case v0: True
    hence e: "dyadic_interval_vec_triples todo' = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)"
      "qtodo' = butlast qtodo" "es' = butlast es" "ss' = butlast ss" "acc' = (alns, arns, aks)"
      using char by (simp_all add: Let_def)
    show ?thesis using v0 e by (subst step_red) (simp add: base)
  next
    case v0: False
    show ?thesis
    proof (cases "carried_descartes_count (last qtodo) = 1")
      case v1: True
      hence e: "dyadic_interval_vec_triples todo' = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)"
        "qtodo' = butlast qtodo" "es' = butlast es" "ss' = butlast ss"
        "acc' = (alns @ [last lns], arns @ [last rns], aks @ [last ks])"
        using char v0 by (simp_all add: Let_def)
      show ?thesis using v0 v1 e
        by (subst step_red) (simp add: base blr_triples_append_bl[OF ia])
    next
      case v1: False
      \<comment> \<open>the split branches' \<open>ss'\<close>: from \<open>char\<close>'s \<open>\<exists>cl cr\<close> (classify trichotomy) the decay equals the
         exact-count decay \<open>?srl\<close> (@{thm [source] newton_split_run_len_cong_bl}).\<close>
      have srl_match: "newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss) = ?srl"
        if "(cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)"
           "(cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)" for cl cr
        by (rule newton_split_run_len_cong_bl[OF that])
      show ?thesis
      proof (cases "newton_pol_gate (length (last qtodo) - 1) (last es) (last ks) (last ss)")
        case gate: False
        hence e: "dyadic_interval_vec_triples todo'
                  = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)
                    @ [((last lns + last lns, last lns + last rns), last ks + 1),
                       ((last lns + last rns, last rns + last rns), last ks + 1)]"
          "qtodo' = butlast qtodo @ [carried_left (last qtodo), carried_right (last qtodo)]"
          "es' = butlast es @ [max 1 (last es - 1), max 1 (last es - 1)]"
          "acc' = (if newton_mid_is_root (last qtodo)
                   then (alns @ [last lns + last rns], arns @ [last lns + last rns], aks @ [last ks + 1])
                   else (alns, arns, aks))"
          using char v0 v1 by (simp_all add: Let_def)
        from char v0 v1 gate have exfull:
          "\<exists>cl cr. ss' = butlast ss @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                                       newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]
                \<and> cs' = butlast cs @ [cl, cr]
                \<and> (cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)
                \<and> (cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)
                \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))
                \<and> (cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)
                \<and> (cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)
                \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))
                \<and> cl \<le> 3 \<and> cr \<le> 3"
          by (simp add: Let_def)
        from exfull obtain cl cr where
            ss'raw: "ss' = butlast ss @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                                         newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]"
          and "cs' = butlast cs @ [cl, cr]"
          and cl0: "(cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)"
          and "(cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)"
          and "(2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))"
          and cr0: "(cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)"
          and "(cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)"
          and "(2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))"
          and "cl \<le> 3" and "cr \<le> 3" by (elim exE conjE)
        have ss'e: "ss' = butlast ss @ [?srl, ?srl]"
          using ss'raw srl_match[OF cl0 cr0] by simp
        show ?thesis using v0 v1 gate
          by (subst step_red)
             (simp add: base split_red ss'e e(1) e(2) e(3) e(4)
                blr_zip4_append2_bl[OF lA(1) lA(2) lA(3)] blr_triples_append_bl[OF ia])
      next
        case gate: True
        show ?thesis
        proof (cases "newton_window_pick_bail (carried_descartes_count (last qtodo)) (last es) (last qtodo)")
          case None
          hence e: "dyadic_interval_vec_triples todo'
                    = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)
                      @ [((last lns + last lns, last lns + last rns), last ks + 1),
                         ((last lns + last rns, last rns + last rns), last ks + 1)]"
            "qtodo' = butlast qtodo @ [carried_left (last qtodo), carried_right (last qtodo)]"
            "es' = butlast es @ [max 1 (last es - 1), max 1 (last es - 1)]"
            "acc' = (if newton_mid_is_root (last qtodo)
                     then (alns @ [last lns + last rns], arns @ [last lns + last rns], aks @ [last ks + 1])
                     else (alns, arns, aks))"
            using char v0 v1 gate by (simp_all add: Let_def)
          from char v0 v1 gate None have exfull:
            "\<exists>cl cr. ss' = butlast ss @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                                         newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]
                  \<and> cs' = butlast cs @ [cl, cr]
                  \<and> (cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)
                  \<and> (cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)
                  \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))
                  \<and> (cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)
                  \<and> (cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)
                  \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))
                  \<and> cl \<le> 3 \<and> cr \<le> 3"
            by (simp add: Let_def)
          from exfull obtain cl cr where
              ss'raw: "ss' = butlast ss @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                                           newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]"
            and "cs' = butlast cs @ [cl, cr]"
            and cl0: "(cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)"
            and "(cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)"
            and "(2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))"
            and cr0: "(cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)"
            and "(cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)"
            and "(2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))"
            and "cl \<le> 3" and "cr \<le> 3" by (elim exE conjE)
          have ss'e: "ss' = butlast ss @ [?srl, ?srl]"
            using ss'raw srl_match[OF cl0 cr0] by simp
          show ?thesis using v0 v1 gate None
            by (subst step_red)
               (simp add: base split_red ss'e e(1) e(2) e(3) e(4)
                  blr_zip4_append2_bl[OF lA(1) lA(2) lA(3)] blr_triples_append_bl[OF ia])
        next
          case (Some mc)
          obtain m cand where mc: "mc = (m, cand)" by (cases mc)
          obtain l' r' k' where dwc: "newton_window_child (last lns) (last rns) (last ks) (last es) m
                                    = (l', r', k')"
            by (cases "newton_window_child (last lns) (last rns) (last ks) (last es) m") auto
          from char v0 v1 gate Some mc dwc
          have e: "dyadic_interval_vec_triples todo'
                   = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) @ [((l', r'), k')]"
            "qtodo' = butlast qtodo @ [cand]" "es' = butlast es @ [last es + 1]"
            "ss' = butlast ss @ [last ss]" "acc' = (alns, arns, aks)"
            by (simp_all add: Let_def)
          show ?thesis using v0 v1 gate Some mc dwc
            apply (subst step_red)
            apply (simp only: blr_alpha_def blr_alpha_todo_def blr_alpha_acc_def prod.case
                      e(1) e(2) e(3) e(4) e(5) BL accst)
            apply (subst blr_zip4_append1_bl[OF lA(1) lA(2) lA(3)])
            apply simp
            done
        qed
      qed
    qed
  qed
qed

subsection \<open>Step preservation: each @{const blr_refine_invar} conjunct survives one pure step\<close>

lemma blr_length_carried_right_bl[simp]: "length (carried_right xs) = length xs"
  by (simp add: carried_right_def)

text \<open>Poly-length is preserved: split children carry @{const carried_left}/@{const carried_right}
  of the popped poly, the window child @{const newton_wcand}; all three preserve length.\<close>
lemma newton_gmp_step_bail_preserves_polylen:
  assumes "\<forall>nd \<in> set (fst st). length (snd (snd (snd nd))) = n"
  shows "\<forall>nd \<in> set (fst (newton_gmp_step_bail st)). length (snd (snd (snd nd))) = n"
proof (cases "fst st = []")
  case True thus ?thesis by (cases st) (simp add: newton_gmp_step_bail_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain lr k e s Q where last_eq0: "last todo = ((lr, k), e, s, Q)" by (cases "last todo") auto
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), e, s, Q)" using last_eq0 lr_eq by simp
  have alln: "\<forall>nd \<in> set todo. length (snd (snd (snd nd))) = n" using assms by (simp add: st)
  have lenQ: "length Q = n" using alln[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  have rest: "\<forall>nd \<in> set (butlast todo). length (snd (snd (snd nd))) = n"
    using alln by (auto dest: in_set_butlastD)
  show ?thesis
  proof (cases "carried_descartes_count Q = 0 \<or> carried_descartes_count Q = 1")
    case True
    thus ?thesis using rest last_eq todo_ne by (auto simp: st newton_gmp_step_bail_def Let_def)
  next
    case False
    hence v: "carried_descartes_count Q \<noteq> 0" "carried_descartes_count Q \<noteq> 1" by auto
    show ?thesis
    proof (cases "newton_pol_gate (length Q - 1) e k s")
      case gF: False
      hence "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
        using todo_ne last_eq v by (simp add: st newton_gmp_step_bail_def Let_def)
      thus ?thesis using rest lenQ by (auto simp: newton_split_def Let_def)
    next
      case gT: True
      show ?thesis
      proof (cases "newton_window_pick_bail (carried_descartes_count Q) e Q")
        case None
        hence "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
          using todo_ne last_eq v gT by (simp add: st newton_gmp_step_bail_def Let_def)
        thus ?thesis using rest lenQ by (auto simp: newton_split_def Let_def)
      next
        case (Some mc)
        obtain m cand where mc: "mc = (m, cand)" by (cases mc)
        obtain l' r' k' where dwc: "newton_window_child l r k e m = (l', r', k')"
          by (cases "newton_window_child l r k e m") auto
        have cc: "cand = newton_wcand e m Q"
          using newton_window_pick_bail_cand[OF Some[unfolded mc]] .
        have "fst (newton_gmp_step_bail st) = butlast todo @ [(((l', r'), k'), e+1, s, cand)]"
          using todo_ne last_eq v gT Some mc dwc by (simp add: st newton_gmp_step_bail_def Let_def)
        thus ?thesis using rest lenQ cc by (auto simp: newton_wcand_def)
      qed
    qed
  qed
qed

text \<open>W1: the run-length bound \<open>s \<le> k\<close> is preserved. A split child carries \<open>k + 1\<close> and
  \<open>s' = newton_split_run_len \<dots> s \<le> s + 1 \<le> k + 1\<close>; the window child keeps \<open>s\<close> and jumps to
  \<open>k' = k + 2^e + 2 \<ge> k \<ge> s\<close>. (\<open>s\<close>-accessor \<open>fst (snd (snd nd))\<close>, \<open>k\<close>-accessor \<open>snd (fst nd)\<close>.)\<close>
lemma newton_gmp_step_bail_preserves_sbound:
  assumes "\<forall>nd \<in> set (fst st). fst (snd (snd nd)) \<le> snd (fst nd)"
  shows "\<forall>nd \<in> set (fst (newton_gmp_step_bail st)). fst (snd (snd nd)) \<le> snd (fst nd)"
proof (cases "fst st = []")
  case True thus ?thesis by (cases st) (simp add: newton_gmp_step_bail_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain l r k e s Q where last_eq: "last todo = (((l, r), k), e, s, Q)"
    by (cases "last todo") auto
  have alls: "\<forall>nd \<in> set todo. fst (snd (snd nd)) \<le> snd (fst nd)" using assms by (simp add: st)
  have sk: "s \<le> k" using alls[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  have rest: "\<forall>nd \<in> set (butlast todo). fst (snd (snd nd)) \<le> snd (fst nd)"
    using alls by (auto dest: in_set_butlastD)
  show ?thesis
  proof (cases "carried_descartes_count Q = 0 \<or> carried_descartes_count Q = 1")
    case True
    thus ?thesis using rest last_eq todo_ne by (auto simp: st newton_gmp_step_bail_def Let_def)
  next
    case False
    hence v: "carried_descartes_count Q \<noteq> 0" "carried_descartes_count Q \<noteq> 1" by auto
    show ?thesis
    proof (cases "newton_pol_gate (length Q - 1) e k s")
      case gF: False
      hence "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
        using todo_ne last_eq v by (simp add: st newton_gmp_step_bail_def Let_def)
      thus ?thesis using rest sk
        by (auto simp: newton_split_def Let_def newton_split_run_len_def)
    next
      case gT: True
      show ?thesis
      proof (cases "newton_window_pick_bail (carried_descartes_count Q) e Q")
        case None
        hence "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
          using todo_ne last_eq v gT by (simp add: st newton_gmp_step_bail_def Let_def)
        thus ?thesis using rest sk
          by (auto simp: newton_split_def Let_def newton_split_run_len_def)
      next
        case (Some mc)
        obtain m cand where mc: "mc = (m, cand)" by (cases mc)
        obtain l' r' k' where dwc: "newton_window_child l r k e m = (l', r', k')"
          by (cases "newton_window_child l r k e m") auto
        have kk: "k' = k + (2 ^ e + 2)" using dwc by (simp add: newton_window_child_def)
        have "fst (newton_gmp_step_bail st) = butlast todo @ [(((l', r'), k'), e+1, s, cand)]"
          using todo_ne last_eq v gT Some mc dwc by (simp add: st newton_gmp_step_bail_def Let_def)
        thus ?thesis using rest sk kk by auto
      qed
    qed
  qed
qed

text \<open>The append-budget is strictly monotone in \<open>\<mu>\<close> (both children of every branch have strictly
  smaller \<open>\<mu>\<close>, hence a strictly smaller budget — the headroom that pays for the \<open>k\<close>-jump).\<close>
lemma dyadic_iv_interval_todo_budget_strict_mono_bl:
  "dyadic_iv_interval_mu \<delta> I' < dyadic_iv_interval_mu \<delta> I
     \<Longrightarrow> dyadic_iv_interval_todo_budget \<delta> I' < dyadic_iv_interval_todo_budget \<delta> I"
  unfolding dyadic_iv_interval_todo_budget_def by simp

lemma dyadic_iv_interval_acc_budget_strict_mono_bl:
  "dyadic_iv_interval_mu \<delta> I' < dyadic_iv_interval_mu \<delta> I
     \<Longrightarrow> dyadic_iv_interval_acc_budget \<delta> I' < dyadic_iv_interval_acc_budget \<delta> I"
  unfolding dyadic_iv_interval_acc_budget_def by simp

text \<open>The dyadic-\<open>k\<close> word-bound potential \<open>k + C\<cdot>budget\<close> (\<open>C = 2^ecap+2\<close>) is preserved. Split children
  carry \<open>k+1\<close> paid by any budget drop (\<open>\<ge> 1\<close>); the window child carries \<open>k + 2^e+2\<close> paid by the drop
  times \<open>C\<close> (\<open>2^e+2 \<le> C\<close> since the gate forces \<open>e \<le> ecap\<close>). Uses only the qualitative \<open>\<mu>\<close>-drops
  (@{thm mu_halve_strict}, the window \<open>cellw\<close>), re-derived exactly as in @{thm newton_gmp_step_bail_mu_decreases}.\<close>
lemma newton_gmp_step_bail_preserves_kbud:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and l0r0: "l0 < r0"
    and inv: "\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd"
    and kbud: "\<forall>nd \<in> set (fst st).
        int (snd (fst nd)) + int (2 ^ newton_pol_ecap + 2)
          * dyadic_iv_interval_todo_budget \<delta> (newton_node_iv_of l0 r0 k0 nd)
        < int (max_snat LENGTH(gmp_poly_len))"
  shows "\<forall>nd \<in> set (fst (newton_gmp_step_bail st)).
        int (snd (fst nd)) + int (2 ^ newton_pol_ecap + 2)
          * dyadic_iv_interval_todo_budget \<delta> (newton_node_iv_of l0 r0 k0 nd)
        < int (max_snat LENGTH(gmp_poly_len))"
proof (cases "fst st = []")
  case True thus ?thesis by (cases st) (simp add: newton_gmp_step_bail_def)
next
  case False
  define C where "C = int (2 ^ newton_pol_ecap + 2)"
  define \<Phi> where "\<Phi> = (\<lambda>nd. int (snd (fst nd))
      + C * dyadic_iv_interval_todo_budget \<delta> (newton_node_iv_of l0 r0 k0 nd))"
  have Cpos: "0 < C"
  proof -
    have "(0::int) \<le> 2 ^ newton_pol_ecap" by simp
    moreover have "C = 2 + 2 ^ newton_pol_ecap" by (simp add: C_def)
    ultimately show ?thesis by linarith
  qed
  have C1: "int 1 \<le> C" using Cpos by simp
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain lr k e s Q where last_eq0: "last todo = ((lr, k), e, s, Q)" by (cases "last todo") auto
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), e, s, Q)" using last_eq0 lr_eq by simp
  have inv': "\<forall>nd \<in> set todo. newton_gmp_node_inv P l0 r0 k0 nd" using inv by (simp add: st)
  have ninv: "newton_gmp_node_inv P l0 r0 k0 (((l, r), k), e, s, Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)"
  define b where "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  have headrepr: "carried_repr_scalar P a b Q"
    using ninv by (simp add: newton_gmp_node_inv_def newton_node_iv_of_def
                              dyadic_iv_node_iv_of_def Let_def a_def b_def)
  have ab: "a < b"
    using newton_gmp_node_inv_ordered_bl[OF ninv]
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using carried_descartes_count_scalar_bl[OF headrepr len] ab by simp
  have niv: "newton_node_iv_of l0 r0 k0 (((l, r), k), e, s, Q) = (a, b)"
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  let ?m = "(a + b) / 2"
  have kbud': "\<forall>nd \<in> set todo. \<Phi> nd < int (max_snat LENGTH(gmp_poly_len))"
    using kbud by (simp add: st \<Phi>_def C_def)
  have Phi_par: "int k + C * dyadic_iv_interval_todo_budget \<delta> (a, b) < int (max_snat LENGTH(gmp_poly_len))"
    using kbud'[rule_format, OF last_in_set[OF todo_ne]] last_eq niv by (simp add: \<Phi>_def)
  have rest: "\<forall>nd \<in> set (butlast todo). \<Phi> nd < int (max_snat LENGTH(gmp_poly_len))"
    using kbud' by (auto dest: in_set_butlastD)
  have tl: "dyadic_iv_node_iv l0 r0 k0 (2 * l) (l + r) (Suc k) = (a, ?m)"
    using dyadic_iv_node_iv_bisect_left_bl[of l0 r0 k0 l r k] by (simp add: a_def b_def)
  have tr: "dyadic_iv_node_iv l0 r0 k0 (l + r) (2 * r) (Suc k) = (?m, b)"
    using dyadic_iv_node_iv_bisect_right_bl[of l0 r0 k0 l r k] by (simp add: a_def b_def)
  \<comment> \<open>the unified child bound: a strictly-smaller budget plus a \<open>k\<close>-jump \<open>\<le> C\<close> stays under the parent's Φ\<close>
  have keyle: "\<And>Ic Ip dk. dyadic_iv_interval_todo_budget \<delta> Ic < dyadic_iv_interval_todo_budget \<delta> Ip
      \<Longrightarrow> int dk \<le> C
      \<Longrightarrow> int k + int dk + C * dyadic_iv_interval_todo_budget \<delta> Ic
          \<le> int k + C * dyadic_iv_interval_todo_budget \<delta> Ip"
  proof -
    fix Ic Ip dk
    assume h1: "dyadic_iv_interval_todo_budget \<delta> Ic < dyadic_iv_interval_todo_budget \<delta> Ip"
       and h2: "int dk \<le> C"
    have "dyadic_iv_interval_todo_budget \<delta> Ic + 1 \<le> dyadic_iv_interval_todo_budget \<delta> Ip" using h1 by simp
    hence "C * (dyadic_iv_interval_todo_budget \<delta> Ic + 1) \<le> C * dyadic_iv_interval_todo_budget \<delta> Ip"
      using Cpos by (simp add: mult_left_mono)
    hence "C * dyadic_iv_interval_todo_budget \<delta> Ic + C \<le> C * dyadic_iv_interval_todo_budget \<delta> Ip"
      by (simp add: algebra_simps)
    thus "int k + int dk + C * dyadic_iv_interval_todo_budget \<delta> Ic
          \<le> int k + C * dyadic_iv_interval_todo_budget \<delta> Ip"
      using h2 by linarith
  qed
  show ?thesis
  proof (cases "descartes_list_int a b P = 0 \<or> descartes_list_int a b P = 1")
    case True
    have stf: "fst (newton_gmp_step_bail st) = butlast todo"
      using todo_ne last_eq True count by (auto simp: st newton_gmp_step_bail_def Let_def)
    show ?thesis unfolding stf using rest by (simp add: \<Phi>_def C_def)
  next
    case False
    have v0: "descartes_list_int a b P \<noteq> 0" and v1: "descartes_list_int a b P \<noteq> 1"
      using False by auto
    have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
    proof (rule ccontr)
      assume "\<not> \<delta> < of_rat b - of_rat a"
      then have "of_rat b - of_rat a \<le> \<delta>" by linarith
      then have "descartes_list_int a b P \<le> 1" using small_fast[OF ab] by simp
      with v0 v1 show False by simp
    qed
    have half_lt1: "dyadic_iv_interval_mu \<delta> (a, ?m) < dyadic_iv_interval_mu \<delta> (a, b)"
      using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      by (simp add: dyadic_iv_interval_mu_def of_rat_add of_rat_divide)
    have half_lt2: "dyadic_iv_interval_mu \<delta> (?m, b) < dyadic_iv_interval_mu \<delta> (a, b)"
      using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      by (simp add: dyadic_iv_interval_mu_def of_rat_add of_rat_divide)
    \<comment> \<open>the two split children satisfy the potential (\<open>k+1\<close> paid by any budget drop)\<close>
    have bl: "dyadic_iv_interval_todo_budget \<delta> (a, ?m) < dyadic_iv_interval_todo_budget \<delta> (a, b)"
      by (rule dyadic_iv_interval_todo_budget_strict_mono_bl[OF half_lt1])
    have br: "dyadic_iv_interval_todo_budget \<delta> (?m, b) < dyadic_iv_interval_todo_budget \<delta> (a, b)"
      by (rule dyadic_iv_interval_todo_budget_strict_mono_bl[OF half_lt2])
    have splitok: "\<forall>nd \<in> set (fst (newton_split l r k e s Q (butlast todo, acc))).
          \<Phi> nd < int (max_snat LENGTH(gmp_poly_len))"
    proof
      fix nd assume "nd \<in> set (fst (newton_split l r k e s Q (butlast todo, acc)))"
      then consider "nd \<in> set (butlast todo)"
        | "nd = (((l + l, l + r), k + 1), max 1 (e - 1),
                 newton_split_run_len (newton_mid_is_root Q)
                   (carried_descartes_count (carried_left Q))
                   (carried_descartes_count (carried_right Q)) s, carried_left Q)"
        | "nd = (((l + r, r + r), k + 1), max 1 (e - 1),
                 newton_split_run_len (newton_mid_is_root Q)
                   (carried_descartes_count (carried_left Q))
                   (carried_descartes_count (carried_right Q)) s, carried_right Q)"
        by (auto simp: newton_split_def Let_def)
      thus "\<Phi> nd < int (max_snat LENGTH(gmp_poly_len))"
      proof cases
        case 1 thus ?thesis using rest by blast
      next
        case 2
        have "\<Phi> nd = int k + int 1 + C * dyadic_iv_interval_todo_budget \<delta> (a, ?m)"
          by (simp add: 2 \<Phi>_def newton_node_iv_of_def dyadic_iv_node_iv_of_def tl)
        also have "\<dots> \<le> int k + C * dyadic_iv_interval_todo_budget \<delta> (a, b)"
          by (rule keyle[OF bl C1])
        also have "\<dots> < int (max_snat LENGTH(gmp_poly_len))" using Phi_par .
        finally show ?thesis .
      next
        case 3
        have "\<Phi> nd = int k + int 1 + C * dyadic_iv_interval_todo_budget \<delta> (?m, b)"
          by (simp add: 3 \<Phi>_def newton_node_iv_of_def dyadic_iv_node_iv_of_def tr)
        also have "\<dots> \<le> int k + C * dyadic_iv_interval_todo_budget \<delta> (a, b)"
          by (rule keyle[OF br C1])
        also have "\<dots> < int (max_snat LENGTH(gmp_poly_len))" using Phi_par .
        finally show ?thesis .
      qed
    qed
    show ?thesis
    proof (cases "newton_pol_gate (length Q - Suc 0) e k s")
      case gF: False
      have "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
        using todo_ne last_eq count v0 v1 gF by (simp add: st newton_gmp_step_bail_def Let_def)
      thus ?thesis using splitok by (simp add: \<Phi>_def C_def)
    next
      case gT: True
      show ?thesis
      proof (cases "newton_window_pick_bail (descartes_list_int a b P) e Q")
        case None
        have "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
          using todo_ne last_eq count v0 v1 gT None by (simp add: st newton_gmp_step_bail_def Let_def)
        thus ?thesis using splitok by (simp add: \<Phi>_def C_def)
      next
        case (Some mc)
        obtain m cand where mc_eq: "mc = (m, cand)" by (cases mc)
        obtain l' r' k' where dwc: "newton_window_child l r k e m = (l', r', k')"
          by (cases "newton_window_child l r k e m") auto
        have mb: "m + 4 \<le> int (4 * N_of e)"
          using newton_window_pick_bail_m_bound[OF Some[unfolded mc_eq]] .
        have ecap: "e \<le> newton_pol_ecap" using gT by (simp add: newton_pol_gate_def)
        have kdef: "k' = k + (2 ^ e + 2)" using dwc by (simp add: newton_window_child_def)
        have cellw: "dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv l0 r0 k0 l' r' k') < dyadic_iv_interval_mu \<delta> (a, b)"
        proof -
          have cell: "dyadic_iv_node_iv l0 r0 k0 l' r' k'
              = (a + of_int m * (b - a) / of_nat (4 * N_of e),
                 a + of_int (m + 4) * (b - a) / of_nat (4 * N_of e))"
            using node_iv_window_child_bl[OF l0r0 mb, where l = l and r = r and k = k] dwc
            by (simp add: a_def b_def)
          have Npos: "(0::rat) < of_nat (4 * N_of e)" using N_of_ge_2[of e] by simp
          have wid: "snd (dyadic_iv_node_iv l0 r0 k0 l' r' k') - fst (dyadic_iv_node_iv l0 r0 k0 l' r' k')
              = (b - a) / of_nat (N_of e)"
            unfolding cell fst_conv snd_conv using Npos by (simp add: field_simps of_nat_mult)
          have widr: "of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                      - of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                    = (of_rat b - of_rat a) / of_nat (N_of e)"
          proof -
            have "of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                  - of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                = of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k')
                          - fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))"
              by (simp add: of_rat_diff)
            also have "\<dots> = of_rat ((b - a) / of_nat (N_of e))" using wid by simp
            also have "\<dots> = (of_rat b - of_rat a) / of_nat (N_of e)"
              by (simp add: of_rat_divide of_rat_diff of_rat_of_nat_eq)
            finally show ?thesis .
          qed
          show ?thesis
            unfolding dyadic_iv_interval_mu_def prod.sel
            by (rule mu_subinterval_factor_strict[OF \<delta>_pos _ _ _ widr])
               (use ab \<delta>_lt N_of_ge_2[of e] in \<open>simp_all add: of_rat_less\<close>)
        qed
        have bw: "dyadic_iv_interval_todo_budget \<delta> (dyadic_iv_node_iv l0 r0 k0 l' r' k')
                < dyadic_iv_interval_todo_budget \<delta> (a, b)"
          by (rule dyadic_iv_interval_todo_budget_strict_mono_bl[OF cellw])
        have jumpC: "int (2 ^ e + 2) \<le> C"
          using power_increasing[OF ecap, of "2::nat"] by (simp add: C_def)
        have stf: "fst (newton_gmp_step_bail st) = butlast todo @ [(((l', r'), k'), e + 1, s, cand)]"
          using todo_ne last_eq count v0 v1 gT Some mc_eq dwc
          by (simp add: st newton_gmp_step_bail_def Let_def)
        have windowok: "\<forall>nd \<in> set (butlast todo @ [(((l', r'), k'), e + 1, s, cand)]).
              \<Phi> nd < int (max_snat LENGTH(gmp_poly_len))"
        proof
          fix nd assume "nd \<in> set (butlast todo @ [(((l', r'), k'), e + 1, s, cand)])"
          then consider "nd \<in> set (butlast todo)" | "nd = (((l', r'), k'), e + 1, s, cand)" by auto
          thus "\<Phi> nd < int (max_snat LENGTH(gmp_poly_len))"
          proof cases
            case 1 thus ?thesis using rest by blast
          next
            case 2
            have "\<Phi> nd = int k + int (2 ^ e + 2)
                + C * dyadic_iv_interval_todo_budget \<delta> (dyadic_iv_node_iv l0 r0 k0 l' r' k')"
              by (simp add: 2 \<Phi>_def newton_node_iv_of_def dyadic_iv_node_iv_of_def kdef)
            also have "\<dots> \<le> int k + C * dyadic_iv_interval_todo_budget \<delta> (a, b)"
              by (rule keyle[OF bw jumpC])
            also have "\<dots> < int (max_snat LENGTH(gmp_poly_len))" using Phi_par .
            finally show ?thesis .
          qed
        qed
        show ?thesis unfolding stf using windowok by (simp add: \<Phi>_def C_def)
      qed
    qed
  qed
qed

text \<open>The worklist \<open>size + append-budget\<close> is non-increasing: pop peels \<open>(a,b)\<close>; a split trades
  \<open>2\<close> budget for \<open>1\<close> node (@{thm blr_todo_budget_children_le_bl}); the window trades a strictly-smaller
  budget for the same node count (net \<open>\<le> 0\<close>). Mirrors @{thm newton_gmp_step_bail_mu_decreases}'s geometry.\<close>
lemma newton_gmp_step_bail_preserves_sizebudget:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and l0r0: "l0 < r0"
    and inv: "\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd"
  shows "int (length (fst (newton_gmp_step_bail st)))
       + dyadic_iv_todo_append_budget \<delta> (newton_todo_ivs l0 r0 k0 (fst (newton_gmp_step_bail st)))
     \<le> int (length (fst st))
       + dyadic_iv_todo_append_budget \<delta> (newton_todo_ivs l0 r0 k0 (fst st))"
proof (cases "fst st = []")
  case True thus ?thesis by (cases st) (simp add: newton_gmp_step_bail_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain lr k e s Q where last_eq0: "last todo = ((lr, k), e, s, Q)" by (cases "last todo") auto
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), e, s, Q)" using last_eq0 lr_eq by simp
  have inv': "\<forall>nd \<in> set todo. newton_gmp_node_inv P l0 r0 k0 nd" using inv by (simp add: st)
  have ninv: "newton_gmp_node_inv P l0 r0 k0 (((l, r), k), e, s, Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)"
  define b where "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  have headrepr: "carried_repr_scalar P a b Q"
    using ninv by (simp add: newton_gmp_node_inv_def newton_node_iv_of_def
                              dyadic_iv_node_iv_of_def Let_def a_def b_def)
  have ab: "a < b" using newton_gmp_node_inv_ordered_bl[OF ninv]
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using carried_descartes_count_scalar_bl[OF headrepr len] ab by simp
  have niv: "newton_node_iv_of l0 r0 k0 (((l, r), k), e, s, Q) = (a, b)"
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  let ?m = "(a + b) / 2"
  let ?bud = "dyadic_iv_todo_append_budget \<delta>"
  let ?ib = "dyadic_iv_interval_todo_budget \<delta>"
  have todo_split: "todo = butlast todo @ [(((l, r), k), e, s, Q)]"
    using todo_ne last_eq by (metis append_butlast_last_id)
  have old: "?bud (newton_todo_ivs l0 r0 k0 todo)
      = ?bud (newton_todo_ivs l0 r0 k0 (butlast todo)) + ?ib (a, b)"
    by (subst todo_split) (simp add: newton_todo_ivs_def dyadic_iv_todo_append_budget_def niv)
  have old_len: "int (length todo) = int (length (butlast todo)) + 1"
    using todo_ne by (simp add: length_butlast)
  have fstst: "fst st = todo" by (simp add: st)
  have ib_nn: "?ib (a, b) \<ge> 0" by simp
  have tl: "dyadic_iv_node_iv l0 r0 k0 (2 * l) (l + r) (Suc k) = (a, ?m)"
    using dyadic_iv_node_iv_bisect_left_bl[of l0 r0 k0 l r k] by (simp add: a_def b_def)
  have tr: "dyadic_iv_node_iv l0 r0 k0 (l + r) (2 * r) (Suc k) = (?m, b)"
    using dyadic_iv_node_iv_bisect_right_bl[of l0 r0 k0 l r k] by (simp add: a_def b_def)
  show ?thesis
  proof (cases "descartes_list_int a b P = 0 \<or> descartes_list_int a b P = 1")
    case True
    have stf: "fst (newton_gmp_step_bail st) = butlast todo"
      using todo_ne last_eq True count by (auto simp: st newton_gmp_step_bail_def Let_def)
    show ?thesis unfolding fstst stf using old old_len ib_nn by linarith
  next
    case False
    have v0: "descartes_list_int a b P \<noteq> 0" and v1: "descartes_list_int a b P \<noteq> 1"
      using False by auto
    have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
    proof (rule ccontr)
      assume "\<not> \<delta> < of_rat b - of_rat a"
      then have "of_rat b - of_rat a \<le> \<delta>" by linarith
      then have "descartes_list_int a b P \<le> 1" using small_fast[OF ab] by simp
      with v0 v1 show False by simp
    qed
    have half_lt1: "dyadic_iv_interval_mu \<delta> (a, ?m) < dyadic_iv_interval_mu \<delta> (a, b)"
      using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      by (simp add: dyadic_iv_interval_mu_def of_rat_add of_rat_divide)
    have half_lt2: "dyadic_iv_interval_mu \<delta> (?m, b) < dyadic_iv_interval_mu \<delta> (a, b)"
      using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      by (simp add: dyadic_iv_interval_mu_def of_rat_add of_rat_divide)
    have splitle: "int (length (fst (newton_split l r k e s Q (butlast todo, acc))))
        + ?bud (newton_todo_ivs l0 r0 k0 (fst (newton_split l r k e s Q (butlast todo, acc))))
      \<le> int (length todo) + ?bud (newton_todo_ivs l0 r0 k0 todo)"
    proof -
      have niv: "newton_todo_ivs l0 r0 k0 (fst (newton_split l r k e s Q (butlast todo, acc)))
          = newton_todo_ivs l0 r0 k0 (butlast todo) @ [(a, ?m), (?m, b)]"
        by (simp add: newton_split_def Let_def newton_todo_ivs_def newton_node_iv_of_def
                      dyadic_iv_node_iv_of_def tl tr)
      have nbud: "?bud (newton_todo_ivs l0 r0 k0 (fst (newton_split l r k e s Q (butlast todo, acc))))
          = ?bud (newton_todo_ivs l0 r0 k0 (butlast todo)) + ?ib (a, ?m) + ?ib (?m, b)"
        by (simp add: niv dyadic_iv_todo_append_budget_def)
      have nlen: "int (length (fst (newton_split l r k e s Q (butlast todo, acc))))
          = int (length (butlast todo)) + 2"
        by (simp add: newton_split_def Let_def)
      have child_le: "int 2 + ?ib (a, ?m) + ?ib (?m, b) \<le> ?ib (a, b)"
        using blr_todo_budget_children_le_bl[OF half_lt1 half_lt2]
        unfolding dyadic_iv_interval_todo_budget_def by simp
      show ?thesis using old old_len nbud nlen child_le by linarith
    qed
    show ?thesis
    proof (cases "newton_pol_gate (length Q - Suc 0) e k s")
      case gF: False
      have "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
        using todo_ne last_eq count v0 v1 gF by (simp add: st newton_gmp_step_bail_def Let_def)
      thus ?thesis using splitle fstst by simp
    next
      case gT: True
      show ?thesis
      proof (cases "newton_window_pick_bail (descartes_list_int a b P) e Q")
        case None
        have "fst (newton_gmp_step_bail st) = fst (newton_split l r k e s Q (butlast todo, acc))"
          using todo_ne last_eq count v0 v1 gT None by (simp add: st newton_gmp_step_bail_def Let_def)
        thus ?thesis using splitle fstst by simp
      next
        case (Some mc)
        obtain m cand where mc_eq: "mc = (m, cand)" by (cases mc)
        obtain l' r' k' where dwc: "newton_window_child l r k e m = (l', r', k')"
          by (cases "newton_window_child l r k e m") auto
        have mb: "m + 4 \<le> int (4 * N_of e)" using newton_window_pick_bail_m_bound[OF Some[unfolded mc_eq]] .
        have cellw: "dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv l0 r0 k0 l' r' k') < dyadic_iv_interval_mu \<delta> (a, b)"
        proof -
          have cell: "dyadic_iv_node_iv l0 r0 k0 l' r' k'
              = (a + of_int m * (b - a) / of_nat (4 * N_of e),
                 a + of_int (m + 4) * (b - a) / of_nat (4 * N_of e))"
            using node_iv_window_child_bl[OF l0r0 mb, where l = l and r = r and k = k] dwc
            by (simp add: a_def b_def)
          have Npos: "(0::rat) < of_nat (4 * N_of e)" using N_of_ge_2[of e] by simp
          have wid: "snd (dyadic_iv_node_iv l0 r0 k0 l' r' k') - fst (dyadic_iv_node_iv l0 r0 k0 l' r' k')
              = (b - a) / of_nat (N_of e)"
            unfolding cell fst_conv snd_conv using Npos by (simp add: field_simps of_nat_mult)
          have widr: "of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                      - of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                    = (of_rat b - of_rat a) / of_nat (N_of e)"
          proof -
            have "of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                  - of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                = of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k')
                          - fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))" by (simp add: of_rat_diff)
            also have "\<dots> = of_rat ((b - a) / of_nat (N_of e))" using wid by simp
            also have "\<dots> = (of_rat b - of_rat a) / of_nat (N_of e)"
              by (simp add: of_rat_divide of_rat_diff of_rat_of_nat_eq)
            finally show ?thesis .
          qed
          show ?thesis
            unfolding dyadic_iv_interval_mu_def prod.sel
            by (rule mu_subinterval_factor_strict[OF \<delta>_pos _ _ _ widr])
               (use ab \<delta>_lt N_of_ge_2[of e] in \<open>simp_all add: of_rat_less\<close>)
        qed
        have bw: "?ib (dyadic_iv_node_iv l0 r0 k0 l' r' k') < ?ib (a, b)"
          by (rule dyadic_iv_interval_todo_budget_strict_mono_bl[OF cellw])
        have stf: "fst (newton_gmp_step_bail st) = butlast todo @ [(((l', r'), k'), e + 1, s, cand)]"
          using todo_ne last_eq count v0 v1 gT Some mc_eq dwc
          by (simp add: st newton_gmp_step_bail_def Let_def)
        have nbud: "?bud (newton_todo_ivs l0 r0 k0 (fst (newton_gmp_step_bail st)))
            = ?bud (newton_todo_ivs l0 r0 k0 (butlast todo)) + ?ib (dyadic_iv_node_iv l0 r0 k0 l' r' k')"
          by (simp add: stf newton_todo_ivs_def newton_node_iv_of_def dyadic_iv_node_iv_of_def
                        dyadic_iv_todo_append_budget_def)
        have nlen: "int (length (fst (newton_gmp_step_bail st))) = int (length (butlast todo)) + 1"
          by (simp add: stf)
        show ?thesis unfolding fstst using old old_len nbud nlen bw by linarith
      qed
    qed
  qed
qed

text \<open>The acc \<open>size + acc-budget\<close> is non-increasing: accepting a node / pushing a midpoint grows acc
  by 1, covered by the popped node's acc-budget (\<open>\<ge> 1\<close>); a split's children acc-budgets sum to
  \<open>\<le> popped - 1\<close> (@{thm blr_acc_budget_children_le_bl}); the window adds no accepted interval.\<close>
lemma newton_gmp_step_bail_preserves_accbudget:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and l0r0: "l0 < r0"
    and inv: "\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd"
  shows "int (length (snd (newton_gmp_step_bail st)))
       + dyadic_iv_todo_acc_budget \<delta> (newton_todo_ivs l0 r0 k0 (fst (newton_gmp_step_bail st)))
     \<le> int (length (snd st))
       + dyadic_iv_todo_acc_budget \<delta> (newton_todo_ivs l0 r0 k0 (fst st))"
proof (cases "fst st = []")
  case True thus ?thesis by (cases st) (simp add: newton_gmp_step_bail_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain lr k e s Q where last_eq0: "last todo = ((lr, k), e, s, Q)" by (cases "last todo") auto
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), e, s, Q)" using last_eq0 lr_eq by simp
  have inv': "\<forall>nd \<in> set todo. newton_gmp_node_inv P l0 r0 k0 nd" using inv by (simp add: st)
  have ninv: "newton_gmp_node_inv P l0 r0 k0 (((l, r), k), e, s, Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (dyadic_iv_node_iv l0 r0 k0 l r k)"
  define b where "b = snd (dyadic_iv_node_iv l0 r0 k0 l r k)"
  have headrepr: "carried_repr_scalar P a b Q"
    using ninv by (simp add: newton_gmp_node_inv_def newton_node_iv_of_def
                              dyadic_iv_node_iv_of_def Let_def a_def b_def)
  have ab: "a < b" using newton_gmp_node_inv_ordered_bl[OF ninv]
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using carried_descartes_count_scalar_bl[OF headrepr len] ab by simp
  have niv: "newton_node_iv_of l0 r0 k0 (((l, r), k), e, s, Q) = (a, b)"
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def a_def b_def)
  let ?m = "(a + b) / 2"
  let ?ab = "dyadic_iv_todo_acc_budget \<delta>"
  let ?ia = "dyadic_iv_interval_acc_budget \<delta>"
  have todo_split: "todo = butlast todo @ [(((l, r), k), e, s, Q)]"
    using todo_ne last_eq by (metis append_butlast_last_id)
  have old: "?ab (newton_todo_ivs l0 r0 k0 todo)
      = ?ab (newton_todo_ivs l0 r0 k0 (butlast todo)) + ?ia (a, b)"
    by (subst todo_split) (simp add: newton_todo_ivs_def dyadic_iv_todo_acc_budget_def niv)
  have ia_pos: "?ia (a, b) \<ge> 1" using dyadic_iv_interval_acc_budget_pos_bl[of \<delta> "(a, b)"] by linarith
  have sndst: "snd st = acc" by (simp add: st)
  have fstst: "fst st = todo" by (simp add: st)
  have tl: "dyadic_iv_node_iv l0 r0 k0 (2 * l) (l + r) (Suc k) = (a, ?m)"
    using dyadic_iv_node_iv_bisect_left_bl[of l0 r0 k0 l r k] by (simp add: a_def b_def)
  have tr: "dyadic_iv_node_iv l0 r0 k0 (l + r) (2 * r) (Suc k) = (?m, b)"
    using dyadic_iv_node_iv_bisect_right_bl[of l0 r0 k0 l r k] by (simp add: a_def b_def)
  show ?thesis
  proof (cases "descartes_list_int a b P = 0")
    case True
    have stf: "newton_gmp_step_bail st = (butlast todo, acc)"
      using todo_ne last_eq True count by (simp add: st newton_gmp_step_bail_def Let_def)
    show ?thesis unfolding sndst stf fstst using old ia_pos by simp
  next
    case v0: False
    show ?thesis
    proof (cases "descartes_list_int a b P = 1")
      case True
      have stf: "newton_gmp_step_bail st = (butlast todo, acc @ [((l, r), k)])"
        using todo_ne last_eq True count by (simp add: st newton_gmp_step_bail_def Let_def)
      show ?thesis unfolding sndst stf fstst using old ia_pos by simp
    next
      case v1: False
      have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
      proof (rule ccontr)
        assume "\<not> \<delta> < of_rat b - of_rat a"
        then have "of_rat b - of_rat a \<le> \<delta>" by linarith
        then have "descartes_list_int a b P \<le> 1" using small_fast[OF ab] by simp
        with v0 v1 count show False by simp
      qed
      have half_lt1: "dyadic_iv_interval_mu \<delta> (a, ?m) < dyadic_iv_interval_mu \<delta> (a, b)"
        using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
        by (simp add: dyadic_iv_interval_mu_def of_rat_add of_rat_divide)
      have half_lt2: "dyadic_iv_interval_mu \<delta> (?m, b) < dyadic_iv_interval_mu \<delta> (a, b)"
        using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
        by (simp add: dyadic_iv_interval_mu_def of_rat_add of_rat_divide)
      have vf: "carried_descartes_count Q \<noteq> 0" "carried_descartes_count Q \<noteq> 1"
        using v0 v1 count by auto
      have splitle: "int (length (snd (newton_split l r k e s Q (butlast todo, acc))))
          + ?ab (newton_todo_ivs l0 r0 k0 (fst (newton_split l r k e s Q (butlast todo, acc))))
        \<le> int (length acc) + ?ab (newton_todo_ivs l0 r0 k0 todo)"
      proof -
        have niv2: "newton_todo_ivs l0 r0 k0 (fst (newton_split l r k e s Q (butlast todo, acc)))
            = newton_todo_ivs l0 r0 k0 (butlast todo) @ [(a, ?m), (?m, b)]"
          by (simp add: newton_split_def Let_def newton_todo_ivs_def newton_node_iv_of_def
                        dyadic_iv_node_iv_of_def tl tr)
        have nbud: "?ab (newton_todo_ivs l0 r0 k0 (fst (newton_split l r k e s Q (butlast todo, acc))))
            = ?ab (newton_todo_ivs l0 r0 k0 (butlast todo)) + ?ia (a, ?m) + ?ia (?m, b)"
          by (simp add: niv2 dyadic_iv_todo_acc_budget_def)
        have sndf: "int (length (snd (newton_split l r k e s Q (butlast todo, acc))))
            \<le> int (length acc) + 1"
          by (simp add: newton_split_def Let_def)
        have child_le: "?ia (a, ?m) + ?ia (?m, b) + 1 \<le> ?ia (a, b)"
          using blr_acc_budget_children_le_bl[OF half_lt1 half_lt2]
          unfolding dyadic_iv_interval_acc_budget_def by simp
        show ?thesis using old nbud sndf child_le by linarith
      qed
      show ?thesis
      proof (cases "newton_pol_gate (length Q - Suc 0) e k s")
        case gF: False
        have "newton_gmp_step_bail st = newton_split l r k e s Q (butlast todo, acc)"
          using todo_ne last_eq count vf gF by (simp add: st newton_gmp_step_bail_def Let_def)
        thus ?thesis unfolding fstst using splitle sndst by simp
      next
        case gT: True
        show ?thesis
        proof (cases "newton_window_pick_bail (descartes_list_int a b P) e Q")
          case None
          have "newton_gmp_step_bail st = newton_split l r k e s Q (butlast todo, acc)"
            using todo_ne last_eq count vf gT None by (simp add: st newton_gmp_step_bail_def Let_def)
          thus ?thesis unfolding fstst using splitle sndst by simp
        next
          case (Some mc)
          obtain m cand where mc_eq: "mc = (m, cand)" by (cases mc)
          obtain l' r' k' where dwc: "newton_window_child l r k e m = (l', r', k')"
            by (cases "newton_window_child l r k e m") auto
          have mb: "m + 4 \<le> int (4 * N_of e)" using newton_window_pick_bail_m_bound[OF Some[unfolded mc_eq]] .
          have cellw: "dyadic_iv_interval_mu \<delta> (dyadic_iv_node_iv l0 r0 k0 l' r' k') < dyadic_iv_interval_mu \<delta> (a, b)"
          proof -
            have cell: "dyadic_iv_node_iv l0 r0 k0 l' r' k'
                = (a + of_int m * (b - a) / of_nat (4 * N_of e),
                   a + of_int (m + 4) * (b - a) / of_nat (4 * N_of e))"
              using node_iv_window_child_bl[OF l0r0 mb, where l = l and r = r and k = k] dwc
              by (simp add: a_def b_def)
            have Npos: "(0::rat) < of_nat (4 * N_of e)" using N_of_ge_2[of e] by simp
            have wid: "snd (dyadic_iv_node_iv l0 r0 k0 l' r' k') - fst (dyadic_iv_node_iv l0 r0 k0 l' r' k')
                = (b - a) / of_nat (N_of e)"
              unfolding cell fst_conv snd_conv using Npos by (simp add: field_simps of_nat_mult)
            have widr: "of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                        - of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                      = (of_rat b - of_rat a) / of_nat (N_of e)"
            proof -
              have "of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                    - of_rat (fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))
                  = of_rat (snd (dyadic_iv_node_iv l0 r0 k0 l' r' k')
                            - fst (dyadic_iv_node_iv l0 r0 k0 l' r' k'))" by (simp add: of_rat_diff)
              also have "\<dots> = of_rat ((b - a) / of_nat (N_of e))" using wid by simp
              also have "\<dots> = (of_rat b - of_rat a) / of_nat (N_of e)"
                by (simp add: of_rat_divide of_rat_diff of_rat_of_nat_eq)
              finally show ?thesis .
            qed
            show ?thesis
              unfolding dyadic_iv_interval_mu_def prod.sel
              by (rule mu_subinterval_factor_strict[OF \<delta>_pos _ _ _ widr])
                 (use ab \<delta>_lt N_of_ge_2[of e] in \<open>simp_all add: of_rat_less\<close>)
          qed
          have bw: "?ia (dyadic_iv_node_iv l0 r0 k0 l' r' k') < ?ia (a, b)"
            by (rule dyadic_iv_interval_acc_budget_strict_mono_bl[OF cellw])
          have stf: "newton_gmp_step_bail st = (butlast todo @ [(((l', r'), k'), e + 1, s, cand)], acc)"
            using todo_ne last_eq count vf gT Some mc_eq dwc
            by (simp add: st newton_gmp_step_bail_def Let_def)
          have nbud: "?ab (newton_todo_ivs l0 r0 k0 (fst (newton_gmp_step_bail st)))
              = ?ab (newton_todo_ivs l0 r0 k0 (butlast todo))
                + ?ia (dyadic_iv_node_iv l0 r0 k0 l' r' k')"
            by (simp add: stf newton_todo_ivs_def newton_node_iv_of_def dyadic_iv_node_iv_of_def
                          dyadic_iv_todo_acc_budget_def)
          show ?thesis unfolding sndst fstst using old nbud bw stf by simp
        qed
      qed
    qed
  qed
qed

subsection \<open>Budgets: dyadic-vector \<open>pushable\<close> from the capacity budgets\<close>

lemma blr_dyadic_interval_vec_pushable2_from_budget_bl:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "int (length lns) + B + 2 < int (max_snat LENGTH(gmp_poly_len))" and "0 \<le> B"
  shows "dyadic_interval_vec_pushable2 (lns, rns, ks)"
  using assms unfolding dyadic_interval_vec_invar_def dyadic_interval_vec_pushable2_def by auto

lemma blr_dyadic_interval_vec_pushable_from_budget_bl:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "int (length lns) + B + 1 < int (max_snat LENGTH(gmp_poly_len))" and "0 \<le> B"
  shows "dyadic_interval_vec_pushable (lns, rns, ks)"
  using assms unfolding dyadic_interval_vec_invar_def dyadic_interval_vec_pushable_def by auto

text \<open>The concrete @{const newton_loop_safe_invar} (the body's typing precondition) follows from
  the \<open>\<alpha>\<close>-stated conjuncts of @{const blr_refine_invar} — NOT from \<open>safe_invar\<close> itself, so it is reusable
  for the result state to re-establish safety without circularity. \<open>pushable\<close> from the size/acc budgets;
  \<open>last ks + 1 < max_snat\<close> from the \<open>k\<close>-potential (\<open>a<b \<Longrightarrow> \<mu>\<ge>1 \<Longrightarrow> budget \<ge> 2\<close>); the \<open>qtodo\<close>/\<open>es\<close>
  bounds from the poly-length conjunct + \<open>P\<close> assumptions and the size budget.\<close>
lemma blr_imp_safe_invar_bl:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and si: "newton_loop_state_invar st"
    and ndinv: "\<forall>nd \<in> set (blr_alpha_todo st). newton_gmp_node_inv P l0 r0 k0 nd"
    and szbud: "int (length (blr_alpha_todo st))
        + dyadic_iv_todo_append_budget \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st)) + 2
        < int (max_snat LENGTH(gmp_poly_len))"
    and accbud: "int (length (blr_alpha_acc st))
        + dyadic_iv_todo_acc_budget \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st)) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    and kpot: "\<forall>nd \<in> set (blr_alpha_todo st).
        int (snd (fst nd)) + int (2 ^ newton_pol_ecap + 2)
          * dyadic_iv_interval_todo_budget \<delta> (newton_node_iv_of l0 r0 k0 nd)
        < int (max_snat LENGTH(gmp_poly_len))"
    and plen: "\<forall>nd \<in> set (blr_alpha_todo st). length (snd (snd (snd nd))) = length P"
    and P_len: "0 < length P"
    and P_bound: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "newton_loop_safe_invar st"
proof -
  obtain lns rns ks qtodo es ss cs alns arns aks
    where dstr: "st = (((lns, rns, ks), qtodo, es, ss, cs), (alns, arns, aks))"
    by (cases st) auto
  from si have ivT: "dyadic_interval_vec_invar (lns, rns, ks)"
    and ivA: "dyadic_interval_vec_invar (alns, arns, aks)"
    and ltq: "length qtodo = length lns" and lte: "length es = length lns"
    and lss: "length ss = length lns" and lcs: "length cs = length lns"
    by (auto simp: dstr newton_loop_state_invar_def Let_def)
  from ivT have llr: "length lns = length rns" and llk: "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  have "newton_loop_cond st \<longrightarrow>
      (dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks) \<and>
       dyadic_interval_vec_pushable (alns, arns, aks) \<and>
       qtodo \<noteq> [] \<and> es \<noteq> [] \<and> ss \<noteq> [] \<and> cs \<noteq> [] \<and>
       0 < length (last qtodo) \<and>
       length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
       last ks + 1 < max_snat LENGTH(gmp_poly_len) \<and>
       length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
       length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
       length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
       length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len))"
  proof
    assume cond: "newton_loop_cond st"
    have ne: "lns \<noteq> []" using cond by (simp add: dstr newton_loop_cond_def Let_def)
    have qne: "qtodo \<noteq> []" using ne ltq by (cases qtodo) auto
    have ene: "es \<noteq> []" using ne lte by (cases es) auto
    have sne: "ss \<noteq> []" using ne lss by (cases ss) auto
    have cne: "cs \<noteq> []" using ne lcs by (cases cs) auto
    have lenAt: "length (blr_alpha_todo st) = length lns"
      using blr_alpha_todo_length_bl[OF si] by (simp add: dstr)
    have lenAa: "length (blr_alpha_acc st) = length alns"
      using ivA by (simp add: dstr blr_alpha_acc_def dyadic_interval_vec_triples_length)
    have bud_nn: "0 \<le> dyadic_iv_todo_append_budget \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st))" by simp
    have accbud_nn: "0 \<le> dyadic_iv_todo_acc_budget \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st))" by simp
    \<comment> \<open>pushable2 on butlast dyadic vector\<close>
    have iv_bl: "dyadic_interval_vec_invar (butlast lns, butlast rns, butlast ks)"
      using ivT by (auto simp: dyadic_interval_vec_invar_def llr llk)
    have push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    proof (rule blr_dyadic_interval_vec_pushable2_from_budget_bl[OF iv_bl _ bud_nn])
      have "int (length (butlast lns)) \<le> int (length (blr_alpha_todo st))"
        using lenAt by (simp add: length_butlast)
      thus "int (length (butlast lns))
          + dyadic_iv_todo_append_budget \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st)) + 2
          < int (max_snat LENGTH(gmp_poly_len))" using szbud by linarith
    qed
    have pushA: "dyadic_interval_vec_pushable (alns, arns, aks)"
    proof (rule blr_dyadic_interval_vec_pushable_from_budget_bl[OF ivA _ accbud_nn])
      show "int (length alns)
          + dyadic_iv_todo_acc_budget \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st)) + 1
          < int (max_snat LENGTH(gmp_poly_len))" using accbud lenAa by simp
    qed
    \<comment> \<open>the popped abstract node (its poly and dyadic exponent)\<close>
    have lastA: "last (blr_alpha_todo st)
               = (((last lns, last rns), last ks), last es, last ss, last qtodo)"
      using blr_alpha_todo_last_bl[OF si[unfolded dstr] ne] by (simp add: dstr)
    have Atne: "blr_alpha_todo st \<noteq> []" using blr_alpha_cond_bl[OF si] cond by simp
    have lastA_in: "last (blr_alpha_todo st) \<in> set (blr_alpha_todo st)" using Atne by simp
    \<comment> \<open>poly-length: \<open>last qtodo\<close> has length \<open>P\<close>\<close>
    have lenQ: "length (last qtodo) = length P"
      using plen[rule_format, OF lastA_in] lastA by simp
    have q0: "0 < length (last qtodo)" using lenQ P_len by simp
    have q1: "length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len)" using lenQ P_bound by linarith
    have q1': "length (last qtodo) + 2 < max_snat LENGTH(gmp_poly_len)" using lenQ P_bound by simp
    \<comment> \<open>\<open>last ks + 1 < max_snat\<close> from the \<open>k\<close>-potential + node ordering (\<open>\<mu> \<ge> 1\<close>)\<close>
    have lastk: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
    proof -
      obtain a b where niv: "newton_node_iv_of l0 r0 k0 (last (blr_alpha_todo st)) = (a, b)"
        by (cases "newton_node_iv_of l0 r0 k0 (last (blr_alpha_todo st))")
      have ab: "a < b"
        using newton_gmp_node_inv_ordered_bl[OF ndinv[rule_format, OF lastA_in]] niv by simp
      have mu1: "1 \<le> dyadic_iv_interval_mu \<delta> (a, b)"
      proof -
        let ?x = "(of_rat b - of_rat a) / \<delta>"
        have "0 < ?x" using ab \<delta>_pos by (simp add: of_rat_less)
        hence "(1::int) \<le> \<lceil>?x\<rceil>" by (simp add: le_ceiling_iff)
        hence "1 \<le> nat \<lceil>?x\<rceil>" using nat_mono[of 1 "\<lceil>?x\<rceil>"] by simp
        thus ?thesis by (simp add: dyadic_iv_interval_mu_def mu_def)
      qed
      have bud2: "2 \<le> dyadic_iv_interval_todo_budget \<delta> (a, b)"
      proof -
        obtain n where n: "dyadic_iv_interval_mu \<delta> (a, b) = Suc n"
          using mu1 by (cases "dyadic_iv_interval_mu \<delta> (a, b)") auto
        have "(1::nat) \<le> 2 ^ n" by simp
        hence "(4::int) \<le> int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (a, b)))"
          by (simp add: n)
        thus ?thesis unfolding dyadic_iv_interval_todo_budget_def by linarith
      qed
      have kp: "int (last ks) + int (2 ^ newton_pol_ecap + 2) * dyadic_iv_interval_todo_budget \<delta> (a, b)
          < int (max_snat LENGTH(gmp_poly_len))"
        using kpot[rule_format, OF lastA_in] lastA niv by simp
      have Cge: "(1::int) \<le> int (2 ^ newton_pol_ecap + 2)" by simp
      have "int (last ks) + 2 \<le> int (last ks)
              + int (2 ^ newton_pol_ecap + 2) * dyadic_iv_interval_todo_budget \<delta> (a, b)"
        using bud2 Cge mult_mono[of 1 "int (2 ^ newton_pol_ecap + 2)" 2
                                    "dyadic_iv_interval_todo_budget \<delta> (a, b)"] by simp
      thus ?thesis using kp by linarith
    qed
    \<comment> \<open>butlast \<open>qtodo\<close>/\<open>es\<close> length bounds from the size budget (\<open>length lns + 2 < max_snat\<close>)\<close>
    have lns2: "length lns + 2 < max_snat LENGTH(gmp_poly_len)"
      using szbud bud_nn lenAt by linarith
    have blq: "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
      using ltq ne qne lns2 by (simp add: length_butlast)
    have ble: "length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len)"
      using lte ne ene lns2 by (simp add: length_butlast)
    have bls: "length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len)"
      using lss ne sne lns2 by (simp add: length_butlast)
    have blc: "length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len)"
      using lcs ne cne lns2 by (simp add: length_butlast)
    show "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks) \<and>
       dyadic_interval_vec_pushable (alns, arns, aks) \<and>
       qtodo \<noteq> [] \<and> es \<noteq> [] \<and> ss \<noteq> [] \<and> cs \<noteq> [] \<and> 0 < length (last qtodo) \<and>
       length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
       last ks + 1 < max_snat LENGTH(gmp_poly_len) \<and>
       length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
       length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
       length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len) \<and>
       length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len)"
      using push2 pushA qne ene sne cne q0 q1 lastk blq ble bls blc by blast
  qed
  thus ?thesis
    unfolding newton_loop_safe_invar_def using si by (auto simp: dstr)
qed

subsection \<open>Assembly: one concrete step preserves @{const blr_refine_invar}, the \<open>\<alpha>\<close> equation and the \<open>\<mu>\<close> decrease\<close>

text \<open>A step result matching @{thm blr_after_pop_refine_bl}'s characterisation projects (via
  @{thm blr_step_alpha_eq_bl}) to @{const newton_gmp_step_bail}, so @{const blr_refine_invar} is preserved
  (node-inv by @{thm newton_gmp_node_inv_preserved_bl}, driver-fixpoint by one @{const newton_gmp_main_bail}
  unfold, the five budget/length conjuncts by the five preservation lemmas, safe-invariant by
  @{thm blr_imp_safe_invar_bl}) and the \<open>\<mu>\<close>-mset measure strictly decreases
  (@{thm newton_gmp_step_bail_mu_decreases}).\<close>
lemma blr_step_result_invar_bl:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and l0r0: "l0 < r0"
    and inv: "blr_refine_invar \<delta> P l0 r0 k0 st0
                (((lns, rns, ks), qtodo, es, ss, cs), (alns, arns, aks))"
    and ne: "lns \<noteq> []"
    and P_len: "0 < length P" and P_bound: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
    and vt': "dyadic_interval_vec_invar todo'"
    and char: "let v = carried_descartes_count (last qtodo);
                   base_t = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks);
                   split_t = base_t @ [((last lns + last lns, last lns + last rns), last ks + 1),
                                       ((last lns + last rns, last rns + last rns), last ks + 1)];
                   split_q = butlast qtodo @ [carried_left (last qtodo), carried_right (last qtodo)];
                   split_es = butlast es @ [max 1 (last es - 1), max 1 (last es - 1)];
                   split_acc = (if newton_mid_is_root (last qtodo)
                                then (alns @ [last lns + last rns], arns @ [last lns + last rns],
                                      aks @ [last ks + 1])
                                else (alns, arns, aks));
                   split_sc = (\<lambda>ss'' cs''. \<exists>cl cr.
                        ss'' = butlast ss
                          @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                             newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]
                        \<and> cs'' = butlast cs @ [cl, cr]
                        \<and> (cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)
                        \<and> (cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)
                        \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))
                        \<and> (cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)
                        \<and> (cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)
                        \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))
                        \<and> cl \<le> 3 \<and> cr \<le> 3)
               in
               if v = 0 then dyadic_interval_vec_triples todo' = base_t \<and> qtodo' = butlast qtodo
                             \<and> es' = butlast es \<and> ss' = butlast ss \<and> cs' = butlast cs
                             \<and> acc' = (alns, arns, aks)
               else if v = 1 then dyadic_interval_vec_triples todo' = base_t \<and> qtodo' = butlast qtodo
                                  \<and> es' = butlast es \<and> ss' = butlast ss \<and> cs' = butlast cs
                                  \<and> acc' = (alns @ [last lns], arns @ [last rns], aks @ [last ks])
               else if \<not> newton_pol_gate (length (last qtodo) - 1) (last es) (last ks) (last ss)
                    then dyadic_interval_vec_triples todo' = split_t \<and> qtodo' = split_q
                         \<and> es' = split_es \<and> acc' = split_acc \<and> split_sc ss' cs'
               else (case newton_window_pick_bail v (last es) (last qtodo) of
                       Some (m, cand) \<Rightarrow>
                         (let (l', r', k') = newton_window_child (last lns) (last rns) (last ks) (last es) m in
                          dyadic_interval_vec_triples todo' = base_t @ [((l', r'), k')]
                          \<and> qtodo' = butlast qtodo @ [cand] \<and> es' = butlast es @ [last es + 1]
                          \<and> ss' = butlast ss @ [last ss] \<and> cs' = butlast cs @ [v + 2]
                          \<and> acc' = (alns, arns, aks) \<and> cand = newton_wcand (last es) m (last qtodo))
                     | None \<Rightarrow> dyadic_interval_vec_triples todo' = split_t \<and> qtodo' = split_q
                                \<and> es' = split_es \<and> acc' = split_acc \<and> split_sc ss' cs')"
  shows "blr_refine_invar \<delta> P l0 r0 k0 st0 ((todo', qtodo', es', ss', cs'), acc')
       \<and> blr_alpha ((todo', qtodo', es', ss', cs'), acc')
           = newton_gmp_step_bail (blr_alpha (((lns, rns, ks), qtodo, es, ss, cs), (alns, arns, aks)))
       \<and> dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0
             (blr_alpha_todo ((todo', qtodo', es', ss', cs'), acc')))
         < dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0
             (blr_alpha_todo (((lns, rns, ks), qtodo, es, ss, cs), (alns, arns, aks))))"
proof -
  let ?st = "(((lns, rns, ks), qtodo, es, ss, cs), (alns, arns, aks))"
  let ?st' = "((todo', qtodo', es', ss', cs'), acc')"
  \<comment> \<open>extract the @{const blr_refine_invar} conjuncts of @{term ?st}\<close>
  from inv have safe: "newton_loop_safe_invar ?st"
    and ndinv: "\<forall>nd \<in> set (blr_alpha_todo ?st). newton_gmp_node_inv P l0 r0 k0 nd"
    and main_eq: "newton_gmp_main_bail (blr_alpha ?st) = newton_gmp_main_bail st0"
    and szbud: "int (length (blr_alpha_todo ?st))
        + dyadic_iv_todo_append_budget \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo ?st)) + 2
        < int (max_snat LENGTH(gmp_poly_len))"
    and accbud: "int (length (blr_alpha_acc ?st))
        + dyadic_iv_todo_acc_budget \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo ?st)) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    and kpot: "\<forall>nd \<in> set (blr_alpha_todo ?st).
        int (snd (fst nd)) + int (2 ^ newton_pol_ecap + 2)
          * dyadic_iv_interval_todo_budget \<delta> (newton_node_iv_of l0 r0 k0 nd)
        < int (max_snat LENGTH(gmp_poly_len))"
    and plen: "\<forall>nd \<in> set (blr_alpha_todo ?st). length (snd (snd (snd nd))) = length P"
    and sbound: "\<forall>nd \<in> set (blr_alpha_todo ?st). fst (snd (snd nd)) \<le> snd (fst nd)"
    unfolding blr_refine_invar_def newton_todo_ivs_def by blast+
  from safe have si: "newton_loop_state_invar ?st"
    by (simp add: newton_loop_safe_invar_def)
  from si have ivT: "dyadic_interval_vec_invar (lns, rns, ks)"
    and ivA: "dyadic_interval_vec_invar (alns, arns, aks)"
    and lq: "length qtodo = length lns" and le: "length es = length lns"
    and lss: "length ss = length lns" and lcs: "length cs = length lns"
    by (auto simp: newton_loop_state_invar_def Let_def)
  from ivT have llr: "length lns = length rns" and llk: "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  \<comment> \<open>W1: the popped node's cached classify (last cs entry) aligns with @{term "last qtodo"}'s count\<close>
  from inv have csinv0: "\<forall>i < length cs. dyadic_iv_cs_invar (cs ! i) (carried_descartes_count (qtodo ! i))"
    by (simp add: blr_refine_invar_def)
  have cond: "newton_loop_cond ?st"
    by (simp add: newton_loop_cond_def Let_def ne)
  have At_ne: "blr_alpha_todo ?st \<noteq> []" using blr_alpha_cond_bl[OF si] cond by simp
  have fcl: "fst (blr_alpha ?st) = blr_alpha_todo ?st" by (simp add: blr_alpha_def)
  have scl: "snd (blr_alpha ?st) = blr_alpha_acc ?st" by (simp add: blr_alpha_def)
  \<comment> \<open>the \<open>\<alpha>\<close>-equation\<close>
  have alpha: "blr_alpha ?st' = newton_gmp_step_bail (blr_alpha ?st)"
    by (rule blr_step_alpha_eq_bl[OF si ne char])
  have at_eq: "blr_alpha_todo ?st' = fst (newton_gmp_step_bail (blr_alpha ?st))"
    using arg_cong[OF alpha, of fst] by (simp add: blr_alpha_def)
  have aa_eq: "blr_alpha_acc ?st' = snd (newton_gmp_step_bail (blr_alpha ?st))"
    using arg_cong[OF alpha, of snd] by (simp add: blr_alpha_def)
  have ndinv_a: "\<forall>nd \<in> set (fst (blr_alpha ?st)). newton_gmp_node_inv P l0 r0 k0 nd"
    using ndinv by (simp add: fcl)
  \<comment> \<open>(2) node-inv preserved\<close>
  have ndinv': "\<forall>nd \<in> set (blr_alpha_todo ?st'). newton_gmp_node_inv P l0 r0 k0 nd"
    using newton_gmp_node_inv_preserved_bl[OF P_len l0r0 ndinv_a] by (simp add: at_eq)
  \<comment> \<open>(3) driver-fixpoint preserved\<close>
  have main': "newton_gmp_main_bail (blr_alpha ?st') = newton_gmp_main_bail st0"
  proof -
    obtain x xs where ct: "blr_alpha_todo ?st = x # xs"
      using At_ne by (cases "blr_alpha_todo ?st") auto
    have "blr_alpha ?st = (x # xs, blr_alpha_acc ?st)" using ct by (simp add: blr_alpha_def)
    hence "newton_gmp_main_bail (blr_alpha ?st) = newton_gmp_main_bail (newton_gmp_step_bail (blr_alpha ?st))"
      by (simp add: newton_gmp_main_bail.simps)
    thus ?thesis using alpha main_eq by simp
  qed
  \<comment> \<open>abbreviations for the pure step over @{term "blr_alpha ?st"}\<close>
  have stA: "fst (blr_alpha ?st) \<noteq> []" using At_ne fcl by simp
  note pres = \<delta>_pos len small_fast l0r0 ndinv_a
  \<comment> \<open>(4)/(5)/(6)/(7)/(8): the five preservation lemmas, transferred to @{term ?st'} via @{thm at_eq}\<close>
  have plen': "\<forall>nd \<in> set (blr_alpha_todo ?st'). length (snd (snd (snd nd))) = length P"
    using newton_gmp_step_bail_preserves_polylen[where n = "length P" and st = "blr_alpha ?st"]
          plen by (simp add: at_eq fcl)
  have sbound': "\<forall>nd \<in> set (blr_alpha_todo ?st'). fst (snd (snd nd)) \<le> snd (fst nd)"
    using newton_gmp_step_bail_preserves_sbound[where st = "blr_alpha ?st"] sbound
    by (simp add: at_eq fcl)
  have kpot': "\<forall>nd \<in> set (blr_alpha_todo ?st').
      int (snd (fst nd)) + int (2 ^ newton_pol_ecap + 2)
        * dyadic_iv_interval_todo_budget \<delta> (newton_node_iv_of l0 r0 k0 nd)
      < int (max_snat LENGTH(gmp_poly_len))"
    using newton_gmp_step_bail_preserves_kbud[OF \<delta>_pos len small_fast l0r0 ndinv_a] kpot
    by (simp add: at_eq fcl)
  have szbud': "int (length (blr_alpha_todo ?st'))
      + dyadic_iv_todo_append_budget \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo ?st')) + 2
      < int (max_snat LENGTH(gmp_poly_len))"
    using newton_gmp_step_bail_preserves_sizebudget[OF \<delta>_pos len small_fast l0r0 ndinv_a] szbud
    by (simp add: at_eq fcl)
  have accbud': "int (length (blr_alpha_acc ?st'))
      + dyadic_iv_todo_acc_budget \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo ?st')) + 1
      < int (max_snat LENGTH(gmp_poly_len))"
    using newton_gmp_step_bail_preserves_accbudget[OF \<delta>_pos len small_fast l0r0 ndinv_a] accbud
    by (simp add: at_eq aa_eq fcl scl)
  \<comment> \<open>(1) concrete state-invariant and safe-invariant for @{term ?st'}\<close>
  have lastqt: "last qtodo \<in> set qtodo" using ne lq by (cases qtodo) auto
  have lenbl: "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
             = length (butlast qtodo)"
    using llr llk lq by (simp add: dyadic_interval_vec_triples_simps length_zip length_butlast)
  have lenble: "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
             = length (butlast es)"
    using llr llk le lq by (simp add: dyadic_interval_vec_triples_simps length_zip length_butlast)
  have lenbls: "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
             = length (butlast ss)"
    using llr llk lss lq by (simp add: dyadic_interval_vec_triples_simps length_zip length_butlast)
  have lenblc: "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
             = length (butlast cs)"
    using llr llk lcs lq by (simp add: dyadic_interval_vec_triples_simps length_zip length_butlast)
  note lenb = lenbl lenble lenbls lenblc
  have lenqe: "length (dyadic_interval_vec_triples todo') = length qtodo'
             \<and> length (dyadic_interval_vec_triples todo') = length es'
             \<and> length (dyadic_interval_vec_triples todo') = length ss'
             \<and> length (dyadic_interval_vec_triples todo') = length cs'
             \<and> dyadic_interval_vec_invar acc'"
  proof (cases "carried_descartes_count (last qtodo) = 0")
    case v0: True
    have "dyadic_interval_vec_triples todo'
            = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)
          \<and> qtodo' = butlast qtodo \<and> es' = butlast es \<and> ss' = butlast ss \<and> cs' = butlast cs
          \<and> acc' = (alns, arns, aks)"
      using char v0 by (simp add: Let_def)
    thus ?thesis using lenb ivA by simp
  next
    case v0: False
    show ?thesis
    proof (cases "carried_descartes_count (last qtodo) = 1")
      case v1: True
      have "dyadic_interval_vec_triples todo'
              = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)
            \<and> qtodo' = butlast qtodo \<and> es' = butlast es \<and> ss' = butlast ss \<and> cs' = butlast cs
            \<and> acc' = (alns @ [last lns], arns @ [last rns], aks @ [last ks])"
        using char v0 v1 by (simp add: Let_def)
      thus ?thesis using lenb ivA by (auto simp: dyadic_interval_vec_invar_def)
    next
      case v1: False
      show ?thesis
      proof (cases "newton_pol_gate (length (last qtodo) - 1) (last es) (last ks) (last ss)")
        case gF: False
        obtain cl cr where e: "dyadic_interval_vec_triples todo'
                = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)
                    @ [((last lns + last lns, last lns + last rns), last ks + 1),
                       ((last lns + last rns, last rns + last rns), last ks + 1)]"
              "qtodo' = butlast qtodo @ [carried_left (last qtodo), carried_right (last qtodo)]"
              "es' = butlast es @ [max 1 (last es - 1), max 1 (last es - 1)]"
              "ss' = butlast ss @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                                   newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]"
              "cs' = butlast cs @ [cl, cr]"
              "acc' = (if newton_mid_is_root (last qtodo)
                        then (alns @ [last lns + last rns], arns @ [last lns + last rns],
                              aks @ [last ks + 1])
                        else (alns, arns, aks))"
          using char v0 v1 gF by (simp add: Let_def, blast del: iffI)
        thus ?thesis using lenb ivA
          by (auto simp: dyadic_interval_vec_invar_def split: if_splits)
      next
        case gT: True
        show ?thesis
        proof (cases "newton_window_pick_bail (carried_descartes_count (last qtodo)) (last es) (last qtodo)")
          case None
          obtain cl cr where "dyadic_interval_vec_triples todo'
                  = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)
                      @ [((last lns + last lns, last lns + last rns), last ks + 1),
                         ((last lns + last rns, last rns + last rns), last ks + 1)]"
                "qtodo' = butlast qtodo @ [carried_left (last qtodo), carried_right (last qtodo)]"
                "es' = butlast es @ [max 1 (last es - 1), max 1 (last es - 1)]"
                "ss' = butlast ss @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                                     newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]"
                "cs' = butlast cs @ [cl, cr]"
                "acc' = (if newton_mid_is_root (last qtodo)
                          then (alns @ [last lns + last rns], arns @ [last lns + last rns],
                                aks @ [last ks + 1])
                          else (alns, arns, aks))"
            using char v0 v1 gT None by (simp add: Let_def, blast del: iffI)
          thus ?thesis using lenb ivA
            by (auto simp: dyadic_interval_vec_invar_def split: if_splits)
        next
          case (Some mc)
          obtain m cand where mc: "mc = (m, cand)" by (cases mc)
          obtain l' r' k' where dwc: "newton_window_child (last lns) (last rns) (last ks) (last es) m
                                    = (l', r', k')"
            by (cases "newton_window_child (last lns) (last rns) (last ks) (last es) m") auto
          have "dyadic_interval_vec_triples todo'
                  = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) @ [((l', r'), k')]
                \<and> qtodo' = butlast qtodo @ [cand] \<and> es' = butlast es @ [last es + 1]
                \<and> ss' = butlast ss @ [last ss] \<and> cs' = butlast cs @ [carried_descartes_count (last qtodo) + 2]
                \<and> acc' = (alns, arns, aks)"
            using char v0 v1 gT Some mc dwc by (simp add: Let_def)
          thus ?thesis using lenb ivA by simp
        qed
      qed
    qed
  qed
  obtain tlns trns tks where todo'_eq: "todo' = (tlns, trns, tks)" by (cases todo')
  have siv': "newton_loop_state_invar ?st'"
    using vt' lenqe
    by (simp add: newton_loop_state_invar_def todo'_eq
        dyadic_interval_vec_triples_length[OF vt'[unfolded todo'_eq]])
  have safe': "newton_loop_safe_invar ?st'"
    by (rule blr_imp_safe_invar_bl[OF \<delta>_pos siv' ndinv' szbud' accbud' kpot' plen' P_len P_bound])
  \<comment> \<open>W1: the cs-invariant is preserved (obligation 2) — the butlast prefix is inherited from
     @{term csinv0}; split children get @{const dyadic_iv_cs_invar} from @{term char}'s truncated-classify
     \<open>split_sc\<close>; the window child from @{thm newton_window_pick_bail_count} (\<open>count = v\<close>, cache \<open>v + 2\<close>).\<close>
  have cse: "cs \<noteq> []" using ne lcs by (cases cs) auto
  have lbc: "length (butlast cs) = length (butlast qtodo)" using lenbl lenblc by simp
  have cs_inherit: "\<forall>i < length (butlast cs).
      dyadic_iv_cs_invar (butlast cs ! i) (carried_descartes_count (butlast qtodo ! i))"
  proof (intro allI impI)
    fix i assume i: "i < length (butlast cs)"
    have i': "i < length cs" using less_le_trans[OF i[unfolded length_butlast] diff_le_self] .
    show "dyadic_iv_cs_invar (butlast cs ! i) (carried_descartes_count (butlast qtodo ! i))"
      using csinv0[rule_format, OF i'] i i[unfolded lbc] by (simp add: nth_butlast)
  qed
  have cs_step: "\<And>scs sqt. length scs = length sqt \<Longrightarrow>
      (\<forall>j < length scs. dyadic_iv_cs_invar (scs ! j) (carried_descartes_count (sqt ! j))) \<Longrightarrow>
      (\<forall>i < length (butlast cs @ scs).
         dyadic_iv_cs_invar ((butlast cs @ scs) ! i)
           (carried_descartes_count ((butlast qtodo @ sqt) ! i)))"
  proof (intro allI impI)
    fix scs sqt i
    assume ls: "length scs = length sqt"
       and suf: "\<forall>j < length scs. dyadic_iv_cs_invar (scs ! j) (carried_descartes_count (sqt ! j))"
       and i: "i < length (butlast cs @ scs)"
    show "dyadic_iv_cs_invar ((butlast cs @ scs) ! i) (carried_descartes_count ((butlast qtodo @ sqt) ! i))"
    proof (cases "i < length (butlast cs)")
      case True
      thus ?thesis using cs_inherit[rule_format, OF True] True lbc by (simp add: nth_append)
    next
      case False
      hence j: "i - length (butlast cs) < length scs" using i by (simp add: length_append)
      show ?thesis using suf[rule_format, OF j] False lbc ls by (simp add: nth_append)
    qed
  qed
  have csinv': "\<forall>i < length cs'. dyadic_iv_cs_invar (cs' ! i) (carried_descartes_count (qtodo' ! i))"
  proof (cases "carried_descartes_count (last qtodo) = 0")
    case v0: True
    have "qtodo' = butlast qtodo \<and> cs' = butlast cs" using char v0 by (simp add: Let_def)
    thus ?thesis using cs_step[of "[]" "[]"] by simp
  next
    case v0: False
    show ?thesis
    proof (cases "carried_descartes_count (last qtodo) = 1")
      case v1: True
      have "qtodo' = butlast qtodo \<and> cs' = butlast cs" using char v0 v1 by (simp add: Let_def)
      thus ?thesis using cs_step[of "[]" "[]"] by simp
    next
      case v1: False
      show ?thesis
      proof (cases "newton_pol_gate (length (last qtodo) - 1) (last es) (last ks) (last ss)")
        case gF: False
        from char v0 v1 gF have exfull:
          "\<exists>cl cr. ss' = butlast ss @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                                       newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]
                \<and> cs' = butlast cs @ [cl, cr]
                \<and> (cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)
                \<and> (cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)
                \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))
                \<and> (cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)
                \<and> (cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)
                \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))
                \<and> cl \<le> 3 \<and> cr \<le> 3"
          by (simp add: Let_def)
        have qte: "qtodo' = butlast qtodo @ [carried_left (last qtodo), carried_right (last qtodo)]"
          using char v0 v1 gF by (simp add: Let_def)
        from exfull obtain cl cr where "ss' = butlast ss @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                                        newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]"
          and cs'f: "cs' = butlast cs @ [cl, cr]"
          and cl0: "(cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)"
          and cl1: "(cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)"
          and cl2: "(2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))"
          and cr0: "(cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)"
          and cr1: "(cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)"
          and cr2: "(2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))"
          and cl3: "cl \<le> 3" and cr3: "cr \<le> 3" by (elim exE conjE)
        have tri: "dyadic_iv_cs_invar cl (carried_descartes_count (carried_left (last qtodo)))"
          using cl0 cl1 cl2 cl3 by (rule dyadic_iv_cs_invar_from_classify_bl)
        have tri2: "dyadic_iv_cs_invar cr (carried_descartes_count (carried_right (last qtodo)))"
          using cr0 cr1 cr2 cr3 by (rule dyadic_iv_cs_invar_from_classify_bl)
        have "\<forall>j < length [cl, cr]. dyadic_iv_cs_invar ([cl, cr] ! j)
                (carried_descartes_count ([carried_left (last qtodo), carried_right (last qtodo)] ! j))"
          using tri tri2 by (auto simp: nth_Cons split: nat.splits)
        thus ?thesis
          using cs_step[of "[cl, cr]" "[carried_left (last qtodo), carried_right (last qtodo)]"]
            cs'f qte by simp
      next
        case gT: True
        show ?thesis
        proof (cases "newton_window_pick_bail (carried_descartes_count (last qtodo)) (last es) (last qtodo)")
          case None
          from char v0 v1 gT None have exfull:
            "\<exists>cl cr. ss' = butlast ss @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                                         newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]
                  \<and> cs' = butlast cs @ [cl, cr]
                  \<and> (cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)
                  \<and> (cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)
                  \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))
                  \<and> (cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)
                  \<and> (cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)
                  \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))
                  \<and> cl \<le> 3 \<and> cr \<le> 3"
            by (simp add: Let_def)
          have qte: "qtodo' = butlast qtodo @ [carried_left (last qtodo), carried_right (last qtodo)]"
            using char v0 v1 gT None by (simp add: Let_def)
          from exfull obtain cl cr where "ss' = butlast ss @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                                          newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]"
            and cs'f: "cs' = butlast cs @ [cl, cr]"
            and cl0: "(cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)"
            and cl1: "(cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)"
            and cl2: "(2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))"
            and cr0: "(cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)"
            and cr1: "(cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)"
            and cr2: "(2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))"
            and cl3: "cl \<le> 3" and cr3: "cr \<le> 3" by (elim exE conjE)
          have tri: "dyadic_iv_cs_invar cl (carried_descartes_count (carried_left (last qtodo)))"
            using cl0 cl1 cl2 cl3 by (rule dyadic_iv_cs_invar_from_classify_bl)
          have tri2: "dyadic_iv_cs_invar cr (carried_descartes_count (carried_right (last qtodo)))"
            using cr0 cr1 cr2 cr3 by (rule dyadic_iv_cs_invar_from_classify_bl)
          have "\<forall>j < length [cl, cr]. dyadic_iv_cs_invar ([cl, cr] ! j)
                  (carried_descartes_count ([carried_left (last qtodo), carried_right (last qtodo)] ! j))"
            using tri tri2 by (auto simp: nth_Cons split: nat.splits)
          thus ?thesis
            using cs_step[of "[cl, cr]" "[carried_left (last qtodo), carried_right (last qtodo)]"]
              cs'f qte by simp
        next
          case (Some mc)
          obtain m cand where mc: "mc = (m, cand)" by (cases mc)
          have vge: "2 \<le> carried_descartes_count (last qtodo)" using v0 v1 by simp
          have cc: "carried_descartes_count cand = carried_descartes_count (last qtodo)"
            using newton_window_pick_bail_count[OF Some[unfolded mc]] .
          obtain l' r' k' where dwc: "newton_window_child (last lns) (last rns) (last ks) (last es) m
                                    = (l', r', k')"
            by (cases "newton_window_child (last lns) (last rns) (last ks) (last es) m") auto
          have e: "cs' = butlast cs @ [carried_descartes_count (last qtodo) + 2]
                 \<and> qtodo' = butlast qtodo @ [cand]"
            using char v0 v1 gT Some mc dwc by (simp add: Let_def)
          have "\<forall>j < length [carried_descartes_count (last qtodo) + 2].
                  dyadic_iv_cs_invar ([carried_descartes_count (last qtodo) + 2] ! j)
                    (carried_descartes_count ([cand] ! j))"
            using vge cc by (auto simp: dyadic_iv_cs_invar_def)
          thus ?thesis
            using cs_step[of "[carried_descartes_count (last qtodo) + 2]" "[cand]"] e by simp
        qed
      qed
    qed
  qed
  have invar': "blr_refine_invar \<delta> P l0 r0 k0 st0 ?st'"
    unfolding blr_refine_invar_def newton_todo_ivs_def
    using safe' ndinv' main' szbud' accbud' kpot' plen' sbound' csinv'
    by (simp add: newton_todo_ivs_def)
  \<comment> \<open>the \<open>\<mu>\<close>-mset measure strictly decreases\<close>
  have meas: "dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo ?st'))
       < dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo ?st))"
    using newton_gmp_step_bail_mu_decreases[OF \<delta>_pos len small_fast l0r0 stA ndinv_a]
    by (simp add: at_eq fcl)
  show ?thesis using invar' alpha meas by blast
qed

text \<open>The WHILEIT body step rule: under @{const blr_refine_invar} and the loop condition, the concrete
  @{const bail_loop_step_monadic} refines a pure @{const newton_gmp_step_bail} that preserves the
  invariant and strictly decreases the \<open>\<mu>\<close>-mset. Refines the three pops
  (@{thm dyadic_interval_vec_pop_last_monadic_spec}, @{const poly_vec_pop_last_monadic},
  @{thm dyadic_exp_pop_last_monadic_spec}) and @{thm blr_after_pop_refine_bl}, discharging the nine
  ASSERTs from the \<open>safe_invar\<close> cond-part, then weakens via @{thm blr_step_result_invar_bl}.\<close>
lemma blr_step_refine_bl:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and l0r0: "l0 < r0"
    and inv: "blr_refine_invar \<delta> P l0 r0 k0 st0 st"
    and cond: "newton_loop_cond st"
    and P_bound: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "bail_loop_step_monadic st \<le> SPEC (\<lambda>st'.
      blr_refine_invar \<delta> P l0 r0 k0 st0 st' \<and>
      blr_alpha st' = newton_gmp_step_bail (blr_alpha st) \<and>
      dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st'))
        < dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st)))"
proof -
  obtain lns rns ks qtodo es ss cs alns arns aks
    where st: "st = (((lns, rns, ks), qtodo, es, ss, cs), (alns, arns, aks))" by (cases st) auto
  from inv have safe: "newton_loop_safe_invar st" by (simp add: blr_refine_invar_def)
  from safe have si: "newton_loop_state_invar st"
    by (simp add: newton_loop_safe_invar_def)
  from si have ivT: "dyadic_interval_vec_invar (lns, rns, ks)" and ivA: "dyadic_interval_vec_invar (alns, arns, aks)"
    and lq: "length qtodo = length lns" and le: "length es = length lns"
    and lss: "length ss = length lns" and lcs: "length cs = length lns"
    by (auto simp: st newton_loop_state_invar_def Let_def)
  have ne: "lns \<noteq> []" using cond by (simp add: st newton_loop_cond_def Let_def)
  \<comment> \<open>the thirteen safe-invariant preconditions (from @{term safe} + @{term cond})\<close>
  from safe cond have
    push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)" and
    pushA: "dyadic_interval_vec_pushable (alns, arns, aks)" and
    qne: "qtodo \<noteq> []" and ene: "es \<noteq> []" and sne: "ss \<noteq> []" and cne: "cs \<noteq> []" and
    q0: "0 < length (last qtodo)" and
    q1: "length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len)" and
    lastk: "last ks + 1 < max_snat LENGTH(gmp_poly_len)" and
    blq: "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)" and
    ble: "length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len)" and
    bls: "length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len)" and
    blc: "length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len)"
    by (auto simp: newton_loop_safe_invar_def st newton_loop_cond_def Let_def)
  have iv_bl: "dyadic_interval_vec_invar (butlast lns, butlast rns, butlast ks)"
    using ivT by (auto simp: dyadic_interval_vec_invar_def)
  have Atne: "blr_alpha_todo st \<noteq> []" using blr_alpha_cond_bl[OF si] cond by simp
  have lastA_in: "last (blr_alpha_todo st) \<in> set (blr_alpha_todo st)" using Atne by simp
  have lastA: "last (blr_alpha_todo st)
             = (((last lns, last rns), last ks), last es, last ss, last qtodo)"
    using blr_alpha_todo_last_bl[OF si[unfolded st] ne] by (simp add: st)
  have q1': "length (last qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
  proof -
    from inv have plen: "\<forall>nd \<in> set (blr_alpha_todo st). length (snd (snd (snd nd))) = length P"
      by (simp add: blr_refine_invar_def)
    have "length (last qtodo) = length P" using plen[rule_format, OF lastA_in] lastA by simp
    thus ?thesis using P_bound by simp
  qed
  \<comment> \<open>W1: the popped run-length \<open>s = last ss \<le> last ks\<close> (@{const blr_refine_invar}'s \<open>s \<le> k\<close>
     conjunct), so \<open>s + 1 \<le> last ks + 1 < max_snat\<close> (the \<open>\<sigma>+1\<close> store bound); and the popped
     cached \<open>c = last cs\<close> aligns with @{term "carried_descartes_count (last qtodo)"} (cs-invariant).\<close>
  have sb: "last ss + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    from inv have "\<forall>nd \<in> set (blr_alpha_todo st). fst (snd (snd nd)) \<le> snd (fst nd)"
      by (simp add: blr_refine_invar_def)
    from this[rule_format, OF lastA_in] have "last ss \<le> last ks" using lastA by simp
    thus ?thesis using lastk by simp
  qed
  have csinv_last: "dyadic_iv_cs_invar (last cs) (carried_descartes_count (last qtodo))"
  proof -
    from inv have "\<forall>i < length cs. dyadic_iv_cs_invar (cs ! i) (carried_descartes_count (qtodo ! i))"
      by (simp add: st blr_refine_invar_def)
    moreover have "length cs - 1 < length cs" using cne by (cases cs) auto
    ultimately have "dyadic_iv_cs_invar (cs ! (length cs - 1))
        (carried_descartes_count (qtodo ! (length cs - 1)))" by blast
    thus ?thesis using cne qne lcs lq by (simp add: last_conv_nth)
  qed
  have poppoly: "poly_vec_pop_last_monadic qtodo \<le> RETURN (last qtodo, butlast qtodo)"
    using qne unfolding poly_vec_pop_last_monadic_def by refine_vcg auto
  \<comment> \<open>the concrete step meets the after-pop characterisation (W1 strong \<open>split_sc\<close> = dyadic_iv_cs_invar)\<close>
  have args: "bail_loop_step_monadic st \<le> SPEC (\<lambda>((todo', qtodo', es', ss', cs'), acc').
      dyadic_interval_vec_invar todo' \<and>
      (let v = carried_descartes_count (last qtodo);
           base_t = dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks);
           split_t = base_t @ [((last lns + last lns, last lns + last rns), last ks + 1),
                               ((last lns + last rns, last rns + last rns), last ks + 1)];
           split_q = butlast qtodo @ [carried_left (last qtodo), carried_right (last qtodo)];
           split_es = butlast es @ [max 1 (last es - 1), max 1 (last es - 1)];
           split_acc = (if newton_mid_is_root (last qtodo)
                        then (alns @ [last lns + last rns], arns @ [last lns + last rns],
                              aks @ [last ks + 1])
                        else (alns, arns, aks));
           split_sc = (\<lambda>ss'' cs''. \<exists>cl cr.
                ss'' = butlast ss
                  @ [newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss),
                     newton_split_run_len (newton_mid_is_root (last qtodo)) cl cr (last ss)]
                \<and> cs'' = butlast cs @ [cl, cr]
                \<and> (cl = 0) = (carried_descartes_count (carried_left (last qtodo)) = 0)
                \<and> (cl = 1) = (carried_descartes_count (carried_left (last qtodo)) = 1)
                \<and> (2 \<le> cl) = (2 \<le> carried_descartes_count (carried_left (last qtodo)))
                \<and> (cr = 0) = (carried_descartes_count (carried_right (last qtodo)) = 0)
                \<and> (cr = 1) = (carried_descartes_count (carried_right (last qtodo)) = 1)
                \<and> (2 \<le> cr) = (2 \<le> carried_descartes_count (carried_right (last qtodo)))
                \<and> cl \<le> 3 \<and> cr \<le> 3)
       in
       if v = 0 then dyadic_interval_vec_triples todo' = base_t \<and> qtodo' = butlast qtodo
                     \<and> es' = butlast es \<and> ss' = butlast ss \<and> cs' = butlast cs
                     \<and> acc' = (alns, arns, aks)
       else if v = 1 then dyadic_interval_vec_triples todo' = base_t \<and> qtodo' = butlast qtodo
                          \<and> es' = butlast es \<and> ss' = butlast ss \<and> cs' = butlast cs
                          \<and> acc' = (alns @ [last lns], arns @ [last rns], aks @ [last ks])
       else if \<not> newton_pol_gate (length (last qtodo) - 1) (last es) (last ks) (last ss)
            then dyadic_interval_vec_triples todo' = split_t \<and> qtodo' = split_q
                 \<and> es' = split_es \<and> acc' = split_acc \<and> split_sc ss' cs'
       else (case newton_window_pick_bail v (last es) (last qtodo) of
               Some (m, cand) \<Rightarrow>
                 (let (l', r', k') = newton_window_child (last lns) (last rns) (last ks) (last es) m in
                  dyadic_interval_vec_triples todo' = base_t @ [((l', r'), k')]
                  \<and> qtodo' = butlast qtodo @ [cand] \<and> es' = butlast es @ [last es + 1]
                  \<and> ss' = butlast ss @ [last ss] \<and> cs' = butlast cs @ [v + 2]
                  \<and> acc' = (alns, arns, aks) \<and> cand = newton_wcand (last es) m (last qtodo))
             | None \<Rightarrow> dyadic_interval_vec_triples todo' = split_t \<and> qtodo' = split_q
                        \<and> es' = split_es \<and> acc' = split_acc \<and> split_sc ss' cs')))"
    unfolding st bail_loop_step_monadic_def PR_CONST_def prod.case
    apply (refine_vcg
        dyadic_interval_vec_pop_last_monadic_spec[OF ivT ne, THEN order_trans]
        poppoly[THEN order_trans]
        dyadic_exp_pop_last_monadic_spec[OF ene, THEN order_trans]
        dyadic_exp_pop_last_monadic_spec[OF sne, THEN order_trans]
        dyadic_exp_pop_last_monadic_spec[OF cne, THEN order_trans]
        blr_after_pop_refine_bl[THEN order_trans])
    subgoal using qne by simp
    subgoal using ene by simp
    subgoal using sne by simp
    subgoal using cne by simp
    subgoal using q0 by auto
    subgoal using q1 by auto
    subgoal using lastk by auto
    subgoal using push2 by auto
    subgoal using pushA by auto
    subgoal using blq by auto
    subgoal using ble by auto
    subgoal using bls by auto
    subgoal using blc by auto
    subgoal
      apply (clarsimp simp only: prod.inject)
      apply (rule order_trans[OF blr_after_pop_refine_bl[OF iv_bl push2 lastk q0 q1 q1'
              blq ble bls blc sb pushA csinv_last]])
      by (auto simp: pw_le_iff refine_pw_simps Let_def split: option.splits)
    done
  \<comment> \<open>weaken the characterisation to the invariant + measure via @{thm blr_step_result_invar_bl}\<close>
  show ?thesis
    unfolding st
  proof (rule SPEC_cons_rule[OF args[unfolded st]], goal_cases)
    case (1 r)
    obtain todo' qtodo' es' ss' cs' acc' where r: "r = ((todo', qtodo', es', ss', cs'), acc')"
      by (cases r) auto
    note P = "1"[unfolded r prod.case]
    show ?case
      unfolding r
      using blr_step_result_invar_bl[OF \<delta>_pos len small_fast l0r0 inv[unfolded st] ne len P_bound
              conjunct1[OF P] conjunct2[OF P]]
      by simp
  qed
qed

subsection \<open>Assembly: the abstract Newton loop (a WHILET with free invariant)\<close>

text \<open>The abstract Newton loop iterates @{const newton_gmp_step_bail} until the todo drains. A @{const WHILET}
  (no baked-in invariant), so @{thm WHILET_rule} takes the full invariant freely — computing
  @{const newton_gmp_main_bail} unobstructed by the concrete @{const newton_loop_safe_invar}
  annotation. Clone of ET \<open>bilr_loop_abs\<close>.\<close>
definition blr_loop_abs :: "newton_gmp_state \<Rightarrow> newton_gmp_state nres" where
"blr_loop_abs st0 \<equiv> WHILET (\<lambda>st. fst st \<noteq> []) (\<lambda>st. RETURN (newton_gmp_step_bail st)) st0"

lemma blr_abs_mu_mset_rel_wf_bl:
  "wf {(st' :: newton_gmp_state, st).
      dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st')) <
      dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st))}"
proof -
  have wf_ms_pred: "wfp ((<) :: nat multiset \<Rightarrow> nat multiset \<Rightarrow> bool)" by simp
  have wf_ms: "wf ({(x, y). x < y} :: (nat multiset \<times> nat multiset) set)"
    using wf_ms_pred by (simp add: wfp_def)
  show ?thesis
    using wf_inv_image[OF wf_ms,
      of "\<lambda>st. dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st))"]
    by (simp add: inv_image_def)
qed

lemma blr_mu_mset_rel_wf_bl:
  "wf {(st' :: newton_loop_state, st).
      dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st')) <
      dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st))}"
proof -
  have wf_ms_pred: "wfp ((<) :: nat multiset \<Rightarrow> nat multiset \<Rightarrow> bool)" by simp
  have wf_ms: "wf ({(x, y). x < y} :: (nat multiset \<times> nat multiset) set)"
    using wf_ms_pred by (simp add: wfp_def)
  show ?thesis
    using wf_inv_image[OF wf_ms,
      of "\<lambda>st. dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (blr_alpha_todo st))"]
    by (simp add: inv_image_def)
qed

text \<open>The body VC: one @{const newton_gmp_step_bail} preserves the driver-fixpoint + node-inv and
  decreases the \<open>\<mu>\<close>-mset.\<close>
lemma blr_loop_abs_body_bl:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and l0r0: "l0 < r0"
    and inv: "newton_gmp_main_bail st = newton_gmp_main_bail st0
              \<and> (\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd)"
    and ne: "fst st \<noteq> []"
  shows "RETURN (newton_gmp_step_bail st) \<le> SPEC (\<lambda>st'.
      (newton_gmp_main_bail st' = newton_gmp_main_bail st0
        \<and> (\<forall>nd \<in> set (fst st'). newton_gmp_node_inv P l0 r0 k0 nd)) \<and>
      (st', st) \<in> {(st', st).
        dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st')) <
        dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st))})"
proof -
  from inv have main_eq: "newton_gmp_main_bail st = newton_gmp_main_bail st0"
    and ninv: "\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd" by auto
  have step_main: "newton_gmp_main_bail (newton_gmp_step_bail st) = newton_gmp_main_bail st0"
  proof -
    obtain x xs where "fst st = x # xs" using ne by (cases "fst st") auto
    hence "newton_gmp_main_bail st = newton_gmp_main_bail (newton_gmp_step_bail st)"
      by (cases st) (simp add: newton_gmp_main_bail.simps)
    thus ?thesis using main_eq by simp
  qed
  have step_ninv: "\<forall>nd \<in> set (fst (newton_gmp_step_bail st)). newton_gmp_node_inv P l0 r0 k0 nd"
    by (rule newton_gmp_node_inv_preserved_bl[OF len l0r0 ninv])
  have step_meas: "dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst (newton_gmp_step_bail st)))
      < dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st))"
    by (rule newton_gmp_step_bail_mu_decreases[OF \<delta>_pos len small_fast l0r0 ne ninv])
  show ?thesis using step_main step_ninv step_meas by simp
qed

lemma blr_loop_abs_exit_bl:
  assumes inv: "newton_gmp_main_bail st = newton_gmp_main_bail st0
                \<and> (\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd)"
    and empty: "\<not> (fst st \<noteq> [])"
  shows "fst st = [] \<and> snd st = snd (newton_gmp_main_bail st0)"
proof -
  from inv have main_eq: "newton_gmp_main_bail st = newton_gmp_main_bail st0" by simp
  obtain a b where st: "st = (a, b)" by (cases st)
  have e: "a = []" using empty by (simp add: st)
  have "newton_gmp_main_bail st = st" by (simp add: st e newton_gmp_main_bail_Nil)
  hence seq: "st = newton_gmp_main_bail st0" using main_eq by simp
  have "fst st = []" using e st by simp
  moreover have "snd st = snd (newton_gmp_main_bail st0)" using seq by simp
  ultimately show ?thesis by blast
qed

lemma blr_loop_abs_spec_bl:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and l0r0: "l0 < r0"
    and ninv0: "\<forall>nd \<in> set (fst st0). newton_gmp_node_inv P l0 r0 k0 nd"
  shows "blr_loop_abs st0 \<le> SPEC (\<lambda>st. fst st = [] \<and> snd st = snd (newton_gmp_main_bail st0))"
  unfolding blr_loop_abs_def
  apply (rule WHILET_rule[
    where I="\<lambda>st. newton_gmp_main_bail st = newton_gmp_main_bail st0
                  \<and> (\<forall>nd \<in> set (fst st). newton_gmp_node_inv P l0 r0 k0 nd)"
      and R="{(st', st).
        dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st')) <
        dyadic_iv_todo_mu_mset \<delta> (newton_todo_ivs l0 r0 k0 (fst st))}"])
  subgoal by (rule blr_abs_mu_mset_rel_wf_bl)
  subgoal using ninv0 by simp
  subgoal by (rule blr_loop_abs_body_bl[OF \<delta>_pos len small_fast l0r0]; assumption)
  subgoal by (rule blr_loop_abs_exit_bl; assumption)
  done

subsection \<open>Assembly: the data refinement \<open>concrete loop \<le> \<Down>(br \<alpha>) abstract loop\<close>\<close>

lemma blr_loop_monadic_unfold_bl:
  "bail_loop_monadic todo qtodo es ss cs acc
     = WHILEIT newton_loop_safe_invar newton_loop_cond
         bail_loop_body_checked_monadic ((todo, qtodo, es, ss, cs), acc)"
  unfolding bail_loop_monadic_def PR_CONST_def by simp

text \<open>The concrete WHILEIT (annotated with the weak \<open>safe_invar\<close>) data-refines @{const blr_loop_abs}
  under @{term "br blr_alpha (blr_refine_invar \<delta> P l0 r0 k0 st0)"}. Clone of ET \<open>bilr_loop_stateful_dref\<close>.\<close>
lemma blr_loop_dref_bl:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and l0r0: "l0 < r0"
    and init: "blr_refine_invar \<delta> P l0 r0 k0 st0 ((todo, qtodo, es, ss, cs), acc)"
    and P_bound: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "bail_loop_monadic todo qtodo es ss cs acc
       \<le> \<Down>(br blr_alpha (blr_refine_invar \<delta> P l0 r0 k0 st0))
           (blr_loop_abs (blr_alpha ((todo, qtodo, es, ss, cs), acc)))"
  unfolding blr_loop_monadic_unfold_bl blr_loop_abs_def WHILET_def
  apply (rule WHILEIT_refine[where R="br blr_alpha (blr_refine_invar \<delta> P l0 r0 k0 st0)"])
  subgoal \<comment> \<open>seed related\<close>
    using init by (simp add: in_br_conv)
  subgoal \<comment> \<open>concrete annotation from the abstract invariant\<close>
    by (auto simp: in_br_conv blr_refine_invar_def)
  subgoal for s s' \<comment> \<open>conditions agree\<close>
  proof -
    assume R: "(s, s') \<in> br blr_alpha (blr_refine_invar \<delta> P l0 r0 k0 st0)"
    from R have sa: "s' = blr_alpha s" and inv_s: "blr_refine_invar \<delta> P l0 r0 k0 st0 s"
      by (auto simp: in_br_conv)
    from inv_s have si: "newton_loop_state_invar s"
      by (simp add: blr_refine_invar_def newton_loop_safe_invar_def)
    show "newton_loop_cond s = (fst s' \<noteq> [])"
      using blr_alpha_cond_bl[OF si] by (simp add: sa blr_alpha_def)
  qed
  subgoal for s s' \<comment> \<open>body refines\<close>
  proof -
    assume R: "(s, s') \<in> br blr_alpha (blr_refine_invar \<delta> P l0 r0 k0 st0)"
      and bs: "newton_loop_cond s"
    from R have sa: "s' = blr_alpha s" and inv_s: "blr_refine_invar \<delta> P l0 r0 k0 st0 s"
      by (auto simp: in_br_conv)
    have bc: "bail_loop_body_checked_monadic s = bail_loop_step_monadic s"
      using bs by (simp add: bail_loop_body_checked_monadic_def PR_CONST_def)
    have "bail_loop_step_monadic s \<le> SPEC (\<lambda>c.
        newton_gmp_step_bail (blr_alpha s) = blr_alpha c \<and> blr_refine_invar \<delta> P l0 r0 k0 st0 c)"
      using blr_step_refine_bl[OF \<delta>_pos len small_fast l0r0 inv_s bs P_bound]
      by (auto simp: pw_le_iff refine_pw_simps)
    thus "bail_loop_body_checked_monadic s
        \<le> \<Down>(br blr_alpha (blr_refine_invar \<delta> P l0 r0 k0 st0)) (RETURN (newton_gmp_step_bail s'))"
      unfolding bc sa by (simp add: conc_fun_RETURN in_br_conv)
  qed
  done

text \<open>Composing the data refinement with the abstract loop spec: the concrete loop terminates with the
  invariant holding, the abstract todo drained, and the projected acc = the pure driver's final acc.\<close>
lemma blr_loop_spec_bl:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and l0r0: "l0 < r0"
    and init: "blr_refine_invar \<delta> P l0 r0 k0 st0 ((todo, qtodo, es, ss, cs), acc)"
    and P_bound: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "bail_loop_monadic todo qtodo es ss cs acc \<le> SPEC (\<lambda>c.
      blr_refine_invar \<delta> P l0 r0 k0 st0 c \<and> blr_alpha_todo c = []
      \<and> blr_alpha_acc c = snd (newton_gmp_main_bail (blr_alpha ((todo, qtodo, es, ss, cs), acc))))"
proof -
  let ?s0 = "((todo, qtodo, es, ss, cs), acc)"
  have ninv0: "\<forall>nd \<in> set (fst (blr_alpha ?s0)). newton_gmp_node_inv P l0 r0 k0 nd"
    using init by (auto simp: blr_refine_invar_def blr_alpha_def)
  have "bail_loop_monadic todo qtodo es ss cs acc
      \<le> \<Down>(br blr_alpha (blr_refine_invar \<delta> P l0 r0 k0 st0)) (blr_loop_abs (blr_alpha ?s0))"
    by (rule blr_loop_dref_bl[OF \<delta>_pos len small_fast l0r0 init P_bound])
  also have "\<dots> \<le> \<Down>(br blr_alpha (blr_refine_invar \<delta> P l0 r0 k0 st0))
      (SPEC (\<lambda>st. fst st = [] \<and> snd st = snd (newton_gmp_main_bail (blr_alpha ?s0))))"
    by (rule monoD[OF conc_fun_mono]) (rule blr_loop_abs_spec_bl[OF \<delta>_pos len small_fast l0r0 ninv0])
  also have "\<dots> \<le> SPEC (\<lambda>c. blr_refine_invar \<delta> P l0 r0 k0 st0 c \<and> blr_alpha_todo c = []
      \<and> blr_alpha_acc c = snd (newton_gmp_main_bail (blr_alpha ?s0)))"
    by (auto simp: pw_le_iff refine_pw_simps in_br_conv blr_alpha_def)
  finally show ?thesis .
qed

subsection \<open>Assembly: the seed satisfies the refinement invariant\<close>

text \<open>The main-list seed \<open>((([l_num],[r_num],[k]), [P], [e0]), ([],[],[]))\<close> projects to the pure driver
  seed \<open>([(((l_num,r_num),k), e0, P)], [])\<close> and satisfies @{const blr_refine_invar} with \<open>st0\<close> its own
  projection. Node-inv = the identity @{const carried_repr_scalar} on \<open>[0,1]\<close> (\<open>node01\<close>); the snat
  budgets reduce to the ET-shaped \<open>cap\<close> on \<open>2^(\<mu>+1)\<close>; the \<open>k\<close>-potential and NewDsc item budget are
  the Newton-specific seed cap \<open>kcap\<close> (an explicit precondition, exactly as the
  rational-newton route carries its \<open>item_budget_safe\<close>).\<close>
lemma blr_seed_invar_bl:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and lr: "l_num < r_num"
    and len: "0 < length P"
    and lenb: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
    and cap: "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
              < int (max_snat LENGTH(gmp_poly_len))"
    and kcap: "int k + int (2 ^ newton_pol_ecap + 2)
                 * (int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) - 2)
               < int (max_snat LENGTH(gmp_poly_len))"
    and csinv0: "dyadic_iv_cs_invar c0 (carried_descartes_count P)"
  shows "blr_refine_invar \<delta> P l_num r_num k
           (blr_alpha (((([l_num], [r_num], [k]), [P], [e0], [0], [c0]), ([], [], []))
              :: newton_loop_state))
           ((([l_num], [r_num], [k]), [P], [e0], [0], [c0]), ([], [], []))"
proof -
  let ?s0 = "((([l_num], [r_num], [k]), [P], [e0], [0], [c0]), ([], [], [])) :: newton_loop_state"
  have at0: "blr_alpha_todo ?s0 = [(((l_num, r_num), k), e0, 0, P)]"
    by (simp add: blr_alpha_todo_def dyadic_interval_vec_triples_simps)
  have aa0: "blr_alpha_acc ?s0 = []"
    by (simp add: blr_alpha_acc_def dyadic_interval_vec_triples_simps)
  have node01: "dyadic_iv_node_iv l_num r_num k l_num r_num k = (0, 1)"
  proof -
    have "dyadic_rat l_num k < dyadic_rat r_num k"
      using lr by (simp add: dyadic_rat_def divide_strict_right_mono)
    hence "dyadic_rat r_num k - dyadic_rat l_num k \<noteq> 0" by simp
    thus ?thesis by (simp add: dyadic_iv_node_iv_def Let_def)
  qed
  have niv0: "newton_node_iv_of l_num r_num k (((l_num, r_num), k), e0, 0, P) = (0, 1)"
    by (simp add: newton_node_iv_of_def dyadic_iv_node_iv_of_def node01)
  have seedrepr: "carried_repr_scalar P 0 1 P"
    unfolding carried_repr_scalar_def
    by (rule exI[of _ 1]) (simp add: local_poly_rat_def smult_list_def rev_map)
  have ndinv: "\<forall>nd \<in> set (blr_alpha_todo ?s0). newton_gmp_node_inv P l_num r_num k nd"
    by (simp add: at0 newton_gmp_node_inv_def newton_node_iv_of_def dyadic_iv_node_iv_of_def
                  Let_def node01 seedrepr)
  have tivs0: "map (newton_node_iv_of l_num r_num k) (blr_alpha_todo ?s0) = [(0, 1)]"
    by (simp add: at0 niv0)
  have si: "newton_loop_state_invar ?s0"
    by (simp add: newton_loop_state_invar_def dyadic_interval_vec_invar_def Let_def)
  have szbud: "int (length (blr_alpha_todo ?s0))
      + dyadic_iv_todo_append_budget \<delta> (newton_todo_ivs l_num r_num k (blr_alpha_todo ?s0)) + 2
      < int (max_snat LENGTH(gmp_poly_len))"
    using cap by (simp add: at0 niv0 newton_todo_ivs_def dyadic_iv_todo_append_budget_def dyadic_iv_interval_todo_budget_def)
  have accbud: "int (length (blr_alpha_acc ?s0))
      + dyadic_iv_todo_acc_budget \<delta> (newton_todo_ivs l_num r_num k (blr_alpha_todo ?s0)) + 1
      < int (max_snat LENGTH(gmp_poly_len))"
    using cap by (simp add: aa0 at0 niv0 newton_todo_ivs_def dyadic_iv_todo_acc_budget_def dyadic_iv_interval_acc_budget_def)
  have kpot: "\<forall>nd \<in> set (blr_alpha_todo ?s0).
      int (snd (fst nd)) + int (2 ^ newton_pol_ecap + 2)
        * dyadic_iv_interval_todo_budget \<delta> (newton_node_iv_of l_num r_num k nd)
      < int (max_snat LENGTH(gmp_poly_len))"
    using kcap by (simp add: at0 niv0 dyadic_iv_interval_todo_budget_def)
  have plen: "\<forall>nd \<in> set (blr_alpha_todo ?s0). length (snd (snd (snd nd))) = length P"
    by (simp add: at0)
  have sbound: "\<forall>nd \<in> set (blr_alpha_todo ?s0). fst (snd (snd nd)) \<le> snd (fst nd)"
    by (simp add: at0)
  have safe: "newton_loop_safe_invar ?s0"
    by (rule blr_imp_safe_invar_bl[OF \<delta>_pos si ndinv szbud accbud kpot plen len lenb])
  \<comment> \<open>W1: the single seed \<open>cs\<close> entry \<open>c0\<close> matches @{term "carried_descartes_count P"} (the seed poly)\<close>
  have csinv: "\<forall>i < length [c0]. dyadic_iv_cs_invar ([c0] ! i) (carried_descartes_count ([P] ! i))"
    using csinv0 by (simp add: nth_Cons split: nat.splits)
  show ?thesis
    unfolding blr_refine_invar_def
    using safe ndinv szbud accbud kpot plen sbound csinv
    by (simp add: blr_alpha_def newton_todo_ivs_def)
qed

text \<open>Exit fact for the main-list's \<open>ASSERT (qtodo = [])\<close>: an empty abstract todo forces the poly
  stack empty (the state invariant keeps all columns in length lockstep).\<close>
lemma blr_exit_qtodo_empty_bl:
  assumes si: "newton_loop_state_invar c"
    and empty: "blr_alpha_todo c = []"
  shows "fst (snd (fst c)) = []"
proof -
  obtain lns rns ks qtodo es ss cs acc where c: "c = (((lns, rns, ks), qtodo, es, ss, cs), acc)"
    by (cases c) auto
  from si have lq: "length qtodo = length lns" and le: "length es = length lns"
    and lss: "length ss = length lns"
    and llr: "length lns = length rns" and llk: "length lns = length ks"
    by (auto simp: c newton_loop_state_invar_def Let_def
        dyadic_interval_vec_invar_def)
  have lt: "length (dyadic_interval_vec_triples (lns, rns, ks)) = length (zip es (zip ss qtodo))"
    using lq le lss llr llk by (simp add: dyadic_interval_vec_triples_simps length_zip)
  have "zip (dyadic_interval_vec_triples (lns, rns, ks)) (zip es (zip ss qtodo)) = []"
    using empty by (simp add: c blr_alpha_todo_def)
  hence "dyadic_interval_vec_triples (lns, rns, ks) = [] \<or> zip es (zip ss qtodo) = []"
    by (simp add: zip_eq_Nil_iff)
  hence lz: "length (zip es (zip ss qtodo)) = 0" using lt by auto
  hence "length qtodo = 0" using lq le lss by (simp add: length_zip)
  thus ?thesis by (simp add: c)
qed

text \<open>The seeded loop drains and leaves an acc projecting to exactly the abstract NewDsc multiset: the
  composition of @{thm blr_seed_invar_bl}, @{thm blr_loop_spec_bl}, and the capstone
  @{thm newton_gmp_main_bail_seed_mset}.\<close>
lemma blr_loop_seed_correct_bl:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len2: "Suc 0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and sf: "square_free (map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
    and lenb: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
    and lr: "l_num < r_num"
    and cap: "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
              < int (max_snat LENGTH(gmp_poly_len))"
    and kcap: "int k + int (2 ^ newton_pol_ecap + 2)
                 * (int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) - 2)
               < int (max_snat LENGTH(gmp_poly_len))"
    and csinv0: "dyadic_iv_cs_invar c0 (carried_descartes_count P)"
  shows "bail_loop_monadic ([l_num], [r_num], [k]) [P] [e0] [0] [c0] ([], [], [])
       \<le> SPEC (\<lambda>c. newton_loop_safe_invar c \<and> blr_alpha_todo c = []
              \<and> mset (dyadic_iv_acc_ivs l_num r_num k (blr_alpha_acc c))
                = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P)))"
proof -
  let ?s0 = "((([l_num], [r_num], [k]), [P], [e0], [0], [c0]), ([], [], [])) :: newton_loop_state"
  have len: "0 < length P" using len2 by simp
  have aseed: "blr_alpha ?s0 = ([(((l_num, r_num), k), e0, 0, P)], [])"
    by (simp add: blr_alpha_def blr_alpha_todo_def blr_alpha_acc_def
        dyadic_interval_vec_triples_simps)
  have inv0: "blr_refine_invar \<delta> P l_num r_num k (blr_alpha ?s0) ?s0"
    by (rule blr_seed_invar_bl[OF \<delta>_pos lr len lenb cap kcap csinv0])
  have loop: "bail_loop_monadic ([l_num], [r_num], [k]) [P] [e0] [0] [c0] ([], [], [])
      \<le> SPEC (\<lambda>c. blr_refine_invar \<delta> P l_num r_num k (blr_alpha ?s0) c \<and> blr_alpha_todo c = []
      \<and> blr_alpha_acc c = snd (newton_gmp_main_bail (blr_alpha ?s0)))"
    by (rule blr_loop_spec_bl[OF \<delta>_pos len small_fast lr inv0 lenb])
  have l8: "mset (dyadic_iv_acc_ivs l_num r_num k (snd (newton_gmp_main_bail (blr_alpha ?s0))))
          = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))"
    using newton_gmp_main_bail_seed_mset[OF \<delta>_pos len2 small_fast sf P0 canon lr]
    by (simp add: aseed)
  have w: "SPEC (\<lambda>c. blr_refine_invar \<delta> P l_num r_num k (blr_alpha ?s0) c \<and> blr_alpha_todo c = []
              \<and> blr_alpha_acc c = snd (newton_gmp_main_bail (blr_alpha ?s0)))
        \<le> SPEC (\<lambda>c. newton_loop_safe_invar c \<and> blr_alpha_todo c = []
              \<and> mset (dyadic_iv_acc_ivs l_num r_num k (blr_alpha_acc c))
                = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P)))"
    using l8 by (auto simp: pw_le_iff refine_pw_simps blr_refine_invar_def)
  show ?thesis using order_trans[OF loop w] .
qed


section \<open>THE KEYSTONE (proof under construction)\<close>

text \<open>Stated; proof built bottom-up above/below across the pure model / tree-preservation
  / \<open>\<mu>\<close>-decrease / WHILEIT-refinement layers. Preconditions mirror
  \<open>bisection_main_list_spec\<close>'s.\<close>

lemma bail_main_list_correct:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and len2: "Suc 0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and sf: "square_free (map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
    and lenb: "length P + 2 < max_snat LENGTH(gmp_poly_len)"
    and lr: "l_num < r_num"
    and cap: "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
              < int (max_snat LENGTH(gmp_poly_len))"
    and kcap: "int k + int (2 ^ newton_pol_ecap + 2)
                 * (int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) - 2)
               < int (max_snat LENGTH(gmp_poly_len))"
  shows "bail_main_list_monadic e0 l_num r_num k P \<le> SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      mset (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
        = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P)))"
proof -
  have len: "0 < length P" using len2 by simp
  have Pne: "P \<noteq> []" using len by auto
  \<comment> \<open>W1: the seed facts are parameterised over the cached seed classify \<open>cc\<close> that the impl computes
     (\<open>carried_descartes_count_trunc_monadic P\<close>); a witness \<open>min 2 (count P)\<close> discharges the
     \<open>cc\<close>-independent \<open>k\<close>-bound.\<close>
  have cs_wit: "dyadic_iv_cs_invar (min 2 (carried_descartes_count P)) (carried_descartes_count P)"
    by (auto simp: dyadic_iv_cs_invar_def)
  have seed_safe: "\<And>cc. dyadic_iv_cs_invar cc (carried_descartes_count P) \<Longrightarrow>
      newton_loop_safe_invar
        (((([l_num], [r_num], [k]), [P], [e0], [0], [cc]), ([], [], [])) :: newton_loop_state)"
    using blr_seed_invar_bl[OF \<delta>_pos lr len lenb cap kcap] by (simp add: blr_refine_invar_def)
  have seedC: "\<And>cc. dyadic_iv_cs_invar cc (carried_descartes_count P) \<Longrightarrow>
      bail_loop_monadic ([l_num], [r_num], [k]) [P] [e0] [0] [cc] ([], [], [])
      \<le> SPEC (\<lambda>c. newton_loop_safe_invar c \<and> blr_alpha_todo c = []
             \<and> mset (dyadic_iv_acc_ivs l_num r_num k (blr_alpha_acc c))
               = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P)))"
    by (rule blr_loop_seed_correct_bl[OF \<delta>_pos len2 small_fast sf P0 canon lenb lr cap kcap])
  have phi: "\<And>cc c. dyadic_iv_cs_invar cc (carried_descartes_count P) \<Longrightarrow>
      inres (bail_loop_monadic ([l_num], [r_num], [k]) [P] [e0] [0] [cc] ([], [], [])) c \<Longrightarrow>
      newton_loop_safe_invar c \<and> blr_alpha_todo c = []
      \<and> mset (dyadic_iv_acc_ivs l_num r_num k (blr_alpha_acc c))
        = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))"
    using seedC by (auto simp: pw_le_iff refine_pw_simps)
  have free_d: "\<And>v. dyadic_interval_vec_free_monadic v \<le> SPEC (\<lambda>_. True)"
    unfolding dyadic_interval_vec_free_monadic_def PR_CONST_def
    by (refine_vcg) (auto simp: pw_le_iff refine_pw_simps mop_free_def)
  have free_d_nofail: "\<And>v. nofail (dyadic_interval_vec_free_monadic v)"
    using free_d by (auto simp: pw_le_iff refine_pw_simps)
  have loop_nofail: "\<And>cc. dyadic_iv_cs_invar cc (carried_descartes_count P) \<Longrightarrow>
      nofail (bail_loop_monadic ([l_num], [r_num], [k]) [P] [e0] [0] [cc] ([], [], []))"
    using seedC by (auto simp: pw_le_iff refine_pw_simps)
  have max1: "Suc 0 < max_snat LENGTH(gmp_poly_len)" using len lenb by linarith
  have kb: "Suc k < max_snat LENGTH(gmp_poly_len)"
    using seed_safe[OF cs_wit]
    by (simp add: newton_loop_safe_invar_def newton_loop_cond_def)
  have max2: "Suc (Suc 0) < max_snat LENGTH(gmp_poly_len)" using lenb len2 by linarith
  have lenP1: "Suc (length P) < max_snat LENGTH(gmp_poly_len)" using lenb by linarith
  have pb2: "dyadic_interval_vec_pushable2 ([], [], [] :: nat list)"
    using max2 by (simp add: dyadic_interval_vec_pushable2_def)
  \<comment> \<open>the implementation's cached seed classification \<open>cc\<close> satisfies @{const dyadic_iv_cs_invar}\<close>
  have lenP1': "length P + 1 < max_snat LENGTH(gmp_poly_len)" using lenb by linarith
  have ccl: "carried_descartes_count_trunc_monadic P
      \<le> SPEC (\<lambda>cc. dyadic_iv_cs_invar cc (carried_descartes_count P))"
    apply (rule order_trans[OF carried_descartes_count_trunc_monadic_classify_le3[OF lenP1']])
    by (auto simp: pw_le_iff refine_pw_simps dyadic_iv_cs_invar_def)
  \<comment> \<open>the impl's trunc op is nofail and each result is a valid cached classify, so the loop/seed
     facts transfer through @{term "inres (carried_descartes_count_trunc_monadic P)"}\<close>
  have ccl_nofail: "nofail (carried_descartes_count_trunc_monadic P)"
    using ccl by (auto simp: pw_le_iff refine_pw_simps)
  have ccl_inres: "\<And>x. inres (carried_descartes_count_trunc_monadic P) x
      \<Longrightarrow> dyadic_iv_cs_invar x (carried_descartes_count P)"
    using ccl by (auto simp: pw_le_iff refine_pw_simps)
  have seed_safe': "\<And>x. inres (carried_descartes_count_trunc_monadic P) x \<Longrightarrow>
      newton_loop_safe_invar
        (((([l_num], [r_num], [k]), [P], [e0], [0], [x]), ([], [], [])) :: newton_loop_state)"
    using seed_safe ccl_inres by blast
  have loop_nofail': "\<And>x. inres (carried_descartes_count_trunc_monadic P) x \<Longrightarrow>
      nofail (bail_loop_monadic ([l_num], [r_num], [k]) [P] [e0] [0] [x] ([], [], []))"
    using loop_nofail ccl_inres by blast
  have phi': "\<And>x c. inres (carried_descartes_count_trunc_monadic P) x \<Longrightarrow>
      inres (bail_loop_monadic ([l_num], [r_num], [k]) [P] [e0] [0] [x] ([], [], [])) c \<Longrightarrow>
      newton_loop_safe_invar c \<and> blr_alpha_todo c = []
      \<and> mset (dyadic_iv_acc_ivs l_num r_num k (blr_alpha_acc c))
        = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))"
    using phi ccl_inres by blast
  \<comment> \<open>the trunc+loop composite: the cached-classify prefix followed by the loop, bounded cleanly
     (the loop stays \<open>\<le> SPEC\<close> via @{thm seedC}, so \<open>c0\<close>'s classify is not lost to \<open>pw\<close>)\<close>
  have tl: "carried_descartes_count_trunc_monadic P \<bind>
      (\<lambda>c0. bail_loop_monadic ([l_num], [r_num], [k]) [P] [e0] [0] [c0] ([], [], []))
      \<le> SPEC (\<lambda>c. newton_loop_safe_invar c \<and> blr_alpha_todo c = []
             \<and> mset (dyadic_iv_acc_ivs l_num r_num k (blr_alpha_acc c))
               = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P)))"
    using ccl seedC by (auto simp: pw_le_iff refine_pw_simps)
  show ?thesis
    unfolding bail_main_list_monadic_def PR_CONST_def COPY_def
      dyadic_interval_vec_empty_sz_monadic_def poly_empty_sz_monadic_def
      poly_push_coeff_monadic_def poly_vec_empty_sz_monadic_def poly_vec_push_monadic_def
      poly_vec_free_empty_monadic_def mop_list_append_def
    apply (refine_vcg free_d)
    apply (simp_all add: dyadic_interval_vec_pushable_def
        newton_loop_safe_invar_def newton_loop_state_invar_def
        dyadic_interval_vec_invar_def dyadic_interval_vec_triples_simps zip_eq_Nil_iff length_zip
        seed_safe max1 max2 kb lenP1 pb2 len Pne Let_def)
    \<comment> \<open>the surviving core \<open>trunc \<bind> (\<lambda>c0. loop \<bind> post)\<close>: bound the trunc (introduces
       \<open>dyadic_iv_cs_invar c0\<close>), then the loop by @{thm seedC}; the post-loop \<open>ASSERT (qtodo = [])\<close> is
       @{thm blr_exit_qtodo_empty_bl}\<close>
    apply (all \<open>(refine_vcg free_d seedC)?\<close>)
    apply (all \<open>(rule SPEC_cons_rule[OF ccl])?\<close>)
    apply (all \<open>(refine_vcg free_d seedC)?\<close>)
    apply (all \<open>(auto dest: blr_exit_qtodo_empty_bl
        simp: newton_loop_safe_invar_def newton_loop_state_invar_def
              blr_alpha_acc_def blr_alpha_todo_def dyadic_interval_vec_triples_simps
              dyadic_interval_vec_invar_def zip_eq_Nil_iff length_zip)?\<close>)
    apply (all \<open>(use kb lenP1 lenb max2 Pne in \<open>simp add: max_snat_def\<close>)?\<close>)
    done
qed

text \<open>\<^bold>\<open>Termination\<close> — immediate from the keystone's \<open>\<le> SPEC\<close> (\<open>nofail\<close>).\<close>
lemma bail_main_list_terminates:
  fixes \<delta> :: real
  assumes "\<delta> > 0" "Suc 0 < length P"
    and "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and "square_free (map_poly of_int (Poly P) :: real poly)"
    and "Poly P \<noteq> 0" and "coeffs (Poly P) = P"
    and "length P + 2 < max_snat LENGTH(gmp_poly_len)"
    and "l_num < r_num"
    and "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
         < int (max_snat LENGTH(gmp_poly_len))"
    and "int k + int (2 ^ newton_pol_ecap + 2)
           * (int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) - 2)
         < int (max_snat LENGTH(gmp_poly_len))"
  shows "nofail (bail_main_list_monadic e0 l_num r_num k P)"
  using bail_main_list_correct[OF assms]
  by (auto simp: pw_le_iff refine_pw_simps)

text \<open>The \<open>pol_final\<close>-specialised soundness/completeness of @{const newdsc_pol_bail} — the bail
  analogs of @{thm [source] newdsc_pol_pol_final_sound}/@{thm [source] newdsc_pol_pol_final_complete}
  (Newton.thy). Discharge @{const newdsc_pol_bail}'s general sound/complete
  (@{thm [source] newdsc_pol_bail_sound}/@{thm [source] newdsc_pol_bail_complete}, Bail_Spec)
  at the concrete policy via @{thm [source] newdsc_pol_bail_pol_final_dom}. The completeness twin
  keeps the general lemma's \<open>\<And>x. root \<Longrightarrow> a<x \<Longrightarrow> x<b \<Longrightarrow> \<dots>\<close> shape (unlike the bisection clone,
  which packages the root as an assumption).\<close>
theorem newdsc_pol_bail_pol_final_sound:
  fixes P :: "int poly"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "\<forall>I \<in> set (newdsc_pol_bail pol_final_real (degree P) a b e dk s (map_poly of_int P)).
           dsc_pair_ok (map_poly of_int P) I"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  show ?thesis
    by (rule newdsc_pol_bail_sound[OF newdsc_pol_bail_pol_final_dom[OF P0 p0 sf ab] dle dne ab])
qed

theorem newdsc_pol_bail_pol_final_complete:
  fixes P :: "int poly"
  assumes P0: "P \<noteq> 0" and p0: "degree P \<noteq> 0"
    and sf: "square_free (map_poly of_int P :: real poly)" and ab: "a < b"
  shows "\<And>x. poly (map_poly of_int P :: real poly) x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol_bail pol_final_real (degree P) a b e dk s (map_poly of_int P)).
              fst I \<le> x \<and> x \<le> snd I)"
proof -
  have dne: "(map_poly of_int P :: real poly) \<noteq> 0" using P0 by simp
  have dle: "degree (map_poly of_int P :: real poly) \<le> degree P" by simp
  show "\<And>x. poly (map_poly of_int P :: real poly) x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol_bail pol_final_real (degree P) a b e dk s (map_poly of_int P)).
              fst I \<le> x \<and> x \<le> snd I)"
    by (rule newdsc_pol_bail_complete[OF newdsc_pol_bail_pol_final_dom[OF P0 p0 sf ab] dle dne])
qed

subsection \<open>FCOMP: the carried-Newton LLVM impl satisfies the \<open>newdsc_pol_bail_int\<close> spec\<close>

text \<open>The abstract spec for the Newton driver: the returned dyadic vector's @{const dyadic_iv_acc_ivs}
  interpretation is exactly the multiset @{const newdsc_pol_bail_int} at the concrete policy
  @{const pol_final} produces on \<open>[0,1]\<close>. Mirrors the bisection route's \<open>bilr_dsc_int_spec\<close>.\<close>
definition blr_newdsc_int_spec ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"blr_newdsc_int_spec e0 l_num r_num k P \<equiv>
  SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
    mset (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
      = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P)))"

text \<open>The precondition bundle, parameterised by the subdivision granularity \<open>\<delta>\<close>: exactly the
  keystone's hypotheses, plus the two \<open>snat\<close>-capacity facts the impl's own HNR wants
  (\<open>0 < length P\<close> and \<open>k + 1 < max_snat\<close> — the latter is NOT implied by \<open>kcap\<close> when the initial
  \<open>\<mu>\<close> is 0, so it is stated).\<close>
definition blr_newdsc_int_pre ::
  "real \<Rightarrow> ((((nat \<times> int) \<times> int) \<times> nat) \<times> gmp_poly) \<Rightarrow> bool" where
"blr_newdsc_int_pre \<delta> x \<longleftrightarrow>
  (case x of ((((e0, l_num), r_num), k), P) \<Rightarrow>
    \<delta> > 0 \<and>
    Suc 0 < length P \<and>
    (\<forall>a b. a < b \<longrightarrow> of_rat b - of_rat a \<le> \<delta> \<longrightarrow> descartes_list_int a b P \<le> 1) \<and>
    square_free (map_poly of_int (Poly P) :: real poly) \<and>
    Poly P \<noteq> 0 \<and> coeffs (Poly P) = P \<and>
    length P + 2 < max_snat LENGTH(gmp_poly_len) \<and>
    k + 1 < max_snat LENGTH(gmp_poly_len) \<and>
    l_num < r_num \<and>
    int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len)) \<and>
    int k + int (2 ^ newton_pol_ecap + 2)
      * (int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) - 2) < int (max_snat LENGTH(gmp_poly_len)))"

text \<open>The functional refinement (the \<open>Id\<close>-fref \<open>FCOMP\<close> composes), straight from the keystone.\<close>
lemma blr_newdsc_int_refine_bl:
  "(uncurry4 bail_main_list_monadic, uncurry4 blr_newdsc_int_spec)
   \<in> [blr_newdsc_int_pre \<delta>]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI)
  unfolding blr_newdsc_int_pre_def blr_newdsc_int_spec_def
  apply clarsimp
  apply (rule bail_main_list_correct)
             apply auto
  done

text \<open>\<^bold>\<open>The capstone HNR theorem\<close>:
  @{const bail_main_list_impl} — borrowing the \<open>mpz_t\<close> endpoints, owning the pushed
  polynomial — refines the abstract @{const newdsc_pol_bail_int} multiset spec. \<open>FCOMP\<close> of the impl's
  \<open>.refine\<close> with @{thm blr_newdsc_int_refine_bl}, then @{thm hfref_weaken_pre} to shed Sepref's
  normalized length precondition.\<close>
theorem blr_main_list_impl_refine_newdsc_int_bl:
  "(uncurry4 bail_main_list_impl, uncurry4 blr_newdsc_int_spec)
   \<in> [blr_newdsc_int_pre \<delta>]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
proof -
  have h:
    "(uncurry4 bail_main_list_impl, uncurry4 blr_newdsc_int_spec)
     \<in> [\<lambda>((((e0, l_num), r_num), k), P).
          blr_newdsc_int_pre \<delta> ((((e0, l_num), r_num), k), P) \<and>
          0 < length P \<and>
          length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
          k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
        \<rightarrow> gmp_dyadic_interval_vec_assn"
    using bail_main_list_impl.refine[FCOMP blr_newdsc_int_refine_bl[where \<delta>=\<delta>]]
    by (simp add: PR_CONST_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF _ h])
    apply (clarsimp simp: blr_newdsc_int_pre_def)
    done
qed

subsection \<open>Soundness + completeness of the carried-Newton LLVM impl\<close>

text \<open>The bridge @{thm [source] newdsc_pol_bail_int_eq_newdsc_pol_bail} carries the impl's
  \<open>newdsc_pol_bail_int pol_final\<close> result over to the real-level @{const newdsc_pol_bail}\<open> pol_final_real\<close>
  list, where the for-all-policy theorems (instantiated at \<open>pol_final\<close> in
  @{thm [source] newdsc_pol_bail_pol_final_sound} / @{thm [source] newdsc_pol_bail_pol_final_complete})
  apply directly. Only the SET image is needed, so the bridge's \<open>rev\<close> is irrelevant.\<close>
lemma blr_newdsc_int_set_image_bl:
  fixes \<delta> :: real
  assumes pre: "blr_newdsc_int_pre \<delta> ((((e0, l_num), r_num), k), P)"
  shows "set (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))
       = real_to_rat_pair ` set (newdsc_pol_bail pol_final_real (degree (Poly P))
             (of_rat 0) (of_rat 1) e0 k 0 (map_poly of_int (Poly P)))"
proof -
  have P0: "Poly P \<noteq> 0" using pre by (simp add: blr_newdsc_int_pre_def)
  have sf: "square_free (map_poly of_int (Poly P) :: real poly)"
    using pre by (simp add: blr_newdsc_int_pre_def)
  have canon: "coeffs (Poly P) = P" using pre by (simp add: blr_newdsc_int_pre_def)
  have len2: "Suc 0 < length P" using pre by (simp add: blr_newdsc_int_pre_def)
  have dg: "degree (Poly P) \<noteq> 0"
    using canon len2 by (simp add: degree_eq_length_coeffs)
  have abr: "(of_rat (0::rat) :: real) < of_rat (1::rat)" by simp
  have ab: "(0::rat) < 1" by simp
  have dom: "newdsc_pol_bail_dom (pol_final_real, degree (Poly P),
      of_rat (0::rat), of_rat (1::rat), e0, k, 0, map_poly of_int (Poly P))"
    by (rule newdsc_pol_bail_pol_final_dom[OF P0 dg sf abr])
  have "rev (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))
      = map real_to_rat_pair (newdsc_pol_bail pol_final_real (degree (Poly P))
          (of_rat 0) (of_rat 1) e0 k 0 (map_poly of_int (Poly P)))"
    by (rule newdsc_pol_bail_int_eq_newdsc_pol_bail[OF dom refl P0 ab]) (rule pol_final_real_rel)
  hence "set (rev (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P)))
       = set (map real_to_rat_pair (newdsc_pol_bail pol_final_real (degree (Poly P))
             (of_rat 0) (of_rat 1) e0 k 0 (map_poly of_int (Poly P))))" by simp
  thus ?thesis by simp
qed

text \<open>The combined sound+complete spec, as a standalone \<open>SPEC\<close> so it can be \<open>FCOMP\<close>-composed
  through to the impl. Mirrors the ET route's \<open>bilr_dsc_sound_complete_spec\<close>.\<close>
definition blr_newdsc_sound_complete_spec ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"blr_newdsc_sound_complete_spec e0 l_num r_num k P \<equiv>
  (let P_real = (map_poly of_int (Poly P) :: real poly);
       ns = newdsc_pol_bail pol_final_real (degree (Poly P)) (of_rat 0) (of_rat 1) e0 k 0 P_real
   in SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      (\<forall>R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
        \<exists>J \<in> set ns. R = real_to_rat_pair J \<and> dsc_pair_ok P_real J) \<and>
      (\<forall>x. poly P_real x = 0 \<longrightarrow> of_rat 0 < x \<longrightarrow> x < of_rat 1 \<longrightarrow>
        (\<exists>R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
          \<exists>J \<in> set ns. R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))))"

text \<open>The exact-multiset spec implies the sound+complete spec (one \<open>set_mset_mset\<close> bridge, then
  @{thm [source] blr_newdsc_int_set_image_bl} and the for-all-policy soundness and completeness).\<close>
lemma blr_newdsc_int_spec_sound_complete_bl:
  fixes \<delta> :: real
  assumes pre: "blr_newdsc_int_pre \<delta> ((((e0, l_num), r_num), k), P)"
  shows "blr_newdsc_int_spec e0 l_num r_num k P
       \<le> blr_newdsc_sound_complete_spec e0 l_num r_num k P"
proof -
  let ?P_real = "map_poly of_int (Poly P) :: real poly"
  let ?ns = "newdsc_pol_bail pol_final_real (degree (Poly P)) (of_rat 0) (of_rat 1) e0 k 0 ?P_real"
  have P0: "Poly P \<noteq> 0" using pre by (simp add: blr_newdsc_int_pre_def)
  have sf: "square_free ?P_real" using pre by (simp add: blr_newdsc_int_pre_def)
  have canon: "coeffs (Poly P) = P" using pre by (simp add: blr_newdsc_int_pre_def)
  have len2: "Suc 0 < length P" using pre by (simp add: blr_newdsc_int_pre_def)
  have dg: "degree (Poly P) \<noteq> 0"
    using canon len2 by (simp add: degree_eq_length_coeffs)
  have abr: "(of_rat (0::rat) :: real) < of_rat (1::rat)" by simp
  have img: "set (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P)) = real_to_rat_pair ` set ?ns"
    by (rule blr_newdsc_int_set_image_bl[OF pre])
  have sound: "\<forall>J \<in> set ?ns. dsc_pair_ok ?P_real J"
    by (rule newdsc_pol_bail_pol_final_sound[OF P0 dg sf abr])
  have complete: "\<And>x. poly ?P_real x = 0 \<Longrightarrow> of_rat 0 < x \<Longrightarrow> x < of_rat 1 \<Longrightarrow>
        \<exists>J \<in> set ?ns. fst J \<le> x \<and> x \<le> snd J"
    using newdsc_pol_bail_pol_final_complete[OF P0 dg sf abr] by blast
  text \<open>Re-simplified twins of \<open>img\<close>/\<open>sound\<close>/\<open>complete\<close>: after \<open>clarsimp\<close> unfolds the spec's own
    \<open>of_rat 0\<close>/\<open>of_rat 1\<close> (from \<open>blr_newdsc_sound_complete_spec\<close>'s \<open>let ns = \<dots>\<close>) down to bare
    \<open>0\<close>/\<open>1\<close>, the ORIGINAL facts no longer match syntactically, and a single \<open>metis\<close> bridging that
    gap while also chaining \<open>imageE\<close>/\<open>imageI\<close> over two nested existentials searches for a very
    long time. Simplify the facts to the SAME normal form first so every closing step is a small,
    explicit, non-searching one.\<close>
  have img': "set (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))
            = real_to_rat_pair ` set (newdsc_pol_bail pol_final_real (degree (Poly P)) 0 1 e0 k 0
                (real_of_int_poly (Poly P)))"
    using img by (simp add: of_rat_0 of_rat_1)
  have sound': "\<forall>J \<in> set (newdsc_pol_bail pol_final_real (degree (Poly P)) 0 1 e0 k 0
                  (real_of_int_poly (Poly P))). dsc_pair_ok (real_of_int_poly (Poly P)) J"
    using sound by (simp add: of_rat_0 of_rat_1)
  have complete': "\<And>x. poly (real_of_int_poly (Poly P)) x = 0 \<Longrightarrow> 0 < x \<Longrightarrow> x < 1 \<Longrightarrow>
        \<exists>J \<in> set (newdsc_pol_bail pol_final_real (degree (Poly P)) 0 1 e0 k 0 (real_of_int_poly (Poly P))).
          fst J \<le> x \<and> x \<le> snd J"
    using complete by (simp add: of_rat_0 of_rat_1)
  show ?thesis
    unfolding blr_newdsc_int_spec_def blr_newdsc_sound_complete_spec_def Let_def
    apply (rule SPEC_rule)
    apply (clarsimp simp: refine_pw_simps)
    apply (intro conjI)
    subgoal for acc na ra
    proof (rule ballI)
      fix R
      assume inv: "dyadic_interval_vec_invar (acc, na, ra)"
      assume mseteq: "mset (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples (acc, na, ra)))
                        = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))"
      assume Rmem: "R \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples (acc, na, ra)))"
      have seteq: "set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples (acc, na, ra)))
                 = set (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))"
        using mseteq by (metis set_mset_mset)
      from Rmem seteq img' obtain J where
        Jmem: "J \<in> set (newdsc_pol_bail pol_final_real (degree (Poly P)) 0 1 e0 k 0 (real_of_int_poly (Poly P)))"
        and Req: "R = real_to_rat_pair J" by auto
      show "\<exists>J\<in>set (newdsc_pol_bail pol_final_real (degree (Poly P)) 0 1 e0 k 0 (real_of_int_poly (Poly P))).
              R = real_to_rat_pair J \<and> dsc_pair_ok (real_of_int_poly (Poly P)) J"
        using Jmem Req sound' by blast
    qed
    subgoal for acc na ra
    proof (intro allI impI)
      fix x
      assume inv: "dyadic_interval_vec_invar (acc, na, ra)"
      assume mseteq: "mset (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples (acc, na, ra)))
                        = mset (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))"
      assume root: "poly (real_of_int_poly (Poly P)) x = 0"
      assume lo: "(0::real) < x" and hi: "x < (1::real)"
      have seteq: "set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples (acc, na, ra)))
                 = set (newdsc_pol_bail_int pol_final 0 1 e0 k (Poly P))"
        using mseteq by (metis set_mset_mset)
      obtain J where
        Jmem: "J \<in> set (newdsc_pol_bail pol_final_real (degree (Poly P)) 0 1 e0 k 0 (real_of_int_poly (Poly P)))"
        and Jlo: "fst J \<le> x" and Jhi: "x \<le> snd J"
        using complete'[OF root lo hi] by blast
      have Rmem: "real_to_rat_pair J
                    \<in> set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples (acc, na, ra)))"
        using Jmem seteq img' by auto
      show "\<exists>R\<in>set (dyadic_iv_acc_ivs l_num r_num k (dyadic_interval_vec_triples (acc, na, ra))).
              \<exists>J\<in>set (newdsc_pol_bail pol_final_real (degree (Poly P)) 0 1 e0 k 0 (real_of_int_poly (Poly P))).
                R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
        using Rmem Jmem Jlo Jhi by blast
    qed
    done
qed

text \<open>The functional refinement \<open>blr_newdsc_int_spec \<le> blr_newdsc_sound_complete_spec\<close>, as the
  \<open>Id\<close>-fref \<open>FCOMP\<close> composes.\<close>
lemma blr_newdsc_sound_complete_refine_bl:
  "(uncurry4 blr_newdsc_int_spec, uncurry4 blr_newdsc_sound_complete_spec)
   \<in> [blr_newdsc_int_pre \<delta>]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI)
  apply clarsimp
  apply (rule blr_newdsc_int_spec_sound_complete_bl)
  apply assumption
  done

text \<open>\<^bold>\<open>The user-facing capstone\<close>: the exported @{const bail_main_list_impl} returns,
  under @{const blr_newdsc_int_pre}, a dyadic vector that is a SOUND and COMPLETE real-root cover
  of @{term "Poly P"} on \<open>(0,1)\<close>. \<open>FCOMP\<close> of @{thm [source] blr_main_list_impl_refine_newdsc_int_bl}
  with @{thm [source] blr_newdsc_sound_complete_refine_bl}.\<close>
theorem blr_main_list_impl_refine_newdsc_sound_complete_bl:
  "(uncurry4 bail_main_list_impl, uncurry4 blr_newdsc_sound_complete_spec)
   \<in> [blr_newdsc_int_pre \<delta>]\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
      (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
proof -
  have h:
    "(uncurry4 bail_main_list_impl, uncurry4 blr_newdsc_sound_complete_spec)
     \<in> [\<lambda>((((e0, l_num), r_num), k), P).
          blr_newdsc_int_pre \<delta> ((((e0, l_num), r_num), k), P)]\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a
        (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
        \<rightarrow> gmp_dyadic_interval_vec_assn"
    using blr_main_list_impl_refine_newdsc_int_bl[where \<delta>=\<delta>,
      FCOMP blr_newdsc_sound_complete_refine_bl[where \<delta>=\<delta>]]
    by (simp add: PR_CONST_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF _ h])
    apply clarsimp
    done
qed

end
