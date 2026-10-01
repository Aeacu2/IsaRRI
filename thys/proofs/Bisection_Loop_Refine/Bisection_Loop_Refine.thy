theory Bisection_Loop_Refine
  imports Solvers_Refine Bisection_Poly_Eval
begin

text \<open>STEP 1 of the carried-solver refinement: the concrete GMP loop
  @{const bisection_loop_monadic} (a LIFO stack over parallel dyadic-interval vectors and a
  carried-polynomial vector) returns, projected to rational intervals, exactly the affine image of
  @{term "dsc_int 0 1 (Poly P)"}. The count frame is @{text "[0,1]"} (carried via the polynomials
  @{term Q} with @{const carried_repr}); the output frame is @{text "[l_num/2^k, r_num/2^k]"}.

  Because the GMP loop is a stack (pop-last / push-children-to-tail) while the proven functional
  driver @{const carried_main} is a queue (pop-head / append-tail), we do NOT refine to
  @{const carried_main}; instead we use an order-agnostic multiset invariant, reusing the endpoint
  tree accounting @{thm rational_queue_fun_int_mset_tree}.

  Layer: NRES REFINEMENT.\<close>

subsection \<open>The affine count-frame \<open>\<leftrightarrow>\<close> output-frame map\<close>

text \<open>\<open>phi l0 r0 k0\<close> sends a count-frame @{text "[0,1]"} interval to the output frame
  \<open>[l0/2^k0, r0/2^k0]\<close>; \<open>node_iv\<close> is its inverse on a node's output triple.\<close>

definition phi :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (rat \<times> rat) \<Rightarrow> (rat \<times> rat)" where
"phi l0 r0 k0 ab =
  (let lo = dyadic_rat l0 k0; hi = dyadic_rat r0 k0 in
   (lo + fst ab * (hi - lo), lo + snd ab * (hi - lo)))"

definition node_iv :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (rat \<times> rat)" where
"node_iv l0 r0 k0 l r k =
  (let lo = dyadic_rat l0 k0; hi = dyadic_rat r0 k0 in
   ((dyadic_rat l k - lo) / (hi - lo), (dyadic_rat r k - lo) / (hi - lo)))"

definition rat_intervals_of :: "gmp_dyadic_interval_vec \<Rightarrow> (rat \<times> rat) list" where
"rat_intervals_of acc = dyadic_interval_vec_to_list acc"

text \<open>Cornerstone: \<open>phi\<close> applied to a node's count-frame interval recovers the node's output
  dyadic interval. Needs \<open>l0 < r0\<close> so the frame width is nonzero.\<close>
lemma phi_node_iv:
  assumes "l0 < r0"
  shows "phi l0 r0 k0 (node_iv l0 r0 k0 l r k)
       = (dyadic_rat l k, dyadic_rat r k)"
proof -
  have "dyadic_rat l0 k0 < dyadic_rat r0 k0"
    using assms by (simp add: dyadic_rat_def divide_strict_right_mono)
  hence den_ne: "dyadic_rat r0 k0 - dyadic_rat l0 k0 \<noteq> 0" by simp
  show ?thesis
    unfolding phi_def node_iv_def Let_def fst_conv snd_conv
    using den_ne by (simp add: field_simps)
qed

text \<open>Hence the \<open>phi\<close>-image of the count-frame projection of an accumulator vector is exactly its
  output rational-interval list. This transports the multiset identity from count to output frame.\<close>
lemma phi_image_to_list:
  assumes "l0 < r0"
  shows "map (phi l0 r0 k0)
           (map (\<lambda>((l, r), k). node_iv l0 r0 k0 l r k)
             (dyadic_interval_vec_triples acc))
       = rat_intervals_of acc"
  by (simp add: rat_intervals_of_def dyadic_interval_vec_to_list_def
      dyadic_interval_of_triple_def phi_node_iv[OF assms] o_def split_def
      cong: map_cong)

subsection \<open>The pure LIFO model of the GMP loop\<close>

text \<open>A node is an output triple @{text "((l,r),k)"} paired with its carried polynomial @{term Q};
  the pure state is a stack of nodes (the todo) and a list of accepted output triples (the acc).
  This mirrors \<open>bisection_loop_state\<close> (parallel-vectors + poly-vector) under the
  @{const dyadic_interval_vec_triples} projection.\<close>

type_synonym bisection_gmp_state =
  "((((int \<times> int) \<times> nat) \<times> gmp_poly) list) \<times> (((int \<times> int) \<times> nat) list)"

text \<open>The carried midpoint-root test the GMP body computes: the carried polynomial vanishes at the
  count-frame midpoint, i.e.\ @{term "Q"} evaluated at @{text "1/2"} is zero
  (= @{const bisection_mid_zero_monadic}).\<close>
definition bisection_mid_is_root :: "gmp_poly \<Rightarrow> bool" where
"bisection_mid_is_root Q \<longleftrightarrow> poly (map_poly rat_of_int (Poly Q)) (1 / 2) = 0"

text \<open>One pure loop step: pop the LAST node (LIFO), classify by the carried Descartes count, and
  discard / accept / split exactly as @{const bisection_loop_step_monadic} does. The two split
  children carry the output triples @{text "((2l,l+r),k+1)"}, @{text "((l+r,2r),k+1)"} (cf.\
  @{thm dyadic_interval_vec_push_children_monadic_spec}) with carried polys
  @{const carried_left}/@{const carried_right}; the midpoint point-interval
  @{text "((l+r,l+r),k+1)"} is appended to acc iff the carried midpoint test fires.\<close>
definition bisection_gmp_step :: "bisection_gmp_state \<Rightarrow> bisection_gmp_state" where
"bisection_gmp_step st =
  (case st of (todo, acc) \<Rightarrow>
    if todo = [] then st
    else
      (let (((l, r), k), Q) = last todo;
           todo' = butlast todo;
           v = carried_descartes_count Q
       in if v = 0 then (todo', acc)
          else if v = 1 then (todo', acc @ [((l, r), k)])
          else
            (let lc = (((l + l, l + r), k + 1), carried_left Q);
                 rc = (((l + r, r + r), k + 1), carried_right Q)
             in (todo' @ [lc, rc],
                 if bisection_mid_is_root Q
                 then acc @ [((l + r, l + r), k + 1)] else acc))))"

text \<open>The pure LIFO driver: iterate @{const bisection_gmp_step} until the stack empties.\<close>
partial_function (tailrec) carried_gmp_main ::
  "bisection_gmp_state \<Rightarrow> bisection_gmp_state" where
"carried_gmp_main st =
  (case st of (todo, acc) \<Rightarrow>
    (case todo of [] \<Rightarrow> st | _ \<Rightarrow> carried_gmp_main (bisection_gmp_step st)))"

text \<open>Count-frame projection of a stack node and of the whole todo / acc.\<close>
definition node_iv_of :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> ((int \<times> int) \<times> nat) \<Rightarrow> (rat \<times> rat)" where
"node_iv_of l0 r0 k0 t = node_iv l0 r0 k0 (fst (fst t)) (snd (fst t)) (snd t)"

text \<open>The per-node stack invariant: the carried polynomial represents the node's count-frame
  interval, which is unit-dyadic. Order-agnostic (a set/multiset predicate).\<close>
definition gmp_node_inv ::
  "gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (((int \<times> int) \<times> nat) \<times> gmp_poly) \<Rightarrow> bool" where
"gmp_node_inv P l0 r0 k0 e =
  (let iv = node_iv_of l0 r0 k0 (fst e)
   in carried_repr P (fst iv) (snd iv) (snd e) \<and> unit_dyadic iv)"

subsection \<open>Count-frame intervals of the split children are the bisection halves\<close>

text \<open>Arithmetic helpers. CRITICAL: never expose \<open>2^k\<close> to \<open>field_simps\<close> — its power simproc grinds
  for minutes on a symbolic exponent. Keep @{term "(2::rat) ^ k"} an OPAQUE atom and use only the
  distributive/cancel lemmas below (\<open>of_int_add\<close>, \<open>add_divide_distrib\<close>, \<open>divide_divide_eq_left\<close> are
  default simp; \<open>2^(k+1)\<close> is reduced once via \<open>power_add\<close>).\<close>

lemma dr_step:
  "dyadic_rat n (k + 1) = dyadic_rat n k / 2"
  by (simp add: dyadic_rat_def power_add)

lemma dr_add_same:
  "dyadic_rat (m + n) k = dyadic_rat m k + dyadic_rat n k"
  by (simp add: dyadic_rat_def add_divide_distrib)

lemma dr_double_left:
  "dyadic_rat (l + l) (k + 1) = dyadic_rat l k"
proof -
  have "dyadic_rat (l + l) (k + 1) = dyadic_rat (l + l) k / 2"
    by (rule dr_step)
  also have "\<dots> = (dyadic_rat l k + dyadic_rat l k) / 2"
    using dr_add_same[of l l k] by simp
  finally show ?thesis by (simp add: field_simps)
qed

lemma dr_double_right:
  "dyadic_rat (r + r) (k + 1) = dyadic_rat r k"
proof -
  have "dyadic_rat (r + r) (k + 1) = dyadic_rat (r + r) k / 2"
    by (rule dr_step)
  also have "\<dots> = (dyadic_rat r k + dyadic_rat r k) / 2"
    using dr_add_same[of r r k] by simp
  finally show ?thesis by (simp add: field_simps)
qed

lemma dr_sum_mid:
  "dyadic_rat (l + r) (k + 1)
     = (dyadic_rat l k + dyadic_rat r k) / 2"
proof -
  have "dyadic_rat (l + r) (k + 1) = dyadic_rat (l + r) k / 2"
    by (rule dr_step)
  also have "\<dots> = (dyadic_rat l k + dyadic_rat r k) / 2"
    by (simp only: dr_add_same)
  finally show ?thesis .
qed

text \<open>The single scalar identity behind the bisection (holds unconditionally, incl.\ \<open>D = 0\<close>);
  \<open>field_simps\<close> is used only here on four plain rationals.\<close>
lemma half_diff_div:
  fixes x y lo D :: rat
  shows "((x + y) / 2 - lo) / D = ((x - lo) / D + (y - lo) / D) / 2"
proof (cases "D = 0")
  case True thus ?thesis by simp
next
  case False thus ?thesis by (simp add: field_simps)
qed


text \<open>The output children @{text "((2l,l+r),k+1)"} and @{text "((l+r,2r),k+1)"} project, in the
  count frame, to the left and right halves of the parent's count-frame interval. No
  \<open>field_simps\<close>: only the targeted rewrites @{thm dr_double_left}/@{thm dr_sum_mid}/@{thm half_diff_div}.\<close>
lemma node_iv_bisect_left:
  "node_iv l0 r0 k0 (l + l) (l + r) (k + 1)
     = (fst (node_iv l0 r0 k0 l r k),
        (fst (node_iv l0 r0 k0 l r k) + snd (node_iv l0 r0 k0 l r k)) / 2)"
proof -
  have e1: "dyadic_rat (l + l) (k + 1) = dyadic_rat l k"
    by (rule dr_double_left)
  have e2: "dyadic_rat (l + r) (k + 1)
      = (dyadic_rat l k + dyadic_rat r k) / 2"
    by (rule dr_sum_mid)
  show ?thesis
    unfolding node_iv_def Let_def fst_conv snd_conv e1 e2
    by (simp add: half_diff_div)
qed

lemma node_iv_bisect_right:
  "node_iv l0 r0 k0 (l + r) (r + r) (k + 1)
     = ((fst (node_iv l0 r0 k0 l r k) + snd (node_iv l0 r0 k0 l r k)) / 2,
        snd (node_iv l0 r0 k0 l r k))"
proof -
  have e1: "dyadic_rat (l + r) (k + 1)
      = (dyadic_rat l k + dyadic_rat r k) / 2"
    by (rule dr_sum_mid)
  have e2: "dyadic_rat (r + r) (k + 1) = dyadic_rat r k"
    by (rule dr_double_right)
  show ?thesis
    unfolding node_iv_def Let_def fst_conv snd_conv e1 e2
    by (simp add: half_diff_div)
qed

lemma node_iv_bisect_mid:
  "node_iv l0 r0 k0 (l + r) (l + r) (k + 1)
     = ((fst (node_iv l0 r0 k0 l r k) + snd (node_iv l0 r0 k0 l r k)) / 2,
        (fst (node_iv l0 r0 k0 l r k) + snd (node_iv l0 r0 k0 l r k)) / 2)"
proof -
  have e: "dyadic_rat (l + r) (k + 1)
      = (dyadic_rat l k + dyadic_rat r k) / 2"
    by (rule dr_sum_mid)
  show ?thesis
    unfolding node_iv_def Let_def fst_conv snd_conv e
    by (simp add: half_diff_div)
qed

subsection \<open>The stack node invariant is preserved by one pure step\<close>

text \<open>Analogue of @{thm carried_step_preserves_node} for the LIFO @{const bisection_gmp_step}: the two
  split children get @{const carried_repr} from B1/B2 (@{thm carried_step_preserves_repr}) and
  @{const unit_dyadic} from the bisection lemmas, with the count-frame children supplied by
  @{thm node_iv_bisect_left}/@{thm node_iv_bisect_right}.\<close>
lemma gmp_node_inv_preserved:
  assumes lenP: "0 < length P"
    and inv: "\<forall>e \<in> set (fst st). gmp_node_inv P l0 r0 k0 e"
  shows "\<forall>e \<in> set (fst (bisection_gmp_step st)). gmp_node_inv P l0 r0 k0 e"
proof (cases "fst st = []")
  case True
  thus ?thesis by (cases st) (simp add: bisection_gmp_step_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain t Q where tQ: "last todo = (t, Q)" by (cases "last todo")
  obtain lr k where lrk: "t = (lr, k)" by (cases t)
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), Q)" using tQ lrk lr_eq by simp
  define a where "a = fst (node_iv l0 r0 k0 l r k)"
  define b where "b = snd (node_iv l0 r0 k0 l r k)"
  have inv': "\<forall>e \<in> set todo. gmp_node_inv P l0 r0 k0 e" using inv by (simp add: st)
  have last_in: "last todo \<in> set todo" using todo_ne by (rule last_in_set)
  have ninv: "gmp_node_inv P l0 r0 k0 (((l, r), k), Q)"
    using inv'[rule_format, OF last_in] last_eq by simp
  have head: "carried_repr P a b Q" "unit_dyadic (a, b)"
    using ninv by (simp_all add: gmp_node_inv_def node_iv_of_def Let_def a_def b_def)
  have ab: "a < b" using head(2) by (rule unit_dyadic_less)
  have onw: "odd (fst (quotient_of ((b - a) * of_int (snd (quotient_of a)))))"
    using head(2) by (rule unit_dyadic_odd_nw)
  have rest_inv: "\<forall>e \<in> set (butlast todo). gmp_node_inv P l0 r0 k0 e"
    using inv' by (auto dest: in_set_butlastD)
  show ?thesis
  proof (cases "carried_descartes_count Q = 0")
    case True
    thus ?thesis using rest_inv last_eq todo_ne
      by (simp add: st bisection_gmp_step_def Let_def)
  next
    case v0: False
    show ?thesis
    proof (cases "carried_descartes_count Q = 1")
      case True
      thus ?thesis using rest_inv last_eq todo_ne
        by (simp add: st bisection_gmp_step_def Let_def)
    next
      case v1: False
      have cliv: "node_iv_of l0 r0 k0 ((l + l, l + r), k + 1) = (a, (a + b) / 2)"
        unfolding node_iv_of_def fst_conv snd_conv
        using node_iv_bisect_left[of l0 r0 k0 l r k] by (simp add: a_def b_def)
      have criv: "node_iv_of l0 r0 k0 ((l + r, r + r), k + 1) = ((a + b) / 2, b)"
        unfolding node_iv_of_def fst_conv snd_conv
        using node_iv_bisect_right[of l0 r0 k0 l r k] by (simp add: a_def b_def)
      have cl: "gmp_node_inv P l0 r0 k0
          (((l + l, l + r), k + 1), carried_left Q)"
        unfolding gmp_node_inv_def Let_def fst_conv snd_conv cliv
        using carried_step_preserves_repr(1)[OF head(1) lenP ab onw]
          unit_dyadic_bisect_left[OF head(2)]
        by simp
      have cr: "gmp_node_inv P l0 r0 k0
          (((l + r, r + r), k + 1), carried_right Q)"
        unfolding gmp_node_inv_def Let_def fst_conv snd_conv criv
        using carried_step_preserves_repr(2)[OF head(1) lenP ab onw]
          unit_dyadic_bisect_right[OF head(2)]
        by simp
      have step_eq: "fst (bisection_gmp_step st)
          = butlast todo @ [(((l + l, l + r), k + 1), carried_left Q),
                            (((l + r, r + r), k + 1), carried_right Q)]"
        using v0 v1 last_eq todo_ne by (simp add: st bisection_gmp_step_def Let_def)
      show ?thesis unfolding step_eq using rest_inv cl cr by auto
    qed
  qed
qed

subsection \<open>The carried midpoint-root test equals the count-frame midpoint test on \<open>P\<close>\<close>

text \<open>The carried polynomial @{term Q} vanishes at @{text "1/2"} iff the original polynomial
  @{term P} vanishes at the count-frame midpoint @{term "(a+b)/2"}. The hard transform algebra is
  @{thm p3_rat_equiv}: since @{term "rev Q = fast_descartes_p3 a b P"} and @{const fast_descartes_p3}
  has its own internal @{const rev}, the two reversals CANCEL, giving
  @{term "map rat_of_int Q = smult_list S (scale_poly_list (b-a) (taylor_shift_list a (map rat_of_int P)))"}
  for a nonzero scalar @{term S}. The pure poly-evaluation then uses @{thm poly_scale_taylor_list_eval}
  (proven in the clean @{theory IsaRRI_Refine.Bisection_Poly_Eval} namespace, so
  applying it does not re-trigger the @{const pcompose} namespace clash that this leaf's full
  GMP/Sepref imports cause for \<open>simp\<close>-formed @{const pcompose} terms), and an @{thm arg_cong} step
  bridges @{term "a + 1/2*(b-a)"} to @{term "(a+b)/2"}.\<close>
lemma carried_mid_zero_iff_poly:
  assumes Q: "carried_repr P a b Q" and ab: "a < b" and len: "0 < length P"
  shows "bisection_mid_is_root Q
       \<longleftrightarrow> poly (map_poly rat_of_int (Poly P)) ((a + b) / 2) = 0"
proof -
  define S where "S = (rat_of_int (snd (quotient_of a))
      * rat_of_int (snd (quotient_of ((b - a) * of_int (snd (quotient_of a)))))) ^ (length P - 1)"
  have anb: "a \<noteq> b" using ab by simp
  have key: "map rat_of_int (fast_descartes_p3 a b P)
      = smult_list S (rev (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int P))))"
    using p3_rat_equiv[OF len anb]
    by (simp add: fast_descartes_p3_def Let_def case_prod_beta S_def)
  have Qrev: "Q = rev (fast_descartes_p3 a b P)"
    using Q by (metis carried_repr_def rev_rev_ident)
  have Qmap: "map rat_of_int Q
      = smult_list S (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int P)))"
  proof -
    have "map rat_of_int Q = rev (map rat_of_int (fast_descartes_p3 a b P))"
      by (simp add: Qrev rev_map)
    also have "\<dots> = rev (smult_list S
        (rev (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int P)))))"
      by (simp add: key)
    also have "\<dots> = smult_list S (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int P)))"
      by (simp add: rev_smult_list)
    finally show ?thesis .
  qed
  have pq: "map_poly rat_of_int (Poly Q)
      = Poly (smult_list S (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int P))))"
    by (simp add: Qmap flip: Poly_map_rat_of_int)
  have eval: "poly (map_poly rat_of_int (Poly Q)) (1 / 2)
      = S * poly (map_poly rat_of_int (Poly P)) (a + 1 / 2 * (b - a))"
    unfolding pq
    by (simp add: Poly_smult_list poly_scale_taylor_list_eval Poly_map_rat_of_int)
  have S_ne: "S \<noteq> 0"
  proof -
    have "0 < snd (quotient_of a)" using quotient_of_denom_pos' by blast
    moreover have "0 < snd (quotient_of ((b - a) * of_int (snd (quotient_of a))))"
      using quotient_of_denom_pos' by blast
    ultimately show ?thesis unfolding S_def by simp
  qed
  have midpt: "poly (map_poly rat_of_int (Poly P)) (a + 1 / 2 * (b - a))
      = poly (map_poly rat_of_int (Poly P)) ((a + b) / 2)"
    by (rule arg_cong[where f = "poly (map_poly rat_of_int (Poly P))"]) (simp add: field_simps)
  show ?thesis
    unfolding bisection_mid_is_root_def using eval midpt S_ne by simp
qed

subsection \<open>The order-agnostic multiset invariant of the pure LIFO driver\<close>

text \<open>Count-frame interval projections of the stack todo and of the accepted list.\<close>
definition todo_ivs :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (((int \<times> int) \<times> nat) \<times> gmp_poly) list \<Rightarrow> (rat \<times> rat) list" where
"todo_ivs l0 r0 k0 todo = map (\<lambda>nd. node_iv_of l0 r0 k0 (fst nd)) todo"

definition acc_ivs :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> ((int \<times> int) \<times> nat) list \<Rightarrow> (rat \<times> rat) list" where
"acc_ivs l0 r0 k0 acc = map (node_iv_of l0 r0 k0) acc"

lemma todo_ivs_Nil[simp]: "todo_ivs l0 r0 k0 [] = []" by (simp add: todo_ivs_def)
lemma todo_ivs_append[simp]:
  "todo_ivs l0 r0 k0 (xs @ ys) = todo_ivs l0 r0 k0 xs @ todo_ivs l0 r0 k0 ys"
  by (simp add: todo_ivs_def)
lemma acc_ivs_append[simp]:
  "acc_ivs l0 r0 k0 (xs @ ys) = acc_ivs l0 r0 k0 xs @ acc_ivs l0 r0 k0 ys"
  by (simp add: acc_ivs_def)

text \<open>Per-node bridges from @{const gmp_node_inv}: the count-frame interval is ordered (\<open>a<b\<close>),
  and the carried Descartes count equals the endpoint count on that interval (B3).\<close>
lemma gmp_node_inv_ordered:
  assumes "gmp_node_inv P l0 r0 k0 (t, Q)"
  shows "fst (node_iv_of l0 r0 k0 t) < snd (node_iv_of l0 r0 k0 t)"
proof -
  have "unit_dyadic (node_iv_of l0 r0 k0 t)" using assms by (simp add: gmp_node_inv_def Let_def)
  thus ?thesis using unit_dyadic_less by (cases "node_iv_of l0 r0 k0 t") simp
qed

lemma gmp_node_inv_count:
  assumes "gmp_node_inv P l0 r0 k0 (t, Q)"
  shows "carried_descartes_count Q
       = descartes_list_int (fst (node_iv_of l0 r0 k0 t)) (snd (node_iv_of l0 r0 k0 t)) P"
proof -
  have "carried_repr P (fst (node_iv_of l0 r0 k0 t)) (snd (node_iv_of l0 r0 k0 t)) Q"
    using assms by (simp add: gmp_node_inv_def Let_def)
  thus ?thesis by (rule carried_repr_count)
qed

text \<open>One-step preservation: the total @{term "acc + tree"} measure is preserved by one pure step.
  The step pops the last node's count-frame interval @{term "(a,b)"}; its endpoint tree contribution
  (@{const rational_tree_fun_int}) splits exactly as @{const bisection_gmp_step} routes it: to acc
  (v=1), to the two children's todo contributions (v\<ge>2), or nowhere (v=0). The midpoint point
  interval lands in acc iff @{const bisection_mid_is_root} holds, which by
  @{thm carried_mid_zero_iff_poly} is the tree's @{term "poly P ((a+b)/2) = 0"} condition. The
  argument is order-agnostic because the tree contribution is a sum over the todo.\<close>
lemma bisection_gmp_step_tree_preservation:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and ne: "fst st \<noteq> []"
    and inv: "\<forall>e \<in> set (fst st). gmp_node_inv P l0 r0 k0 e"
  shows "mset (acc_ivs l0 r0 k0 (snd (bisection_gmp_step st)))
       + rational_tree_mset_list P (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st)))
     = mset (acc_ivs l0 r0 k0 (snd st))
       + rational_tree_mset_list P (todo_ivs l0 r0 k0 (fst st))"
proof -
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with ne have todo_ne: "todo \<noteq> []" by simp
  obtain t Q where tQ: "last todo = (t, Q)" by (cases "last todo")
  obtain lr k where lrk: "t = (lr, k)" by (cases t)
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), Q)" using tQ lrk lr_eq by simp
  have inv': "\<forall>e \<in> set todo. gmp_node_inv P l0 r0 k0 e" using inv by (simp add: st)
  have ninv: "gmp_node_inv P l0 r0 k0 (((l, r), k), Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (node_iv l0 r0 k0 l r k)"
  define b where "b = snd (node_iv l0 r0 k0 l r k)"
  have ab: "a < b" using gmp_node_inv_ordered[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have headrepr: "carried_repr P a b Q"
    using ninv by (simp add: gmp_node_inv_def node_iv_of_def Let_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using gmp_node_inv_count[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have tree_dom: "rational_tree_fun_int_dom (P, a, b)"
    using rational_tree_fun_int_domI[OF \<delta>_pos small_fast] ab by blast
  have niv: "node_iv_of l0 r0 k0 ((l, r), k) = (a, b)"
    by (simp add: node_iv_of_def a_def b_def)
  have todo_split: "todo = butlast todo @ [(((l, r), k), Q)]"
    using todo_ne last_eq by (metis append_butlast_last_id)
  have tree_todo: "rational_tree_mset_list P (todo_ivs l0 r0 k0 todo)
      = rational_tree_mset_list P (todo_ivs l0 r0 k0 (butlast todo))
        + mset (rational_tree_fun_int P a b)"
    by (subst todo_split) (simp add: todo_ivs_def niv)
  let ?m = "(a + b) / 2"
  let ?accb = "mset (acc_ivs l0 r0 k0 acc)"
  let ?treeb = "rational_tree_mset_list P (todo_ivs l0 r0 k0 (butlast todo))"
  show ?thesis
  proof (cases "descartes_list_int a b P = 0")
    case v0: True
    have step: "bisection_gmp_step st = (butlast todo, acc)"
      using todo_ne last_eq count v0 by (simp add: st bisection_gmp_step_def Let_def)
    have tree_ab: "rational_tree_fun_int P a b = []"
      using tree_dom v0 by (subst rational_tree_fun_int.psimps) (simp_all add: v0)
    show ?thesis using step tree_todo tree_ab by (simp add: st)
  next
    case v0: False
    show ?thesis
    proof (cases "descartes_list_int a b P = 1")
      case v1: True
      have step: "bisection_gmp_step st = (butlast todo, acc @ [((l, r), k)])"
        using todo_ne last_eq count v0 v1 by (simp add: st bisection_gmp_step_def Let_def)
      have tree_ab: "rational_tree_fun_int P a b = [(a, b)]"
        using tree_dom v0 v1 by (subst rational_tree_fun_int.psimps) (simp_all add: v1)
      show ?thesis using step tree_todo tree_ab
        by (simp add: st acc_ivs_def node_iv_of_def a_def b_def)
    next
      case v1: False
      have isroot: "bisection_mid_is_root Q
          \<longleftrightarrow> poly (map_poly rat_of_int (Poly P)) ?m = 0"
        using carried_mid_zero_iff_poly[OF headrepr ab len] .
      have step: "bisection_gmp_step st
          = (butlast todo @ [(((l + l, l + r), k + 1), carried_left Q),
                             (((l + r, r + r), k + 1), carried_right Q)],
             if bisection_mid_is_root Q then acc @ [((l + r, l + r), k + 1)] else acc)"
        using todo_ne last_eq count v0 v1 by (simp add: st bisection_gmp_step_def Let_def)
      have nl: "node_iv_of l0 r0 k0 ((l + l, l + r), k + 1) = (a, ?m)"
        using node_iv_bisect_left[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
      have nr: "node_iv_of l0 r0 k0 ((l + r, r + r), k + 1) = (?m, b)"
        using node_iv_bisect_right[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
      have nm: "node_iv_of l0 r0 k0 ((l + r, l + r), k + 1) = (?m, ?m)"
        unfolding node_iv_of_def fst_conv snd_conv
        using node_iv_bisect_mid[of l0 r0 k0 l r k] by (simp add: a_def b_def)
      have tree_ab: "rational_tree_fun_int P a b
          = (if poly (map_poly rat_of_int (Poly P)) ?m = 0 then [(?m, ?m)] else [])
            @ rational_tree_fun_int P a ?m @ rational_tree_fun_int P ?m b"
        using tree_dom v0 v1 by (subst rational_tree_fun_int.psimps) (simp_all add: v0 v1 Let_def)
      have tivs2: "todo_ivs l0 r0 k0
          [(((l + l, l + r), k + 1), carried_left Q),
           (((l + r, r + r), k + 1), carried_right Q)]
          = [(a, ?m), (?m, b)]"
        by (simp only: todo_ivs_def list.map fst_conv nl nr)
      have tivs: "todo_ivs l0 r0 k0 (fst (bisection_gmp_step st))
          = todo_ivs l0 r0 k0 (butlast todo) @ [(a, ?m), (?m, b)]"
        unfolding step fst_conv by (simp only: todo_ivs_append tivs2)
      have tstep: "rational_tree_mset_list P (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st)))
          = ?treeb + (mset (rational_tree_fun_int P a ?m)
                      + mset (rational_tree_fun_int P ?m b))"
        unfolding tivs by simp
      have aivs2: "acc_ivs l0 r0 k0 [((l + r, l + r), k + 1)] = [(?m, ?m)]"
        by (simp only: acc_ivs_def list.map nm)
      have astep0: "acc_ivs l0 r0 k0 (snd (bisection_gmp_step st))
          = (if bisection_mid_is_root Q then acc_ivs l0 r0 k0 acc @ [(?m, ?m)] else acc_ivs l0 r0 k0 acc)"
        unfolding step snd_conv
        by (simp only: if_distrib[where f = "acc_ivs l0 r0 k0"] acc_ivs_append aivs2)
      have astep: "mset (acc_ivs l0 r0 k0 (snd (bisection_gmp_step st)))
          = ?accb + (if poly (map_poly rat_of_int (Poly P)) ?m = 0 then {# (?m, ?m) #} else {#})"
        unfolding astep0 using isroot by (simp add: mset_append)
      show ?thesis
        unfolding tstep astep
        using tree_todo tree_ab by (simp add: st mset_append ac_simps)
    qed
  qed
qed

text \<open>Measure decrease: one pure step strictly decreases the count-frame \<open>\<mu>\<close>-multiset of the stack,
  so the LIFO driver terminates. As in @{thm rational_queue_step_mu_mset_decreases}: the pop removes
  \<open>\<mu>(a,b)\<close>; for v\<ge>2 it is replaced by two strictly smaller children (@{thm mu_halve_strict}, with
  width \<open>> \<delta>\<close> forced by v\<ge>2 and @{term small_fast}); for v=0/1 it is just removed.\<close>
lemma bisection_gmp_step_mu_decreases:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and ne: "fst st \<noteq> []"
    and inv: "\<forall>e \<in> set (fst st). gmp_node_inv P l0 r0 k0 e"
  shows "rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st)))
       < rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st))"
proof -
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with ne have todo_ne: "todo \<noteq> []" by simp
  obtain t Q where tQ: "last todo = (t, Q)" by (cases "last todo")
  obtain lr k where lrk: "t = (lr, k)" by (cases t)
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), Q)" using tQ lrk lr_eq by simp
  have inv': "\<forall>e \<in> set todo. gmp_node_inv P l0 r0 k0 e" using inv by (simp add: st)
  have ninv: "gmp_node_inv P l0 r0 k0 (((l, r), k), Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (node_iv l0 r0 k0 l r k)"
  define b where "b = snd (node_iv l0 r0 k0 l r k)"
  have ab: "a < b" using gmp_node_inv_ordered[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using gmp_node_inv_count[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have niv: "node_iv_of l0 r0 k0 ((l, r), k) = (a, b)"
    by (simp add: node_iv_of_def a_def b_def)
  have todo_split: "todo = butlast todo @ [(((l, r), k), Q)]"
    using todo_ne last_eq by (metis append_butlast_last_id)
  let ?m = "(a + b) / 2"
  let ?rank = "rational_interval_mu \<delta>"
  let ?R = "mset (map (rational_interval_mu \<delta>) (todo_ivs l0 r0 k0 (butlast todo)))"
  have old: "rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st))
      = add_mset (?rank (a, b)) ?R"
    unfolding st fst_conv
    by (subst todo_split) (simp add: todo_ivs_def niv rational_todo_mu_mset_def)
  have nl: "node_iv_of l0 r0 k0 ((l + l, l + r), k + 1) = (a, ?m)"
    using node_iv_bisect_left[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
  have nr: "node_iv_of l0 r0 k0 ((l + r, r + r), k + 1) = (?m, b)"
    using node_iv_bisect_right[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
  show ?thesis
  proof (cases "descartes_list_int a b P = 0 \<or> descartes_list_int a b P = 1")
    case True
    have stf: "fst (bisection_gmp_step st) = butlast todo"
      using todo_ne last_eq True by (auto simp: st bisection_gmp_step_def Let_def count)
    have lhs: "rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st))) = ?R"
      by (simp add: stf rational_todo_mu_mset_def)
    show ?thesis unfolding lhs old
      by (simp add: subset_implies_multp less_multiset_def)
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
    have left_lt: "?rank (a, ?m) < ?rank (a, b)"
      using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def by (simp add: of_rat_add of_rat_divide)
    have right_lt: "?rank (?m, b) < ?rank (a, b)"
      using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def by (simp add: of_rat_add of_rat_divide)
    have tivs2: "todo_ivs l0 r0 k0
        [(((l + l, l + r), k + 1), carried_left Q),
         (((l + r, r + r), k + 1), carried_right Q)]
        = [(a, ?m), (?m, b)]"
      by (simp only: todo_ivs_def list.map fst_conv nl nr)
    have stf: "todo_ivs l0 r0 k0 (fst (bisection_gmp_step st))
        = todo_ivs l0 r0 k0 (butlast todo) @ [(a, ?m), (?m, b)]"
    proof -
      have "fst (bisection_gmp_step st)
          = butlast todo @ [(((l + l, l + r), k + 1), carried_left Q),
                            (((l + r, r + r), k + 1), carried_right Q)]"
        using todo_ne last_eq v0 v1 by (auto simp: st bisection_gmp_step_def Let_def count)
      thus ?thesis by (simp only: todo_ivs_append tivs2)
    qed
    have lhs: "rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st)))
        = ?R + {# ?rank (a, ?m), ?rank (?m, b) #}"
      by (simp add: stf rational_todo_mu_mset_def)
    show ?thesis unfolding lhs old
      by (rule rational_todo_mu_mset_two_smaller[OF left_lt right_lt])
  qed
qed

text \<open>The order-agnostic multiset invariant of the pure LIFO driver, by well-founded induction on the
  count-frame \<open>\<mu>\<close>-measure (decreasing by @{thm bisection_gmp_step_mu_decreases}), combining the
  one-step preservation @{thm bisection_gmp_step_tree_preservation} with
  @{thm gmp_node_inv_preserved}.\<close>
lemma carried_gmp_main_mset:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and inv: "\<forall>e \<in> set (fst st). gmp_node_inv P l0 r0 k0 e"
  shows "mset (acc_ivs l0 r0 k0 (snd (carried_gmp_main st)))
       = mset (acc_ivs l0 r0 k0 (snd st))
         + rational_tree_mset_list P (todo_ivs l0 r0 k0 (fst st))"
  using inv
proof (induction st rule: wf_induct_rule[OF wf_inv_image[OF rational_todo_mu_mset_list_rel_wf[where \<delta> = \<delta>],
    where f = "\<lambda>st. todo_ivs l0 r0 k0 (fst st)"]])
  case (1 st)
  show ?case
  proof (cases "fst st = []")
    case True
    have "carried_gmp_main st = st"
      using True by (cases st) (simp add: carried_gmp_main.simps)
    thus ?thesis using True by simp
  next
    case False
    have unfold: "carried_gmp_main st = carried_gmp_main (bisection_gmp_step st)"
    proof -
      obtain todo acc where st: "st = (todo, acc)" by (cases st)
      with False have tne: "todo \<noteq> []" by simp
      show ?thesis
        by (subst carried_gmp_main.simps) (simp add: st tne split: list.splits)
    qed
    have dec: "(bisection_gmp_step st, st)
        \<in> inv_image {(todo', todo). rational_todo_mu_mset \<delta> todo'
              < rational_todo_mu_mset \<delta> todo}
            (\<lambda>st. todo_ivs l0 r0 k0 (fst st))"
      using bisection_gmp_step_mu_decreases[OF \<delta>_pos small_fast False "1.prems"]
      by (simp add: inv_image_def)
    have step_inv: "\<forall>e \<in> set (fst (bisection_gmp_step st)). gmp_node_inv P l0 r0 k0 e"
      using gmp_node_inv_preserved[OF len "1.prems"] .
    show ?thesis
      unfolding unfold
      using "1.IH"[OF dec step_inv]
        bisection_gmp_step_tree_preservation[OF \<delta>_pos len small_fast False "1.prems"]
      by simp
  qed
qed

subsection \<open>The pure driver from the seed computes \<open>dsc_int 0 1 P\<close>\<close>

text \<open>Starting the pure carried driver from the single seed node @{term "(((l_num,r_num),k), P)"} (output
  triple, carried poly @{term P}) with empty acc, its accepted intervals, projected to the count frame,
  are exactly @{term "dsc_int 0 1 (Poly P)"} (as multisets). Instantiates @{thm carried_gmp_main_mset} at
  the seed (whose count-frame interval is @{text "(0,1)"}, with @{thm carried_repr_init} [B0] and
  @{term "unit_dyadic (0,1)"}) and chains @{thm carried_gmp_main_mset}'s tree contribution
  @{term "rational_tree_mset_list P [(0,1)]"} to @{term "dsc_int 0 1 (Poly P)"} through the endpoint
  queue (@{thm rational_queue_fun_int_mset_tree} + @{thm rational_queue_main_int_mset_dsc_int}).\<close>
lemma carried_gmp_main_seed_mset_dsc_int:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and dom: "dsc_dom (degree (Poly P), of_rat 0, of_rat 1, map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
    and lr: "l_num < r_num"
  shows "mset (acc_ivs l_num r_num k
            (snd (carried_gmp_main ([(((l_num, r_num), k), P)], []))))
       = mset (dsc_int 0 1 (Poly P))"
proof -
  have node01: "node_iv l_num r_num k l_num r_num k = (0, 1)"
  proof -
    have "dyadic_rat l_num k < dyadic_rat r_num k"
      using lr by (simp add: dyadic_rat_def divide_strict_right_mono)
    hence "dyadic_rat r_num k - dyadic_rat l_num k \<noteq> 0" by simp
    thus ?thesis by (simp add: node_iv_def Let_def)
  qed
  have unit01: "unit_dyadic (0 :: rat, 1 :: rat)"
    unfolding unit_dyadic_def by (auto intro!: exI[of _ "0 :: int"] exI[of _ "0 :: nat"])
  have seed_inv: "\<forall>e \<in> set (fst ([(((l_num, r_num), k), P)], [] :: ((int \<times> int) \<times> nat) list)).
      gmp_node_inv P l_num r_num k e"
    by (simp add: gmp_node_inv_def node_iv_of_def Let_def node01 carried_repr_init unit01)
  have l6: "mset (acc_ivs l_num r_num k (snd (carried_gmp_main ([(((l_num, r_num), k), P)], []))))
      = mset (acc_ivs l_num r_num k (snd ([(((l_num, r_num), k), P)], [])))
        + rational_tree_mset_list P (todo_ivs l_num r_num k (fst ([(((l_num, r_num), k), P)], [])))"
    using carried_gmp_main_mset[OF \<delta>_pos len small_fast seed_inv] by simp
  have tdivs: "rational_tree_mset_list P (todo_ivs l_num r_num k [(((l_num, r_num), k), P)])
      = mset (rational_tree_fun_int P 0 1)"
    by (simp add: todo_ivs_def node_iv_of_def node01)
  have ord: "\<And>I. I \<in> set [(0 :: rat, 1 :: rat)] \<Longrightarrow> fst I < snd I" by simp
  have dom01: "rational_queue_fun_int_dom (P, [(0, 1)], [])"
    by (rule rational_queue_fun_int_domI[OF \<delta>_pos ord small_fast])
  have mt: "mset (rational_queue_fun_int P [(0, 1)] []) = mset [] + rational_tree_mset_list P [(0, 1)]"
    by (rule rational_queue_fun_int_mset_tree[OF \<delta>_pos _ small_fast]) simp
  have bridge: "mset (rational_tree_fun_int P 0 1) = mset (dsc_int 0 1 (Poly P))"
  proof -
    have "mset (dsc_int 0 1 (Poly P)) = mset (rational_queue_main_int P [(0, 1)] [])"
      using rational_queue_main_int_mset_dsc_int[OF \<delta>_pos small_fast dom P0 canon] by simp
    also have "\<dots> = mset (rational_queue_fun_int P [(0, 1)] [])"
      by (simp add: rational_queue_main_int_eq_fun_int[OF dom01])
    also have "\<dots> = rational_tree_mset_list P [(0, 1)]" using mt by simp
    also have "\<dots> = mset (rational_tree_fun_int P 0 1)" by simp
    finally show ?thesis ..
  qed
  show ?thesis
  proof -
    have "mset (acc_ivs l_num r_num k (snd (carried_gmp_main ([(((l_num, r_num), k), P)], []))))
        = mset (acc_ivs l_num r_num k (snd ([(((l_num, r_num), k), P)], [])))
          + rational_tree_mset_list P (todo_ivs l_num r_num k (fst ([(((l_num, r_num), k), P)], [])))"
      by (rule l6)
    also have "mset (acc_ivs l_num r_num k (snd ([(((l_num, r_num), k), P)], [])))
          + rational_tree_mset_list P (todo_ivs l_num r_num k (fst ([(((l_num, r_num), k), P)], [])))
        = mset (dsc_int 0 1 (Poly P))"
      by (simp add: acc_ivs_def tdivs bridge)
    finally show ?thesis .
  qed
qed

subsection \<open>The projection \<open>\<alpha>\<close> from the concrete loop state to the abstract \<open>carried_gmp_main\<close> state\<close>

text \<open>The concrete loop state @{typ bisection_loop_state} is @{term "((todo, qtodo), acc)"} where
  @{term todo} and @{term acc} are parallel dyadic-interval vectors @{term "(lns, rns, ks)"} and @{term qtodo}
  is the carried-polynomial stack (parallel to @{term lns}). It projects to the abstract @{const carried_gmp_main}
  state via @{const dyadic_interval_vec_triples} (= @{term "zip (zip lns rns) ks"}, the @{typ "(int \<times> int) \<times> nat"}
  node list): the todo nodes pair the interval triples with their carried polynomials, the acc nodes drop the poly.\<close>

definition bilr_alpha_todo :: "bisection_loop_state \<Rightarrow> (((int \<times> int) \<times> nat) \<times> gmp_poly) list" where
"bilr_alpha_todo st = (case st of ((todo, qtodo), _) \<Rightarrow>
   zip (dyadic_interval_vec_triples todo) qtodo)"

definition bilr_alpha_acc :: "bisection_loop_state \<Rightarrow> ((int \<times> int) \<times> nat) list" where
"bilr_alpha_acc st = dyadic_interval_vec_triples (snd st)"

definition bilr_alpha :: "bisection_loop_state \<Rightarrow> bisection_gmp_state" where
"bilr_alpha st = (bilr_alpha_todo st, bilr_alpha_acc st)"

text \<open>Under the data invariant (all four lists in lockstep), the concrete loop condition @{term "lns \<noteq> []"}
  is exactly nonemptiness of the abstract todo \<open>\<longleftrightarrow>\<close> @{const carried_gmp_main}'s recursion guard.\<close>
lemma bilr_alpha_todo_length:
  assumes "bisection_loop_state_invar st"
  shows "length (bilr_alpha_todo st) = (case st of (((lns, _, _), _), _) \<Rightarrow> length lns)"
proof -
  obtain todo qtodo acc where st: "st = ((todo, qtodo), acc)" by (cases st) auto
  obtain lns rns ks where todo: "todo = (lns, rns, ks)" by (cases todo) auto
  from assms have "length lns = length rns" and "length lns = length ks"
    and "length qtodo = length lns"
    by (auto simp: st todo bisection_loop_state_invar_def
      dyadic_interval_vec_invar_def)
  thus ?thesis
    by (simp add: st todo bilr_alpha_todo_def dyadic_interval_vec_triples_simps)
qed

lemma bilr_alpha_cond:
  assumes "bisection_loop_state_invar st"
  shows "bisection_loop_cond st \<longleftrightarrow> bilr_alpha_todo st \<noteq> []"
proof -
  obtain todo qtodo acc where st: "st = ((todo, qtodo), acc)" by (cases st) auto
  obtain lns rns ks where todo: "todo = (lns, rns, ks)" by (cases todo) auto
  have "bisection_loop_cond st \<longleftrightarrow> lns \<noteq> []"
    by (simp add: st todo bisection_loop_cond_def)
  also have "\<dots> \<longleftrightarrow> length (bilr_alpha_todo st) \<noteq> 0"
    using bilr_alpha_todo_length[OF assms] by (simp add: st todo)
  finally show ?thesis by simp
qed

subsection \<open>The refinement invariant and the two easy WHILEIT subgoals\<close>

text \<open>The driver-fixpoint refinement invariant for the @{const bisection_loop_monadic} WHILEIT, modelled on
  the endpoint @{text rational_loop_invar}: the concrete state is data-safe, every abstract todo
  node carries a valid @{const gmp_node_inv} (needed for the \<open>\<mu>\<close>-mset measure and preserved by
  @{thm gmp_node_inv_preserved}), and running the pure driver from the projected state yields the same final
  state as from the seed @{term st0} (preserved because under @{const bisection_loop_cond} the body
  refines @{const bisection_gmp_step} and @{thm carried_gmp_main.simps} unfolds one step).\<close>
definition bilr_refine_invar ::
  "real \<Rightarrow> gmp_poly \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bisection_gmp_state \<Rightarrow>
    bisection_loop_state \<Rightarrow> bool" where
"bilr_refine_invar \<delta> P l0 r0 k0 st0 st \<equiv>
  bisection_loop_safe_invar st \<and>
  (\<forall>nd \<in> set (bilr_alpha_todo st). gmp_node_inv P l0 r0 k0 nd) \<and>
  carried_gmp_main (bilr_alpha st) = carried_gmp_main st0 \<and>
  \<comment> \<open>snat-bound budgets (ported from the endpoint loop invariant \<open>rational_loop_invar\<close>):
     worklist-size + max-future-appends stays under \<open>max_snat\<close>, so the step_pre \<open>pushable\<close>
     ASSERTs are preserved (via \<open>interval_vec_pushable2_from_budget\<close>); the dyadic-\<open>k\<close>
     depth bound is per-node \<open>k + \<mu>(node_iv) + 1 < max_snat\<close> (preserved since \<open>k + \<mu>\<close> is invariant); and the
     carried polynomials keep \<open>degree = degree P\<close>.\<close>
  int (length (bilr_alpha_todo st))
    + rational_todo_append_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st)) + 2
    < int (max_snat LENGTH(gmp_poly_len)) \<and>
  int (length (bilr_alpha_acc st))
    + rational_todo_acc_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st)) + 1
    < int (max_snat LENGTH(gmp_poly_len)) \<and>
  (\<forall>nd \<in> set (bilr_alpha_todo st).
     snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1
       < max_snat LENGTH(gmp_poly_len)) \<and>
  (\<forall>nd \<in> set (bilr_alpha_todo st). length (snd nd) = length P)"

lemma carried_gmp_main_Nil: "carried_gmp_main ([], acc) = ([], acc)"
  by (simp add: carried_gmp_main.simps)

text \<open>Subgoal 3 of the WHILEIT rule: when the loop condition fails the abstract todo is empty.\<close>
lemma bilr_not_cond_todo_empty:
  assumes inv: "bilr_refine_invar \<delta> P l0 r0 k0 st0 st"
    and not_cond: "\<not> bisection_loop_cond st"
  shows "bilr_alpha_todo st = []"
proof -
  from inv have "bisection_loop_state_invar st"
    by (simp add: bilr_refine_invar_def bisection_loop_safe_invar_def)
  with not_cond bilr_alpha_cond show ?thesis by blast
qed

text \<open>Exit fact: once the abstract todo is empty, the projected acc is exactly the pure driver's final
  acc from the seed, which connects to the pure capstone above.\<close>
lemma bilr_invar_exit:
  assumes inv: "bilr_refine_invar \<delta> P l0 r0 k0 st0 st"
    and empty: "bilr_alpha_todo st = []"
  shows "bilr_alpha_acc st = snd (carried_gmp_main st0)"
proof -
  from inv have main_eq: "carried_gmp_main (bilr_alpha st) = carried_gmp_main st0"
    by (simp add: bilr_refine_invar_def)
  have "bilr_alpha st = ([], bilr_alpha_acc st)"
    using empty by (simp add: bilr_alpha_def)
  with main_eq have "carried_gmp_main st0 = ([], bilr_alpha_acc st)"
    by (simp add: carried_gmp_main_Nil)
  thus ?thesis by simp
qed

subsection \<open>Body refinement: branch building blocks\<close>

text \<open>@{const bisection_branch_zero_monadic} (the count-0 case: drop the popped node) frees the popped
  GMP data and returns the already-popped state unchanged. The discards are @{term "RETURN ()"} and
  @{thm poly_free_monadic_bind_rule} erases the free, so it refines to a pure @{const RETURN} \<open>\<Longrightarrow>\<close>
  it leaves @{term "(todo, qtodo, acc)"} (= the abstract @{const bisection_gmp_step} \<open>v = 0\<close> output) intact.\<close>
lemma bilr_branch_zero_refine:
  "bisection_branch_zero_monadic todo qtodo acc l_num r_num k Q \<le> RETURN ((todo, qtodo), acc)"
  unfolding bisection_branch_zero_monadic_def mpzb_discard_monadic_def PR_CONST_def
  by refine_vcg simp

text \<open>@{const bisection_branch_one_monadic} (the count-1 case: accept the popped interval) pushes
  @{term "(l_num, r_num, k)"} onto the acc vector and frees @{term Q}, so it refines to the unchanged
  todo/qtodo and the acc with the triple appended (= @{const bisection_gmp_step} \<open>v = 1\<close> on the projection,
  since @{const dyadic_interval_vec_triples} of the extended acc is the old triples with \<open>((l,r),k)\<close> appended).\<close>
lemma bilr_branch_one_refine:
  assumes "dyadic_interval_vec_pushable (lns, rns, ks)"
  shows "bisection_branch_one_monadic todo qtodo (lns, rns, ks) l_num r_num k Q \<le>
    RETURN ((todo, qtodo), (lns @ [l_num], rns @ [r_num], ks @ [k]))"
  using assms
  unfolding bisection_branch_one_monadic_def poly_push_coeff_monadic_def PR_CONST_def
    dyadic_interval_vec_pushable_def
  by refine_vcg auto

text \<open>Helper for the count-\<open>\<ge>2\<close> (split) branch: pushing the two carried children of @{term Q} onto the
  poly stack appends exactly @{term "carried_left Q"} and @{term "carried_right Q"}
  (the abstract @{const bisection_gmp_step} child polynomials), via @{thm carried_left_right_monadic_correct}
  and @{thm poly_vec_push2_monadic_correct}; @{term Q} is freed.\<close>
lemma bilr_carried_push_children_refine:
  assumes "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and "0 < length Q"
  shows "bisection_push_children_monadic qtodo Q \<le>
    RETURN (qtodo @ [carried_left Q, carried_right Q])"
  using assms
  unfolding bisection_push_children_monadic_def PR_CONST_def
  apply (refine_vcg carried_left_right_monadic_correct[THEN order_trans]
      poly_vec_push2_monadic_correct[THEN order_trans])
  apply auto
  done

text \<open>Helper for the root sub-case of the split branch: pushing the midpoint appends the dyadic triple
  @{term "((l_num + r_num, l_num + r_num), k + 1)"} (the abstract @{const bisection_gmp_step} midpoint at
  level @{term "k + 1"}) to the acc vector. \<open>COPY\<close> is identity and @{term "mpz_add.amop_r1"} adds.\<close>
lemma bilr_push_mid_refine:
  assumes "dyadic_interval_vec_pushable (lns, rns, ks)"
  shows "carried_push_mid_monadic (lns, rns, ks) l_num r_num k \<le>
    RETURN (lns @ [l_num + r_num], rns @ [l_num + r_num], ks @ [k + 1])"
  using assms
  unfolding carried_push_mid_monadic_def poly_push_coeff_monadic_def PR_CONST_def
    dyadic_interval_vec_pushable_def
    mpz_add.amop_r1_def mpz_add.aop_r1_def COPY_def
  by refine_vcg auto

text \<open>The concrete midpoint-root test refines the abstract @{const bisection_mid_is_root}.
  \<open>bisection_mid_zero_monadic\<close> calls the specialised \<open>half_eval_zero_monadic\<close> (rather than
  @{const poly_hom_eval_zero_nd_monadic}), so this is a direct application of
  \<open>half_eval_zero_monadic_correct\<close>, which gives \<open>poly (map_poly rat_of_int (Poly Q)) (1/2) = 0\<close>.\<close>
lemma bilr_carried_mid_zero_refine:
  assumes len0: "0 < length Q"
    and bound: "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_mid_zero_monadic Q \<le> RETURN (bisection_mid_is_root Q)"
  using half_eval_zero_monadic_correct[OF len0 bound]
  unfolding bisection_mid_zero_monadic_def PR_CONST_def bisection_mid_is_root_def
  by (simp add: pw_le_iff refine_pw_simps)

text \<open>The split-pair update pushes the two child intervals onto the todo vector (@{thm
  dyadic_interval_vec_push_children_monadic_spec}) and the two carried child polynomials onto the
  poly stack (@{thm bilr_carried_push_children_refine}), characterised by triples: exactly the
  @{const bisection_gmp_step} \<open>v \<ge> 2\<close> children @{term "(((l+l,l+r),k+1),left)"} and @{term "(((l+r,r+r),k+1),right)"}.\<close>
lemma bilr_split_pair_state_refine:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and "0 < length Q"
  shows "bisection_split_pair_state_monadic ((lns, rns, ks), qtodo) l_num r_num k Q \<le>
    SPEC (\<lambda>(todo', qtodo').
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num + l_num, l_num + r_num), k + 1),
           ((l_num + r_num, r_num + r_num), k + 1)] \<and>
      qtodo' = qtodo @ [carried_left Q, carried_right Q])"
  using assms
  unfolding bisection_split_pair_state_monadic_def PR_CONST_def
  apply (simp only: Let_def prod.case)
  apply (refine_vcg
      dyadic_interval_vec_push_children_monadic_spec[OF assms(1) assms(2) assms(3), THEN order_trans]
      bilr_carried_push_children_refine[OF assms(4) assms(5) assms(6), THEN order_trans])
  apply (auto simp: dyadic_interval_vec_triples_simps)
  done

text \<open>The non-root split branch leaves acc unchanged and pushes the two children onto todo/qtodo.\<close>
lemma bilr_branch_split_nonroot_refine:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and "0 < length Q"
  shows "bisection_branch_split_nonroot_monadic (lns, rns, ks) qtodo acc l_num r_num k Q \<le>
    SPEC (\<lambda>((todo', qtodo'), acc').
      acc' = acc \<and>
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num + l_num, l_num + r_num), k + 1),
           ((l_num + r_num, r_num + r_num), k + 1)] \<and>
      qtodo' = qtodo @ [carried_left Q, carried_right Q])"
  unfolding bisection_branch_split_nonroot_monadic_def PR_CONST_def
  apply (refine_vcg bilr_split_pair_state_refine[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6),
      THEN order_trans])
  using assms apply auto
  done

text \<open>The root split branch additionally pushes the midpoint @{term "((l_num+r_num,l_num+r_num),k+1)"}
  onto acc (via @{thm bilr_push_mid_refine}) before the children.\<close>
lemma bilr_branch_split_root_refine:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and "dyadic_interval_vec_pushable (alns, arns, aks)"
    and "0 < length Q"
  shows "bisection_branch_split_root_monadic (lns, rns, ks) qtodo (alns, arns, aks) l_num r_num k Q \<le>
    SPEC (\<lambda>((todo', qtodo'), acc').
      acc' = (alns @ [l_num + r_num], arns @ [l_num + r_num], aks @ [k + 1]) \<and>
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num + l_num, l_num + r_num), k + 1),
           ((l_num + r_num, r_num + r_num), k + 1)] \<and>
      qtodo' = qtodo @ [carried_left Q, carried_right Q])"
  unfolding bisection_branch_split_root_monadic_def PR_CONST_def
  apply (refine_vcg bilr_push_mid_refine[OF assms(6), THEN order_trans]
      bilr_split_pair_state_refine[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(7), THEN order_trans])
  using assms apply auto
  done

text \<open>The full split branch dispatches on the midpoint-root test: it pushes the children and, iff
  @{const bisection_mid_is_root}, the midpoint \<open>\<Longrightarrow>\<close> exactly the @{const bisection_gmp_step} \<open>v \<ge> 2\<close> case.\<close>
lemma bilr_branch_split_refine:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and "0 < length Q"
    and "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and "dyadic_interval_vec_pushable (alns, arns, aks)"
  shows "bisection_branch_split_monadic (lns, rns, ks) qtodo (alns, arns, aks) l_num r_num k Q \<le>
    SPEC (\<lambda>((todo', qtodo'), acc').
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        dyadic_interval_vec_triples (lns, rns, ks) @
          [((l_num + l_num, l_num + r_num), k + 1),
           ((l_num + r_num, r_num + r_num), k + 1)] \<and>
      qtodo' = qtodo @ [carried_left Q, carried_right Q] \<and>
      acc' = (if bisection_mid_is_root Q
              then (alns @ [l_num + r_num], arns @ [l_num + r_num], aks @ [k + 1])
              else (alns, arns, aks)))"
  unfolding bisection_branch_split_monadic_def PR_CONST_def
  apply (refine_vcg bilr_carried_mid_zero_refine[OF assms(4) assms(5), THEN order_trans]
      bilr_branch_split_root_refine[OF assms(1) assms(2) assms(3) assms(5) assms(6) assms(7) assms(4)]
      bilr_branch_split_nonroot_refine[OF assms(1) assms(2) assms(3) assms(5) assms(6) assms(4)])
  using assms apply (auto split: if_splits)
  done

text \<open>@{const bisection_after_pop_monadic} dispatches on the carried Descartes count; via
  @{thm carried_descartes_count_trunc_monadic_classify} (the truncated count, with the same statement
  as @{thm [source] carried_descartes_count_monadic_classify}) the concrete count agrees with
  @{const carried_descartes_count} on \<open>=0 / =1 / \<ge>2\<close>, so the result matches
  @{const bisection_gmp_step}'s three branches (todo/qtodo/acc are the already-popped state). The
  result is characterised by todo' triples and concrete qtodo'/acc'.\<close>
lemma bilr_after_pop_refine:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "dyadic_interval_vec_pushable2 (lns, rns, ks)"
    and "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and "0 < length Q"
    and "length Q + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length qtodo + 2 < max_snat LENGTH(gmp_poly_len)"
    and "dyadic_interval_vec_pushable (alns, arns, aks)"
  shows "bisection_after_pop_monadic (lns, rns, ks) qtodo (alns, arns, aks) l_num r_num k Q \<le>
    SPEC (\<lambda>((todo', qtodo'), acc').
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        (if 2 \<le> carried_descartes_count Q
         then dyadic_interval_vec_triples (lns, rns, ks) @
                [((l_num + l_num, l_num + r_num), k + 1),
                 ((l_num + r_num, r_num + r_num), k + 1)]
         else dyadic_interval_vec_triples (lns, rns, ks)) \<and>
      qtodo' = (if 2 \<le> carried_descartes_count Q
                then qtodo @ [carried_left Q, carried_right Q]
                else qtodo) \<and>
      acc' = (if carried_descartes_count Q = 0 then (alns, arns, aks)
              else if carried_descartes_count Q = 1
                   then (alns @ [l_num], arns @ [r_num], aks @ [k])
              else if bisection_mid_is_root Q
                   then (alns @ [l_num + r_num], arns @ [l_num + r_num], aks @ [k + 1])
                   else (alns, arns, aks)))"
  unfolding bisection_after_pop_monadic_def PR_CONST_def
  apply (refine_vcg carried_descartes_count_trunc_monadic_classify[OF assms(5), THEN order_trans]
      bilr_branch_zero_refine[THEN order_trans]
      bilr_branch_one_refine[OF assms(7), THEN order_trans]
      bilr_branch_split_refine[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7)])
  using assms by (auto simp: dyadic_interval_vec_triples_simps)

text \<open>@{const bisection_pop_poly_args_monadic} pops the last carried polynomial @{term "last qtodo"}
  (leaving @{term "butlast qtodo"}) and runs @{const bisection_after_pop_monadic} on it.\<close>
lemma bilr_pop_poly_args_refine:
  assumes "dyadic_interval_vec_invar todo"
    and "dyadic_interval_vec_pushable2 todo"
    and "qtodo \<noteq> []"
    and "0 < length (last qtodo)"
    and "length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len)"
    and "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    and "dyadic_interval_vec_pushable (alns, arns, aks)"
  shows "bisection_pop_poly_args_monadic todo qtodo (alns, arns, aks) l_num r_num k \<le>
    SPEC (\<lambda>((todo', qtodo'), acc').
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        (if 2 \<le> carried_descartes_count (last qtodo)
         then dyadic_interval_vec_triples todo @
                [((l_num + l_num, l_num + r_num), k + 1),
                 ((l_num + r_num, r_num + r_num), k + 1)]
         else dyadic_interval_vec_triples todo) \<and>
      qtodo' = (if 2 \<le> carried_descartes_count (last qtodo)
                then butlast qtodo @
                       [carried_left (last qtodo), carried_right (last qtodo)]
                else butlast qtodo) \<and>
      acc' = (if carried_descartes_count (last qtodo) = 0 then (alns, arns, aks)
              else if carried_descartes_count (last qtodo) = 1
                   then (alns @ [l_num], arns @ [r_num], aks @ [k])
              else if bisection_mid_is_root (last qtodo)
                   then (alns @ [l_num + r_num], arns @ [l_num + r_num], aks @ [k + 1])
                   else (alns, arns, aks)))"
proof -
  obtain lns rns ks where t: "todo = (lns, rns, ks)" by (cases todo)
  show ?thesis
    using assms unfolding t
    unfolding bisection_pop_poly_args_monadic_def bisection_pop_poly_args_pre_def
      poly_vec_pop_last_monadic_def PR_CONST_def
    apply (refine_vcg bilr_after_pop_refine[THEN order_trans])
    apply (auto simp: dyadic_interval_vec_triples_simps)
    done
qed

subsection \<open>Body: the \<open>\<alpha>\<close>-relation list helpers (\<open>butlast\<close>/\<open>last\<close> of the zipped triples)\<close>

text \<open>Popping the concrete vectors commutes with the @{const dyadic_interval_vec_triples} projection:
  @{term butlast} of the triples is the triples of the @{term butlast} vectors, and @{term last} of the
  triples is the triple of the last components. The data invariant (all three lists in lockstep) is what
  makes the \<open>butlast_zip'\<close>/\<open>last_zip'\<close> commutation apply.\<close>
lemma butlast_zip':
  "length xs = length ys \<Longrightarrow> butlast (zip xs ys) = zip (butlast xs) (butlast ys)"
  by (induction xs ys rule: list_induct2) auto

lemma last_zip':
  "length xs = length ys \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> last (zip xs ys) = (last xs, last ys)"
proof (induction xs ys rule: list_induct2)
  case (Cons x xs y ys)
  show ?case by (cases "xs = []") (use Cons in auto)
qed simp

lemma bilr_triples_butlast:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
  shows "dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)
       = butlast (dyadic_interval_vec_triples (lns, rns, ks))"
  using assms
  by (simp add: dyadic_interval_vec_triples_simps
      dyadic_interval_vec_invar_def butlast_zip'[symmetric] length_zip)

lemma bilr_triples_append:
  assumes "dyadic_interval_vec_invar (alns, arns, aks)"
  shows "dyadic_interval_vec_triples (alns @ [x], arns @ [y], aks @ [z])
       = dyadic_interval_vec_triples (alns, arns, aks) @ [((x, y), z)]"
  using assms
  by (simp add: dyadic_interval_vec_triples_simps
      dyadic_interval_vec_invar_def zip_append)

lemma bilr_triples_last:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)" and "lns \<noteq> []"
  shows "last (dyadic_interval_vec_triples (lns, rns, ks)) = ((last lns, last rns), last ks)"
proof -
  from assms have l: "length lns = length rns" "length lns = length ks" "lns \<noteq> []"
    by (auto simp: dyadic_interval_vec_invar_def)
  hence ne: "zip lns rns \<noteq> []" by (cases lns) auto
  have "last (zip (zip lns rns) ks) = (last (zip lns rns), last ks)"
    using l ne by (simp add: last_zip' length_zip)
  also have "last (zip lns rns) = (last lns, last rns)" using l by (simp add: last_zip')
  finally show ?thesis by (simp add: dyadic_interval_vec_triples_simps)
qed

text \<open>Lifting the triples \<open>butlast\<close>/\<open>last\<close> commutation to @{const bilr_alpha_todo}: popping the concrete
  state's last node corresponds to @{term butlast} on the abstract todo, and the popped node is its
  @{term last} — exactly what @{const bisection_gmp_step} reads.\<close>
lemma bilr_alpha_todo_butlast:
  assumes "bisection_loop_state_invar (((lns, rns, ks), qtodo), acc)"
  shows "bilr_alpha_todo (((butlast lns, butlast rns, butlast ks), butlast qtodo), acc')
       = butlast (bilr_alpha_todo (((lns, rns, ks), qtodo), acc))"
proof -
  from assms have inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lq: "length qtodo = length lns"
    by (auto simp: bisection_loop_state_invar_def)
  from inv have "length lns = length rns" "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  hence lt: "length (dyadic_interval_vec_triples (lns, rns, ks)) = length qtodo"
    using lq by (simp add: dyadic_interval_vec_triples_simps length_zip)
  show ?thesis
    by (simp add: bilr_alpha_todo_def bilr_triples_butlast[OF inv]
        butlast_zip'[OF lt, symmetric])
qed

lemma bilr_alpha_todo_last:
  assumes "bisection_loop_state_invar (((lns, rns, ks), qtodo), acc)" and "lns \<noteq> []"
  shows "last (bilr_alpha_todo (((lns, rns, ks), qtodo), acc))
       = (((last lns, last rns), last ks), last qtodo)"
proof -
  from assms have inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and lq: "length qtodo = length lns"
    by (auto simp: bisection_loop_state_invar_def)
  from inv have "length lns = length rns" "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  hence lt: "length (dyadic_interval_vec_triples (lns, rns, ks)) = length qtodo"
    using lq by (simp add: dyadic_interval_vec_triples_simps length_zip)
  have ne: "dyadic_interval_vec_triples (lns, rns, ks) \<noteq> []"
    using \<open>lns \<noteq> []\<close> lt lq by (cases qtodo) auto
  show ?thesis
    by (simp add: bilr_alpha_todo_def last_zip'[OF lt ne] bilr_triples_last[OF inv \<open>lns \<noteq> []\<close>])
qed

subsection \<open>Body: \<open>step_args\<close> composition (pop the dyadic node, pop the carried polynomial, after-pop)\<close>

text \<open>@{const bisection_loop_step_args_monadic} pops the last interval @{term "(last lns, last rns, last ks)"}
  off the dyadic vector and then runs @{const bisection_pop_poly_args_monadic} on the @{term butlast} vector;
  the result is characterised in terms of @{term "carried_descartes_count (last qtodo)"} exactly as
  @{const bisection_gmp_step}'s three branches read it.\<close>
lemma bilr_step_args_spec:
  assumes "dyadic_interval_vec_invar (lns, rns, ks)"
    and "lns \<noteq> []"
    and "length qtodo = length lns"
    and "0 < length (last qtodo)"
    and "length (last qtodo) + 1 < max_snat LENGTH(gmp_poly_len)"
    and "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
    and "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    and "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    and "dyadic_interval_vec_pushable (alns, arns, aks)"
  shows "bisection_loop_step_args_monadic (lns, rns, ks) qtodo (alns, arns, aks) \<le>
    SPEC (\<lambda>((todo', qtodo'), acc').
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        (if 2 \<le> carried_descartes_count (last qtodo)
         then dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) @
                [((last lns + last lns, last lns + last rns), last ks + 1),
                 ((last lns + last rns, last rns + last rns), last ks + 1)]
         else dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)) \<and>
      qtodo' = (if 2 \<le> carried_descartes_count (last qtodo)
                then butlast qtodo @
                       [carried_left (last qtodo), carried_right (last qtodo)]
                else butlast qtodo) \<and>
      acc' = (if carried_descartes_count (last qtodo) = 0 then (alns, arns, aks)
              else if carried_descartes_count (last qtodo) = 1
                   then (alns @ [last lns], arns @ [last rns], aks @ [last ks])
              else if bisection_mid_is_root (last qtodo)
                   then (alns @ [last lns + last rns], arns @ [last lns + last rns], aks @ [last ks + 1])
                   else (alns, arns, aks)))"
proof -
  have iv': "dyadic_interval_vec_invar (butlast lns, butlast rns, butlast ks)"
    using assms(1) by (auto simp: dyadic_interval_vec_invar_def)
  have qne: "qtodo \<noteq> []" using assms(2,3) by (cases lns) auto
  show ?thesis
    using assms iv' qne
    unfolding bisection_loop_step_args_monadic_def PR_CONST_def
    apply (refine_vcg
        dyadic_interval_vec_pop_last_monadic_spec[OF assms(1) assms(2), THEN order_trans]
        bilr_pop_poly_args_refine[THEN order_trans])
    apply (auto simp: dyadic_interval_vec_triples_simps
        bisection_pop_poly_args_pre_def length_butlast)
    done
qed

subsection \<open>Body: the \<open>\<alpha>\<close>-bridge \<open>bilr_alpha (step result) = bisection_gmp_step (bilr_alpha st)\<close>\<close>

text \<open>The data-refinement crux: a concrete result satisfying the @{thm bilr_step_args_spec} characterisation
  projects (via @{const bilr_alpha}) to exactly @{const bisection_gmp_step} of the projected input — case
  analysis on @{term "carried_descartes_count (last qtodo)"} using the @{const bilr_alpha_todo} pop
  connectors and @{thm bilr_triples_append}.\<close>
lemma bilr_step_alpha_eq:
  assumes si: "bisection_loop_state_invar (((lns, rns, ks), qtodo), (alns, arns, aks))"
    and ne: "lns \<noteq> []"
    and tt': "dyadic_interval_vec_triples todo' =
        (if 2 \<le> carried_descartes_count (last qtodo)
         then dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) @
                [((last lns + last lns, last lns + last rns), last ks + 1),
                 ((last lns + last rns, last rns + last rns), last ks + 1)]
         else dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))"
    and qt': "qtodo' = (if 2 \<le> carried_descartes_count (last qtodo)
                then butlast qtodo @
                       [carried_left (last qtodo), carried_right (last qtodo)]
                else butlast qtodo)"
    and at': "acc' = (if carried_descartes_count (last qtodo) = 0 then (alns, arns, aks)
              else if carried_descartes_count (last qtodo) = 1
                   then (alns @ [last lns], arns @ [last rns], aks @ [last ks])
              else if bisection_mid_is_root (last qtodo)
                   then (alns @ [last lns + last rns], arns @ [last lns + last rns], aks @ [last ks + 1])
                   else (alns, arns, aks))"
  shows "bilr_alpha ((todo', qtodo'), acc')
       = bisection_gmp_step (bilr_alpha (((lns, rns, ks), qtodo), (alns, arns, aks)))"
proof -
  define st where "st = (((lns, rns, ks), qtodo), (alns, arns, aks))"
  from si have inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and ia: "dyadic_interval_vec_invar (alns, arns, aks)"
    and lq: "length qtodo = length lns"
    by (auto simp: bisection_loop_state_invar_def)
  from inv have ll: "length lns = length rns" "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  have A_ne: "bilr_alpha_todo st \<noteq> []"
    using ne lq ll unfolding st_def bilr_alpha_todo_def
    by (cases lns; cases qtodo) (auto simp: dyadic_interval_vec_triples_simps)
  have lastA: "last (bilr_alpha_todo st) = (((last lns, last rns), last ks), last qtodo)"
    unfolding st_def by (rule bilr_alpha_todo_last[OF si ne])
  have BL: "butlast (bilr_alpha_todo st)
          = zip (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
                (butlast qtodo)"
    using bilr_alpha_todo_butlast[OF si, of "(alns, arns, aks)"]
    unfolding st_def bilr_alpha_todo_def by simp
  have lenbl: "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
             = length (butlast qtodo)"
    using ll lq by (simp add: dyadic_interval_vec_triples_simps length_zip)
  have accst: "bilr_alpha_acc st = dyadic_interval_vec_triples (alns, arns, aks)"
    unfolding st_def bilr_alpha_acc_def by simp
  text \<open>@{const bisection_gmp_step} of the projected input, with all the internal \<open>let\<close>s reduced via
    @{thm lastA} (the popped node) and \<open>A_ne\<close> (todo nonempty).\<close>
  have step: "bisection_gmp_step (bilr_alpha st) =
    (if carried_descartes_count (last qtodo) = 0
       then (butlast (bilr_alpha_todo st), bilr_alpha_acc st)
     else if carried_descartes_count (last qtodo) = 1
       then (butlast (bilr_alpha_todo st), bilr_alpha_acc st @ [((last lns, last rns), last ks)])
     else (butlast (bilr_alpha_todo st) @
             [(((last lns + last lns, last lns + last rns), last ks + 1),
               carried_left (last qtodo)),
              (((last lns + last rns, last rns + last rns), last ks + 1),
               carried_right (last qtodo))],
           if bisection_mid_is_root (last qtodo)
           then bilr_alpha_acc st @ [((last lns + last rns, last lns + last rns), last ks + 1)]
           else bilr_alpha_acc st))"
    unfolding bisection_gmp_step_def bilr_alpha_def
    using A_ne by (simp add: lastA Let_def)
  have lhs_t: "bilr_alpha_todo ((todo', qtodo'), acc') = zip (dyadic_interval_vec_triples todo') qtodo'"
    by (simp add: bilr_alpha_todo_def)
  have lhs_a: "bilr_alpha_acc ((todo', qtodo'), acc') = dyadic_interval_vec_triples acc'"
    by (simp add: bilr_alpha_acc_def)
  have todo_eq: "bilr_alpha_todo ((todo', qtodo'), acc') = fst (bisection_gmp_step (bilr_alpha st))"
    unfolding step lhs_t
    by (simp add: tt' qt' BL zip_append lenbl split: if_splits)
  have acc_eq: "bilr_alpha_acc ((todo', qtodo'), acc') = snd (bisection_gmp_step (bilr_alpha st))"
    unfolding step lhs_a
    by (simp add: at' accst bilr_triples_append[OF ia] split: if_splits)
  show ?thesis
    using todo_eq acc_eq by (simp add: bilr_alpha_def st_def)
qed

subsection \<open>Budgets: \<open>bisection_gmp_step\<close> preserves the bound conjuncts\<close>

lemma length_carried_right[simp]:
  "length (carried_right xs) = length xs"
  by (simp add: carried_right_def length_taylor_shift_list)

text \<open>The carried polynomials all keep \<open>degree = degree P\<close>: the children's polys are
  @{const carried_left}/@{const carried_right} of the popped poly, both length-preserving.\<close>
lemma carried_step_preserves_polylen:
  assumes "\<forall>nd \<in> set (fst st). length (snd nd) = n"
  shows "\<forall>nd \<in> set (fst (bisection_gmp_step st)). length (snd nd) = n"
proof (cases "fst st = []")
  case True
  thus ?thesis by (cases st) (simp add: bisection_gmp_step_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain t Q where tQ: "last todo = (t, Q)" by (cases "last todo")
  obtain lr k where lrk: "t = (lr, k)" by (cases t)
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), Q)" using tQ lrk lr_eq by simp
  have last_in: "last todo \<in> set todo" using todo_ne by (rule last_in_set)
  have alln: "\<forall>nd \<in> set todo. length (snd nd) = n" using assms by (simp add: st)
  have lenQ: "length Q = n"
    using alln[rule_format, OF last_in] last_eq by simp
  have rest: "\<forall>nd \<in> set (butlast todo). length (snd nd) = n"
    using alln by (auto dest: in_set_butlastD)
  show ?thesis
  proof (cases "carried_descartes_count Q = 0")
    case True thus ?thesis using rest last_eq todo_ne
      by (simp add: st bisection_gmp_step_def Let_def)
  next
    case v0: False
    show ?thesis
    proof (cases "carried_descartes_count Q = 1")
      case True thus ?thesis using rest last_eq todo_ne
        by (simp add: st bisection_gmp_step_def Let_def)
    next
      case v1: False
      have "\<forall>nd \<in> set (butlast todo @
              [(((l + l, l + r), k + 1), carried_left Q),
               (((l + r, r + r), k + 1), carried_right Q)]).
            length (snd nd) = n"
        using rest lenQ by auto
      thus ?thesis using v0 v1 last_eq todo_ne
        by (simp add: st bisection_gmp_step_def Let_def)
    qed
  qed
qed

text \<open>The dyadic-\<open>k\<close> depth bound \<open>k + \<mu>(node_iv) + 1 < B\<close> is preserved: a split node's children carry
  @{term "k+1"} but their @{const node_iv} is a half-interval, so by @{thm mu_halve_strict} the child \<open>\<mu>\<close> is
  strictly smaller, keeping \<open>(k+1) + \<mu>_child + 1 \<le> k + \<mu>_parent + 1 < B\<close>. Mirrors @{thm bisection_gmp_step_mu_decreases}.\<close>
lemma carried_step_preserves_depth:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and inv: "\<forall>e \<in> set (fst st). gmp_node_inv P l0 r0 k0 e"
    and bound: "\<forall>nd \<in> set (fst st).
        snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1 < B"
  shows "\<forall>nd \<in> set (fst (bisection_gmp_step st)).
        snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1 < B"
proof (cases "fst st = []")
  case True
  thus ?thesis by (cases st) (simp add: bisection_gmp_step_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain t Q where tQ: "last todo = (t, Q)" by (cases "last todo")
  obtain lr k where lrk: "t = (lr, k)" by (cases t)
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), Q)" using tQ lrk lr_eq by simp
  have inv': "\<forall>e \<in> set todo. gmp_node_inv P l0 r0 k0 e" using inv by (simp add: st)
  have bound': "\<forall>nd \<in> set todo.
      snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1 < B"
    using bound by (simp add: st)
  have ninv: "gmp_node_inv P l0 r0 k0 (((l, r), k), Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (node_iv l0 r0 k0 l r k)"
  define b where "b = snd (node_iv l0 r0 k0 l r k)"
  have ab: "a < b" using gmp_node_inv_ordered[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using gmp_node_inv_count[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have niv: "node_iv_of l0 r0 k0 ((l, r), k) = (a, b)"
    by (simp add: node_iv_of_def a_def b_def)
  let ?m = "(a + b) / 2"
  have rest: "\<forall>nd \<in> set (butlast todo).
      snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1 < B"
    using bound' by (auto dest: in_set_butlastD)
  have pbound: "k + rational_interval_mu \<delta> (a, b) + 1 < B"
    using bound'[rule_format, OF last_in_set[OF todo_ne]] last_eq niv by simp
  show ?thesis
  proof (cases "carried_descartes_count Q = 0 \<or> carried_descartes_count Q = 1")
    case True
    have stf: "fst (bisection_gmp_step st) = butlast todo"
      using todo_ne last_eq True by (auto simp: st bisection_gmp_step_def Let_def)
    show ?thesis using rest by (simp add: stf)
  next
    case False
    have v0: "descartes_list_int a b P \<noteq> 0" and v1: "descartes_list_int a b P \<noteq> 1"
      using False count by auto
    have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
    proof (rule ccontr)
      assume "\<not> \<delta> < of_rat b - of_rat a"
      then have "of_rat b - of_rat a \<le> \<delta>" by linarith
      then have "descartes_list_int a b P \<le> 1" using small_fast[OF ab] by simp
      with v0 v1 show False by simp
    qed
    have left_lt: "rational_interval_mu \<delta> (a, ?m) < rational_interval_mu \<delta> (a, b)"
      using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def by (simp add: of_rat_add of_rat_divide)
    have right_lt: "rational_interval_mu \<delta> (?m, b) < rational_interval_mu \<delta> (a, b)"
      using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def by (simp add: of_rat_add of_rat_divide)
    have nl: "node_iv_of l0 r0 k0 ((l + l, l + r), k + 1) = (a, ?m)"
      using node_iv_bisect_left[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
    have nr: "node_iv_of l0 r0 k0 ((l + r, r + r), k + 1) = (?m, b)"
      using node_iv_bisect_right[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
    have stf: "fst (bisection_gmp_step st)
        = butlast todo @ [(((l + l, l + r), k + 1), carried_left Q),
                          (((l + r, r + r), k + 1), carried_right Q)]"
      using todo_ne last_eq v0 v1 count
      by (auto simp: st bisection_gmp_step_def Let_def)
    have lc: "(k + 1) + rational_interval_mu \<delta> (a, ?m) + 1 < B"
      using pbound left_lt by simp
    have rc: "(k + 1) + rational_interval_mu \<delta> (?m, b) + 1 < B"
      using pbound right_lt by simp
    show ?thesis
      unfolding stf
    proof (rule ballI)
      fix nd assume "nd \<in> set (butlast todo @
          [(((l + l, l + r), k + 1), carried_left Q),
           (((l + r, r + r), k + 1), carried_right Q)])"
      then consider "nd \<in> set (butlast todo)"
        | "nd = (((l + l, l + r), k + 1), carried_left Q)"
        | "nd = (((l + r, r + r), k + 1), carried_right Q)" by auto
      thus "snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1 < B"
      proof cases
        case 1 thus ?thesis using rest by blast
      next
        case 2 thus ?thesis using lc nl by simp
      next
        case 3 thus ?thesis using rc nr by simp
      qed
    qed
  qed
qed

text \<open>The worklist \<open>size + append-budget\<close> is non-increasing: a split trades 2 budget for 1 node (the
  children's budgets sum to \<open>\<le> popped - 2\<close> by @{thm rational_todo_budget_children_le}, since their
  \<open>\<mu>\<close> is strictly smaller), so the @{term max_snat} size bound is preserved.\<close>
lemma carried_step_preserves_sizebudget:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and inv: "\<forall>e \<in> set (fst st). gmp_node_inv P l0 r0 k0 e"
  shows "int (length (fst (bisection_gmp_step st)))
       + rational_todo_append_budget \<delta> (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st)))
     \<le> int (length (fst st))
       + rational_todo_append_budget \<delta> (todo_ivs l0 r0 k0 (fst st))"
proof (cases "fst st = []")
  case True thus ?thesis by (cases st) (simp add: bisection_gmp_step_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain t Q where tQ: "last todo = (t, Q)" by (cases "last todo")
  obtain lr k where lrk: "t = (lr, k)" by (cases t)
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), Q)" using tQ lrk lr_eq by simp
  have inv': "\<forall>e \<in> set todo. gmp_node_inv P l0 r0 k0 e" using inv by (simp add: st)
  have ninv: "gmp_node_inv P l0 r0 k0 (((l, r), k), Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (node_iv l0 r0 k0 l r k)"
  define b where "b = snd (node_iv l0 r0 k0 l r k)"
  have ab: "a < b" using gmp_node_inv_ordered[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using gmp_node_inv_count[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have niv: "node_iv_of l0 r0 k0 ((l, r), k) = (a, b)" by (simp add: node_iv_of_def a_def b_def)
  let ?m = "(a + b) / 2"
  let ?bud = "rational_todo_append_budget \<delta>"
  let ?ib = "rational_interval_todo_budget \<delta>"
  have todo_split: "todo = butlast todo @ [(((l, r), k), Q)]"
    using todo_ne last_eq by (metis append_butlast_last_id)
  have old_ivs: "todo_ivs l0 r0 k0 todo = todo_ivs l0 r0 k0 (butlast todo) @ [(a, b)]"
    by (subst todo_split) (simp add: todo_ivs_def niv)
  have old_bud: "?bud (todo_ivs l0 r0 k0 todo) = ?bud (todo_ivs l0 r0 k0 (butlast todo)) + ?ib (a, b)"
    by (simp add: old_ivs rational_todo_append_budget_def)
  have old_len: "int (length todo) = int (length (butlast todo)) + 1"
    using todo_ne by (simp add: length_butlast)
  have fstst: "fst st = todo" by (simp add: st)
  have ib_nn: "?ib (a, b) \<ge> 0" by simp
  show ?thesis
  proof (cases "carried_descartes_count Q = 0 \<or> carried_descartes_count Q = 1")
    case True
    have stf: "fst (bisection_gmp_step st) = butlast todo"
      using todo_ne last_eq True by (auto simp: st bisection_gmp_step_def Let_def)
    show ?thesis unfolding fstst stf using old_bud old_len ib_nn by linarith
  next
    case False
    have v0: "descartes_list_int a b P \<noteq> 0" and v1: "descartes_list_int a b P \<noteq> 1"
      using False count by auto
    have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
    proof (rule ccontr)
      assume "\<not> \<delta> < of_rat b - of_rat a"
      then have "of_rat b - of_rat a \<le> \<delta>" by linarith
      then have "descartes_list_int a b P \<le> 1" using small_fast[OF ab] by simp
      with v0 v1 show False by simp
    qed
    have left_lt: "rational_interval_mu \<delta> (a, ?m) < rational_interval_mu \<delta> (a, b)"
      using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def by (simp add: of_rat_add of_rat_divide)
    have right_lt: "rational_interval_mu \<delta> (?m, b) < rational_interval_mu \<delta> (a, b)"
      using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
      unfolding rational_interval_mu_def by (simp add: of_rat_add of_rat_divide)
    have nl: "node_iv_of l0 r0 k0 ((l + l, l + r), k + 1) = (a, ?m)"
      using node_iv_bisect_left[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
    have nr: "node_iv_of l0 r0 k0 ((l + r, r + r), k + 1) = (?m, b)"
      using node_iv_bisect_right[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
    have stf: "fst (bisection_gmp_step st)
        = butlast todo @ [(((l + l, l + r), k + 1), carried_left Q),
                          (((l + r, r + r), k + 1), carried_right Q)]"
      using todo_ne last_eq v0 v1 count by (auto simp: st bisection_gmp_step_def Let_def)
    have new_ivs: "todo_ivs l0 r0 k0 (fst (bisection_gmp_step st))
        = todo_ivs l0 r0 k0 (butlast todo) @ [(a, ?m), (?m, b)]"
      by (simp only: stf todo_ivs_def map_append list.map fst_conv nl nr)
    have new_bud: "?bud (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st)))
        = ?bud (todo_ivs l0 r0 k0 (butlast todo)) + ?ib (a, ?m) + ?ib (?m, b)"
      by (simp add: new_ivs rational_todo_append_budget_def)
    have new_len: "int (length (fst (bisection_gmp_step st))) = int (length (butlast todo)) + 2"
      by (simp add: stf)
    have child_le: "1 + ?ib (a, ?m) + ?ib (?m, b) \<le> ?ib (a, b)"
      using rational_todo_budget_children_le[OF left_lt right_lt]
      unfolding rational_interval_todo_budget_def by linarith
    show ?thesis
      unfolding fstst
      using old_bud old_len new_bud new_len child_le by linarith
  qed
qed

text \<open>The acc \<open>size + acc-budget\<close> is non-increasing: accepting a node / pushing a midpoint grows acc by 1,
  but the popped node's acc-budget (\<open>2^(\<mu>+1)-1 \<ge> 1\<close>) covers it, and a split's children acc-budgets sum to
  \<open>\<le> popped - 1\<close> (@{thm rational_acc_budget_children_le}).\<close>
lemma carried_step_preserves_accbudget:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and inv: "\<forall>e \<in> set (fst st). gmp_node_inv P l0 r0 k0 e"
  shows "int (length (snd (bisection_gmp_step st)))
       + rational_todo_acc_budget \<delta> (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st)))
     \<le> int (length (snd st))
       + rational_todo_acc_budget \<delta> (todo_ivs l0 r0 k0 (fst st))"
proof (cases "fst st = []")
  case True thus ?thesis by (cases st) (simp add: bisection_gmp_step_def)
next
  case False
  obtain todo acc where st: "st = (todo, acc)" by (cases st)
  with False have todo_ne: "todo \<noteq> []" by simp
  obtain t Q where tQ: "last todo = (t, Q)" by (cases "last todo")
  obtain lr k where lrk: "t = (lr, k)" by (cases t)
  obtain l r where lr_eq: "lr = (l, r)" by (cases lr)
  have last_eq: "last todo = (((l, r), k), Q)" using tQ lrk lr_eq by simp
  have inv': "\<forall>e \<in> set todo. gmp_node_inv P l0 r0 k0 e" using inv by (simp add: st)
  have ninv: "gmp_node_inv P l0 r0 k0 (((l, r), k), Q)"
    using inv'[rule_format, OF last_in_set[OF todo_ne]] last_eq by simp
  define a where "a = fst (node_iv l0 r0 k0 l r k)"
  define b where "b = snd (node_iv l0 r0 k0 l r k)"
  have ab: "a < b" using gmp_node_inv_ordered[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have count: "carried_descartes_count Q = descartes_list_int a b P"
    using gmp_node_inv_count[OF ninv] by (simp add: node_iv_of_def a_def b_def)
  have niv: "node_iv_of l0 r0 k0 ((l, r), k) = (a, b)" by (simp add: node_iv_of_def a_def b_def)
  let ?m = "(a + b) / 2"
  let ?ab = "rational_todo_acc_budget \<delta>"
  let ?ia = "rational_interval_acc_budget \<delta>"
  have todo_split: "todo = butlast todo @ [(((l, r), k), Q)]"
    using todo_ne last_eq by (metis append_butlast_last_id)
  have old_ivs: "todo_ivs l0 r0 k0 todo = todo_ivs l0 r0 k0 (butlast todo) @ [(a, b)]"
    by (subst todo_split) (simp add: todo_ivs_def niv)
  have old_bud: "?ab (todo_ivs l0 r0 k0 todo) = ?ab (todo_ivs l0 r0 k0 (butlast todo)) + ?ia (a, b)"
    by (simp add: old_ivs rational_todo_acc_budget_def)
  have ia_pos: "?ia (a, b) \<ge> 1"
    using rational_interval_acc_budget_pos[of \<delta> "(a, b)"] by linarith
  have sndst: "snd st = acc" by (simp add: st)
  have fstst: "fst st = todo" by (simp add: st)
  show ?thesis
  proof (cases "carried_descartes_count Q = 0")
    case True
    have stf: "bisection_gmp_step st = (butlast todo, acc)"
      using todo_ne last_eq True by (simp add: st bisection_gmp_step_def Let_def)
    show ?thesis unfolding fstst sndst stf using old_bud ia_pos by simp
  next
    case v0: False
    show ?thesis
    proof (cases "carried_descartes_count Q = 1")
      case True
      have stf: "bisection_gmp_step st = (butlast todo, acc @ [((l, r), k)])"
        using todo_ne last_eq True by (simp add: st bisection_gmp_step_def Let_def)
      show ?thesis unfolding fstst sndst stf using old_bud ia_pos by simp
    next
      case v1: False
      have vf0: "descartes_list_int a b P \<noteq> 0"
        and vf1: "descartes_list_int a b P \<noteq> 1" using v0 v1 count by auto
      have \<delta>_lt: "\<delta> < of_rat b - of_rat a"
      proof (rule ccontr)
        assume "\<not> \<delta> < of_rat b - of_rat a"
        then have "of_rat b - of_rat a \<le> \<delta>" by linarith
        then have "descartes_list_int a b P \<le> 1" using small_fast[OF ab] by simp
        with vf0 vf1 show False by simp
      qed
      have left_lt: "rational_interval_mu \<delta> (a, ?m) < rational_interval_mu \<delta> (a, b)"
        using mu_halve_strict(1)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
        unfolding rational_interval_mu_def by (simp add: of_rat_add of_rat_divide)
      have right_lt: "rational_interval_mu \<delta> (?m, b) < rational_interval_mu \<delta> (a, b)"
        using mu_halve_strict(2)[of \<delta> "of_rat a" "of_rat b"] \<delta>_pos ab \<delta>_lt
        unfolding rational_interval_mu_def by (simp add: of_rat_add of_rat_divide)
      have nl: "node_iv_of l0 r0 k0 ((l + l, l + r), k + 1) = (a, ?m)"
        using node_iv_bisect_left[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
      have nr: "node_iv_of l0 r0 k0 ((l + r, r + r), k + 1) = (?m, b)"
        using node_iv_bisect_right[of l0 r0 k0 l r k] by (simp add: node_iv_of_def a_def b_def)
      have fstf: "fst (bisection_gmp_step st)
          = butlast todo @ [(((l + l, l + r), k + 1), carried_left Q),
                            (((l + r, r + r), k + 1), carried_right Q)]"
        using todo_ne last_eq vf0 vf1 count by (auto simp: st bisection_gmp_step_def Let_def)
      have new_ivs: "todo_ivs l0 r0 k0 (fst (bisection_gmp_step st))
          = todo_ivs l0 r0 k0 (butlast todo) @ [(a, ?m), (?m, b)]"
        by (simp only: fstf todo_ivs_def map_append list.map fst_conv nl nr)
      have new_bud: "?ab (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st)))
          = ?ab (todo_ivs l0 r0 k0 (butlast todo)) + ?ia (a, ?m) + ?ia (?m, b)"
        by (simp add: new_ivs rational_todo_acc_budget_def)
      have child_le: "?ia (a, ?m) + ?ia (?m, b) + 1 \<le> ?ia (a, b)"
        using rational_acc_budget_children_le[OF left_lt right_lt]
        unfolding rational_interval_acc_budget_def by linarith
      have sndf: "int (length (snd (bisection_gmp_step st))) \<le> int (length acc) + 1"
        using todo_ne last_eq vf0 vf1 count by (auto simp: st bisection_gmp_step_def Let_def)
      show ?thesis
        unfolding fstst sndst
        using old_bud new_bud child_le sndf by linarith
    qed
  qed
qed

subsection \<open>Budgets: dyadic-vector \<open>pushable\<close> from the capacity budgets\<close>

text \<open>The 3-tuple dyadic analogues of @{thm interval_vec_pushable2_from_budget_tuple} /
  @{thm interval_vec_pushable_from_budget_tuple}: a nonneg budget headroom on @{term "length lns"}
  yields the \<open>+2\<close> / \<open>+1\<close> push capacity on all three component lists (equal length by the invariant). Kept in
  the leaf so the frozen dyadic-interval base is untouched.\<close>
lemma dyadic_interval_vec_pushable2_from_budget:
  assumes inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and cap: "int (length lns) + B + 2 < int (max_snat LENGTH(gmp_poly_len))"
    and nonneg: "0 \<le> B"
  shows "dyadic_interval_vec_pushable2 (lns, rns, ks)"
  using assms
  unfolding dyadic_interval_vec_invar_def dyadic_interval_vec_pushable2_def
  by auto

lemma dyadic_interval_vec_pushable_from_budget:
  assumes inv: "dyadic_interval_vec_invar (lns, rns, ks)"
    and cap: "int (length lns) + B + 1 < int (max_snat LENGTH(gmp_poly_len))"
    and nonneg: "0 \<le> B"
  shows "dyadic_interval_vec_pushable (lns, rns, ks)"
  using assms
  unfolding dyadic_interval_vec_invar_def dyadic_interval_vec_pushable_def
  by auto

subsection \<open>Assembly: the WHILEIT step rule\<close>

text \<open>The concrete @{const bisection_loop_step_pre} (the body's typing precondition) follows from the
  \<open>\<alpha>\<close>-stated budget/depth/poly-length conjuncts of @{const bilr_refine_invar} (NOT from \<open>safe_invar\<close>, so this is
  reusable for the result state \<open>st'\<close> to re-establish \<open>safe_invar st'\<close> without circularity). The \<open>pushable\<close>
  ASSERTs come from the size/acc budgets via @{thm dyadic_interval_vec_pushable2_from_budget} /
  @{thm dyadic_interval_vec_pushable_from_budget}; \<open>last ks + 1 < max_snat\<close> from the per-node depth
  bound (\<open>\<mu> \<ge> 0\<close>); the \<open>qtodo\<close> length bounds from the poly-length conjunct + \<open>P\<close> assumptions.\<close>
lemma bilr_imp_step_pre:
  fixes \<delta> :: real
  assumes si: "bisection_loop_state_invar st"
    and cond: "bisection_loop_cond st"
    and szbud: "int (length (bilr_alpha_todo st))
        + rational_todo_append_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st)) + 2
        < int (max_snat LENGTH(gmp_poly_len))"
    and accbud: "int (length (bilr_alpha_acc st))
        + rational_todo_acc_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st)) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    and depth: "\<forall>nd \<in> set (bilr_alpha_todo st).
        snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1
          < max_snat LENGTH(gmp_poly_len)"
    and plen: "\<forall>nd \<in> set (bilr_alpha_todo st). length (snd nd) = length P"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_loop_step_pre st"
proof -
  obtain todo qtodo acc where st0: "st = ((todo, qtodo), acc)" by (cases st) auto
  obtain lns rns ks where todo: "todo = (lns, rns, ks)" by (cases todo) auto
  obtain alns arns aks where acc: "acc = (alns, arns, aks)" by (cases acc) auto
  note dstr = st0 todo acc
  from si have ivT: "dyadic_interval_vec_invar (lns, rns, ks)"
    and ivA: "dyadic_interval_vec_invar (alns, arns, aks)"
    and ltq: "length qtodo = length lns"
    by (auto simp: dstr bisection_loop_state_invar_def)
  from ivT have llr: "length lns = length rns" and llk: "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  from cond have ne: "lns \<noteq> []" by (simp add: dstr bisection_loop_cond_def)
  \<comment> \<open>length of the abstract todo = length lns; nonempty\<close>
  have lenAt: "length (bilr_alpha_todo st) = length lns"
    using bilr_alpha_todo_length[OF si] by (simp add: dstr)
  have Atne: "bilr_alpha_todo st \<noteq> []" using bilr_alpha_cond[OF si] cond by simp
  have lastA: "last (bilr_alpha_todo st) = (((last lns, last rns), last ks), last qtodo)"
    using bilr_alpha_todo_last[OF si[unfolded dstr] ne] by (simp add: dstr)
  have lastA_in: "last (bilr_alpha_todo st) \<in> set (bilr_alpha_todo st)" using Atne by simp
  \<comment> \<open>budget non-negativity\<close>
  have bud_nn: "0 \<le> rational_todo_append_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st))" by simp
  have accbud_nn: "0 \<le> rational_todo_acc_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st))" by simp
  \<comment> \<open>(3) pushable2 on the butlast dyadic vector\<close>
  have iv_bl: "dyadic_interval_vec_invar (butlast lns, butlast rns, butlast ks)"
    using ivT by (auto simp: dyadic_interval_vec_invar_def llr llk)
  have push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
  proof (rule dyadic_interval_vec_pushable2_from_budget[OF iv_bl _ bud_nn])
    have "int (length (butlast lns)) \<le> int (length (bilr_alpha_todo st))"
      using lenAt by (simp add: length_butlast)
    thus "int (length (butlast lns))
        + rational_todo_append_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st)) + 2
        < int (max_snat LENGTH(gmp_poly_len))" using szbud by linarith
  qed
  \<comment> \<open>(4) pushable on the acc vector\<close>
  have lenAa: "length (bilr_alpha_acc st) = length alns"
    using ivA by (simp add: dstr bilr_alpha_acc_def dyadic_interval_vec_triples_length)
  have pushA: "dyadic_interval_vec_pushable (alns, arns, aks)"
  proof (rule dyadic_interval_vec_pushable_from_budget[OF ivA _ accbud_nn])
    show "int (length alns)
        + rational_todo_acc_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st)) + 1
        < int (max_snat LENGTH(gmp_poly_len))" using accbud lenAa by simp
  qed
  \<comment> \<open>(5) length (butlast qtodo) + 2 < max_snat\<close>
  have qne: "qtodo \<noteq> []" using ne ltq by (cases qtodo) auto
  have blq: "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "length (butlast qtodo) + 1 = length lns"
      using qne ltq ne by (cases lns) (auto simp: length_butlast)
    moreover have "int (length lns) + 2 < int (max_snat LENGTH(gmp_poly_len))"
      using szbud bud_nn lenAt by linarith
    ultimately show ?thesis by linarith
  qed
  \<comment> \<open>(6) list_all on qtodo via the poly-length conjunct\<close>
  have qmap: "map snd (bilr_alpha_todo st) = qtodo"
    using ltq llr llk
    by (simp add: dstr bilr_alpha_todo_def dyadic_interval_vec_triples_simps map_snd_zip)
  have listall: "list_all (\<lambda>Q. 0 < length Q
        \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)) qtodo"
    unfolding list_all_iff
  proof (intro ballI)
    fix Q assume "Q \<in> set qtodo"
    then have "Q \<in> set (map snd (bilr_alpha_todo st))" using qmap by simp
    then obtain nd where "nd \<in> set (bilr_alpha_todo st)" and "Q = snd nd" by auto
    then have "length Q = length P" using plen by auto
    thus "0 < length Q \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)"
      using P_len P_bound by simp
  qed
  \<comment> \<open>(7) last ks + 1 < max_snat from the per-node depth bound\<close>
  have lastk: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "snd (fst (last (bilr_alpha_todo st)))
        + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst (last (bilr_alpha_todo st)))) + 1
        < max_snat LENGTH(gmp_poly_len)"
      using depth lastA_in by blast
    then have "last ks
        + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 ((last lns, last rns), last ks)) + 1
        < max_snat LENGTH(gmp_poly_len)" by (simp add: lastA)
    thus ?thesis by simp
  qed
  show ?thesis
    unfolding bisection_loop_step_pre_def
    using si cond push2 pushA blq listall lastk
    by (simp add: dstr)
qed

text \<open>The carried analogue of the endpoint @{thm rational_loop_invar_stepI}: a step result that
  matches @{thm bilr_step_args_spec}'s characterisation projects (via @{thm bilr_step_alpha_eq}) to
  @{const bisection_gmp_step}, so @{const bilr_refine_invar} is preserved (node-inv by @{thm gmp_node_inv_preserved},
  driver-fixpoint by @{thm carried_gmp_main.simps}, the four budget/depth/poly-length conjuncts by the five
  preservation lemmas) and the \<open>\<mu>\<close>-mset measure strictly decreases (@{thm bisection_gmp_step_mu_decreases}).\<close>
lemma bilr_step_result_invar:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and inv: "bilr_refine_invar \<delta> P l0 r0 k0 st0 (((lns, rns, ks), qtodo), (alns, arns, aks))"
    and ne: "lns \<noteq> []"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and vt': "dyadic_interval_vec_invar todo'"
    and tt': "dyadic_interval_vec_triples todo' =
        (if 2 \<le> carried_descartes_count (last qtodo)
         then dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) @
                [((last lns + last lns, last lns + last rns), last ks + 1),
                 ((last lns + last rns, last rns + last rns), last ks + 1)]
         else dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))"
    and qt': "qtodo' = (if 2 \<le> carried_descartes_count (last qtodo)
                then butlast qtodo @
                       [carried_left (last qtodo), carried_right (last qtodo)]
                else butlast qtodo)"
    and at': "acc' = (if carried_descartes_count (last qtodo) = 0 then (alns, arns, aks)
              else if carried_descartes_count (last qtodo) = 1
                   then (alns @ [last lns], arns @ [last rns], aks @ [last ks])
              else if bisection_mid_is_root (last qtodo)
                   then (alns @ [last lns + last rns], arns @ [last lns + last rns], aks @ [last ks + 1])
                   else (alns, arns, aks))"
  shows "bilr_refine_invar \<delta> P l0 r0 k0 st0 ((todo', qtodo'), acc')
       \<and> bilr_alpha ((todo', qtodo'), acc')
           = bisection_gmp_step (bilr_alpha (((lns, rns, ks), qtodo), (alns, arns, aks)))
       \<and> rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo ((todo', qtodo'), acc')))
         < rational_todo_mu_mset \<delta>
             (todo_ivs l0 r0 k0 (bilr_alpha_todo (((lns, rns, ks), qtodo), (alns, arns, aks))))"
proof -
  let ?st = "(((lns, rns, ks), qtodo), (alns, arns, aks))"
  let ?st' = "((todo', qtodo'), acc')"
  \<comment> \<open>extract the invariant conjuncts of @{term ?st}\<close>
  from inv have safe: "bisection_loop_safe_invar ?st"
    and ndinv: "\<forall>nd \<in> set (bilr_alpha_todo ?st). gmp_node_inv P l0 r0 k0 nd"
    and main_eq: "carried_gmp_main (bilr_alpha ?st) = carried_gmp_main st0"
    and szbud: "int (length (bilr_alpha_todo ?st))
        + rational_todo_append_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo ?st)) + 2
        < int (max_snat LENGTH(gmp_poly_len))"
    and accbud: "int (length (bilr_alpha_acc ?st))
        + rational_todo_acc_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo ?st)) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    and depth: "\<forall>nd \<in> set (bilr_alpha_todo ?st).
        snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1
          < max_snat LENGTH(gmp_poly_len)"
    and plen: "\<forall>nd \<in> set (bilr_alpha_todo ?st). length (snd nd) = length P"
    unfolding bilr_refine_invar_def by blast+
  from safe have si: "bisection_loop_state_invar ?st"
    by (simp add: bisection_loop_safe_invar_def)
  have cond: "bisection_loop_cond ?st"
    by (simp add: bisection_loop_cond_def ne)
  \<comment> \<open>nonemptiness of the abstract todo (for the driver-step + measure)\<close>
  have At_ne: "bilr_alpha_todo ?st \<noteq> []" using bilr_alpha_cond[OF si] cond by simp
  have fcl: "fst (bilr_alpha ?st) = bilr_alpha_todo ?st" by (simp add: bilr_alpha_def)
  have scl: "snd (bilr_alpha ?st) = bilr_alpha_acc ?st" by (simp add: bilr_alpha_def)
  \<comment> \<open>the \<open>\<alpha>\<close>-equation: the result projects to @{const bisection_gmp_step}\<close>
  have alpha: "bilr_alpha ?st' = bisection_gmp_step (bilr_alpha ?st)"
    by (rule bilr_step_alpha_eq[OF si ne tt' qt' at'])
  have at_eq: "bilr_alpha_todo ?st' = fst (bisection_gmp_step (bilr_alpha ?st))"
    using arg_cong[OF alpha, of fst] by (simp add: bilr_alpha_def)
  have aa_eq: "bilr_alpha_acc ?st' = snd (bisection_gmp_step (bilr_alpha ?st))"
    using arg_cong[OF alpha, of snd] by (simp add: bilr_alpha_def)
  have ndinv_a: "\<forall>e \<in> set (fst (bilr_alpha ?st)). gmp_node_inv P l0 r0 k0 e"
    using ndinv by (simp add: fcl)
  \<comment> \<open>(2) node-inv preserved\<close>
  have ndinv': "\<forall>nd \<in> set (bilr_alpha_todo ?st'). gmp_node_inv P l0 r0 k0 nd"
    using gmp_node_inv_preserved[OF P_len ndinv_a] by (simp add: at_eq)
  \<comment> \<open>(3) driver-fixpoint preserved (one @{const carried_gmp_main} unfold)\<close>
  have main': "carried_gmp_main (bilr_alpha ?st') = carried_gmp_main st0"
  proof -
    obtain x xs where ct: "bilr_alpha_todo ?st = x # xs"
      using At_ne by (cases "bilr_alpha_todo ?st") auto
    have "bilr_alpha ?st = (x # xs, bilr_alpha_acc ?st)" using ct by (simp add: bilr_alpha_def)
    hence "carried_gmp_main (bilr_alpha ?st) = carried_gmp_main (bisection_gmp_step (bilr_alpha ?st))"
      by (simp add: carried_gmp_main.simps)
    thus ?thesis using alpha main_eq by simp
  qed
  \<comment> \<open>(4) size budget preserved\<close>
  have szbud': "int (length (bilr_alpha_todo ?st'))
      + rational_todo_append_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo ?st')) + 2
      < int (max_snat LENGTH(gmp_poly_len))"
    using carried_step_preserves_sizebudget[OF \<delta>_pos small_fast ndinv_a] szbud
    by (simp add: at_eq fcl)
  \<comment> \<open>(5) acc budget preserved\<close>
  have accbud': "int (length (bilr_alpha_acc ?st'))
      + rational_todo_acc_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo ?st')) + 1
      < int (max_snat LENGTH(gmp_poly_len))"
    using carried_step_preserves_accbudget[OF \<delta>_pos small_fast ndinv_a] accbud
    by (simp add: at_eq aa_eq fcl scl)
  \<comment> \<open>(6) depth bound preserved\<close>
  have depth': "\<forall>nd \<in> set (bilr_alpha_todo ?st').
      snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1
        < max_snat LENGTH(gmp_poly_len)"
    using carried_step_preserves_depth[OF \<delta>_pos small_fast ndinv_a, where B = "max_snat LENGTH(gmp_poly_len)"]
          depth by (simp add: at_eq fcl)
  \<comment> \<open>(7) poly-length preserved\<close>
  have plen': "\<forall>nd \<in> set (bilr_alpha_todo ?st'). length (snd nd) = length P"
    using carried_step_preserves_polylen[where st = "bilr_alpha ?st" and n = "length P"] plen
    by (simp add: at_eq fcl)
  \<comment> \<open>(1) concrete data invariant @{const bisection_loop_safe_invar} for @{term ?st'}\<close>
  from si have ivA: "dyadic_interval_vec_invar (alns, arns, aks)"
    and ivT: "dyadic_interval_vec_invar (lns, rns, ks)"
    and ltq: "length qtodo = length lns"
    by (auto simp: bisection_loop_state_invar_def)
  from ivT have llr: "length lns = length rns" and llk: "length lns = length ks"
    by (auto simp: dyadic_interval_vec_invar_def)
  have ivA': "dyadic_interval_vec_invar acc'"
    using at' ivA by (auto simp: dyadic_interval_vec_invar_def split: if_splits)
  have lqt': "length qtodo' = length (dyadic_interval_vec_triples todo')"
  proof -
    have blq_len: "length (dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))
        = length (butlast qtodo)"
      using llr llk ltq by (simp add: dyadic_interval_vec_triples_simps length_zip)
    show ?thesis using tt' qt' blq_len by (simp split: if_splits)
  qed
  obtain tlns trns tks where todo'_eq: "todo' = (tlns, trns, tks)" by (cases todo')
  have siv': "bisection_loop_state_invar ?st'"
    using vt' ivA' lqt'
    by (simp add: bisection_loop_state_invar_def todo'_eq
        dyadic_interval_vec_triples_length[OF vt'[unfolded todo'_eq]])
  have steppre': "bisection_loop_cond ?st' \<Longrightarrow> bisection_loop_step_pre ?st'"
    by (rule bilr_imp_step_pre[OF siv' _ szbud' accbud' depth' plen' P_len P_bound])
  have safe': "bisection_loop_safe_invar ?st'"
    using siv' steppre' by (simp add: bisection_loop_safe_invar_def)
  \<comment> \<open>assemble the invariant\<close>
  have invar': "bilr_refine_invar \<delta> P l0 r0 k0 st0 ?st'"
    unfolding bilr_refine_invar_def
    using safe' ndinv' main' szbud' accbud' depth' plen' by blast
  \<comment> \<open>the measure strictly decreases\<close>
  have meas: "rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo ?st'))
       < rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo ?st))"
    using bisection_gmp_step_mu_decreases[OF \<delta>_pos small_fast _ ndinv_a] At_ne
    by (simp add: at_eq fcl)
  show ?thesis using invar' alpha meas by blast
qed

text \<open>The WHILEIT body step rule: under @{const bilr_refine_invar} and the loop condition, the concrete
  @{const bisection_loop_step_monadic} refines a pure @{const bisection_gmp_step} that preserves the invariant and
  strictly decreases the \<open>\<mu>\<close>-mset measure. Assembles @{thm bilr_step_args_spec} (the concrete characterisation,
  its nine ASSERT preconditions discharged from @{thm bilr_imp_step_pre}) with @{thm bilr_step_result_invar} (the
  pure invariant-preservation), weakening the result \<open>SPEC\<close> via @{thm pw_le_iff}.\<close>
lemma bilr_step_refine:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and inv: "bilr_refine_invar \<delta> P l0 r0 k0 st0 st"
    and cond: "bisection_loop_cond st"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_loop_step_monadic st \<le> SPEC (\<lambda>st'.
      bilr_refine_invar \<delta> P l0 r0 k0 st0 st' \<and>
      bilr_alpha st' = bisection_gmp_step (bilr_alpha st) \<and>
      rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st'))
        < rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st)))"
proof -
  obtain todo qd acc where st1: "st = ((todo, qd), acc)" by (cases st) auto
  obtain lns rns ks where todoeq: "todo = (lns, rns, ks)" by (cases todo) auto
  obtain alns arns aks where acceq: "acc = (alns, arns, aks)" by (cases acc) auto
  have st: "st = (((lns, rns, ks), qd), (alns, arns, aks))" by (simp add: st1 todoeq acceq)
  \<comment> \<open>extract the conjuncts needed to discharge @{const bisection_loop_step_pre}\<close>
  from inv have safe: "bisection_loop_safe_invar st"
    and szbud: "int (length (bilr_alpha_todo st))
        + rational_todo_append_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st)) + 2
        < int (max_snat LENGTH(gmp_poly_len))"
    and accbud: "int (length (bilr_alpha_acc st))
        + rational_todo_acc_budget \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st)) + 1
        < int (max_snat LENGTH(gmp_poly_len))"
    and depth: "\<forall>nd \<in> set (bilr_alpha_todo st).
        snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l0 r0 k0 (fst nd)) + 1
          < max_snat LENGTH(gmp_poly_len)"
    and plen: "\<forall>nd \<in> set (bilr_alpha_todo st). length (snd nd) = length P"
    unfolding bilr_refine_invar_def by blast+
  from safe have si: "bisection_loop_state_invar st"
    by (simp add: bisection_loop_safe_invar_def)
  have steppre: "bisection_loop_step_pre st"
    by (rule bilr_imp_step_pre[OF si cond szbud accbud depth plen P_len P_bound])
  \<comment> \<open>the nine @{thm bilr_step_args_spec} preconditions\<close>
  have ivT: "dyadic_interval_vec_invar (lns, rns, ks)" and lq: "length qd = length lns"
    using si by (auto simp: st bisection_loop_state_invar_def)
  have ne: "lns \<noteq> []" using cond by (simp add: st bisection_loop_cond_def)
  have qne: "qd \<noteq> []" using ne lq by (cases qd) auto
  have lqin: "last qd \<in> set qd" using qne by simp
  from steppre have push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    and pushA: "dyadic_interval_vec_pushable (alns, arns, aks)"
    and blq: "length (butlast qd) + 2 < max_snat LENGTH(gmp_poly_len)"
    and listall: "list_all (\<lambda>Q. 0 < length Q \<and> length Q + 1 < max_snat LENGTH(gmp_poly_len)) qd"
    and lastk: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
    by (simp_all add: st bisection_loop_step_pre_def)
  have lqp: "0 < length (last qd) \<and> length (last qd) + 1 < max_snat LENGTH(gmp_poly_len)"
    using listall[unfolded list_all_iff, rule_format, OF lqin] .
  \<comment> \<open>the concrete step matches the characterisation\<close>
  have argspec: "bisection_loop_step_monadic st \<le> SPEC (\<lambda>((todo', qtodo'), acc').
      dyadic_interval_vec_invar todo' \<and>
      dyadic_interval_vec_triples todo' =
        (if 2 \<le> carried_descartes_count (last qd)
         then dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) @
                [((last lns + last lns, last lns + last rns), last ks + 1),
                 ((last lns + last rns, last rns + last rns), last ks + 1)]
         else dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks)) \<and>
      qtodo' = (if 2 \<le> carried_descartes_count (last qd)
                then butlast qd @
                       [carried_left (last qd), carried_right (last qd)]
                else butlast qd) \<and>
      acc' = (if carried_descartes_count (last qd) = 0 then (alns, arns, aks)
              else if carried_descartes_count (last qd) = 1
                   then (alns @ [last lns], arns @ [last rns], aks @ [last ks])
              else if bisection_mid_is_root (last qd)
                   then (alns @ [last lns + last rns], arns @ [last lns + last rns], aks @ [last ks + 1])
                   else (alns, arns, aks)))"
    unfolding st bisection_loop_step_monadic_def PR_CONST_def prod.case
    by (rule bilr_step_args_spec[OF ivT ne lq lqp[THEN conjunct1] lqp[THEN conjunct2]
          lastk push2 blq pushA])
  \<comment> \<open>weaken the characterisation to the invariant + measure via @{thm bilr_step_result_invar}; a structured
     proof (NOT clarsimp) so the exact \<open>if\<close>-equations reach @{thm bilr_step_result_invar} un-normalised\<close>
  show ?thesis
    unfolding st
  proof (rule SPEC_cons_rule[OF argspec[unfolded st]], goal_cases)
    case (1 r)
    obtain todo' qtodo' acc' where r: "r = ((todo', qtodo'), acc')" by (cases r) auto
    from "1" have
      vt': "dyadic_interval_vec_invar todo'" and
      tt': "dyadic_interval_vec_triples todo' =
        (if 2 \<le> carried_descartes_count (last qd)
         then dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks) @
                [((last lns + last lns, last lns + last rns), last ks + 1),
                 ((last lns + last rns, last rns + last rns), last ks + 1)]
         else dyadic_interval_vec_triples (butlast lns, butlast rns, butlast ks))" and
      qt': "qtodo' = (if 2 \<le> carried_descartes_count (last qd)
                then butlast qd @ [carried_left (last qd), carried_right (last qd)]
                else butlast qd)" and
      at': "acc' = (if carried_descartes_count (last qd) = 0 then (alns, arns, aks)
              else if carried_descartes_count (last qd) = 1
                   then (alns @ [last lns], arns @ [last rns], aks @ [last ks])
              else if bisection_mid_is_root (last qd)
                   then (alns @ [last lns + last rns], arns @ [last lns + last rns], aks @ [last ks + 1])
                   else (alns, arns, aks))"
      by (simp_all add: r)
    show ?case
      unfolding r
      by (rule bilr_step_result_invar[OF \<delta>_pos small_fast inv[unfolded st] ne P_len P_bound vt' tt' qt' at'])
  qed
qed

subsection \<open>Assembly: the WHILEIT loop specification\<close>

text \<open>The \<open>\<mu>\<close>-mset measure relation is well-founded (inverse image of the wf multiset order on @{typ "nat multiset"}).\<close>
lemma bilr_mu_mset_rel_wf:
  "wf {(st' :: bisection_loop_state, st).
      rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st')) <
      rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st))}"
proof -
  have wf_ms_pred: "wfp ((<) :: nat multiset \<Rightarrow> nat multiset \<Rightarrow> bool)" by simp
  have wf_ms: "wf ({(x, y). x < y} :: (nat multiset \<times> nat multiset) set)"
    using wf_ms_pred by (simp add: wfp_def)
  show ?thesis
    using wf_inv_image[OF wf_ms,
      of "\<lambda>st. rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st))"]
    by (simp add: inv_image_def)
qed

text \<open>The loop body (the @{const bisection_loop_cond}-guarded @{const bisection_loop_step_monadic}) wrapped
  into the well-founded-relation shape @{thm bilr_step_refine} requires for @{thm WHILEIT_rule}.\<close>
lemma bilr_body_checked_rel_spec:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and inv: "bilr_refine_invar \<delta> P l0 r0 k0 st0 st"
    and cond: "bisection_loop_cond st"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_loop_body_checked_monadic st \<le>
    SPEC (\<lambda>st'. bilr_refine_invar \<delta> P l0 r0 k0 st0 st' \<and>
      (st', st) \<in> {(st', st).
        rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st')) <
        rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (bilr_alpha_todo st))})"
proof -
  have bc: "bisection_loop_body_checked_monadic st = bisection_loop_step_monadic st"
    using cond by (simp add: bisection_loop_body_checked_monadic_def PR_CONST_def)
  show ?thesis
    unfolding bc
    using bilr_step_refine[OF \<delta>_pos small_fast inv cond P_len P_bound]
    by (auto simp: pw_le_iff refine_pw_simps)
qed

text \<open>\<^bold>\<open>Why the loop specification goes through a data refinement.\<close> The concrete loop should refine the
  pure driver fixpoint: from a state satisfying @{const bilr_refine_invar},
  @{const bisection_loop_stateful_monadic} terminates with the invariant still holding and the
  abstract todo drained, so (via @{thm bilr_invar_exit}) the projected acc is the driver's final acc.

  @{const bisection_loop_stateful_monadic} is a \<open>WHILEIT\<close> annotated with
  @{const bisection_loop_safe_invar} (for the Sepref body typing). \<open>refine_vcg WHILEIT_rule\<close> uses the
  annotation as the loop invariant (the body obligation is \<open>safe_invar s \<Longrightarrow> cond s \<Longrightarrow> \<dots>\<close>), not a
  supplied \<open>I = bilr_refine_invar\<close>, and \<open>WHILEIT_weaken\<close> gives \<open>WHILEIT (strong) \<le> WHILEIT (weak)\<close>,
  the wrong direction. \<open>safe_invar\<close> alone lacks the @{const carried_gmp_main} fixpoint conjunct, so a
  direct \<open>SPEC\<close> proof does not close. Instead, an abstract carried loop is introduced and
  \<open>bisection_loop_stateful_monadic s0 \<le> \<Down>(br bilr_alpha \<dots>) (abstract_loop (bilr_alpha s0))\<close> is proved:
  the concrete \<open>safe_invar\<close> annotation stays on the concrete side and correctness is carried by the
  abstract loop, a \<open>WHILET\<close> whose invariant is free. The helpers @{thm bilr_mu_mset_rel_wf} and
  @{thm bilr_body_checked_rel_spec} and the step rule @{thm [source] bilr_step_refine} are used
  there.\<close>

subsection \<open>Assembly: the abstract carried loop (a WHILET with free invariant)\<close>

text \<open>The abstract carried loop iterates @{const bisection_gmp_step} until the todo drains. As a @{const WHILET}
  (no baked-in invariant) @{thm [source] WHILET_rule} takes the full invariant freely, so this computes
  @{const carried_gmp_main} unobstructed by the concrete @{const bisection_loop_safe_invar} annotation.\<close>
definition bilr_loop_abs :: "bisection_gmp_state \<Rightarrow> bisection_gmp_state nres" where
"bilr_loop_abs st0 \<equiv> WHILET (\<lambda>st. fst st \<noteq> []) (\<lambda>st. RETURN (bisection_gmp_step st)) st0"

text \<open>The abstract \<open>\<mu>\<close>-mset measure relation (over the abstract todo @{term "fst st"}) is well-founded.\<close>
lemma bilr_abs_mu_mset_rel_wf:
  "wf {(st' :: bisection_gmp_state, st).
      rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st')) <
      rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st))}"
proof -
  have wf_ms_pred: "wfp ((<) :: nat multiset \<Rightarrow> nat multiset \<Rightarrow> bool)" by simp
  have wf_ms: "wf ({(x, y). x < y} :: (nat multiset \<times> nat multiset) set)"
    using wf_ms_pred by (simp add: wfp_def)
  show ?thesis
    using wf_inv_image[OF wf_ms,
      of "\<lambda>st. rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st))"]
    by (simp add: inv_image_def)
qed

text \<open>The body VC: one @{const bisection_gmp_step} preserves the invariant (driver-fixpoint via
  @{thm carried_gmp_main.simps}, node-inv via @{thm gmp_node_inv_preserved}) and decreases the \<open>\<mu>\<close>-mset
  (@{thm bisection_gmp_step_mu_decreases}).\<close>
lemma bilr_loop_abs_body:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and P_len: "0 < length P"
    and inv: "carried_gmp_main st = carried_gmp_main st0
              \<and> (\<forall>nd \<in> set (fst st). gmp_node_inv P l0 r0 k0 nd)"
    and ne: "fst st \<noteq> []"
  shows "RETURN (bisection_gmp_step st) \<le> SPEC (\<lambda>st'.
      (carried_gmp_main st' = carried_gmp_main st0
        \<and> (\<forall>nd \<in> set (fst st'). gmp_node_inv P l0 r0 k0 nd)) \<and>
      (st', st) \<in> {(st', st).
        rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st')) <
        rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st))})"
proof -
  from inv have main_eq: "carried_gmp_main st = carried_gmp_main st0"
    and ninv: "\<forall>nd \<in> set (fst st). gmp_node_inv P l0 r0 k0 nd" by auto
  have step_main: "carried_gmp_main (bisection_gmp_step st) = carried_gmp_main st0"
  proof -
    obtain x xs where "fst st = x # xs" using ne by (cases "fst st") auto
    hence "carried_gmp_main st = carried_gmp_main (bisection_gmp_step st)"
      by (cases st) (simp add: carried_gmp_main.simps)
    thus ?thesis using main_eq by simp
  qed
  have step_ninv: "\<forall>nd \<in> set (fst (bisection_gmp_step st)). gmp_node_inv P l0 r0 k0 nd"
    by (rule gmp_node_inv_preserved[OF P_len ninv])
  have step_meas: "rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst (bisection_gmp_step st)))
      < rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st))"
    by (rule bisection_gmp_step_mu_decreases[OF \<delta>_pos small_fast ne ninv])
  show ?thesis using step_main step_ninv step_meas by simp
qed

text \<open>The exit VC: when the todo drains, @{const carried_gmp_main} of the state is the state itself, so the acc is
  the driver's final acc.\<close>
lemma bilr_loop_abs_exit:
  assumes inv: "carried_gmp_main st = carried_gmp_main st0
                \<and> (\<forall>nd \<in> set (fst st). gmp_node_inv P l0 r0 k0 nd)"
    and empty: "\<not> (fst st \<noteq> [])"
  shows "fst st = [] \<and> snd st = snd (carried_gmp_main st0)"
proof -
  from inv have main_eq: "carried_gmp_main st = carried_gmp_main st0" by simp
  obtain a b where st: "st = (a, b)" by (cases st)
  have e: "a = []" using empty by (simp add: st)
  have "carried_gmp_main st = st" by (simp add: st e carried_gmp_main_Nil)
  hence seq: "st = carried_gmp_main st0" using main_eq by simp
  have "fst st = []" using e st by simp
  moreover have "snd st = snd (carried_gmp_main st0)" using seq by simp
  ultimately show ?thesis by blast
qed

text \<open>@{const bilr_loop_abs} computes the driver fixpoint: from a node-inv todo it terminates with the todo drained
  and the acc equal to @{const carried_gmp_main}'s final acc.\<close>
lemma bilr_loop_abs_spec:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and P_len: "0 < length P"
    and ninv0: "\<forall>nd \<in> set (fst st0). gmp_node_inv P l0 r0 k0 nd"
  shows "bilr_loop_abs st0 \<le> SPEC (\<lambda>st. fst st = [] \<and> snd st = snd (carried_gmp_main st0))"
  unfolding bilr_loop_abs_def
  apply (rule WHILET_rule[
    where I="\<lambda>st. carried_gmp_main st = carried_gmp_main st0
                  \<and> (\<forall>nd \<in> set (fst st). gmp_node_inv P l0 r0 k0 nd)"
      and R="{(st', st).
        rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st')) <
        rational_todo_mu_mset \<delta> (todo_ivs l0 r0 k0 (fst st))}"])
  subgoal by (rule bilr_abs_mu_mset_rel_wf)
  subgoal using ninv0 by simp
  subgoal by (rule bilr_loop_abs_body[OF \<delta>_pos small_fast P_len]; assumption)
  subgoal by (rule bilr_loop_abs_exit; assumption)
  done

subsection \<open>Assembly: the data refinement \<open>concrete loop \<le> \<Down>(br \<alpha>) abstract loop\<close>\<close>

text \<open>The @{const ASSN_ANNOT}/@{const RETURN} prefix of @{const bisection_loop_stateful_monadic} is identity, so the
  loop reduces to the bare @{const WHILEIT}.\<close>
lemma loop_stateful_unfold:
  "bisection_loop_stateful_monadic s0 = WHILEIT bisection_loop_safe_invar
      bisection_loop_cond bisection_loop_body_checked_monadic s0"
  unfolding bisection_loop_stateful_monadic_def PR_CONST_def ASSN_ANNOT_def by simp

text \<open>The concrete @{const bisection_loop_stateful_monadic} (annotated with the weak @{const bisection_loop_safe_invar})
  data-refines the abstract @{const bilr_loop_abs} under @{term "br bilr_alpha (bilr_refine_invar \<delta> P l0 r0 k0 st0)"} —
  the relation that carries @{const bilr_refine_invar} on the concrete side. @{thm WHILEIT_refine}'s four obligations:
  the seed is related (@{thm in_br_conv}, the seed invariant); the concrete annotation @{const bisection_loop_safe_invar}
  follows from @{const bilr_refine_invar} (so the asserts pass); the conditions agree (@{thm bilr_alpha_cond}); and the body
  refines via @{thm bilr_step_refine} (its \<open>\<alpha>\<close>-equation result feeds @{thm conc_fun_RETURN}).\<close>
lemma bilr_loop_stateful_dref:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and init: "bilr_refine_invar \<delta> P l0 r0 k0 st0 s0"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_loop_stateful_monadic s0
       \<le> \<Down>(br bilr_alpha (bilr_refine_invar \<delta> P l0 r0 k0 st0)) (bilr_loop_abs (bilr_alpha s0))"
  unfolding loop_stateful_unfold bilr_loop_abs_def WHILET_def
  apply (rule WHILEIT_refine[where R="br bilr_alpha (bilr_refine_invar \<delta> P l0 r0 k0 st0)"])
  subgoal \<comment> \<open>seed related\<close>
    using init by (simp add: in_br_conv)
  subgoal \<comment> \<open>concrete annotation from the abstract invariant\<close>
    by (auto simp: in_br_conv bilr_refine_invar_def)
  subgoal for s s' \<comment> \<open>conditions agree\<close>
  proof -
    assume R: "(s, s') \<in> br bilr_alpha (bilr_refine_invar \<delta> P l0 r0 k0 st0)"
    from R have sa: "s' = bilr_alpha s" and inv_s: "bilr_refine_invar \<delta> P l0 r0 k0 st0 s"
      by (auto simp: in_br_conv)
    from inv_s have si: "bisection_loop_state_invar s"
      by (simp add: bilr_refine_invar_def bisection_loop_safe_invar_def)
    show "bisection_loop_cond s = (fst s' \<noteq> [])"
      using bilr_alpha_cond[OF si] by (simp add: sa bilr_alpha_def)
  qed
  subgoal for s s' \<comment> \<open>body refines\<close>
  proof -
    assume R: "(s, s') \<in> br bilr_alpha (bilr_refine_invar \<delta> P l0 r0 k0 st0)"
      and bs: "bisection_loop_cond s"
    from R have sa: "s' = bilr_alpha s" and inv_s: "bilr_refine_invar \<delta> P l0 r0 k0 st0 s"
      by (auto simp: in_br_conv)
    have bc: "bisection_loop_body_checked_monadic s = bisection_loop_step_monadic s"
      using bs by (simp add: bisection_loop_body_checked_monadic_def PR_CONST_def)
    have "bisection_loop_step_monadic s \<le> SPEC (\<lambda>c.
        bisection_gmp_step (bilr_alpha s) = bilr_alpha c \<and> bilr_refine_invar \<delta> P l0 r0 k0 st0 c)"
      using bilr_step_refine[OF \<delta>_pos small_fast inv_s bs P_len P_bound]
      by (auto simp: pw_le_iff refine_pw_simps)
    thus "bisection_loop_body_checked_monadic s
        \<le> \<Down>(br bilr_alpha (bilr_refine_invar \<delta> P l0 r0 k0 st0)) (RETURN (bisection_gmp_step s'))"
      unfolding bc sa by (simp add: conc_fun_RETURN in_br_conv)
  qed
  done

text \<open>Composing @{thm bilr_loop_stateful_dref} with @{thm bilr_loop_abs_spec} (through \<open>\<Down>\<close>-monotonicity): the
  concrete loop terminates with the invariant holding, the abstract todo drained, and the projected acc equal to
  the pure driver's final acc. This is the loop spec the direct-SPEC route could not reach.\<close>
lemma bilr_loop_stateful_spec:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and init: "bilr_refine_invar \<delta> P l0 r0 k0 st0 s0"
    and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
  shows "bisection_loop_stateful_monadic s0 \<le> SPEC (\<lambda>c.
      bilr_refine_invar \<delta> P l0 r0 k0 st0 c \<and> bilr_alpha_todo c = []
      \<and> bilr_alpha_acc c = snd (carried_gmp_main (bilr_alpha s0)))"
proof -
  have ninv0: "\<forall>nd \<in> set (fst (bilr_alpha s0)). gmp_node_inv P l0 r0 k0 nd"
    using init by (auto simp: bilr_refine_invar_def bilr_alpha_def)
  have "bisection_loop_stateful_monadic s0
      \<le> \<Down>(br bilr_alpha (bilr_refine_invar \<delta> P l0 r0 k0 st0)) (bilr_loop_abs (bilr_alpha s0))"
    by (rule bilr_loop_stateful_dref[OF \<delta>_pos small_fast init P_len P_bound])
  also have "\<dots> \<le> \<Down>(br bilr_alpha (bilr_refine_invar \<delta> P l0 r0 k0 st0))
      (SPEC (\<lambda>st. fst st = [] \<and> snd st = snd (carried_gmp_main (bilr_alpha s0))))"
    by (rule monoD[OF conc_fun_mono]) (rule bilr_loop_abs_spec[OF \<delta>_pos small_fast P_len ninv0])
  also have "\<dots> \<le> SPEC (\<lambda>c. bilr_refine_invar \<delta> P l0 r0 k0 st0 c \<and> bilr_alpha_todo c = []
      \<and> bilr_alpha_acc c = snd (carried_gmp_main (bilr_alpha s0)))"
    by (auto simp: pw_le_iff refine_pw_simps in_br_conv bilr_alpha_def)
  finally show ?thesis .
qed

subsection \<open>Assembly: the seed satisfies the refinement invariant\<close>

text \<open>The main-list seed state \<open>((([l_num],[r_num],[k]),[P]),([],[],[]))\<close> projects to the driver seed
  \<open>([(((l_num,r_num),k),P)],[])\<close> and satisfies @{const bilr_refine_invar} with the reference \<open>st0\<close>
  taken as its own projection (so the driver-fixpoint conjunct is reflexive). The node invariant is
  the seed fact @{thm carried_repr_init} (the root maps to \<open>[0,1]\<close> by \<open>node01\<close>); the snat budgets
  reduce to a capacity bound on the initial interval's \<open>\<mu>\<close>; @{const bisection_loop_step_pre} follows
  via @{thm bilr_imp_step_pre}.\<close>
lemma bilr_seed_invar:
  fixes \<delta> :: real
  assumes lr: "l_num < r_num"
    and len: "0 < length P"
    and lenb: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and cap: "int (2 ^ Suc (rational_interval_mu \<delta> (0, 1))) + 1
              < int (max_snat LENGTH(gmp_poly_len))"
  shows "bilr_refine_invar \<delta> P l_num r_num k
           (bilr_alpha (((([l_num], [r_num], [k]), [P]), ([], [], [])) :: bisection_loop_state))
           ((([l_num], [r_num], [k]), [P]), ([], [], []))"
proof -
  let ?s0 = "((([l_num], [r_num], [k]), [P]), ([], [], [])) :: bisection_loop_state"
  have at0: "bilr_alpha_todo ?s0 = [(((l_num, r_num), k), P)]"
    by (simp add: bilr_alpha_todo_def dyadic_interval_vec_triples_simps)
  have aa0: "bilr_alpha_acc ?s0 = []"
    by (simp add: bilr_alpha_acc_def dyadic_interval_vec_triples_simps)
  have node01: "node_iv l_num r_num k l_num r_num k = (0, 1)"
  proof -
    have "dyadic_rat l_num k < dyadic_rat r_num k"
      using lr by (simp add: dyadic_rat_def divide_strict_right_mono)
    hence "dyadic_rat r_num k - dyadic_rat l_num k \<noteq> 0" by simp
    thus ?thesis by (simp add: node_iv_def Let_def)
  qed
  have niv0: "node_iv_of l_num r_num k ((l_num, r_num), k) = (0, 1)"
    by (simp add: node_iv_of_def node01)
  have unit01: "unit_dyadic (0 :: rat, 1 :: rat)"
    unfolding unit_dyadic_def by (auto intro!: exI[of _ "0 :: int"] exI[of _ "0 :: nat"])
  have ndinv: "\<forall>nd \<in> set (bilr_alpha_todo ?s0). gmp_node_inv P l_num r_num k nd"
    by (simp add: at0 gmp_node_inv_def niv0 carried_repr_init unit01)
  have tivs0: "todo_ivs l_num r_num k [(((l_num, r_num), k), P)] = [(0, 1)]"
    by (simp add: todo_ivs_def niv0)
  have si: "bisection_loop_state_invar ?s0"
    by (simp add: bisection_loop_state_invar_def dyadic_interval_vec_invar_def)
  have szbud: "int (length (bilr_alpha_todo ?s0))
      + rational_todo_append_budget \<delta> (todo_ivs l_num r_num k (bilr_alpha_todo ?s0)) + 2
      < int (max_snat LENGTH(gmp_poly_len))"
    using cap by (simp add: at0 tivs0 rational_todo_append_budget_def
        rational_interval_todo_budget_def)
  have accbud: "int (length (bilr_alpha_acc ?s0))
      + rational_todo_acc_budget \<delta> (todo_ivs l_num r_num k (bilr_alpha_todo ?s0)) + 1
      < int (max_snat LENGTH(gmp_poly_len))"
    using cap by (simp add: aa0 at0 tivs0 rational_todo_acc_budget_def
        rational_interval_acc_budget_def)
  have depth: "\<forall>nd \<in> set (bilr_alpha_todo ?s0).
      snd (fst nd) + rational_interval_mu \<delta> (node_iv_of l_num r_num k (fst nd)) + 1
        < max_snat LENGTH(gmp_poly_len)"
    using dcap by (simp add: at0 niv0)
  have plen: "\<forall>nd \<in> set (bilr_alpha_todo ?s0). length (snd nd) = length P"
    by (simp add: at0)
  have cond: "bisection_loop_cond ?s0"
    by (simp add: bisection_loop_cond_def)
  have steppre: "bisection_loop_step_pre ?s0"
    by (rule bilr_imp_step_pre[OF si cond szbud accbud depth plen len lenb])
  have safe: "bisection_loop_safe_invar ?s0"
    by (simp add: bisection_loop_safe_invar_def si steppre)
  show ?thesis
    unfolding bilr_refine_invar_def
    using safe ndinv szbud accbud depth plen by (simp add: bilr_alpha_def)
qed

subsection \<open>Capstone: the seeded loop isolates the roots\<close>

text \<open>End to end: running @{const bisection_loop_stateful_monadic} from the main-list seed drains the
  todo and leaves an acc that projects (via @{const acc_ivs}, the @{const node_iv} interpretation) to
  exactly @{term "mset (dsc_int 0 1 (Poly P))"}. Combines @{thm bilr_seed_invar} (the seed invariant),
  @{thm bilr_loop_stateful_spec} (the loop drains to the driver fixpoint), and
  @{thm carried_gmp_main_seed_mset_dsc_int} (the driver fixpoint is the abstract Descartes
  multiset).\<close>
lemma bilr_loop_stateful_seed_correct:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and lenb: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and cap: "int (2 ^ Suc (rational_interval_mu \<delta> (0, 1))) + 1
              < int (max_snat LENGTH(gmp_poly_len))"
    and lr: "l_num < r_num"
    and dom: "dsc_dom (degree (Poly P), of_rat 0, of_rat 1, map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
  shows "bisection_loop_stateful_monadic ((([l_num], [r_num], [k]), [P]), ([], [], []))
       \<le> SPEC (\<lambda>c. bisection_loop_safe_invar c \<and> bilr_alpha_todo c = []
              \<and> mset (acc_ivs l_num r_num k (bilr_alpha_acc c)) = mset (dsc_int 0 1 (Poly P)))"
proof -
  let ?s0 = "((([l_num], [r_num], [k]), [P]), ([], [], [])) :: bisection_loop_state"
  have aseed: "bilr_alpha ?s0 = ([(((l_num, r_num), k), P)], [])"
    by (simp add: bilr_alpha_def bilr_alpha_todo_def bilr_alpha_acc_def
        dyadic_interval_vec_triples_simps)
  have inv0: "bilr_refine_invar \<delta> P l_num r_num k (bilr_alpha ?s0) ?s0"
    by (rule bilr_seed_invar[OF lr len lenb dcap cap])
  have loop: "bisection_loop_stateful_monadic ?s0 \<le> SPEC (\<lambda>c.
      bilr_refine_invar \<delta> P l_num r_num k (bilr_alpha ?s0) c \<and> bilr_alpha_todo c = []
      \<and> bilr_alpha_acc c = snd (carried_gmp_main (bilr_alpha ?s0)))"
    by (rule bilr_loop_stateful_spec[OF \<delta>_pos small_fast inv0 len lenb])
  have l8: "mset (acc_ivs l_num r_num k (snd (carried_gmp_main (bilr_alpha ?s0))))
          = mset (dsc_int 0 1 (Poly P))"
    using carried_gmp_main_seed_mset_dsc_int[OF \<delta>_pos len small_fast dom P0 canon lr]
    by (simp add: aseed)
  have w: "SPEC (\<lambda>c. bilr_refine_invar \<delta> P l_num r_num k (bilr_alpha ?s0) c \<and> bilr_alpha_todo c = []
              \<and> bilr_alpha_acc c = snd (carried_gmp_main (bilr_alpha ?s0)))
        \<le> SPEC (\<lambda>c. bisection_loop_safe_invar c \<and> bilr_alpha_todo c = []
              \<and> mset (acc_ivs l_num r_num k (bilr_alpha_acc c)) = mset (dsc_int 0 1 (Poly P)))"
    using l8 by (auto simp: pw_le_iff refine_pw_simps bilr_refine_invar_def
        bisection_loop_safe_invar_def)
  show ?thesis using order_trans[OF loop w] .
qed

text \<open>The main-list exit fact: when the abstract todo is drained, the concrete carried-polynomial stack
  @{term qtodo} is empty (the @{const bisection_loop_state_invar} keeps @{term qtodo} and the interval
  triples in length lockstep, so an empty @{const bilr_alpha_todo} zip forces both empty). Discharges the
  main-list's \<open>ASSERT (qtodo = [])\<close>.\<close>
lemma bilr_exit_qtodo_empty:
  assumes si: "bisection_loop_state_invar c"
    and empty: "bilr_alpha_todo c = []"
  shows "snd (fst c) = []"
proof -
  obtain todo qtodo acc where c: "c = ((todo, qtodo), acc)" by (cases c) auto
  obtain lns rns ks where todo: "todo = (lns, rns, ks)" by (cases todo) auto
  from si have lq: "length qtodo = length lns" and llr: "length lns = length rns"
    and llk: "length lns = length ks"
    by (auto simp: c todo bisection_loop_state_invar_def
        dyadic_interval_vec_invar_def)
  have lt: "length (dyadic_interval_vec_triples todo) = length qtodo"
    using lq llr llk by (simp add: todo dyadic_interval_vec_triples_simps length_zip)
  have "zip (dyadic_interval_vec_triples todo) qtodo = []"
    using empty by (simp add: c bilr_alpha_todo_def)
  hence "dyadic_interval_vec_triples todo = [] \<or> qtodo = []"
    by (simp add: zip_eq_Nil_iff)
  thus ?thesis using lt by (auto simp: c)
qed

text \<open>The carried loop wrapper @{const bisection_loop_monadic} on the seed components, as a \<^emph>\<open>named-function\<close>
  \<open>\<le> SPEC\<close> rule (so \<open>refine_vcg\<close> matches the main-list's loop call without unfolding it to @{const bisection_loop_stateful_monadic}).\<close>
lemma bisection_loop_monadic_seed_correct:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and lenb: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and cap: "int (2 ^ Suc (rational_interval_mu \<delta> (0, 1))) + 1
              < int (max_snat LENGTH(gmp_poly_len))"
    and lr: "l_num < r_num"
    and dom: "dsc_dom (degree (Poly P), of_rat 0, of_rat 1, map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
  shows "bisection_loop_monadic ([l_num], [r_num], [k]) [P] ([], [], []) \<le> SPEC (\<lambda>c.
      bisection_loop_safe_invar c \<and> bilr_alpha_todo c = []
      \<and> mset (acc_ivs l_num r_num k (bilr_alpha_acc c)) = mset (dsc_int 0 1 (Poly P)))"
  unfolding bisection_loop_monadic_def PR_CONST_def
  by (rule bilr_loop_stateful_seed_correct[OF \<delta>_pos len small_fast lenb dcap cap lr dom P0 canon])

text \<open>The full main-list driver isolates the roots. The seed-setup ops are pure \<open>RETURN\<close>/\<open>ASSERT\<close>;
  the loop is matched by @{thm bisection_loop_monadic_seed_correct} (a named-function specification
  supplied to \<open>refine_vcg\<close>); the exit \<open>ASSERT (qtodo = [])\<close> by @{thm bilr_exit_qtodo_empty}; the
  result acc carries @{const dyadic_interval_vec_invar} and the @{const acc_ivs} multiset from the
  loop specification (\<open>bilr_alpha_acc c = triples acc\<close>).\<close>
lemma bisection_main_list_spec:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0"
    and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and lenb: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and cap: "int (2 ^ Suc (rational_interval_mu \<delta> (0, 1))) + 1
              < int (max_snat LENGTH(gmp_poly_len))"
    and lr: "l_num < r_num"
    and dom: "dsc_dom (degree (Poly P), of_rat 0, of_rat 1, map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
  shows "bisection_main_list l_num r_num k P \<le> SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      mset (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
        = mset (dsc_int 0 1 (Poly P)))"
proof -
  have seed_safe: "bisection_loop_safe_invar
      (((([l_num], [r_num], [k]), [P]), ([], [], [])) :: bisection_loop_state)"
    using bilr_seed_invar[OF lr len lenb dcap cap] by (simp add: bilr_refine_invar_def)
  have phi: "\<And>c. inres (bisection_loop_monadic ([l_num], [r_num], [k]) [P] ([], [], [])) c \<Longrightarrow>
      bisection_loop_safe_invar c \<and> bilr_alpha_todo c = []
      \<and> mset (acc_ivs l_num r_num k (bilr_alpha_acc c)) = mset (dsc_int 0 1 (Poly P))"
    using bisection_loop_monadic_seed_correct[OF \<delta>_pos len small_fast lenb dcap cap lr dom P0 canon]
    by (auto simp: pw_le_iff refine_pw_simps)
  have free_d: "\<And>v. dyadic_interval_vec_free_monadic v \<le> SPEC (\<lambda>_. True)"
    unfolding dyadic_interval_vec_free_monadic_def PR_CONST_def
    by (refine_vcg) (auto simp: pw_le_iff refine_pw_simps mop_free_def)
  have free_d_nofail: "\<And>v. nofail (dyadic_interval_vec_free_monadic v)"
    using free_d by (auto simp: pw_le_iff refine_pw_simps)
  have loop_nofail: "nofail (bisection_loop_monadic ([l_num], [r_num], [k]) [P] ([], [], []))"
    using bisection_loop_monadic_seed_correct[OF \<delta>_pos len small_fast lenb dcap cap lr dom P0 canon]
    by (auto simp: pw_le_iff refine_pw_simps)
  have max1: "Suc 0 < max_snat LENGTH(gmp_poly_len)" using len lenb by linarith
  have seed_steppre: "bisection_loop_step_pre
      (((([l_num], [r_num], [k]), [P]), ([], [], [])) :: bisection_loop_state)"
    using seed_safe
    by (simp add: bisection_loop_safe_invar_def bisection_loop_cond_def)
  show ?thesis
    unfolding bisection_main_list_def PR_CONST_def COPY_def
      dyadic_interval_vec_empty_sz_monadic_def poly_empty_sz_monadic_def
      poly_push_coeff_monadic_def poly_vec_empty_sz_monadic_def poly_vec_push_monadic_def
      poly_vec_free_empty_monadic_def
    apply (refine_vcg free_d)
    apply (all \<open>(rule order_trans[OF bisection_loop_monadic_seed_correct[OF
        \<delta>_pos len small_fast lenb dcap cap lr dom P0 canon]])?\<close>)
    apply (auto simp: pw_le_iff refine_pw_simps dyadic_interval_vec_pushable_def
        bilr_alpha_acc_def bilr_alpha_todo_def bisection_loop_safe_invar_def
        bisection_loop_state_invar_def dyadic_interval_vec_invar_def
        dyadic_interval_vec_triples_simps zip_eq_Nil_iff length_zip seed_safe free_d_nofail
        loop_nofail max1 seed_steppre
        dest!: phi dest: bilr_exit_qtodo_empty)
    apply (simp add: max_snat_def)
    done
qed

subsection \<open>FCOMP: the carried LLVM impl satisfies the \<open>dsc_int\<close> spec\<close>

text \<open>The abstract dsc-int spec for the carried driver: the returned dyadic vector's @{const node_iv}
  interpretation (@{const acc_ivs}) is the Descartes multiset on \<open>[0,1]\<close>.\<close>
definition bilr_dsc_int_spec ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"bilr_dsc_int_spec l_num r_num k P \<equiv>
  SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
    mset (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
      = mset (dsc_int 0 1 (Poly P)))"

text \<open>The precondition bundle (parameterised by the subdivision granularity \<open>\<delta>\<close>): positivity, the small-interval
  Descartes bound, the seed ordering, the snat-capacity caps on the initial \<open>\<mu>\<close>, and the squarefree-domain facts.\<close>
definition bilr_dsc_int_pre :: "real \<Rightarrow> (((int \<times> int) \<times> nat) \<times> gmp_poly) \<Rightarrow> bool" where
"bilr_dsc_int_pre \<delta> x \<longleftrightarrow>
  (case x of (((l_num, r_num), k), P) \<Rightarrow>
    \<delta> > 0 \<and>
    0 < length P \<and>
    (\<forall>a b. a < b \<longrightarrow> of_rat b - of_rat a \<le> \<delta> \<longrightarrow> descartes_list_int a b P \<le> 1) \<and>
    length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
    k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
    int (2 ^ Suc (rational_interval_mu \<delta> (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len)) \<and>
    l_num < r_num \<and>
    dsc_dom (degree (Poly P), of_rat 0, of_rat 1, map_poly of_int (Poly P) :: real poly) \<and>
    Poly P \<noteq> 0 \<and> coeffs (Poly P) = P)"

text \<open>The functional refinement (the \<open>Id\<close>-fref that \<open>FCOMP\<close> composes), from @{thm bisection_main_list_spec}.\<close>
lemma bilr_dsc_int_refine:
  "(uncurry3 bisection_main_list, uncurry3 bilr_dsc_int_spec)
   \<in> [bilr_dsc_int_pre \<delta>]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI)
  unfolding bilr_dsc_int_pre_def bilr_dsc_int_spec_def
  apply clarsimp
  apply (rule bisection_main_list_spec)
           apply auto
  done

text \<open>The capstone HNR theorem: the exported @{const bisection_main_list_impl} (borrowing the \<open>mpz_t\<close>
  endpoints, owning the pushed polynomial) refines the @{const dsc_int} spec under @{const bilr_dsc_int_pre}.
  \<open>FCOMP\<close> of the impl's \<open>.refine\<close> with @{thm bilr_dsc_int_refine}, then @{thm hfref_weaken_pre}
  (@{const bilr_dsc_int_pre} implies the impl pre, since \<open>k + 1 \<le> k + \<mu> + 1 < max_snat\<close>); mirrors the endpoint
  @{thm dsc_rational_main_list_impl_refine_dsc_int}.\<close>
theorem bilr_main_list_impl_refine_dsc_int:
  "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_int_spec)
   \<in> [bilr_dsc_int_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
proof -
  have h:
    "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_int_spec)
     \<in> [\<lambda>(((l_num, r_num), k), P).
          bilr_dsc_int_pre \<delta> (((l_num, r_num), k), P) \<and>
          0 < length P \<and>
          length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
          k + 1 < max_snat LENGTH(gmp_poly_len)]\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
        \<rightarrow> gmp_dyadic_interval_vec_assn"
    using bisection_main_list_impl.refine[FCOMP bilr_dsc_int_refine[where \<delta>=\<delta>]]
    by (simp add: PR_CONST_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF _ h])
    apply (clarsimp simp: bilr_dsc_int_pre_def)
    done
qed

subsection \<open>Squarefree corollary: discharging the precondition from clean polynomial hypotheses\<close>

text \<open>A usable precondition: take \<open>\<delta>\<close> to be the root-separation granularity @{const delta_P} of the (squarefree,
  non-constant, nonzero) real polynomial. This replaces the opaque \<open>\<delta> > 0\<close> / \<open>small_fast\<close> / \<open>dsc_dom\<close> conjuncts of
  @{const bilr_dsc_int_pre} with @{const square_free} + degree facts (the \<open>snat\<close> capacity caps on the initial \<open>\<mu>\<close>
  stay — they are a machine-word budget, not derivable from squarefreeness).\<close>
definition bilr_dsc_squarefree_pre :: "real \<Rightarrow> (((int \<times> int) \<times> nat) \<times> gmp_poly) \<Rightarrow> bool" where
"bilr_dsc_squarefree_pre \<delta> x \<longleftrightarrow>
  (case x of (((l_num, r_num), k), P) \<Rightarrow>
    let P_int = Poly P; P_real = (map_poly of_int P_int :: real poly) in
      \<delta> = delta_P P_real \<and>
      0 < length P \<and>
      length P + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      int (2 ^ Suc (rational_interval_mu \<delta> (0, 1))) + 1 < int (max_snat LENGTH(gmp_poly_len)) \<and>
      l_num < r_num \<and>
      P_int \<noteq> 0 \<and> coeffs P_int = P \<and> degree P_int \<noteq> 0 \<and> square_free P_real)"

text \<open>The squarefree precondition implies the @{const bilr_dsc_int_pre} bundle: \<open>delta_P > 0\<close> gives \<open>\<delta> > 0\<close>; the
  small-interval Descartes bound is the reused endpoint @{thm rational_fast_descartes_list_int_delta_P_le1};
  the \<open>[0,1]\<close> domain fact is @{thm dsc_terminates_squarefree}.\<close>
lemma bilr_dsc_squarefree_pre_imp_int_pre:
  assumes pre: "bilr_dsc_squarefree_pre \<delta> x"
  shows "bilr_dsc_int_pre \<delta> x"
proof -
  obtain l_num r_num k P where x_eq: "x = (((l_num, r_num), k), P)" by (cases x) auto
  let ?P_int = "Poly P"
  let ?P_real = "map_poly of_int ?P_int :: real poly"
  from pre have delta_eq: "\<delta> = delta_P ?P_real" and P_len: "0 < length P"
    and P_bound: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and cap: "int (2 ^ Suc (rational_interval_mu \<delta> (0, 1))) + 1
              < int (max_snat LENGTH(gmp_poly_len))"
    and lr: "l_num < r_num" and P0: "?P_int \<noteq> 0" and canon: "coeffs ?P_int = P"
    and p0: "degree ?P_int \<noteq> 0" and sf: "square_free ?P_real"
    unfolding x_eq bilr_dsc_squarefree_pre_def by (auto simp: Let_def)
  have P_real0: "?P_real \<noteq> 0" using P0 by simp
  have deg_le: "degree ?P_real \<le> degree ?P_int" by simp
  have delta_pos: "\<delta> > 0" using delta_eq P0 delta_P_pos by simp
  have small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    using rational_fast_descartes_list_int_delta_P_le1[OF P0 canon p0 sf] delta_eq by simp
  have I_less: "(of_rat 0 :: real) < of_rat 1" by simp
  have dom: "dsc_dom (degree ?P_int, of_rat 0, of_rat 1, ?P_real)"
    by (rule dsc_terminates_squarefree[OF P_real0 deg_le p0 sf I_less])
  show ?thesis
    unfolding x_eq bilr_dsc_int_pre_def
    apply (simp add: Let_def)
    apply (intro conjI allI impI)
    using delta_pos small_fast P_len P_bound dcap cap lr dom P0 canon
    apply simp_all
    done
qed

text \<open>The user-facing capstone: the carried LLVM impl isolates the roots of any squarefree non-constant integer
  polynomial (with the seed/capacity side-conditions), with \<open>\<delta>\<close> instantiated to its root-separation granularity.\<close>
theorem bilr_main_list_impl_refine_dsc_int_squarefree:
  "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_int_spec)
   \<in> [bilr_dsc_squarefree_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
  apply (rule hfref_weaken_pre[OF _ bilr_main_list_impl_refine_dsc_int])
  using bilr_dsc_squarefree_pre_imp_int_pre by blast

subsection \<open>Termination, soundness, completeness\<close>

text \<open>\<^bold>\<open>Termination.\<close> Under the precondition the carried driver never fails — i.e. it is @{const nofail}
  (the abstract algorithm terminates), inherited from @{thm bisection_main_list_spec} (\<open>\<le> SPEC\<close>).\<close>
theorem bilr_main_list_terminates:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and lenb: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and cap: "int (2 ^ Suc (rational_interval_mu \<delta> (0, 1))) + 1
              < int (max_snat LENGTH(gmp_poly_len))"
    and lr: "l_num < r_num"
    and dom: "dsc_dom (degree (Poly P), of_rat 0, of_rat 1, map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
  shows "nofail (bisection_main_list l_num r_num k P)"
  using bisection_main_list_spec[OF \<delta>_pos len small_fast lenb dcap cap lr dom P0 canon]
  by (auto simp: pw_le_iff refine_pw_simps)

text \<open>\<^bold>\<open>Soundness + completeness.\<close> The result vector's @{const node_iv} interpretation is, as a set, exactly the
  abstract Descartes isolation on \<open>[0,1]\<close>, so: \<^bold>\<open>(sound)\<close> every returned box is a sound real-\<open>dsc\<close> box
  (@{const dsc_pair_ok}); \<^bold>\<open>(complete)\<close> every real root of @{term "Poly P"} in \<open>(0,1)\<close> lies in some returned box.
  Bridged from @{thm bisection_main_list_spec} by \<open>mset\<close>-to-\<open>set\<close> equality + the abstract image lemmas
  @{thm dsc_int_sound_real_image} / @{thm dsc_int_complete_real_image}.\<close>
theorem bilr_main_list_sound_complete:
  fixes \<delta> :: real
  assumes \<delta>_pos: "\<delta> > 0" and len: "0 < length P"
    and small_fast: "\<And>a b. a < b \<Longrightarrow> of_rat b - of_rat a \<le> \<delta> \<Longrightarrow> descartes_list_int a b P \<le> 1"
    and lenb: "length P + 1 < max_snat LENGTH(gmp_poly_len)"
    and dcap: "k + rational_interval_mu \<delta> (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)"
    and cap: "int (2 ^ Suc (rational_interval_mu \<delta> (0, 1))) + 1
              < int (max_snat LENGTH(gmp_poly_len))"
    and lr: "l_num < r_num"
    and dom: "dsc_dom (degree (Poly P), of_rat 0, of_rat 1, map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0" and canon: "coeffs (Poly P) = P"
  shows "bisection_main_list l_num r_num k P \<le> SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      (\<forall>R \<in> set (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
        \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) (map_poly of_int (Poly P) :: real poly)).
          R = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly P) :: real poly) J) \<and>
      (\<forall>x. poly (map_poly of_int (Poly P) :: real poly) x = 0 \<longrightarrow> of_rat 0 < x \<longrightarrow> x < of_rat 1 \<longrightarrow>
        (\<exists>R \<in> set (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
          \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) (map_poly of_int (Poly P) :: real poly)).
            R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)))"
proof -
  let ?P_real = "map_poly of_int (Poly P) :: real poly"
  have spec: "bisection_main_list l_num r_num k P \<le> SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      mset (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
        = mset (dsc_int 0 1 (Poly P)))"
    by (rule bisection_main_list_spec[OF \<delta>_pos len small_fast lenb dcap cap lr dom P0 canon])
  have ab: "(0 :: rat) < 1" by simp
  show ?thesis
  proof (rule SPEC_cons_rule[OF spec])
    fix acc :: gmp_dyadic_interval_vec
    assume H: "dyadic_interval_vec_invar acc \<and>
        mset (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
          = mset (dsc_int 0 1 (Poly P))"
    let ?A = "set (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))"
    from H have vec: "dyadic_interval_vec_invar acc"
      and mset_eq: "mset (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc))
          = mset (dsc_int 0 1 (Poly P))" by auto
    have set_eq: "?A = set (dsc_int 0 1 (Poly P))"
      using arg_cong[OF mset_eq, of set_mset] by simp
    have sound: "\<forall>R \<in> ?A. \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?P_real).
          R = real_to_rat_pair J \<and> dsc_pair_ok ?P_real J"
      using dsc_int_sound_real_image[OF dom P0 ab] by (simp add: set_eq)
    have complete: "\<forall>x. poly ?P_real x = 0 \<longrightarrow> of_rat 0 < x \<longrightarrow> x < of_rat 1 \<longrightarrow>
          (\<exists>R \<in> ?A. \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?P_real).
            R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J)"
    proof (intro allI impI)
      fix x assume root: "poly ?P_real x = 0" and ax: "of_rat 0 < x" and xb: "x < of_rat 1"
      obtain I J where "I \<in> set (dsc_int 0 1 (Poly P))"
        and "J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?P_real)"
        and "I = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
        using dsc_int_complete_real_image[OF dom P0 root ax xb] by blast
      thus "\<exists>R \<in> ?A. \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?P_real).
          R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
        using set_eq by blast
    qed
    show "dyadic_interval_vec_invar acc \<and>
        (\<forall>R \<in> ?A. \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?P_real).
          R = real_to_rat_pair J \<and> dsc_pair_ok ?P_real J) \<and>
        (\<forall>x. poly ?P_real x = 0 \<longrightarrow> of_rat 0 < x \<longrightarrow> x < of_rat 1 \<longrightarrow>
          (\<exists>R \<in> ?A. \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?P_real).
            R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))"
      using vec sound complete by blast
  qed
qed

subsection \<open>FCOMP: soundness + completeness on the LLVM impl\<close>

text \<open>The sound+complete spec as a standalone SPEC (so it can be \<open>FCOMP\<close>-composed through to the impl), mirroring
  the endpoint \<open>dsc_rational_main_list_dsc_sound_complete_spec\<close>: the returned vector's
  @{const node_iv} interpretation is a sound (@{const dsc_pair_ok}) cover of every real root in \<open>(0,1)\<close>.\<close>
definition bilr_dsc_sound_complete_spec ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"bilr_dsc_sound_complete_spec l_num r_num k P \<equiv>
  (let P_real = (map_poly of_int (Poly P) :: real poly);
       ds = dsc (degree (Poly P)) (of_rat 0) (of_rat 1) P_real
   in SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      (\<forall>R \<in> set (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
        \<exists>J \<in> set ds. R = real_to_rat_pair J \<and> dsc_pair_ok P_real J) \<and>
      (\<forall>x. poly P_real x = 0 \<longrightarrow> of_rat 0 < x \<longrightarrow> x < of_rat 1 \<longrightarrow>
        (\<exists>R \<in> set (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
          \<exists>J \<in> set ds. R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))))"

text \<open>The \<open>dsc_int\<close> spec (exact Descartes multiset) implies the sound+complete spec: the mset-result equals the
  abstract @{const dsc_int}, whose set-image is sound/complete by @{thm dsc_int_sound_real_image} /
  @{thm dsc_int_complete_real_image} (\<open>set_mset_mset\<close> bridges \<open>mset\<close>-equality to set-membership).\<close>
lemma bilr_dsc_int_spec_sound_complete:
  fixes \<delta> :: real
  assumes pre: "bilr_dsc_int_pre \<delta> (((l_num, r_num), k), P)"
  shows "bilr_dsc_int_spec l_num r_num k P \<le> bilr_dsc_sound_complete_spec l_num r_num k P"
proof -
  let ?P_real = "map_poly of_int (Poly P) :: real poly"
  have dom: "dsc_dom (degree (Poly P), of_rat 0, of_rat 1, ?P_real)"
    using pre unfolding bilr_dsc_int_pre_def by simp
  have P0: "Poly P \<noteq> 0" using pre unfolding bilr_dsc_int_pre_def by simp
  have ab: "(0 :: rat) < 1" by simp
  have sound: "\<forall>R \<in> set (dsc_int 0 1 (Poly P)).
        \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?P_real).
          R = real_to_rat_pair J \<and> dsc_pair_ok ?P_real J"
    by (rule dsc_int_sound_real_image[OF dom P0 ab])
  have complete: "\<And>x. poly ?P_real x = 0 \<Longrightarrow> of_rat 0 < x \<Longrightarrow> x < of_rat 1 \<Longrightarrow>
        \<exists>R \<in> set (dsc_int 0 1 (Poly P)).
          \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?P_real).
            R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
    by (rule dsc_int_complete_real_image[OF dom P0])
  show ?thesis
    unfolding bilr_dsc_int_spec_def bilr_dsc_sound_complete_spec_def Let_def
    using sound complete
    apply (auto simp: refine_pw_simps)
    apply (metis set_mset_mset)
    by (metis set_mset_mset)
qed

text \<open>The functional refinement \<open>bilr_dsc_int_spec \<le> bilr_dsc_sound_complete_spec\<close> as an \<open>Id\<close>-fref (for \<open>FCOMP\<close>).\<close>
lemma bilr_dsc_sound_complete_refine:
  "(uncurry3 bilr_dsc_int_spec, uncurry3 bilr_dsc_sound_complete_spec)
   \<in> [bilr_dsc_int_pre \<delta>]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI)
  apply clarsimp
  apply (rule bilr_dsc_int_spec_sound_complete)
  apply assumption
  done

text \<open>The user-facing soundness+completeness HNR: the exported @{const bisection_main_list_impl}
  returns, under @{const bilr_dsc_int_pre}, a dyadic vector that is a sound, complete real-root cover of
  @{term "Poly P"} on \<open>(0,1)\<close>. \<open>FCOMP\<close> of @{thm bilr_main_list_impl_refine_dsc_int} with
  @{thm bilr_dsc_sound_complete_refine}; mirrors @{thm dsc_rational_main_list_impl_refine_dsc_sound_complete}.\<close>
theorem bilr_main_list_impl_refine_dsc_sound_complete:
  "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_sound_complete_spec)
   \<in> [bilr_dsc_int_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
proof -
  have h:
    "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_sound_complete_spec)
     \<in> [\<lambda>(((l_num, r_num), k), P). bilr_dsc_int_pre \<delta> (((l_num, r_num), k), P)]\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
        \<rightarrow> gmp_dyadic_interval_vec_assn"
    using bilr_main_list_impl_refine_dsc_int[where \<delta>=\<delta>,
      FCOMP bilr_dsc_sound_complete_refine[where \<delta>=\<delta>]]
    by (simp add: PR_CONST_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF _ h])
    apply clarsimp
    done
qed

subsection \<open>Separated soundness / completeness specs (the preferred public form)\<close>

text \<open>Soundness alone (no completeness conjunct): every returned box is a sound real-\<open>dsc\<close> box. Mirrors
  \<open>dsc_rational_main_list_dsc_sound_spec\<close>.\<close>
definition bilr_dsc_sound_spec ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"bilr_dsc_sound_spec l_num r_num k P \<equiv>
  (let P_real = (map_poly of_int (Poly P) :: real poly);
       ds = dsc (degree (Poly P)) (of_rat 0) (of_rat 1) P_real
   in SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      (\<forall>R \<in> set (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
        \<exists>J \<in> set ds. R = real_to_rat_pair J \<and> dsc_pair_ok P_real J)))"

text \<open>Completeness alone (no soundness conjunct): every real root in \<open>(0,1)\<close> lies in a returned box. Mirrors
  \<open>dsc_rational_main_list_dsc_complete_spec\<close>.\<close>
definition bilr_dsc_complete_spec ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> gmp_poly \<Rightarrow> gmp_dyadic_interval_vec nres" where
"bilr_dsc_complete_spec l_num r_num k P \<equiv>
  (let P_real = (map_poly of_int (Poly P) :: real poly);
       ds = dsc (degree (Poly P)) (of_rat 0) (of_rat 1) P_real
   in SPEC (\<lambda>acc.
      dyadic_interval_vec_invar acc \<and>
      (\<forall>x. poly P_real x = 0 \<longrightarrow> of_rat 0 < x \<longrightarrow> x < of_rat 1 \<longrightarrow>
        (\<exists>R \<in> set (acc_ivs l_num r_num k (dyadic_interval_vec_triples acc)).
          \<exists>J \<in> set ds. R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J))))"

text \<open>\<open>bilr_dsc_int_spec\<close> implies each separated spec (one \<open>set_mset_mset\<close> bridge each).\<close>
lemma bilr_dsc_int_spec_sound:
  fixes \<delta> :: real
  assumes pre: "bilr_dsc_int_pre \<delta> (((l_num, r_num), k), P)"
  shows "bilr_dsc_int_spec l_num r_num k P \<le> bilr_dsc_sound_spec l_num r_num k P"
proof -
  let ?P_real = "map_poly of_int (Poly P) :: real poly"
  have dom: "dsc_dom (degree (Poly P), of_rat 0, of_rat 1, ?P_real)"
    using pre unfolding bilr_dsc_int_pre_def by simp
  have P0: "Poly P \<noteq> 0" using pre unfolding bilr_dsc_int_pre_def by simp
  have sound: "\<forall>R \<in> set (dsc_int 0 1 (Poly P)).
        \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?P_real).
          R = real_to_rat_pair J \<and> dsc_pair_ok ?P_real J"
    by (rule dsc_int_sound_real_image[OF dom P0]) simp
  show ?thesis
    unfolding bilr_dsc_int_spec_def bilr_dsc_sound_spec_def Let_def
    using sound apply (auto simp: refine_pw_simps) by (metis set_mset_mset)
qed

lemma bilr_dsc_int_spec_complete:
  fixes \<delta> :: real
  assumes pre: "bilr_dsc_int_pre \<delta> (((l_num, r_num), k), P)"
  shows "bilr_dsc_int_spec l_num r_num k P \<le> bilr_dsc_complete_spec l_num r_num k P"
proof -
  let ?P_real = "map_poly of_int (Poly P) :: real poly"
  have dom: "dsc_dom (degree (Poly P), of_rat 0, of_rat 1, ?P_real)"
    using pre unfolding bilr_dsc_int_pre_def by simp
  have P0: "Poly P \<noteq> 0" using pre unfolding bilr_dsc_int_pre_def by simp
  have complete: "\<And>x. poly ?P_real x = 0 \<Longrightarrow> of_rat 0 < x \<Longrightarrow> x < of_rat 1 \<Longrightarrow>
        \<exists>R \<in> set (dsc_int 0 1 (Poly P)).
          \<exists>J \<in> set (dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?P_real).
            R = real_to_rat_pair J \<and> fst J \<le> x \<and> x \<le> snd J"
    by (rule dsc_int_complete_real_image[OF dom P0])
  show ?thesis
    unfolding bilr_dsc_int_spec_def bilr_dsc_complete_spec_def Let_def
    using complete apply (auto simp: refine_pw_simps) by (metis set_mset_mset)
qed

text \<open>The \<open>Id\<close>-frefs for each separated weakening.\<close>
lemma bilr_dsc_sound_refine:
  "(uncurry3 bilr_dsc_int_spec, uncurry3 bilr_dsc_sound_spec)
   \<in> [bilr_dsc_int_pre \<delta>]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI) apply clarsimp
  apply (rule bilr_dsc_int_spec_sound) apply assumption done

lemma bilr_dsc_complete_refine:
  "(uncurry3 bilr_dsc_int_spec, uncurry3 bilr_dsc_complete_spec)
   \<in> [bilr_dsc_int_pre \<delta>]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI) apply clarsimp
  apply (rule bilr_dsc_int_spec_complete) apply assumption done

text \<open>The separated soundness / completeness HNRs on the LLVM impl, mirroring
  @{thm dsc_rational_main_list_impl_refine_dsc_sound} /
  @{thm dsc_rational_main_list_impl_refine_dsc_complete}.\<close>
theorem bilr_main_list_impl_refine_dsc_sound:
  "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_sound_spec)
   \<in> [bilr_dsc_int_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
proof -
  have h:
    "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_sound_spec)
     \<in> [\<lambda>(((l_num, r_num), k), P). bilr_dsc_int_pre \<delta> (((l_num, r_num), k), P)]\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
        \<rightarrow> gmp_dyadic_interval_vec_assn"
    using bilr_main_list_impl_refine_dsc_int[where \<delta>=\<delta>, FCOMP bilr_dsc_sound_refine[where \<delta>=\<delta>]]
    by (simp add: PR_CONST_def)
  show ?thesis by (rule hfref_weaken_pre[OF _ h]) clarsimp
qed

theorem bilr_main_list_impl_refine_dsc_complete:
  "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_complete_spec)
   \<in> [bilr_dsc_int_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
proof -
  have h:
    "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_complete_spec)
     \<in> [\<lambda>(((l_num, r_num), k), P). bilr_dsc_int_pre \<delta> (((l_num, r_num), k), P)]\<^sub>a
        mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
        \<rightarrow> gmp_dyadic_interval_vec_assn"
    using bilr_main_list_impl_refine_dsc_int[where \<delta>=\<delta>, FCOMP bilr_dsc_complete_refine[where \<delta>=\<delta>]]
    by (simp add: PR_CONST_def)
  show ?thesis by (rule hfref_weaken_pre[OF _ h]) clarsimp
qed

text \<open>Squarefree-precondition versions of the sound / complete / sound+complete HNRs (clean \<open>square_free\<close>
  hypotheses in place of @{const bilr_dsc_int_pre}'s opaque domain conjuncts), via
  @{thm bilr_dsc_squarefree_pre_imp_int_pre}.\<close>
theorem bilr_main_list_impl_refine_dsc_sound_squarefree:
  "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_sound_spec)
   \<in> [bilr_dsc_squarefree_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
  apply (rule hfref_weaken_pre[OF _ bilr_main_list_impl_refine_dsc_sound])
  using bilr_dsc_squarefree_pre_imp_int_pre by blast

theorem bilr_main_list_impl_refine_dsc_complete_squarefree:
  "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_complete_spec)
   \<in> [bilr_dsc_squarefree_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
  apply (rule hfref_weaken_pre[OF _ bilr_main_list_impl_refine_dsc_complete])
  using bilr_dsc_squarefree_pre_imp_int_pre by blast

theorem bilr_main_list_impl_refine_dsc_sound_complete_squarefree:
  "(uncurry3 bisection_main_list_impl, uncurry3 bilr_dsc_sound_complete_spec)
   \<in> [bilr_dsc_squarefree_pre \<delta>]\<^sub>a
      mpzb_assn\<^sup>k *\<^sub>a mpzb_assn\<^sup>k *\<^sub>a (snat_assn' TYPE(gmp_poly_len))\<^sup>k *\<^sub>a gmp_poly_assn\<^sup>d
      \<rightarrow> gmp_dyadic_interval_vec_assn"
  apply (rule hfref_weaken_pre[OF _ bilr_main_list_impl_refine_dsc_sound_complete])
  using bilr_dsc_squarefree_pre_imp_int_pre by blast

end
