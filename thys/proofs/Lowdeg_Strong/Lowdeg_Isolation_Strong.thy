theory Lowdeg_Isolation_Strong
  imports
    IsaRRI_Refine.Isolation_Contract
    Lowdeg_Lin
begin

text \<open>\<^bold>\<open>The degree \<open>\<le>\<close> 8 path of the solver, proven to isolate every positive root exactly once.\<close>
  \<open>lowdeg_isolate_all_split_main_correct\<close> gives, per half, soundness (every window
  isolates a root) and CLOSED-hull coverage. This theory proves the full contract,
  \<open>half_strong\<close>: soundness, strict-or-degenerate coverage (every positive root lies strictly
  inside some window or IS a degenerate window), pairwise disjointness of the windows, and that
  every window's contents are positive.

  \<^bold>\<open>Fall-through (bisection).\<close> The concrete output is multiset-equal to the rescaled output of
  the abstract recursion \<open>dsc\<close> (\<open>dsc_int_eq_dsc\<close> and the loop's own multiset
  specification), so the three properties are proven once for \<open>dsc\<close> by induction
  (\<open>dsc_complete_strong\<close>, \<open>dsc_iv_disj_inside\<close>) and transported.
  \<^bold>\<open>Closed forms (degrees 2 and 3).\<close> Each emission is proven to produce a list of a known SHAPE ---
  empty, \<open>[(0, 2\<^sup>k)]\<close>, or two windows split at a certified non-root separator --- and the contract is
  read off that shape.\<close>

lemma dsc_windows_inside:
  assumes dom: "dsc_dom (p, a, b, P)"
  shows "a < b \<Longrightarrow> \<forall>w \<in> set (dsc p a b P). \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < b"
  using dom
proof (induction p a b P rule: dsc.pinduct)
  case (1 p a b P)
  let ?v = "Bernstein_changes p a b P"
  let ?m = "(a + b) / 2"
  have eq: "dsc p a b P = (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
      (if poly P ?m = 0 then [(?m, ?m)] else []) @ dsc p a ?m P @ dsc p ?m b P)"
    using dsc.psimps[OF "1.hyps"] by (simp add: Let_def)
  have am: "a < ?m" and mb: "?m < b" using "1.prems" by auto
  show ?case
  proof (cases "?v = 0 \<or> ?v = 1")
    case True
    then show ?thesis using "1.prems" unfolding eq iv_in_def by auto
  next
    case False
    then have v0: "?v \<noteq> 0" and v1: "?v \<noteq> 1" by auto
    have L: "\<forall>w \<in> set (dsc p a ?m P). \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < ?m"
      using "1.IH"(1)[OF refl v0 v1 refl am] .
    have R: "\<forall>w \<in> set (dsc p ?m b P). \<forall>x. iv_in x w \<longrightarrow> ?m < x \<and> x < b"
      using "1.IH"(2)[OF refl v0 v1 refl mb] .
    show ?thesis
    proof (intro ballI allI impI)
      fix w x assume wm: "w \<in> set (dsc p a b P)" and xi: "iv_in x w"
      have cases: "w = (?m, ?m) \<or> w \<in> set (dsc p a ?m P) \<or> w \<in> set (dsc p ?m b P)"
        using wm v0 v1 unfolding eq by (auto split: if_splits)
      show "a < x \<and> x < b"
      proof -
        from cases consider "w = (?m, ?m)" | "w \<in> set (dsc p a ?m P)" | "w \<in> set (dsc p ?m b P)"
          by blast
        then show ?thesis
        proof cases
          case 1
          have "(?m < x \<and> x < ?m) \<or> (?m = x \<and> ?m = x)"
            using xi unfolding 1 iv_in_def by simp
          then have "x = ?m" by linarith
          then show ?thesis using am mb by simp
        next
          case 2 then show ?thesis using L xi mb by force
        next
          case 3 then show ?thesis using R xi am by force
        qed
      qed
    qed
  qed
qed

lemma dsc_complete_strong:
  assumes dom: "dsc_dom (p, a, b, P)" and deg: "degree P \<le> p" and P0: "P \<noteq> 0"
  shows "poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow> (\<exists>w \<in> set (dsc p a b P). iv_in x w)"
  using dom deg P0
proof (induction p a b P rule: dsc.pinduct)
  case (1 p a b P)
  let ?v = "Bernstein_changes p a b P"
  let ?m = "(a + b) / 2"
  have eq: "dsc p a b P = (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
      (if poly P ?m = 0 then [(?m, ?m)] else []) @ dsc p a ?m P @ dsc p ?m b P)"
    using dsc.psimps[OF "1.hyps"] by (simp add: Let_def)
  have ab: "a < b" using "1.prems" by linarith
  have vnz: "?v \<noteq> 0"
    using Bernstein_changes_pos_of_root[OF "1.prems"(4) "1.prems"(5) ab "1.prems"(1-3)] .
  show ?case
  proof (cases "?v = 1")
    case True
    then show ?thesis using vnz "1.prems" unfolding eq iv_in_def by auto
  next
    case False
    consider "x = ?m" | "x < ?m" | "?m < x" by linarith
    then show ?thesis
    proof cases
      case 1
      have pm: "poly P ?m = 0" using "1.prems"(1) unfolding 1 .
      have "(?m, ?m) \<in> set (dsc p a b P)" using vnz False pm unfolding eq by simp
      moreover have "iv_in x (?m, ?m)" using 1 by (simp add: iv_in_def)
      ultimately show ?thesis by blast
    next
      case 2
      obtain w where "w \<in> set (dsc p a ?m P)" "iv_in x w"
        using "1.IH"(1)[OF refl vnz False refl "1.prems"(1) "1.prems"(2) 2 "1.prems"(4,5)] by blast
      then show ?thesis using vnz False unfolding eq by auto
    next
      case 3
      obtain w where "w \<in> set (dsc p ?m b P)" "iv_in x w"
        using "1.IH"(2)[OF refl vnz False refl "1.prems"(1) 3 "1.prems"(3) "1.prems"(4,5)] by blast
      then show ?thesis using vnz False unfolding eq by auto
    qed
  qed
qed

lemma dsc_iv_disj_inside:
  assumes dom: "dsc_dom (p, a, b, P)"
  shows "a < b \<Longrightarrow> iv_disj_mset (mset (dsc p a b P))
                 \<and> (\<forall>w \<in> set (dsc p a b P). \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < b)"
  using dom
proof (induction p a b P rule: dsc.pinduct)
  case (1 p a b P)
  let ?v = "Bernstein_changes p a b P"
  let ?m = "(a + b) / 2"
  have eq: "dsc p a b P = (if ?v = 0 then [] else if ?v = 1 then [(a, b)] else
      (if poly P ?m = 0 then [(?m, ?m)] else []) @ dsc p a ?m P @ dsc p ?m b P)"
    using dsc.psimps[OF "1.hyps"] by (simp add: Let_def)
  have am: "a < ?m" and mb: "?m < b" using "1.prems" by auto
  show ?case
  proof (cases "?v = 0 \<or> ?v = 1")
    case True
    then show ?thesis using "1.prems" unfolding eq iv_disj_mset_def iv_in_def by auto
  next
    case False
    then have v0: "?v \<noteq> 0" and v1: "?v \<noteq> 1" by auto
    define Ml where "Ml = (if poly P ?m = 0 then [(?m, ?m)] else [])"
    define Lw where "Lw = dsc p a ?m P"
    define Rw where "Rw = dsc p ?m b P"
    have deq: "dsc p a b P = Ml @ Lw @ Rw"
      unfolding eq Ml_def Lw_def Rw_def using v0 v1 by simp
    have IL: "iv_disj_mset (mset Lw)" and inL: "\<forall>w \<in> set Lw. \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < ?m"
      unfolding Lw_def using "1.IH"(1)[OF refl v0 v1 refl am] by auto
    have IR: "iv_disj_mset (mset Rw)" and inR: "\<forall>w \<in> set Rw. \<forall>x. iv_in x w \<longrightarrow> ?m < x \<and> x < b"
      unfolding Rw_def using "1.IH"(2)[OF refl v0 v1 refl mb] by auto
    have inM: "\<forall>w \<in> set Ml. \<forall>x. iv_in x w \<longrightarrow> x = ?m"
      unfolding Ml_def iv_in_def by auto
    have IM: "iv_disj_mset (mset Ml)" unfolding Ml_def iv_disj_mset_def by auto
    have LR: "\<forall>w \<in># mset Lw. \<forall>w' \<in># mset Rw. iv_disj w w'"
      using inL inR unfolding iv_disj_def by fastforce
    have MLR: "\<forall>w \<in># mset Ml. \<forall>w' \<in># mset Lw + mset Rw. iv_disj w w'"
      using inM inL inR unfolding iv_disj_def by fastforce
    have d1: "iv_disj_mset (mset Lw + mset Rw)" by (rule iv_disj_mset_union[OF IL IR LR])
    have d2: "iv_disj_mset (mset Ml + (mset Lw + mset Rw))" by (rule iv_disj_mset_union[OF IM d1 MLR])
    have ins: "\<forall>w \<in> set (dsc p a b P). \<forall>x. iv_in x w \<longrightarrow> a < x \<and> x < b"
      unfolding deq using inL inR inM am mb by fastforce
    show ?thesis using d2 ins unfolding deq by (simp add: add.assoc)
  qed
qed

text \<open>\<^bold>\<open>The Descartes output has at most one window per root\<close>: disjoint windows,
  each isolating a root. This is the accumulator bound of the linear bisection loop
  (\<open>bisection_main_list_spec_lin\<close>).\<close>

lemma lowdeg_pair_ok_has_root:
  assumes ok: "dsc_pair_ok P w" and nz: "P \<noteq> 0"
  shows "\<exists>x. poly P x = 0 \<and> iv_in x w"
proof (cases "fst w = snd w \<and> poly P (fst w) = 0")
  case True
  then have "poly P (fst w) = 0 \<and> iv_in (fst w) w" unfolding iv_in_def by auto
  then show ?thesis by blast
next
  case False
  then have ab: "fst w < snd w" and one: "roots_in P (fst w) (snd w) = 1"
    using ok unfolding dsc_pair_ok_def by auto
  have "\<exists>x. fst w < x \<and> x < snd w \<and> poly P x = 0"
  proof (rule ccontr)
    assume none: "\<not> (\<exists>x. fst w < x \<and> x < snd w \<and> poly P x = 0)"
    have "roots_in P (fst w) (snd w) = 0"
      using none unfolding roots_in_def proots_count_def by (auto intro!: sum.neutral)
    then show False using one by simp
  qed
  then show ?thesis unfolding iv_in_def by blast
qed

lemma dsc_int_length_bound:
  fixes P :: "int list"
  assumes dom: "dsc_dom (degree (Poly P), of_rat (0::rat), of_rat (1::rat),
                  map_poly of_int (Poly P) :: real poly)"
    and P0: "Poly P \<noteq> 0"
  shows "length (dsc_int 0 1 (Poly P)) \<le> degree (Poly P)"
proof -
  let ?Pr = "map_poly of_int (Poly P) :: real poly"
  let ?D = "dsc (degree (Poly P)) (of_rat 0) (of_rat 1) ?Pr"
  have revD: "rev (dsc_int 0 1 (Poly P)) = map real_to_rat_pair ?D"
    by (rule dsc_int_eq_dsc[OF dom refl P0 zero_less_one])
  have len: "length (dsc_int 0 1 (Poly P)) = length ?D"
    using arg_cong[OF revD, of length] by simp
  have DD: "iv_disj_mset (mset ?D)" using dsc_iv_disj_inside[OF dom] by simp
  have Pr0: "?Pr \<noteq> 0" using P0 by simp
  have ok: "\<forall>J \<in> set ?D. dsc_pair_ok ?Pr J"
    by (rule dsc_sound[OF dom _ Pr0]) simp_all
  have hit: "\<forall>w \<in> set ?D. \<exists>x \<in> {x. poly ?Pr x = 0}. iv_in x w"
    using ok lowdeg_pair_ok_has_root[OF _ Pr0] by blast
  have "length ?D \<le> card {x. poly ?Pr x = 0}"
    by (rule iv_disj_mset_length_le_card[OF DD poly_roots_finite[OF Pr0] hit])
  also have "\<dots> \<le> degree ?Pr" by (rule poly_roots_degree[OF Pr0])
  also have "\<dots> \<le> degree (Poly P)" by simp
  finally show ?thesis using len by simp
qed

lemma dsc_carried_et_pos_half_mset_windows:
  fixes xs :: "int list" and rpos :: int
  defines "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and dom_init: "dsc_dom (degree (Poly Pinit), of_rat (0::rat), of_rat (1::rat),
        map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (dsc_int 0 1 (Poly Pinit))"
  shows "mset (map rat_pair_real (dyadic_interval_vec_to_list acc))
       = image_mset (iv_scale (of_int rpos))
           (mset (dsc (degree (Poly Pinit)) (of_rat 0) (of_rat 1)
                   (map_poly of_int (Poly Pinit) :: real poly)))"
proof -
  let ?D = "dsc (degree (Poly Pinit)) (of_rat 0) (of_rat 1) (map_poly of_int (Poly Pinit) :: real poly)"
  have Pinit0: "Poly Pinit \<noteq> 0"
    unfolding Pinit_def using poly_scale_poly_list_nonzero[OF P0] rpos_pos by simp
  have revD: "rev (dsc_int 0 1 (Poly Pinit)) = map real_to_rat_pair ?D"
    by (rule dsc_int_eq_dsc[OF dom_init refl Pinit0 zero_less_one])
  have Drat: "\<forall>J \<in> set ?D. rat_pair_real (real_to_rat_pair J) = J"
  proof
    fix J assume "J \<in> set ?D"
    then obtain rx ry where "J = (of_rat rx, of_rat ry)"
      using dsc_elems_of_rat_image[OF dom_init, of "0::rat" "1::rat"] by auto
    then show "rat_pair_real (real_to_rat_pair J) = J"
      by (simp add: rat_pair_real_def)
  qed
  have step1: "map rat_pair_real (dyadic_interval_vec_to_list acc)
      = map (iv_scale (of_int rpos) \<circ> rat_pair_real) (acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))"
    unfolding dyadic_interval_vec_to_list_def acc_ivs_def
    by (simp add: dyadic_interval_of_triple_eq_r0_times_node_iv_of[OF rpos_pos]
        rat_pair_real_def iv_scale_def of_rat_mult)
  have "mset (map rat_pair_real (dyadic_interval_vec_to_list acc))
      = image_mset (iv_scale (of_int rpos) \<circ> rat_pair_real) (mset (acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc)))"
    unfolding step1 by simp
  also have "\<dots> = image_mset (iv_scale (of_int rpos) \<circ> rat_pair_real) (mset (dsc_int 0 1 (Poly Pinit)))"
    using acc_eq by simp
  also have "\<dots> = image_mset (iv_scale (of_int rpos) \<circ> rat_pair_real) (mset (rev (dsc_int 0 1 (Poly Pinit))))"
    by simp
  also have "\<dots> = image_mset (iv_scale (of_int rpos)) (image_mset (rat_pair_real \<circ> real_to_rat_pair) (mset ?D))"
    unfolding revD by (simp add: image_mset.compositionality comp_def)
  also have "image_mset (rat_pair_real \<circ> real_to_rat_pair) (mset ?D) = mset ?D"
  proof -
    have "image_mset (rat_pair_real \<circ> real_to_rat_pair) (mset ?D) = image_mset (\<lambda>x. x) (mset ?D)"
      by (rule image_mset_cong) (use Drat in simp)
    then show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma dsc_carried_et_pos_half_strong:
  fixes xs :: "int list" and rpos :: int
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and dom_init: "dsc_dom (degree (Poly Pinit), of_rat (0::rat), of_rat (1::rat),
        map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (dsc_int 0 1 (Poly Pinit))"
  shows "(\<forall>x::real. 0 < x \<longrightarrow> x < of_int rpos \<longrightarrow> poly P_real x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I)))
       \<and> iv_disj_mset (mset (map rat_pair_real (dyadic_interval_vec_to_list acc)))
       \<and> (\<forall>I \<in> set (dyadic_interval_vec_to_list acc). \<forall>x.
            iv_in x (rat_pair_real I) \<longrightarrow> 0 < x \<and> x < of_int rpos)"
proof -
  let ?Pr = "map_poly of_int (Poly Pinit) :: real poly"
  let ?D = "dsc (degree (Poly Pinit)) (of_rat 0) (of_rat 1) ?Pr"
  have c: "(0::real) < of_int rpos" using rpos_pos by simp
  have ms: "mset (map rat_pair_real (dyadic_interval_vec_to_list acc))
       = image_mset (iv_scale (of_int rpos)) (mset ?D)"
    using dsc_carried_et_pos_half_mset_windows[OF P0 rpos_pos dom_init[unfolded Pinit_def]
        acc_eq[unfolded Pinit_def]] unfolding Pinit_def .
  have DD: "iv_disj_mset (mset ?D) \<and> (\<forall>w \<in> set ?D. \<forall>x. iv_in x w \<longrightarrow> 0 < x \<and> x < 1)"
    using dsc_iv_disj_inside[OF dom_init] by simp
  have setm: "set (map rat_pair_real (dyadic_interval_vec_to_list acc)) = iv_scale (of_int rpos) ` set ?D"
    using arg_cong[OF ms, of set_mset] by simp
  have U: "iv_disj_mset (mset (map rat_pair_real (dyadic_interval_vec_to_list acc)))"
    unfolding ms using iv_disj_mset_scale[OF c] DD by blast
  have IN: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc). \<forall>x.
            iv_in x (rat_pair_real I) \<longrightarrow> 0 < x \<and> x < of_int rpos"
  proof (intro ballI allI impI)
    fix I x assume I: "I \<in> set (dyadic_interval_vec_to_list acc)" and xi: "iv_in x (rat_pair_real I)"
    have "rat_pair_real I \<in> iv_scale (of_int rpos) ` set ?D" using I setm by auto
    then obtain w where w: "w \<in> set ?D" and eqw: "rat_pair_real I = iv_scale (of_int rpos) w" by auto
    have "iv_in (x / of_int rpos) w" using xi unfolding eqw iv_in_scale[OF c] .
    then have "0 < x / of_int rpos \<and> x / of_int rpos < 1" using DD w by blast
    then show "0 < x \<and> x < of_int rpos" using c by (simp add: field_simps)
  qed
  have C: "\<forall>x::real. 0 < x \<longrightarrow> x < of_int rpos \<longrightarrow> poly P_real x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I))"
  proof (intro allI impI)
    fix x :: real assume x_pos: "0 < x" and x_lt: "x < of_int rpos" and root: "poly P_real x = 0"
    have Pinit0: "Poly Pinit \<noteq> 0"
      unfolding Pinit_def using poly_scale_poly_list_nonzero[OF P0] rpos_pos by simp
    define y where "y = x / of_int rpos"
    have y_pos: "0 < y" unfolding y_def using x_pos rpos_pos by simp
    have y_lt: "y < 1" unfolding y_def using x_lt rpos_pos by (simp add: pos_divide_less_eq)
    have rooty: "poly ?Pr y = 0"
    proof -
      have "?Pr = P_real \<circ>\<^sub>p [:0, of_int rpos:]"
        unfolding Pinit_def P_real_def by (rule Poly_scale_poly_list_eq_pcompose)
      also have "poly \<dots> y = poly P_real (of_int rpos * y)" by (simp add: poly_pcompose mult.commute)
      also have "of_int rpos * y = x" unfolding y_def using rpos_pos by simp
      finally show ?thesis using root by simp
    qed
    have Pr0: "?Pr \<noteq> 0" using Pinit0 by simp
    have degle: "degree ?Pr \<le> degree (Poly Pinit)" by simp
    have ya: "of_rat 0 < y" and yb: "y < of_rat 1" using y_pos y_lt by simp_all
    obtain w where w: "w \<in> set ?D" and yw: "iv_in y w"
      using dsc_complete_strong[OF dom_init degle Pr0 rooty ya yb] by blast
    have "iv_scale (of_int rpos) w \<in> set (map rat_pair_real (dyadic_interval_vec_to_list acc))"
      using w setm by blast
    then obtain I where I: "I \<in> set (dyadic_interval_vec_to_list acc)"
      and eqI: "rat_pair_real I = iv_scale (of_int rpos) w" by auto
    have "iv_in x (rat_pair_real I)" unfolding eqI iv_in_scale[OF c] using yw unfolding y_def .
    then show "\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I)" using I by blast
  qed
  show ?thesis using C U IN by blast
qed

abbreviation half_strong :: "real poly \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "half_strong P acc \<equiv>
     dyadic_interval_vec_invar acc
   \<and> (\<forall>I \<in> set (dyadic_interval_vec_to_list acc). dsc_pair_ok P (rat_pair_real I))
   \<and> (\<forall>I \<in> set (dyadic_interval_vec_to_list acc). \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P J)
   \<and> (\<forall>x::real. 0 < x \<longrightarrow> poly P x = 0 \<longrightarrow>
        (\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I)))
   \<and> iv_disj_mset (mset (map rat_pair_real (dyadic_interval_vec_to_list acc)))
   \<and> (\<forall>I \<in> set (dyadic_interval_vec_to_list acc). \<forall>x. iv_in x (rat_pair_real I) \<longrightarrow> 0 < x)"

text \<open>\<^bold>\<open>Soundness about the emitted window itself.\<close> @{thm [source] dsc_carried_et_pos_half_sound}
  concludes \<open>\<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok P J\<close>. Because @{const real_to_rat_pair} is
  a \<open>THE\<close>, that does not by itself say anything about \<open>rat_pair_real I\<close> --- the window a caller
  reads --- when \<open>J\<close> has an irrational endpoint. Its proof does establish the real-window form
  (\<open>J\<close> is a \<open>dsc\<close> interval, hence rational); this replays it and keeps the conclusion.\<close>
lemma dsc_carried_et_pos_half_sound_real:
  fixes xs :: "int list" and rpos :: int
  defines "P_real \<equiv> (map_poly of_int (Poly xs) :: real poly)"
    and "Pinit \<equiv> scale_poly_list rpos xs"
  assumes P0: "Poly xs \<noteq> 0" and rpos_pos: "rpos > 0"
    and dom_init: "dsc_dom (degree (Poly Pinit), of_rat (0::rat), of_rat (1::rat),
        map_poly of_int (Poly Pinit) :: real poly)"
    and acc_eq: "mset (acc_ivs 0 rpos 0 (dyadic_interval_vec_triples acc))
        = mset (dsc_int 0 1 (Poly Pinit))"
  shows "\<forall>I \<in> set (dyadic_interval_vec_to_list acc). dsc_pair_ok P_real (rat_pair_real I)"
proof
  fix I assume "I \<in> set (dyadic_interval_vec_to_list acc)"
  then obtain t where t_in: "t \<in> set (dyadic_interval_vec_triples acc)"
    and I_eq: "I = dyadic_interval_of_triple t"
    unfolding dyadic_interval_vec_to_list_def by auto
  have niv_in: "node_iv_of 0 rpos 0 t \<in> set (dsc_int 0 1 (Poly Pinit))"
    using t_in acc_eq unfolding acc_ivs_def
    by (metis (no_types, lifting) image_eqI mset_map mset_eq_setD set_map)
  have Pinit0: "Poly Pinit \<noteq> 0"
    unfolding Pinit_def using poly_scale_poly_list_nonzero[OF P0] rpos_pos by simp
  obtain J where J_in: "J \<in> set (dsc (degree (Poly Pinit)) (of_rat 0) (of_rat 1)
      (map_poly of_int (Poly Pinit) :: real poly))"
    and IJ: "node_iv_of 0 rpos 0 t = real_to_rat_pair J"
    and okPinit: "dsc_pair_ok (map_poly of_int (Poly Pinit) :: real poly) J"
    using dsc_int_sound_real_image'[OF dom_init Pinit0 zero_less_one] niv_in by fastforce
  obtain rx ry where J_rat: "J = (of_rat rx, of_rat ry)"
    using dsc_elems_of_rat_image[OF dom_init, of "0::rat" "1::rat"] J_in by auto
  have dit_eq: "I = (rat_of_int rpos * fst (node_iv_of 0 rpos 0 t),
                      rat_of_int rpos * snd (node_iv_of 0 rpos 0 t))"
    using I_eq dyadic_interval_of_triple_eq_r0_times_node_iv_of[OF rpos_pos] by simp
  have scale_eq: "(of_rat (rat_of_int rpos * fst (real_to_rat_pair J)),
                   of_rat (rat_of_int rpos * snd (real_to_rat_pair J)))
      = (of_rat (rat_of_int rpos) * fst J, of_rat (rat_of_int rpos) * snd J :: real)"
    using real_to_rat_pair_scale[OF J_rat, of "rat_of_int rpos"] .
  let ?J' = "(of_rat (rat_of_int rpos) * fst J, of_rat (rat_of_int rpos) * snd J :: real)"
  have I_real: "(of_rat (fst I), of_rat (snd I)) = ?J'"
    using dit_eq IJ scale_eq by simp
  have okP: "dsc_pair_ok P_real ?J'"
    using dsc_pair_ok_scale_poly_list[OF P0 rpos_pos, of J] okPinit
    unfolding P_real_def Pinit_def by (simp add: of_rat_of_int_eq)
  show "dsc_pair_ok P_real (rat_pair_real I)"
    using okP I_real unfolding rat_pair_real_def by simp
qed

lemma lowdeg_lin_pre_len2: "lowdeg_lin_pre xs \<Longrightarrow> 2 \<le> length xs"
  unfolding lowdeg_lin_pre_def by simp

lemma lowdeg_zero_check_len2:
  fixes xs :: "int list"
  assumes len2: "2 \<le> length xs"
  shows "dsc_split_zero_check_monadic xs \<le> SPEC (\<lambda>xs0. xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
  unfolding dsc_split_zero_check_monadic_def PR_CONST_def poly_coeff_sgn_monadic_def
  apply refine_vcg
  using len2 by (auto simp: sgn_eq_0_iff)

lemma bisection_isolate_all_split_pos_half_step_strong:
  fixes xs :: "int list" and kpos :: nat
  assumes pre: "lowdeg_lin_pre xs"
    and kpos_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ kpos"
    and kpos_cap: "kpos * length xs < max_snat LENGTH(gmp_poly_len)"
    and kpos_lt: "kpos < max_snat LENGTH(gmp_poly_len)"
    and cap_at: "bisect_cap_lin xs kpos"
  shows "(doN {
      Pinit \<leftarrow> split_init_pow2_l0_monadic kpos xs;
      ASSERT (0 < length Pinit \<and> length Pinit + 1 < max_snat LENGTH(gmp_poly_len));
      zl \<leftarrow> RETURN (0::int);
      rpos \<leftarrow> mpz_pow2_monadic kpos;
      accP \<leftarrow> bisection_main_list zl rpos 0 Pinit;
      RETURN ();
      RETURN ();
      RETURN accP
    }) \<le> SPEC (half_strong (map_poly of_int (Poly xs) :: real poly))"
proof -
  from pre have sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and lenb0: "kiou_headroom xs"
    unfolding lowdeg_lin_pre_def by auto
  have P0: "Poly xs \<noteq> 0" using sfxs unfolding square_free_def by simp
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF lenb0] by linarith
  define Pinit0 where "Pinit0 = scale_poly_list (2 ^ kpos) xs"
  have Pinit_eq: "carried_init_same_den 0 1 (2 ^ kpos) xs = Pinit0"
    unfolding Pinit0_def by (rule split_init_pow2_l0_eq_scale_poly_list)
  from pre have lastnz: "last xs \<noteq> 0" and len2: "2 \<le> length xs"
    unfolding lowdeg_lin_pre_def by auto
  note sd = bisection_seed_facts_lin[OF len2 lastnz sfxs lenb0 cap_at, folded Pinit0_def]
  have \<delta>_pos: "delta_P (map_poly of_int (Poly Pinit0) :: real poly) > 0" by (rule sd(1))
  have lenPinit: "0 < length Pinit0" by (rule sd(2))
  have small_fast: "\<And>a b. a < b \<Longrightarrow>
        of_rat b - of_rat a \<le> delta_P (map_poly of_int (Poly Pinit0) :: real poly)
        \<Longrightarrow> descartes_list_int a b Pinit0 \<le> 1" by (rule sd(3))
  have lenbPinit: "length Pinit0 + 1 < max_snat LENGTH(gmp_poly_len)" by (rule sd(4))
  have dcap: "0 + rational_interval_mu (delta_P (map_poly of_int (Poly Pinit0) :: real poly))
        (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)" by (rule sd(5))
  have capl: "rational_interval_mu (delta_P (map_poly of_int (Poly Pinit0) :: real poly)) (0, 1) + 3
        < max_snat LENGTH(gmp_poly_len)" by (rule sd(6))
  have dom_init: "dsc_dom (degree (Poly Pinit0), of_rat 0, of_rat 1,
        map_poly of_int (Poly Pinit0) :: real poly)" by (rule sd(7))
  have P0init: "Poly Pinit0 \<noteq> 0" by (rule sd(8))
  have canonPinit: "coeffs (Poly Pinit0) = Pinit0" by (rule sd(9))
  have rpos_pos: "(0::int) < 2 ^ kpos" by simp
  have accD: "length (dsc_int 0 1 (Poly Pinit0)) + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "length (dsc_int 0 1 (Poly Pinit0)) \<le> degree (Poly Pinit0)"
      by (rule dsc_int_length_bound[OF dom_init P0init])
    moreover have "degree (Poly Pinit0) \<le> length Pinit0" using degree_Poly[of Pinit0] by simp
    ultimately show ?thesis using lenbPinit by linarith
  qed
  have carried_init_direct: "split_init_pow2_l0_monadic kpos xs \<le> RETURN Pinit0"
    using split_init_pow2_l0_monadic_correct[OF lenb kpos_cap]
    by (simp add: Pinit_eq)
  have post: "half_strong (map_poly of_int (Poly xs) :: real poly) acc"
    if inv: "dyadic_interval_vec_invar acc"
      and eq: "mset (acc_ivs 0 (2 ^ kpos) 0 (dyadic_interval_vec_triples acc))
               = mset (dsc_int 0 1 (Poly Pinit0))" for acc
  proof -
    have S: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) J"
      by (rule dsc_carried_et_pos_half_sound[OF P0 rpos_pos dom_init[unfolded Pinit0_def] inv
             eq[unfolded Pinit0_def]])
    have R: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
        dsc_pair_ok (map_poly of_int (Poly xs) :: real poly) (rat_pair_real I)"
      by (rule dsc_carried_et_pos_half_sound_real[OF P0 rpos_pos dom_init[unfolded Pinit0_def]
             eq[unfolded Pinit0_def]])
    have St: "(\<forall>x::real. 0 < x \<longrightarrow> x < of_int ((2::int) ^ kpos) \<longrightarrow> poly (map_poly of_int (Poly xs) :: real poly) x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I)))
       \<and> iv_disj_mset (mset (map rat_pair_real (dyadic_interval_vec_to_list acc)))
       \<and> (\<forall>I \<in> set (dyadic_interval_vec_to_list acc). \<forall>x.
            iv_in x (rat_pair_real I) \<longrightarrow> 0 < x \<and> x < of_int ((2::int) ^ kpos))"
      by (rule dsc_carried_et_pos_half_strong[OF P0 rpos_pos dom_init[unfolded Pinit0_def]
             eq[unfolded Pinit0_def]])
    have C: "\<forall>x::real. 0 < x \<longrightarrow> poly (map_poly of_int (Poly xs) :: real poly) x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I))"
    proof (intro allI impI)
      fix x :: real assume x0: "0 < x" and rx: "poly (map_poly of_int (Poly xs) :: real poly) x = 0"
      have "x < 2 ^ kpos" using kpos_sound x0 rx by blast
      then have "x < of_int ((2::int) ^ kpos)" by (simp add: of_int_power)
      then show "\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I)"
        using St x0 rx by blast
    qed
    show ?thesis using inv R S C St by blast
  qed
  show ?thesis
    unfolding PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg
        carried_init_direct[THEN order_trans]
        mpz_pow2_monadic_spec[OF kpos_lt, THEN order_trans]
        bisection_main_list_spec_lin[OF
          \<delta>_pos lenPinit small_fast lenbPinit dcap capl accD rpos_pos dom_init P0init canonPinit,
          THEN order_trans])
    subgoal using lenPinit lenbPinit by simp
    subgoal using lenPinit lenbPinit by simp
    apply (all \<open>use post in blast\<close>)
    done
qed

lemma bisection_isolate_all_split_pos_half_strong:
  fixes xs :: "int list"
  assumes pre: "lowdeg_lin_pre xs"
  shows "dsc_split_pos_solve_monadic xs \<le> SPEC (half_strong (map_poly of_int (Poly xs) :: real poly))"
proof -
  from pre have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs"
    and capY: "kiou_bound_k_monadic xs \<le> SPEC (bisect_cap_lin xs)"
    unfolding lowdeg_lin_pre_def by auto
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  show ?thesis
    unfolding dsc_split_pos_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg kiou_bound_k_monadic_spec_capped_bisect_lin[OF len2 lastnz hr capY, THEN order_trans])
    subgoal using len2 lenb by (cases xs) auto
    subgoal using lenb by simp
    subgoal by blast
    subgoal by blast
    apply (rule bisection_isolate_all_split_pos_half_step_strong[OF pre,
        THEN bind_rule_complete[THEN iffD1]])
       apply blast
      apply blast
     apply blast
    apply blast
    done
qed

lemma bisection_isolate_all_split_neg_half_step_strong:
  fixes xs :: "int list" and Qb :: "int list" and kneg :: nat
  assumes pre: "lowdeg_lin_pre xs"
    and Qb_eq: "Qb = (refl_list xs)"
    and kneg_sound_Qb: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly Qb) x = 0 \<longrightarrow> x < 2 ^ kneg"
    and kneg_cap: "kneg * length Qb < max_snat LENGTH(gmp_poly_len)"
    and kneg_lt: "kneg < max_snat LENGTH(gmp_poly_len)"
    and cap_at: "bisect_cap_lin (refl_list xs) kneg"
  shows "(doN {
      Qinit \<leftarrow> split_init_pow2_l0_monadic kneg Qb;
      poly_free_monadic Qb;
      ASSERT (0 < length Qinit \<and> length Qinit + 1 < max_snat LENGTH(gmp_poly_len));
      zln \<leftarrow> RETURN (0::int);
      rneg \<leftarrow> mpz_pow2_monadic kneg;
      accQ \<leftarrow> bisection_main_list zln rneg 0 Qinit;
      RETURN ();
      RETURN ();
      RETURN accQ
    }) \<le> SPEC (half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly))"
proof -
  have len_Qb: "length Qb = length xs" unfolding Qb_eq by simp
  have kneg_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ kneg"
  proof (intro allI impI)
    fix x :: real assume x0: "0 < x" and hx: "ripoly (Poly (refl_list xs)) x = 0"
    have "ripoly (Poly Qb) x = 0"
      unfolding Qb_eq using hx by (simp add: ripoly_map_uminus)
    thus "x < 2 ^ kneg" using kneg_sound_Qb x0 by simp
  qed
  define Qinit0 where "Qinit0 = scale_poly_list (2 ^ kneg) Qb"
  have Qinit_eq: "carried_init_same_den 0 1 (2 ^ kneg) Qb = Qinit0"
    unfolding Qinit0_def by (rule split_init_pow2_l0_eq_scale_poly_list)
  from pre have len2x: "2 \<le> length xs" and lastnzx: "last xs \<noteq> 0"
    and sfx: "square_free (map_poly of_int (Poly xs) :: real poly)" and hrx: "kiou_headroom xs"
    unfolding lowdeg_lin_pre_def by auto
  have xsne: "xs \<noteq> []" using len2x by auto
  have len2Qb: "2 \<le> length Qb" using len2x unfolding Qb_eq by simp
  have lastnzQb: "last Qb \<noteq> 0" unfolding Qb_eq using last_refl_list_nz[OF xsne lastnzx] .
  have sfQb: "square_free (map_poly of_int (Poly Qb) :: real poly)"
    unfolding Qb_eq using square_free_refl_list[OF sfx] .
  have hrQb: "kiou_headroom Qb" unfolding Qb_eq using kiou_headroom_refl_list[of xs] hrx by simp
  have capQ: "bisect_cap_lin Qb kneg" using cap_at unfolding Qb_eq .
  note sd = bisection_seed_facts_lin[OF len2Qb lastnzQb sfQb hrQb capQ, folded Qinit0_def]
  have \<delta>_pos: "delta_P (map_poly of_int (Poly Qinit0) :: real poly) > 0" by (rule sd(1))
  have lenQinit: "0 < length Qinit0" by (rule sd(2))
  have small_fast: "\<And>a b. a < b \<Longrightarrow>
        of_rat b - of_rat a \<le> delta_P (map_poly of_int (Poly Qinit0) :: real poly)
        \<Longrightarrow> descartes_list_int a b Qinit0 \<le> 1" by (rule sd(3))
  have lenbQinit: "length Qinit0 + 1 < max_snat LENGTH(gmp_poly_len)" by (rule sd(4))
  have dcap: "0 + rational_interval_mu (delta_P (map_poly of_int (Poly Qinit0) :: real poly))
        (0, 1) + 1 < max_snat LENGTH(gmp_poly_len)" by (rule sd(5))
  have capl: "rational_interval_mu (delta_P (map_poly of_int (Poly Qinit0) :: real poly)) (0, 1) + 3
        < max_snat LENGTH(gmp_poly_len)" by (rule sd(6))
  have dom_init: "dsc_dom (degree (Poly Qinit0), of_rat 0, of_rat 1,
        map_poly of_int (Poly Qinit0) :: real poly)" by (rule sd(7))
  have Q0init: "Poly Qinit0 \<noteq> 0" by (rule sd(8))
  have canonQinit: "coeffs (Poly Qinit0) = Qinit0" by (rule sd(9))
  have rneg_pos: "(0::int) < 2 ^ kneg" by simp
  have accD: "length (dsc_int 0 1 (Poly Qinit0)) + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "length (dsc_int 0 1 (Poly Qinit0)) \<le> degree (Poly Qinit0)"
      by (rule dsc_int_length_bound[OF dom_init Q0init])
    moreover have "degree (Poly Qinit0) \<le> length Qinit0" using degree_Poly[of Qinit0] by simp
    ultimately show ?thesis using lenbQinit by linarith
  qed
  have Q0: "Poly Qb \<noteq> 0"
  proof
    assume contra: "Poly Qb = 0"
    have "(map_poly of_int (Poly Qinit0) :: real poly)
        = (map_poly of_int (Poly Qb) :: real poly) \<circ>\<^sub>p [:0, of_int (2 ^ kneg):]"
      unfolding Qinit0_def by (rule Poly_scale_poly_list_eq_pcompose)
    also have "\<dots> = 0" using contra by simp
    finally have "(map_poly of_int (Poly Qinit0) :: real poly) = 0" .
    hence "Poly Qinit0 = 0" by simp
    thus False using Q0init by contradiction
  qed
  have Q0real: "Poly (refl_list xs) \<noteq> 0" using Q0 unfolding Qb_eq by simp
  have hr: "kiou_headroom xs" using pre unfolding lowdeg_lin_pre_def by auto
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have lenbQb: "length Qb + 1 < max_snat LENGTH(gmp_poly_len)"
    using lenb unfolding len_Qb .
  have carried_init_direct: "split_init_pow2_l0_monadic kneg Qb \<le> RETURN Qinit0"
    using split_init_pow2_l0_monadic_correct[OF lenbQb kneg_cap]
    by (simp add: Qinit_eq)
  have post: "half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly) acc"
    if inv: "dyadic_interval_vec_invar acc"
      and eq: "mset (acc_ivs 0 (2 ^ kneg) 0 (dyadic_interval_vec_triples acc))
               = mset (dsc_int 0 1 (Poly Qinit0))" for acc
  proof -
    have S: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
        \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) J"
      by (rule dsc_carried_et_neg_half_sound[OF Q0real rneg_pos
             dom_init[unfolded Qinit0_def Qb_eq] inv eq[unfolded Qinit0_def Qb_eq]])
    have R: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
        dsc_pair_ok (map_poly of_int (Poly (refl_list xs)) :: real poly) (rat_pair_real I)"
      by (rule dsc_carried_et_pos_half_sound_real[OF Q0real rneg_pos
             dom_init[unfolded Qinit0_def Qb_eq] eq[unfolded Qinit0_def Qb_eq]])
    have St: "(\<forall>x::real. 0 < x \<longrightarrow> x < of_int ((2::int) ^ kneg) \<longrightarrow>
              poly (map_poly of_int (Poly (refl_list xs)) :: real poly) x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I)))
       \<and> iv_disj_mset (mset (map rat_pair_real (dyadic_interval_vec_to_list acc)))
       \<and> (\<forall>I \<in> set (dyadic_interval_vec_to_list acc). \<forall>x.
            iv_in x (rat_pair_real I) \<longrightarrow> 0 < x \<and> x < of_int ((2::int) ^ kneg))"
      by (rule dsc_carried_et_pos_half_strong[OF Q0real rneg_pos
             dom_init[unfolded Qinit0_def Qb_eq] eq[unfolded Qinit0_def Qb_eq]])
    have C: "\<forall>x::real. 0 < x \<longrightarrow> poly (map_poly of_int (Poly (refl_list xs)) :: real poly) x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I))"
    proof (intro allI impI)
      fix x :: real assume x0: "0 < x"
        and rx: "poly (map_poly of_int (Poly (refl_list xs)) :: real poly) x = 0"
      have "x < 2 ^ kneg" using kneg_sound x0 rx by blast
      then have "x < of_int ((2::int) ^ kneg)" by (simp add: of_int_power)
      then show "\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I)"
        using St x0 rx by blast
    qed
    show ?thesis using inv R S C St by blast
  qed
  show ?thesis
    apply (refine_vcg
        carried_init_direct[THEN order_trans]
        mpz_pow2_monadic_spec[OF kneg_lt, THEN order_trans]
        bisection_main_list_spec_lin[OF
          \<delta>_pos lenQinit small_fast lenbQinit dcap capl accD rneg_pos dom_init Q0init canonQinit,
          THEN order_trans])
    subgoal using lenQinit lenbQinit by simp
    subgoal using lenQinit lenbQinit by simp
    apply (all \<open>use post in blast\<close>)
    done
qed

lemma bisection_isolate_all_split_neg_half_bridge_strong:
  fixes xs :: "int list"
  assumes pre: "lowdeg_lin_pre xs"
  shows "(doN {
      kneg \<leftarrow> kiou_bound_k_monadic (refl_list xs);
      ASSERT (kneg * length (refl_list xs) < max_snat LENGTH(gmp_poly_len) \<and>
        kneg < max_snat LENGTH(gmp_poly_len));
      Qinit \<leftarrow> split_init_pow2_l0_monadic kneg (refl_list xs);
      poly_free_monadic (refl_list xs);
      ASSERT (0 < length Qinit \<and> length Qinit + 1 < max_snat LENGTH(gmp_poly_len));
      zln \<leftarrow> RETURN (0::int);
      rneg \<leftarrow> mpz_pow2_monadic kneg;
      accQ \<leftarrow> bisection_main_list zln rneg 0 Qinit;
      RETURN ();
      RETURN ();
      RETURN accQ
    }) \<le> SPEC (half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly))"
proof -
  from pre have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and xsne: "xs \<noteq> []"
    unfolding lowdeg_lin_pre_def by auto
  have lastnzQb: "last (refl_list xs) \<noteq> 0" using last_refl_list_nz[OF xsne lastnz] .
  have hrQb: "kiou_headroom (refl_list xs)" using kiou_headroom_refl_list[of xs] hr by simp
  have len2Qb: "2 \<le> length (refl_list xs)" using len2 by simp
  have capYQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (bisect_cap_lin (refl_list xs))"
    using pre unfolding lowdeg_lin_pre_def by auto
  show ?thesis
    apply (refine_vcg kiou_bound_k_monadic_spec_capped_bisect_lin[OF len2Qb lastnzQb hrQb capYQb,
        THEN order_trans])
    subgoal by blast
    subgoal by blast
    apply (rule bisection_isolate_all_split_neg_half_step_strong[OF pre refl,
        THEN bind_rule_complete[THEN iffD1]])
       apply blast
      apply blast
     apply blast
    apply blast
    done
qed

lemma bisection_isolate_all_split_neg_half_strong:
  fixes xs :: "int list"
  assumes pre: "lowdeg_lin_pre xs"
  shows "dsc_split_neg_solve_monadic xs
    \<le> SPEC (half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly))"
proof -
  from pre have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and xsne: "xs \<noteq> []"
    unfolding lowdeg_lin_pre_def by auto
  have len2Qb: "2 \<le> length (refl_list xs)" using len2 by simp
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have lenscaleQb: "length (refl_list xs) + 1 < max_snat LENGTH(gmp_poly_len)"
    using lenb by simp
  have Qbne: "refl_list xs \<noteq> []" using len2Qb by (cases "refl_list xs") auto
  have lenbQb: "length (refl_list xs) + 1 < max_snat LENGTH(gmp_poly_len)"
    using lenb by simp
  have poly_reflect_correct: "poly_reflect_in_place_monadic xs \<le> RETURN (refl_list xs)"
    using poly_reflect_in_place_correct[OF lenb] by (simp add: refl_list_def)
  show ?thesis
    unfolding dsc_split_neg_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def poly_length_monadic_def
    apply (refine_vcg
        poly_clone_monadic_correct[OF lenb, THEN order_trans]
        poly_reflect_correct[THEN order_trans])
    subgoal using len2 len2Qb lenb lenscaleQb Qbne lenbQb by auto
    subgoal using len2 len2Qb lenb lenscaleQb Qbne lenbQb by auto
    subgoal using len2 len2Qb lenb lenscaleQb Qbne lenbQb by auto
    apply (rule bisection_isolate_all_split_neg_half_bridge_strong[OF pre,
        THEN bind_rule_complete[THEN iffD1]])
    done
qed

theorem bisection_isolate_all_split_main_correct_strong:
  fixes xs :: "int list"
  assumes pre: "lowdeg_lin_pre xs"
  shows "bisection_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accQ, xs0).
      half_strong (map_poly of_int (Poly xs) :: real poly) accP
    \<and> half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly) accQ
    \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  have len2: "2 \<le> length xs" using pre unfolding lowdeg_lin_pre_def by auto
  show ?thesis
    unfolding bisection_isolate_all_split_main_def PR_CONST_def
    apply (refine_vcg
        bisection_isolate_all_split_pos_half_strong[OF pre, THEN order_trans]
        bisection_isolate_all_split_neg_half_strong[OF pre, THEN order_trans]
        lowdeg_zero_check_len2[OF lowdeg_lin_pre_len2[OF pre], THEN order_trans])
    using len2 by auto
qed

lemma rat_pair_real_zero_pow2[simp]:
  "rat_pair_real (real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)) = (0, 2 ^ k)"
  by (simp add: real_to_rat_pair_zero_pow2 rat_pair_real_def of_rat_power)

text \<open>\<open>lowdeg_push_one_window\<close> with the vector invariant kept in the postcondition: the exported
  store loops read the right-endpoint and exponent columns at every index of the left one, so the
  theorem about the exported function needs the three columns to have equal length.\<close>
lemma lowdeg_push_one_window_inv:
  fixes k :: nat
  assumes invar: "dyadic_interval_vec_invar acc"
    and push: "dyadic_interval_vec_pushable acc"
    and empty: "dyadic_interval_vec_to_list acc = []"
  shows "dyadic_interval_vec_push_monadic acc 0 (2 ^ k) 0
           \<le> SPEC (\<lambda>v. dyadic_interval_vec_invar v \<and> dyadic_interval_vec_to_list v
                          = [real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)])"
  apply (rule order_trans[OF dyadic_push_spec_any[OF invar push]])
  using empty by (auto simp: dyadic_triple_zero_pow2 real_to_rat_pair_zero_pow2)

lemma lowdeg_emit_pos_one_shape:
  fixes ys :: "int list"
  assumes len2: "2 \<le> length ys" and lastnz: "last ys \<noteq> 0"
    and hr: "kiou_headroom ys"
    and capY: "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k. k * length ys < max_snat LENGTH(gmp_poly_len))"
  shows "lowdeg_emit_pos_monadic True ys
           \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
                        (\<exists>k. (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k)
                          \<and> dyadic_interval_vec_to_list acc = [real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)]))"
proof -
  have lenb: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have room: "(1::nat) < max_snat LENGTH(gmp_poly_len)" using len2 lenb by linarith
  have ysne: "ys \<noteq> []" using len2 by (cases ys) auto
  have len1: "1 \<le> length ys" using len2 by linarith
  show ?thesis
    unfolding lowdeg_emit_pos_monadic_def PR_CONST_def mpz_from_int_def
    apply (refine_vcg
        dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans]
        kiou_bound_k_monadic_spec_kcap[OF len2 lastnz hr capY, THEN order_trans]
        mpz_pow2_monadic_spec[THEN order_trans]
        lowdeg_push_one_window_inv[THEN order_trans])
    apply (all \<open>(solves \<open>use len1 len2 lenb ysne room in auto\<close>)?\<close>)
    apply (all \<open>(solves \<open>use room in \<open>auto intro: dyadic_vec_empty_pushable\<close>\<close>)?\<close>)
    apply (all \<open>(solves \<open>blast\<close>)?\<close>)
    done
qed

lemma lowdeg_one_window_half_strong:
  fixes ys :: "int list" and k :: nat
  assumes sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and bound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k"
    and one: "\<exists>!x::real. 0 < x \<and> ripoly (Poly ys) x = 0"
    and lst: "dyadic_interval_vec_to_list acc = [real_to_rat_pair ((0, 2 ^ k) :: real \<times> real)]"
    and inv: "dyadic_interval_vec_invar acc"
  shows "half_strong (map_poly of_int (Poly ys) :: real poly) acc"
proof -
  have S: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
            \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) J"
    by (rule lowdeg_one_window_isolates_list[OF sf bound one lst])
  have R: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc).
            dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) (rat_pair_real I)"
  proof -
    have ok: "dsc_pair_ok (map_poly of_int (Poly ys) :: real poly) (0, 2 ^ k)"
      using lowdeg_bound_window_isolates[OF sf _ one] bound by blast
    show ?thesis unfolding lst using ok
      by (simp add: real_to_rat_pair_zero_pow2 rat_pair_real_def of_rat_power)
  qed
  have C: "\<forall>x::real. 0 < x \<longrightarrow> poly (map_poly of_int (Poly ys) :: real poly) x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I))"
    using bound unfolding lst by (auto simp: iv_in_def)
  have U: "iv_disj_mset (mset (map rat_pair_real (dyadic_interval_vec_to_list acc)))"
    unfolding lst by simp
  have IN: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc). \<forall>x. iv_in x (rat_pair_real I) \<longrightarrow> 0 < x"
    unfolding lst by (auto simp: iv_in_def)
  show ?thesis using inv R S C U IN by blast
qed

lemma lowdeg_emit_pos_one_strong:
  fixes ys :: "int list"
  assumes len2: "2 \<le> length ys" and lastnz: "last ys \<noteq> 0"
    and hr: "kiou_headroom ys"
    and capY: "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k. k * length ys < max_snat LENGTH(gmp_poly_len))"
    and sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and one: "\<exists>!x::real. 0 < x \<and> ripoly (Poly ys) x = 0"
  shows "lowdeg_emit_pos_monadic True ys \<le> SPEC (half_strong (map_poly of_int (Poly ys) :: real poly))"
  by (rule weaken_SPEC[OF lowdeg_emit_pos_one_shape[OF len2 lastnz hr capY]])
     (use lowdeg_one_window_half_strong[OF sf _ one] in blast)

lemma lowdeg_emit_pos_zero_strong:
  fixes ys :: "int list"
  assumes none: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly ys) x \<noteq> 0"
  shows "lowdeg_emit_pos_monadic False ys \<le> SPEC (half_strong (map_poly of_int (Poly ys) :: real poly))"
  unfolding lowdeg_emit_pos_monadic_def PR_CONST_def
  apply (refine_vcg dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans]
      lowdeg_vec_empty_sz_monadic_spec[THEN order_trans])
  using none by (auto simp: iv_disj_mset_def dyadic_interval_vec_invar_def)

lemma lowdeg_emit_neg_one_strong:
  fixes xs :: "int list"
  assumes pre: "lowdeg_lin_pre xs"
    and one: "\<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0"
  shows "lowdeg_emit_neg_monadic True xs
           \<le> SPEC (half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly))"
proof -
  note arm = lowdeg_arm_pre[OF lowdeg_lin_pre_basic[OF pre]]
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF arm(3)] by linarith
  have reflect: "poly_reflect_in_place_monadic xs \<le> RETURN (refl_list xs)"
    using poly_reflect_in_place_correct[OF lenb] by (simp add: refl_list_def)
  have body: "lowdeg_emit_pos_monadic True (refl_list xs)
      \<le> SPEC (half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly))"
    by (rule lowdeg_emit_pos_one_strong[OF arm(6) arm(7) arm(8) arm(9) arm(10) one])
  show ?thesis
    unfolding lowdeg_emit_neg_monadic_def PR_CONST_def poly_free_monadic_def
    apply (refine_vcg
        poly_clone_monadic_correct[OF lenb, THEN order_trans]
        reflect[THEN order_trans]
        body[THEN order_trans])
    using lenb arm(1) by auto
qed

lemma lowdeg_emit_neg_zero_strong:
  fixes xs :: "int list"
  assumes pre: "lowdeg_lin_pre xs"
    and none: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
  shows "lowdeg_emit_neg_monadic False xs
           \<le> SPEC (half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly))"
  unfolding lowdeg_emit_neg_monadic_def PR_CONST_def
  apply (refine_vcg dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans]
      lowdeg_vec_empty_sz_monadic_spec[THEN order_trans])
  using none by (auto simp: iv_disj_mset_def dyadic_interval_vec_invar_def)

lemma lowdeg_two_window_half_strong:
  fixes ys :: "int list" and q :: int and j k :: nat
  assumes sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and len3: "length ys = 3" and anz: "ys ! 2 \<noteq> 0"
    and sepr: "of_int (ys!2) *
               (of_int (ys!2) * ((of_int q :: real) / 2 ^ j)\<^sup>2 +
                of_int (ys!1) * ((of_int q :: real) / 2 ^ j) +
                of_int (ys!0)) < (0::real)"
    and bound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k"
    and pos: "\<And>x::real. ripoly (Poly ys) x = 0 \<Longrightarrow> 0 < x"
    and lst: "dyadic_interval_vec_to_list acc =
                [dyadic_interval_of_triple (((0::int), q), j),
                 dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)]"
    and inv: "dyadic_interval_vec_invar acc"
  shows "half_strong (map_poly of_int (Poly ys) :: real poly) acc"
proof -
  let ?P = "map_poly of_int (Poly ys) :: real poly"
  let ?t = "(of_int q :: real) / 2 ^ j"
  have bound': "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly ys) x = 0 \<Longrightarrow> x < 2 ^ k" using bound by blast
  have S: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc). \<exists>J. I = real_to_rat_pair J \<and> dsc_pair_ok ?P J"
    by (rule lowdeg_two_window_isolates_list[OF sf len3 anz sepr bound' pos lst])
  have wins: "dsc_pair_ok ?P (0, ?t)" "dsc_pair_ok ?P (?t, 2 ^ k)"
    using lowdeg_deg2_two_windows[OF len3 anz sf sepr bound' pos] by blast+
  have P00: "poly ?P 0 \<noteq> 0" using pos by force
  have t0: "0 < ?t" using wins(1) P00 unfolding dsc_pair_ok_def by auto
  have tnr: "poly ?P ?t \<noteq> 0"
  proof
    assume pt: "poly ?P ?t = 0"
    have ev: "poly ?P ?t = of_int (ys!2) * ?t\<^sup>2 + of_int (ys!1) * ?t + of_int (ys!0)"
      using poly_of_int_Poly_deg2[OF len3] by simp
    have z: "(of_int (ys!2) * ?t\<^sup>2 + of_int (ys!1) * ?t + of_int (ys!0) :: real) = 0"
      using pt unfolding ev .
    from sepr show False unfolding z by simp
  qed
  have tk: "?t < 2 ^ k"
  proof -
    have "?t = 2 ^ k \<longrightarrow> poly ?P ?t = 0" using wins(2) unfolding dsc_pair_ok_def by auto
    moreover have "?t \<le> 2 ^ k" using wins(2) unfolding dsc_pair_ok_def by auto
    ultimately show ?thesis using tnr by linarith
  qed
  have e1: "rat_pair_real (dyadic_interval_of_triple (((0::int), q), j)) = (0, ?t)"
    by (simp add: dyadic_triple_zero_num rat_pair_real_def of_rat_divide of_rat_power)
  have e2: "rat_pair_real (dyadic_interval_of_triple ((q, 2 ^ (k + j)), j)) = (?t, 2 ^ k)"
    by (simp add: dyadic_triple_num_pow2 rat_pair_real_def of_rat_divide of_rat_power)
  have R: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc). dsc_pair_ok ?P (rat_pair_real I)"
    unfolding lst using wins by (simp add: e1 e2)
  have C: "\<forall>x::real. 0 < x \<longrightarrow> poly ?P x = 0 \<longrightarrow>
            (\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I))"
  proof (intro allI impI)
    fix x :: real assume x0: "0 < x" and rx: "poly ?P x = 0"
    have xk: "x < 2 ^ k" using bound x0 rx by blast
    have xt: "x \<noteq> ?t" using rx tnr by auto
    show "\<exists>I \<in> set (dyadic_interval_vec_to_list acc). iv_in x (rat_pair_real I)"
    proof (cases "x < ?t")
      case True then show ?thesis using x0 unfolding lst by (auto simp: e1 iv_in_def)
    next
      case False then have "?t < x" using xt by linarith
      then show ?thesis using xk unfolding lst by (auto simp: e2 iv_in_def)
    qed
  qed
  have U: "iv_disj_mset (mset (map rat_pair_real (dyadic_interval_vec_to_list acc)))"
  proof -
    have m: "mset (map rat_pair_real (dyadic_interval_vec_to_list acc)) = {#(0, ?t)#} + {#(?t, 2 ^ k)#}"
      unfolding lst by (simp add: e1 e2)
    have d: "iv_disj (0, ?t) (?t, 2 ^ k)"
      using t0 tk unfolding iv_disj_def iv_in_def by auto
    have "iv_disj_mset ({#(0, ?t)#} + {#(?t, 2 ^ k)#})"
      by (rule iv_disj_mset_union) (use d in auto)
    then show ?thesis unfolding m .
  qed
  have IN: "\<forall>I \<in> set (dyadic_interval_vec_to_list acc). \<forall>x. iv_in x (rat_pair_real I) \<longrightarrow> 0 < x"
    using t0 tk unfolding lst by (auto simp: e1 e2 iv_in_def)
  show ?thesis using inv R S C U IN by blast
qed

lemma lowdeg_emit_two_pos_shape:
  fixes ys :: "int list"
  assumes len3: "length ys = 3" and lastnz: "last ys \<noteq> 0"
    and hr: "kiou_headroom ys"
    and capY: "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k. k * length ys < max_snat LENGTH(gmp_poly_len))"
  shows "lowdeg_emit_two_pos_monadic ys
           \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
               (\<exists>k. (\<forall>x::real. 0 < x \<longrightarrow> poly (real_of_int_poly (Poly ys)) x = 0 \<longrightarrow> x < 2 ^ k)
               \<and> dyadic_interval_vec_to_list acc =
                   [dyadic_interval_of_triple (((0::int), lowdeg_sep_q False 64 ys), 64),
                    dyadic_interval_of_triple ((lowdeg_sep_q False 64 ys, 2 ^ (k + 64)), 64)]))"
proof -
  have len2: "2 \<le> length ys" using len3 by linarith
  have lenb: "length ys + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have room: "(1::nat) < max_snat LENGTH(gmp_poly_len)" using len2 lenb by linarith
  have room2: "(2::nat) < max_snat LENGTH(gmp_poly_len)" using len2 lenb by linarith
  have mbig: "(96::nat) \<le> max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
  have kroom: "k + 64 < max_snat LENGTH(gmp_poly_len)"
    if kc: "k * length ys < max_snat LENGTH(gmp_poly_len)" for k :: nat
  proof -
    have "3 * k < max_snat LENGTH(gmp_poly_len)" using kc len3 by (simp add: mult.commute)
    thus ?thesis using mbig by linarith
  qed
  have ysne: "ys \<noteq> []" using len2 by (cases ys) auto
  have anz: "ys ! 2 \<noteq> 0" using lastnz ysne len3 by (simp add: last_conv_nth)
  have j64: "lowdeg_sep_j = 64" by (simp add: lowdeg_sep_j_def)
  show ?thesis
    unfolding lowdeg_emit_two_pos_monadic_def PR_CONST_def mpz_from_int_def COPY_def
    apply (refine_vcg
        lowdeg_sep_num_monadic_correct[THEN order_trans]
        kiou_bound_k_monadic_spec_kcap[OF len2 lastnz hr capY, THEN order_trans]
        mpz_pow2_monadic_spec[THEN order_trans]
        dyadic_interval_vec_empty_sz_monadic_spec[THEN order_trans]
        dyadic_push_spec_any[THEN order_trans])
    apply (all \<open>(solves \<open>use len2 len3 lenb ysne room room2 anz j64 mbig in
                          \<open>auto dest: kroom\<close>\<close>)?\<close>)
    apply (all \<open>(solves \<open>use room room2 mbig in
                          \<open>auto intro: dyadic_vec_pushable_of_len dyadic_vec_empty_pushable simp: dyadic_interval_vec_triples_def max_snat_def\<close>\<close>)?\<close>)
    apply (all \<open>(solves \<open>elim conjE; rule conjI; (assumption | (rule exI; rule conjI; (assumption |
                          (rule dyadic_interval_vec_two_push; assumption))))\<close>)?\<close>)
    done
qed

lemma lowdeg_emit_two_pos_strong:
  fixes ys :: "int list"
  assumes len3: "length ys = 3" and lastnz: "last ys \<noteq> 0"
    and hr: "kiou_headroom ys"
    and capY: "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k. k * length ys < max_snat LENGTH(gmp_poly_len))"
    and sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and pos: "\<And>x::real. ripoly (Poly ys) x = 0 \<Longrightarrow> 0 < x"
    and sep: "lowdeg_sep_ok_pure False ys"
  shows "lowdeg_emit_two_pos_monadic ys \<le> SPEC (half_strong (map_poly of_int (Poly ys) :: real poly))"
proof -
  have len2: "2 \<le> length ys" using len3 by linarith
  have ysne: "ys \<noteq> []" using len2 by (cases ys) auto
  have anz: "ys ! 2 \<noteq> 0" using lastnz ysne len3 by (simp add: last_conv_nth)
  have sepr: "of_int (ys!2) *
      (of_int (ys!2) * ((of_int (lowdeg_sep_q False lowdeg_sep_j ys) :: real) / 2 ^ lowdeg_sep_j)\<^sup>2
       + of_int (ys!1) * ((of_int (lowdeg_sep_q False lowdeg_sep_j ys) :: real) / 2 ^ lowdeg_sep_j)
       + of_int (ys!0)) < (0::real)"
    by (rule lowdeg_sep_bridge[OF sep])
  have sepr64: "of_int (ys!2) *
                  (of_int (ys!2) * ((of_int (lowdeg_sep_q False 64 ys) :: real) / 2 ^ 64)\<^sup>2
                   + of_int (ys!1) * ((of_int (lowdeg_sep_q False 64 ys) :: real) / 2 ^ 64)
                   + of_int (ys!0)) < (0::real)"
    using sepr[unfolded lowdeg_sep_j_def] .
  show ?thesis
    by (rule weaken_SPEC[OF lowdeg_emit_two_pos_shape[OF len3 lastnz hr capY]])
       (use lowdeg_two_window_half_strong[OF sf len3 anz sepr64 _ pos] in blast)
qed

lemma lowdeg_emit_two_neg_strong:
  fixes xs :: "int list"
  assumes pre: "lowdeg_lin_pre xs" and len3: "length xs = 3"
    and pos: "\<And>x::real. ripoly (Poly (refl_list xs)) x = 0 \<Longrightarrow> 0 < x"
    and sep: "lowdeg_sep_ok_pure False (refl_list xs)"
  shows "lowdeg_emit_two_neg_monadic xs
           \<le> SPEC (half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly))"
proof -
  note arm = lowdeg_arm_pre[OF lowdeg_lin_pre_basic[OF pre]]
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF arm(3)] by linarith
  have len3R: "length (refl_list xs) = 3" using len3 by simp
  have reflect: "poly_reflect_in_place_monadic xs \<le> RETURN (refl_list xs)"
    using poly_reflect_in_place_correct[OF lenb] by (simp add: refl_list_def)
  have body: "lowdeg_emit_two_pos_monadic (refl_list xs)
      \<le> SPEC (half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly))"
    by (rule lowdeg_emit_two_pos_strong[OF len3R arm(7) arm(8) arm(9) arm(10) pos sep])
  show ?thesis
    unfolding lowdeg_emit_two_neg_monadic_def PR_CONST_def poly_free_monadic_def
    apply (refine_vcg
        poly_clone_monadic_correct[OF lenb, THEN order_trans]
        reflect[THEN order_trans]
        body[THEN order_trans])
    using lenb arm(1) by auto
qed

lemma lowdeg_body_strong:
  fixes xs :: "int list" and cl :: nat
  assumes pre: "lowdeg_lin_pre xs"
    and cls: "cl \<in> {0,1,2,3,4,5,6}"
    and posone: "cl = 2 \<or> cl = 4 \<Longrightarrow> \<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0"
    and posnone: "cl = 1 \<or> cl = 3 \<Longrightarrow> \<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0"
    and negone: "cl = 3 \<or> cl = 4 \<Longrightarrow> \<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0"
    and negnone: "cl = 1 \<or> cl = 2 \<Longrightarrow> \<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
    and postwo: "cl = 5 \<Longrightarrow> length xs = 3 \<and>
                   (\<forall>x::real. ripoly (Poly xs) x = 0 \<longrightarrow> 0 < x) \<and>
                   (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0) \<and>
                   lowdeg_sep_ok_pure False xs"
    and negtwo: "cl = 6 \<Longrightarrow> length xs = 3 \<and>
                   (\<forall>x::real. ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> 0 < x) \<and>
                   (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
                   lowdeg_sep_ok_pure False (refl_list xs)"
  shows "(if cl = 0 then bisection_isolate_all_split_main xs
          else doN {
            accP \<leftarrow> (if cl = 5 then lowdeg_emit_two_pos_monadic xs
                               else lowdeg_emit_pos_monadic (cl = 2 \<or> cl = 4) xs);
            accQ \<leftarrow> (if cl = 6 then lowdeg_emit_two_neg_monadic xs
                               else lowdeg_emit_neg_monadic (cl = 3 \<or> cl = 4) xs);
            xs0 \<leftarrow> dsc_split_zero_check_monadic xs;
            RETURN (accP, accQ, xs0)
          }) \<le> SPEC (\<lambda>(accP, accQ, xs0).
      half_strong (map_poly of_int (Poly xs) :: real poly) accP
    \<and> half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly) accQ
    \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof (cases "cl = 0")
  case True
  thus ?thesis using bisection_isolate_all_split_main_correct_strong[OF pre] by simp
next
  case False
  with cls have cls': "cl = 1 \<or> cl = 2 \<or> cl = 3 \<or> cl = 4 \<or> cl = 5 \<or> cl = 6" by auto
  note arm = lowdeg_arm_pre[OF lowdeg_lin_pre_basic[OF pre]]
  let ?PP = "half_strong (map_poly of_int (Poly xs) :: real poly)"
  let ?QQ = "half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly)"
  have P5: "lowdeg_emit_two_pos_monadic xs \<le> SPEC ?PP" if h: "cl = 5"
  proof -
    note c = postwo[OF h]
    have len3: "length xs = 3" using c by simp
    have lastnz: "last xs \<noteq> 0" using arm(2) .
    have pos: "\<And>x::real. ripoly (Poly xs) x = 0 \<Longrightarrow> 0 < x" using c by blast
    have sep: "lowdeg_sep_ok_pure False xs" using c by blast
    show ?thesis
      by (rule lowdeg_emit_two_pos_strong[OF len3 lastnz arm(3) arm(4) arm(5) pos sep])
  qed
  have P04: "lowdeg_emit_pos_monadic (cl = 2 \<or> cl = 4) xs \<le> SPEC ?PP" if n5: "cl \<noteq> 5"
  proof (cases "cl = 2 \<or> cl = 4")
    case True
    hence b: "(cl = 2 \<or> cl = 4) = True" by simp
    show ?thesis unfolding b
      by (rule lowdeg_emit_pos_one_strong[OF arm(1) arm(2) arm(3) arm(4) arm(5) posone[OF True]])
  next
    case n24: False
    from n24 have b: "(cl = 2 \<or> cl = 4) = False" by simp
    have nn: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x \<noteq> 0"
    proof (cases "cl = 6")
      case True
      show "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x \<noteq> 0" using negtwo[OF True] by blast
    next
      case n6: False
      with n24 n5 cls' have h: "cl = 1 \<or> cl = 3" by auto
      show "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly xs) x \<noteq> 0" using posnone[OF h] by blast
    qed
    show ?thesis unfolding b by (rule lowdeg_emit_pos_zero_strong[OF nn])
  qed
  have P: "(if cl = 5 then lowdeg_emit_two_pos_monadic xs
            else lowdeg_emit_pos_monadic (cl = 2 \<or> cl = 4) xs) \<le> SPEC ?PP"
    using P5 P04 by simp
  have Q6: "lowdeg_emit_two_neg_monadic xs \<le> SPEC ?QQ" if h: "cl = 6"
  proof -
    note c = negtwo[OF h]
    have len3: "length xs = 3" using c by simp
    have pos: "\<And>x::real. ripoly (Poly (refl_list xs)) x = 0 \<Longrightarrow> 0 < x" using c by blast
    have sep: "lowdeg_sep_ok_pure False (refl_list xs)" using c by blast
    show ?thesis by (rule lowdeg_emit_two_neg_strong[OF pre len3 pos sep])
  qed
  have Q34: "lowdeg_emit_neg_monadic (cl = 3 \<or> cl = 4) xs \<le> SPEC ?QQ" if n6: "cl \<noteq> 6"
  proof (cases "cl = 3 \<or> cl = 4")
    case True
    hence b: "(cl = 3 \<or> cl = 4) = True" by simp
    show ?thesis unfolding b by (rule lowdeg_emit_neg_one_strong[OF pre negone[OF True]])
  next
    case n34: False
    from n34 have b: "(cl = 3 \<or> cl = 4) = False" by simp
    have nn: "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
    proof (cases "cl = 5")
      case True
      show "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
        using postwo[OF True] by blast
    next
      case n5: False
      with n34 n6 cls' have h: "cl = 1 \<or> cl = 2" by auto
      show "\<And>x::real. 0 < x \<Longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
        using negnone[OF h] by blast
    qed
    show ?thesis unfolding b by (rule lowdeg_emit_neg_zero_strong[OF pre nn])
  qed
  have Q: "(if cl = 6 then lowdeg_emit_two_neg_monadic xs
            else lowdeg_emit_neg_monadic (cl = 3 \<or> cl = 4) xs) \<le> SPEC ?QQ"
    using Q6 Q34 by simp
  have c0: "(cl = 0) = False" using False by simp
  show ?thesis
    unfolding c0 if_False
    apply (refine_vcg P[THEN order_trans] Q[THEN order_trans]
        lowdeg_zero_check_len2[OF lowdeg_lin_pre_len2[OF pre], THEN order_trans])
    apply (all \<open>(solves \<open>blast\<close>)?\<close>)
    done
qed

theorem lowdeg_isolate_all_split_main_correct_strong:
  fixes xs :: "int list"
  assumes pre: "lowdeg_lin_pre xs"
  shows "lowdeg_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accQ, xs0).
      half_strong (map_poly of_int (Poly xs) :: real poly) accP
    \<and> half_strong (map_poly of_int (Poly (refl_list xs)) :: real poly) accQ
    \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  from pre have len2: "2 \<le> length xs" unfolding lowdeg_lin_pre_def by auto
  show ?thesis
    unfolding lowdeg_isolate_all_split_main_def PR_CONST_def
    apply (simp add: len2)
    apply (rule nres_bind_SPEC_extend[OF lowdeg_class_correct[OF lowdeg_lin_pre_basic[OF pre]]])
    subgoal premises b for cl
    proof -
      have cls: "cl \<in> {0,1,2,3,4,5,6}" using b by (rule conjunct1)
      note b1 = b[THEN conjunct2]
      note i1 = b1[THEN conjunct1] and b2 = b1[THEN conjunct2]
      note i2 = b2[THEN conjunct1] and b3 = b2[THEN conjunct2]
      note i3 = b3[THEN conjunct1] and b4 = b3[THEN conjunct2]
      note i4 = b4[THEN conjunct1] and b5 = b4[THEN conjunct2]
      note i5 = b5[THEN conjunct1] and i6 = b5[THEN conjunct2]
      have posone: "cl = 2 \<or> cl = 4 \<Longrightarrow> \<exists>!x::real. 0 < x \<and> ripoly (Poly xs) x = 0"
        using i2 i4 by blast
      have posnone: "cl = 1 \<or> cl = 3 \<Longrightarrow> \<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0"
        using i1 i3 by blast
      have negone: "cl = 3 \<or> cl = 4 \<Longrightarrow> \<exists>!x::real. 0 < x \<and> ripoly (Poly (refl_list xs)) x = 0"
        using i3 i4 by blast
      have negnone: "cl = 1 \<or> cl = 2 \<Longrightarrow> \<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0"
        using i1 i2 by blast
      have postwo: "cl = 5 \<Longrightarrow> length xs = 3 \<and>
                   (\<forall>x::real. ripoly (Poly xs) x = 0 \<longrightarrow> 0 < x) \<and>
                   (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x \<noteq> 0) \<and>
                   lowdeg_sep_ok_pure False xs"
        using i5 by blast
      have negtwo: "cl = 6 \<Longrightarrow> length xs = 3 \<and>
                   (\<forall>x::real. ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> 0 < x) \<and>
                   (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x \<noteq> 0) \<and>
                   lowdeg_sep_ok_pure False (refl_list xs)"
        using i6 by blast
      show ?thesis
        apply (rule weaken_SPEC[OF lowdeg_body_strong[OF pre cls posone posnone negone negnone postwo negtwo]])
        apply (all \<open>(solves \<open>assumption\<close>)?\<close>)
        apply (clarsimp split: prod.splits)
        done
    qed
    done
qed

end
