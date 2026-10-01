theory Deflation_Loop_Geom
  imports
    "IsaRRI_Refine.Deflation_Loop_Refine"
    "IsaRRI_Refine.Stack_Bound"
begin

text \<open>\<^bold>\<open>The deflating loop's capstone, carrying the emitted windows' geometry.\<close> It lives
  here rather than in \<open>Deflation_Isolation_Strong\<close> because the loop's own capstone needs it, not
  only the isolation contract.

  \<open>defl_geom\<close>: the accumulated windows together with the pending worklist boxes are
  pairwise disjoint, lie above \<open>glo\<close>, and every pending box is proper. Each arm of the loop
  replaces the popped box by windows inside it (\<open>defl_geom_arm_shape\<close>), which
  preserves the invariant (\<open>defl_geom_of_replace\<close>); at the exit the worklist is
  empty and the invariant is the disjointness claim.

  \<^bold>\<open>What it also pays for\<close>: the accumulator's word capacity. Disjoint windows that each
  isolate a root of \<open>P\<^sub>0\<close> number at most \<open>degree P\<^sub>0\<close> (\<open>defl_acc_len_le_degree\<close>),
  which is what \<open>defl_step_all_cols\<close> takes as its \<open>accroom\<close> premise. A budget that charged
  every pending node a complete binary tree (\<open>2\<^sup>\<mu>\<^sup>+\<^sup>1\<close> entries) would instead need \<open>\<mu> \<le> 61\<close>.\<close>

lemma iv_disj_mset_mono:
  assumes sub: "A \<subseteq># B" and B: "iv_disj_mset B"
  shows "iv_disj_mset A"
  unfolding iv_disj_mset_def
proof (intro ballI)
  fix w w' assume w: "w \<in># A" and w': "w' \<in># A - {#w#}"
  have wB: "w \<in># B" by (rule mset_subset_eqD[OF sub w])
  have "A - {#w#} \<subseteq># B - {#w#}" using sub by (rule mset_le_subtract)
  then have w'B: "w' \<in># B - {#w#}" using w' by (rule mset_subset_eqD)
  show "iv_disj w w'" using B wB w'B unfolding iv_disj_mset_def by blast
qed

lemma iv_disj_mset_replace:
  assumes MN: "iv_disj_mset (M + {#N#})" and C: "iv_disj_mset C"
    and sub: "\<forall>c \<in># C. \<forall>x. iv_in x c \<longrightarrow> iv_in x N"
  shows "iv_disj_mset (M + C)"
proof -
  have M: "iv_disj_mset M" by (rule iv_disj_mset_mono[OF _ MN]) simp
  have NM: "\<forall>m \<in># M. iv_disj N m"
  proof
    fix m assume m: "m \<in># M"
    have "m \<in># (M + {#N#}) - {#N#}" using m by simp
    then show "iv_disj N m" using MN unfolding iv_disj_mset_def by force
  qed
  have MC: "\<forall>m \<in># M. \<forall>c \<in># C. iv_disj m c"
    using NM sub unfolding iv_disj_def by blast
  show ?thesis by (rule iv_disj_mset_union[OF M C MC])
qed

definition defl_wins :: "gmp_dyadic_interval_vec \<Rightarrow> (real \<times> real) list" where
  "defl_wins v = map (\<lambda>((A, B), m). (real_of_int A / 2 ^ m, real_of_int B / 2 ^ m))
                     (dyadic_interval_vec_triples v)"

lemma defl_wins_snoc:
  assumes "length xs = length ys" "length ys = length zs"
  shows "defl_wins (xs @ [a], ys @ [b], zs @ [c])
       = defl_wins (xs, ys, zs) @ [(real_of_int a / 2 ^ c, real_of_int b / 2 ^ c)]"
  unfolding defl_wins_def using defl_acc_triples_push[OF assms] by simp

lemma defl_wins_snoc2:
  assumes "length xs = length ys" "length ys = length zs"
  shows "defl_wins (xs @ [a1, a2], ys @ [b1, b2], zs @ [c1, c2])
       = defl_wins (xs, ys, zs) @ [(real_of_int a1 / 2 ^ c1, real_of_int b1 / 2 ^ c1),
                                   (real_of_int a2 / 2 ^ c2, real_of_int b2 / 2 ^ c2)]"
proof -
  have "defl_wins (xs @ [a1, a2], ys @ [b1, b2], zs @ [c1, c2])
      = defl_wins ((xs @ [a1]) @ [a2], (ys @ [b1]) @ [b2], (zs @ [c1]) @ [c2])" by simp
  also have "\<dots> = defl_wins (xs @ [a1], ys @ [b1], zs @ [c1]) @ [(real_of_int a2 / 2 ^ c2, real_of_int b2 / 2 ^ c2)]"
    by (rule defl_wins_snoc) (use assms in simp_all)
  also have "\<dots> = defl_wins (xs, ys, zs) @ [(real_of_int a1 / 2 ^ c1, real_of_int b1 / 2 ^ c1),
                                   (real_of_int a2 / 2 ^ c2, real_of_int b2 / 2 ^ c2)]"
    using defl_wins_snoc[OF assms, of a1 b1 c1] by simp
  finally show ?thesis .
qed

definition defl_geom :: "real \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> gmp_dyadic_interval_vec \<Rightarrow> bool" where
  "defl_geom lo todo acc \<longleftrightarrow>
     iv_disj_mset (mset (defl_wins acc) + mset (defl_wins todo))
     \<and> (\<forall>w \<in> set (defl_wins acc) \<union> set (defl_wins todo). \<forall>x. iv_in x w \<longrightarrow> lo < x)
     \<and> (\<forall>w \<in> set (defl_wins todo). fst w < snd w)"

section \<open>The accumulator's word capacity, from the geometry\<close>

lemma dsc_pair_ok_has_root:
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

lemma defl_wins_len_eq:
  assumes "length al = length ar" "length ar = length ak"
  shows "length (defl_wins (al, ar, ak)) = length al"
  using assms by (simp add: defl_wins_def dyadic_interval_vec_triples_def)

text \<open>\<^bold>\<open>Disjoint windows, each isolating a root, are at most \<open>degree P\<^sub>0\<close>\<close> --- the whole of what
  bounds the accumulator, and a bound on the INPUT, not on the tree the search explores.\<close>

lemma defl_acc_len_le_degree:
  assumes geom: "defl_geom glo todo (al, ar, ak)"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and nz: "P0 \<noteq> 0"
    and lal: "length al = length ar" and lak: "length ar = length ak"
  shows "length al \<le> degree P0"
proof -
  let ?ws = "defl_wins (al, ar, ak)"
  have D: "iv_disj_mset (mset ?ws)"
    using geom unfolding defl_geom_def by (auto intro: iv_disj_mset_mono[rotated])
  have hit: "\<forall>w \<in> set ?ws. \<exists>x \<in> {x. poly P0 x = 0}. iv_in x w"
  proof
    fix w assume "w \<in> set ?ws"
    then obtain j where j: "j < length (dyadic_interval_vec_triples (al, ar, ak))"
      and wj: "w = (\<lambda>((A, B), m). (real_of_int A / 2 ^ m, real_of_int B / 2 ^ m))
                   (dyadic_interval_vec_triples (al, ar, ak) ! j)"
      unfolding defl_wins_def by (auto simp: in_set_conv_nth)
    have "dsc_pair_ok P0 w"
      using iso j wj unfolding defl_acc_isolates_def by (auto split: prod.splits)
    then show "\<exists>x \<in> {x. poly P0 x = 0}. iv_in x w" using dsc_pair_ok_has_root[OF _ nz] by blast
  qed
  have "length ?ws \<le> card {x. poly P0 x = 0}"
    by (rule iv_disj_mset_length_le_card[OF D poly_roots_finite[OF nz] hit])
  also have "\<dots> \<le> degree P0" by (rule poly_roots_degree[OF nz])
  finally show ?thesis using defl_wins_len_eq[OF lal lak] by simp
qed

lemma defl_acc_room:
  assumes geom: "defl_geom glo todo (al, ar, ak)"
    and iso: "defl_acc_isolates P0 (al, ar, ak)"
    and nz: "P0 \<noteq> 0"
    and lal: "length al = length ar" and lak: "length ar = length ak"
    and degb: "degree P0 + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
  using defl_acc_len_le_degree[OF geom iso nz lal lak] degb by linarith

lemma iv_in_sub_proper:
  assumes "a \<le> u" "v \<le> b" "u < v" "iv_in x (u, v)"
  shows "iv_in x (a, b) \<and> a < x \<and> x < b"
  using assms unfolding iv_in_def by auto

lemma iv_in_sub_point:
  assumes "a < m" "m < b" "iv_in x (m, m)"
  shows "iv_in x (a, b) \<and> a < x \<and> x < b"
  using assms unfolding iv_in_def by auto

lemma defl_halves_real:
  fixes l r :: int and k :: nat
  shows "real_of_int (2 * l) / 2 ^ Suc k = real_of_int l / 2 ^ k"
    and "real_of_int (2 * r) / 2 ^ Suc k = real_of_int r / 2 ^ k"
    and "real_of_int (l + r) / 2 ^ Suc k = (real_of_int l / 2 ^ k + real_of_int r / 2 ^ k) / 2"
  by (simp_all add: field_simps)

lemma defl_window_real:
  fixes l r m :: int and k E :: nat
  assumes lr: "l < r" and m0: "0 \<le> m" and mE: "m + 4 \<le> 2 ^ E"
  defines "a \<equiv> real_of_int l / 2 ^ k" and "b \<equiv> real_of_int r / 2 ^ k"
  defines "u \<equiv> real_of_int (l * 2 ^ E + m * (r - l)) / 2 ^ (k + E)"
    and "v \<equiv> real_of_int (l * 2 ^ E + (m + 4) * (r - l)) / 2 ^ (k + E)"
  shows "a \<le> u" "v \<le> b" "u < v"
proof -
  have ba: "0 < real_of_int (r - l)" using lr by simp
  have eu: "u = a + real_of_int m * (real_of_int (r - l)) / 2 ^ (k + E)"
    unfolding u_def a_def by (simp add: power_add field_simps)
  have ev: "v = a + (real_of_int m + 4) * (real_of_int (r - l)) / 2 ^ (k + E)"
    unfolding v_def a_def by (simp add: power_add field_simps)
  have eb: "b = a + 2 ^ E * (real_of_int (r - l)) / 2 ^ (k + E)"
    unfolding b_def a_def by (simp add: power_add field_simps)
  have m0r: "0 \<le> real_of_int m" using m0 by simp
  have mEr: "real_of_int m + 4 \<le> 2 ^ E"
  proof -
    have "real_of_int (m + 4) \<le> real_of_int (2 ^ E)" using mE by (simp only: of_int_le_iff)
    then show ?thesis by simp
  qed
  show "a \<le> u" unfolding eu using m0r ba by (simp add: divide_nonneg_pos)
  show "v \<le> b"
  proof -
    have "(real_of_int m + 4) * real_of_int (r - l) \<le> 2 ^ E * real_of_int (r - l)"
      using mEr ba by (simp add: mult_right_mono)
    then show ?thesis unfolding ev eb by (simp add: divide_right_mono)
  qed
  show "u < v"
  proof -
    have "real_of_int m * real_of_int (r - l) < (real_of_int m + 4) * real_of_int (r - l)"
      using ba by (simp add: distrib_right)
    then show ?thesis unfolding eu ev by (simp add: divide_strict_right_mono)
  qed
qed

text \<open>One step of the worklist replaces the popped node's box \<open>N\<close> by windows inside it: \<open>Ca\<close> go
  to the accumulator, \<open>Ct\<close> back onto the worklist.\<close>

lemma defl_geom_of_replace:
  assumes MN: "iv_disj_mset (mset Wa + mset Wt + {#N#})"
    and pos: "\<forall>w \<in> insert N (set Wa \<union> set Wt). \<forall>x. iv_in x w \<longrightarrow> lo < x"
    and C: "iv_disj_mset (mset Ca + mset Ct)"
    and sub: "\<forall>c \<in> set Ca \<union> set Ct. \<forall>x. iv_in x c \<longrightarrow> iv_in x N"
    and propt: "\<forall>w \<in> set Wt. fst w < snd w" and propc: "\<forall>w \<in> set Ct. fst w < snd w"
    and eqa: "defl_wins acc' = Wa @ Ca" and eqt: "defl_wins todo' = Wt @ Ct"
  shows "defl_geom lo todo' acc'"
proof -
  have sub': "\<forall>c \<in># mset Ca + mset Ct. \<forall>x. iv_in x c \<longrightarrow> iv_in x N" using sub by simp
  have D: "iv_disj_mset ((mset Wa + mset Wt) + (mset Ca + mset Ct))"
    by (rule iv_disj_mset_replace[OF MN C sub'])
  have eq: "mset (Wa @ Ca) + mset (Wt @ Ct) = (mset Wa + mset Wt) + (mset Ca + mset Ct)"
    by (simp add: add_ac)
  have D': "iv_disj_mset (mset (Wa @ Ca) + mset (Wt @ Ct))" unfolding eq by (rule D)
  have P: "\<forall>w \<in> set (Wa @ Ca) \<union> set (Wt @ Ct). \<forall>x. iv_in x w \<longrightarrow> lo < x"
    using pos sub by fastforce
  have Q: "\<forall>w \<in> set (Wt @ Ct). fst w < snd w" using propt propc by auto
  show ?thesis unfolding defl_geom_def eqa eqt using D' P Q by blast
qed

lemma defl_geom_arm_shape:
  assumes geom: "defl_geom lo (lns, rns, ks) (al, ar, ak)"
    and lne: "lns \<noteq> []"
    and VL: "length rns = length lns" "length ks = length lns"
    and AL: "length al = length ar" "length ar = length ak"
    and shape: "defl_arm_shape (butlast lns) (butlast rns) (butlast ks) qtb esb ssb csb gsb
                  (al, ar, ak) rp (last lns) (last rns) (last ks) e s st'"
  shows "defl_geom lo (fst (fst st')) (snd st')"
proof -
  define l where "l = last lns"
  define r where "r = last rns"
  define k where "k = last ks"
  define a where "a = real_of_int l / 2 ^ k"
  define b where "b = real_of_int r / 2 ^ k"
  define Wa where "Wa = defl_wins (al, ar, ak)"
  define Wt where "Wt = defl_wins (butlast lns, butlast rns, butlast ks)"
  have rne: "rns \<noteq> []" and kne: "ks \<noteq> []" using lne VL by auto
  have BL: "length (butlast lns) = length (butlast rns)" "length (butlast rns) = length (butlast ks)"
    using VL by simp_all
  have split: "(lns, rns, ks) = (butlast lns @ [l], butlast rns @ [r], butlast ks @ [k])"
    unfolding l_def r_def k_def using lne rne kne by simp
  have wfull: "defl_wins (lns, rns, ks) = Wt @ [(a, b)]"
    unfolding Wt_def a_def b_def by (subst split) (rule defl_wins_snoc[OF BL])
  have MN: "iv_disj_mset (mset Wa + mset Wt + {#(a, b)#})"
    using geom unfolding defl_geom_def wfull Wa_def by (simp add: add.assoc)
  have pos: "\<forall>w \<in> insert (a, b) (set Wa \<union> set Wt). \<forall>x. iv_in x w \<longrightarrow> lo < x"
    using geom unfolding defl_geom_def wfull Wa_def by auto
  have propt: "\<forall>w \<in> set Wt. fst w < snd w" and ab: "a < b"
    using geom unfolding defl_geom_def wfull by auto
  have lr: "l < r"
  proof -
    have "real_of_int l / 2 ^ k < real_of_int r / 2 ^ k" using ab unfolding a_def b_def .
    then show ?thesis by (simp add: divide_less_cancel)
  qed
  obtain todo' qtodo' es' ss' cs' gs' rp' acc' where st': "st' = ((todo', qtodo', es', ss', cs', gs', rp'), acc')"
    by (metis prod.exhaust)
  have sh: "defl_arm_shape (butlast lns) (butlast rns) (butlast ks) qtb esb ssb csb gsb
                  (al, ar, ak) rp l r k e s ((todo', qtodo', es', ss', cs', gs', rp'), acc')"
    using shape unfolding st' l_def r_def k_def .
  \<comment> \<open>the two halves and the midpoint, in real coordinates\<close>
  define mid where "mid = (a + b) / 2"
  have h1: "real_of_int (2 * l) / 2 ^ Suc k = a" unfolding a_def by (rule defl_halves_real(1))
  have h2: "real_of_int (2 * r) / 2 ^ Suc k = b" unfolding b_def by (rule defl_halves_real(2))
  have h3: "real_of_int (l + r) / 2 ^ Suc k = mid" unfolding mid_def a_def b_def by (rule defl_halves_real(3))
  have c1: "defl_wins (butlast lns @ [2 * l], butlast rns @ [l + r], butlast ks @ [Suc k]) = Wt @ [(a, mid)]"
    unfolding Wt_def defl_wins_snoc[OF BL] h1 h3 ..
  have c12: "defl_wins (butlast lns @ [2 * l, l + r], butlast rns @ [l + r, 2 * r], butlast ks @ [Suc k, Suc k])
           = Wt @ [(a, mid), (mid, b)]"
    unfolding Wt_def defl_wins_snoc2[OF BL] h1 h2 h3 ..
  have accm: "defl_wins (al @ [l + r], ar @ [l + r], ak @ [Suc k]) = Wa @ [(mid, mid)]"
    unfolding Wa_def defl_wins_snoc[OF AL] h3 ..
  have accN: "defl_wins (al @ [l], ar @ [r], ak @ [k]) = Wa @ [(a, b)]"
    unfolding Wa_def a_def b_def by (rule defl_wins_snoc[OF AL])
  have am: "a < mid" and mb: "mid < b" unfolding mid_def using ab by auto
  have in1: "\<forall>x. iv_in x (a, mid) \<longrightarrow> iv_in x (a, b)" using iv_in_sub_proper[of a a mid b] am mb by auto
  have in2: "\<forall>x. iv_in x (mid, b) \<longrightarrow> iv_in x (a, b)" using iv_in_sub_proper[of a mid b b] am mb by auto
  have inm: "\<forall>x. iv_in x (mid, mid) \<longrightarrow> iv_in x (a, b)" using iv_in_sub_point[of a mid b] am mb by auto
  have d12: "iv_disj (a, mid) (mid, b)" unfolding iv_disj_def iv_in_def using am mb by auto
  have dm1: "iv_disj (mid, mid) (a, mid)" unfolding iv_disj_def iv_in_def using am by auto
  have dm2: "iv_disj (mid, mid) (mid, b)" unfolding iv_disj_def iv_in_def using mb by auto
  have C12: "iv_disj_mset ({#(a, mid)#} + {#(mid, b)#})"
    by (rule iv_disj_mset_union[OF iv_disj_mset_single iv_disj_mset_single]) (use d12 in simp)
  have Cm12: "iv_disj_mset ({#(mid, mid)#} + ({#(a, mid)#} + {#(mid, b)#}))"
    by (rule iv_disj_mset_union[OF iv_disj_mset_single C12]) (use dm1 dm2 in simp)
  from sh[unfolded defl_arm_shape_def prod.case] have "defl_geom lo todo' acc'"
  proof (elim disjE conjE exE)
    \<comment> \<open>POP, reject\<close>
    assume t: "todo' = (butlast lns, butlast rns, butlast ks)" and ac: "acc' = (al, ar, ak)"
    show ?thesis
      by (rule defl_geom_of_replace[OF MN pos, where Ca = "[]" and Ct = "[]"])
         (use propt in \<open>simp_all add: t ac Wa_def Wt_def\<close>)
  next
    \<comment> \<open>POP, accept: the node box moves to the accumulator\<close>
    assume t: "todo' = (butlast lns, butlast rns, butlast ks)"
      and ac: "acc' = (al @ [l], ar @ [r], ak @ [k])"
    show ?thesis
      by (rule defl_geom_of_replace[OF MN pos, where Ca = "[(a, b)]" and Ct = "[]"])
         (use propt accN in \<open>simp_all add: t ac Wt_def\<close>)
  next
    \<comment> \<open>PUSH2, midpoint not a root\<close>
    fix ql qr cl cr gl gr sv
    assume t: "todo' = (butlast lns @ [2 * l, l + r], butlast rns @ [l + r, 2 * r], butlast ks @ [Suc k, Suc k])"
      and ac: "acc' = (al, ar, ak)"
    have C: "iv_disj_mset (mset [] + mset [(a, mid), (mid, b)])"
    proof -
      have "mset [] + mset [(a, mid), (mid, b)] = {#(a, mid)#} + {#(mid, b)#}" by (simp add: add_mset_commute)
      then show ?thesis using C12 by (simp only:)
    qed
    show ?thesis
      by (rule defl_geom_of_replace[OF MN pos C])
         (use propt in1 in2 am mb c12 in \<open>simp_all add: t ac Wa_def\<close>)
  next
    \<comment> \<open>PUSH2, midpoint is a root\<close>
    fix ql qr cl cr gl gr sv
    assume t: "todo' = (butlast lns @ [2 * l, l + r], butlast rns @ [l + r, 2 * r], butlast ks @ [Suc k, Suc k])"
      and ac: "acc' = (al @ [l + r], ar @ [l + r], ak @ [Suc k])"
    have C: "iv_disj_mset (mset [(mid, mid)] + mset [(a, mid), (mid, b)])"
    proof -
      have "mset [(mid, mid)] + mset [(a, mid), (mid, b)] = {#(mid, mid)#} + ({#(a, mid)#} + {#(mid, b)#})"
        by (simp add: add_mset_commute)
      then show ?thesis using Cm12 by (simp only:)
    qed
    show ?thesis
      by (rule defl_geom_of_replace[OF MN pos C])
         (use propt in1 in2 inm am mb c12 accm in \<open>simp_all add: t ac\<close>)
  next
    \<comment> \<open>PUSH1, Newton window\<close>
    fix m cand v QQ
    assume pick: "newton_window_pick_bail v e QQ = Some (m, cand)"
      and t: "todo' = (butlast lns @ [l * 2 ^ (2 ^ e + 2) + m * (r - l)],
        butlast rns @ [l * 2 ^ (2 ^ e + 2) + (m + 4) * (r - l)], butlast ks @ [k + (2 ^ e + 2)])"
      and ac: "acc' = (al, ar, ak)"
    define E :: nat where "E = 2 ^ e + 2"
    define u where "u = real_of_int (l * 2 ^ E + m * (r - l)) / 2 ^ (k + E)"
    define v' where "v' = real_of_int (l * 2 ^ E + (m + 4) * (r - l)) / 2 ^ (k + E)"
    have m0: "0 \<le> m" by (rule newton_window_pick_bail_m_nonneg[OF pick])
    have mE: "m + 4 \<le> 2 ^ E"
      using newton_window_pick_bail_m_bound[OF pick] unfolding E_def N_of_def by (simp add: power_add)
    note W = defl_window_real[OF lr m0 mE, of k, folded a_def b_def u_def v'_def]
    have eqt: "defl_wins todo' = Wt @ [(u, v')]"
      unfolding t Wt_def defl_wins_snoc[OF BL] u_def v'_def E_def ..
    have inw: "\<forall>x. iv_in x (u, v') \<longrightarrow> iv_in x (a, b)" using iv_in_sub_proper[OF W] by auto
    show ?thesis
      by (rule defl_geom_of_replace[OF MN pos, where Ca = "[]" and Ct = "[(u, v')]"])
         (use propt inw W(3) eqt in \<open>simp_all add: ac Wa_def\<close>)
  next
    \<comment> \<open>PUSH1, left half only\<close>
    fix ql cl gl sv
    assume t: "todo' = (butlast lns @ [2 * l], butlast rns @ [l + r], butlast ks @ [Suc k])"
      and ac: "acc' = (al, ar, ak)"
    show ?thesis
      by (rule defl_geom_of_replace[OF MN pos, where Ca = "[]" and Ct = "[(a, mid)]"])
         (use propt in1 am c1 in \<open>simp_all add: t ac Wa_def\<close>)
  qed
  then show ?thesis by (simp add: st')
qed


lemma defl_step_all_cols_geom:
  fixes P :: "int poly" and rp :: gmp_poly
  defines "Pr \<equiv> (of_int_poly P :: real poly)"
  assumes dpos: "0 < \<delta>"
    and lr0: "l0 < r0"
    and Pnz: "Pr \<noteq> 0"
    and sfP: "square_free Pr"
    \<comment> \<open>One \<open>\<delta>\<close> serving every polynomial the deflating run can reach: \<open>delta_defl\<close>.\<close>
    and dlt: "\<delta> \<le> delta_defl Pr"
    and lenP: "0 < length (coeffs P)"
    and pbP: "length (coeffs P) * nat_bitlen (length (coeffs P))
                < max_snat LENGTH(gmp_poly_len)"
    and gbP: "4398046511104 + length (coeffs P) + length (coeffs P)
                < max_snat LENGTH(gmp_poly_len)"
    and sintP: "int (length (coeffs P)) < max_sint LENGTH(gmp_long_len)"
    and smallP: "length (coeffs P) < 1099511627776"
    and kcap: "hybrid_root_potential \<delta> k0 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepthP: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                    kD * (length (coeffs P) - 1) < max_snat LENGTH(gmp_poly_len)"
    and g_roomP: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                    (kD + 1) * length (coeffs P) < 1099511627776"
    \<comment> \<open>\<^bold>\<open>The depth budget with WINDOW headroom.\<close> \<open>kcap\<close> bounds the potential itself; the
       window child sinks \<open>2\<^sup>e + 2 \<le> 2\<^sup>8 + 2\<close> further, and that has to be affordable at the
       DEEPEST live node --- a \<open>k0\<close>-level premise, because the loop's own \<open>last ks\<close> is not
       visible to the caller.\<close>
    and kroom: "hybrid_root_potential \<delta> k0 + 258 < int (max_snat LENGTH(gmp_poly_len))"
    and safe: "hybrid_loop_safe_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and stinvar: "defl_state_invar \<delta> P l0 r0 k0 (of_int_poly (Poly rp) :: real poly) lo
                    (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    and cond: "hybrid_loop_cond (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    \<comment> \<open>the ROOT list's own two facts. \<open>Pr\<close> above is the SEED's local poly --- a different
       object, and \<open>\<delta>\<close> is a smallness witness for that one.\<close>
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and sfrp: "square_free (of_int_poly (Poly rp) :: real poly)"
    and geom: "defl_geom glo (lns, rns, ks) (al, ar, ak)"
  shows "defl_loop_body_checked_monadic (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. ((hybrid_loop_safe_invar s' \<and> defl_state_invar \<delta> P l0 r0 k0 (of_int_poly (Poly rp) :: real poly) lo s')
                   \<and> defl_geom glo (fst (fst s')) (snd s'))
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
proof -
  have capinv: "hybrid_cap_invar \<delta> l0 r0 k0 (lns, rns, ks) ss"
    and stkinv: "defl_stack_invar \<delta> l0 r0 k0 (lns, rns, ks)"
    and Pcoeffs: "coeffs P = carried_init_same_den l0 (2 ^ k0) r0 rp"
    and inv0: "defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using stinvar by simp_all
  have cpl: "defl_trunc_coupling (lns, rns, ks) qtodo cs gs rp"
    using inv0 unfolding defl_loop_invar_def by simp
  have stinv: "hybrid_loop_state_invar (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe unfolding hybrid_loop_safe_invar_def by simp
  have tinv: "dyadic_interval_vec_invar (lns, rns, ks)"
    using stinv unfolding hybrid_loop_state_invar_def by (simp add: Let_def)
  have SL: "length qtodo = length lns" "length es = length lns" "length ss = length lns"
     "length cs = length lns" "length gs = length lns"
    using stinv unfolding hybrid_loop_state_invar_def by (simp_all add: Let_def)
  have VL: "length rns = length lns" "length ks = length lns"
    using tinv unfolding dyadic_interval_vec_invar_def by simp_all
  have lne: "lns \<noteq> []" using cond by (simp add: hybrid_loop_cond_def)
  \<comment> \<open>the length transfer: every premise moves from \<open>coeffs P\<close> to THIS state's \<open>rp\<close>\<close>
  have lenrp: "length rp = length (coeffs P)"
    using Pcoeffs by (simp add: truncate_length_carried_init_same_den)
  have rp_len: "0 < length rp" using lenP lenrp by simp
  have rp_pb: "length rp * nat_bitlen (length rp) < max_snat LENGTH(gmp_poly_len)"
    using pbP lenrp by simp
  have rp_gb: "4398046511104 + length rp + length rp < max_snat LENGTH(gmp_poly_len)"
    using gbP lenrp by simp
  have rp_sint: "int (length rp) < max_sint LENGTH(gmp_long_len)" using sintP lenrp by simp
  have rp_small: "length rp < 1099511627776" using smallP lenrp by simp
  have kdepth: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                  kD * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    using kdepthP lenrp by simp
  have g_room: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k0 \<Longrightarrow>
                  (kD + 1) * length rp < 1099511627776"
    using g_roomP lenrp by simp
  have pre: "hybrid_loop_step_pre (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))"
    using safe cond unfolding hybrid_loop_safe_invar_def by simp
  have ne: "qtodo \<noteq> []" "es \<noteq> []" "ss \<noteq> []" "cs \<noteq> []" "gs \<noteq> []" "ks \<noteq> []" "rns \<noteq> []"
    using lne SL VL by auto
  have BL: "length (butlast lns) = length (butlast rns)"
     "length (butlast rns) = length (butlast ks)"
     "length (butlast es) = length (butlast ks)"
     "length (butlast ss) = length (butlast ks)"
    using VL SL by simp_all
  \<comment> \<open>\<^bold>\<open>The seed's LOCAL poly, which is what \<open>\<delta>\<close> is a smallness witness for\<close> --- not
     \<open>P\<^sub>0\<close>, which is the ROOT list's poly and is what the loop invariant is stated against.
     The two are different objects and both appear here.\<close>
  have Pform: "Pr = (of_int_poly (Poly (carried_init_same_den l0 (2 ^ k0) r0 rp)) :: real poly)"
    unfolding Pr_def by (simp add: Pcoeffs[symmetric])
  have ilast: "length ks - 1 < length ks" using ne(6) by simp
  have abq: "fst (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))
             < snd (dyadic_iv_node_iv_of l0 r0 k0 ((last lns, last rns), last ks))"
    using hybrid_cap_invar_nondeg[OF capinv ilast] lne ne VL by (simp add: last_conv_nth)
  have ab: "real_of_rat (fst (dyadic_iv_node_iv l0 r0 k0 (last lns) (last rns) (last ks)))
            < real_of_rat (snd (dyadic_iv_node_iv l0 r0 k0 (last lns) (last rns) (last ks)))"
    using abq by (simp add: dyadic_iv_node_iv_of_def of_rat_less)
  \<comment> \<open>The node's divisibility plus \<open>2 \<le> count\<close> forces the box to be wider than \<open>\<delta>\<close>.\<close>
  have smalld: "\<And>Y. (of_int_poly (Poly Y) :: real poly)
                       dvd (of_int_poly (Poly (carried_init_same_den (last lns)
                              (2 ^ last ks) (last rns) rp)) :: real poly)
                     \<Longrightarrow> 2 \<le> carried_descartes_count Y
                     \<Longrightarrow> \<delta> < real_of_rat (snd (dyadic_iv_node_iv_of l0 r0 k0
                                  ((last lns, last rns), last ks)))
                           - real_of_rat (fst (dyadic_iv_node_iv_of l0 r0 k0
                                  ((last lns, last rns), last ks)))"
  proof -
    fix Y :: gmp_poly
    assume d: "(of_int_poly (Poly Y) :: real poly)
                 dvd (of_int_poly (Poly (carried_init_same_den (last lns)
                        (2 ^ last ks) (last rns) rp)) :: real poly)"
      and c: "2 \<le> carried_descartes_count Y"
    have yl: "1 < length Y" using defl_count2_len3[OF c] by simp
    show "\<delta> < real_of_rat (snd (dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns, last rns), last ks)))
             - real_of_rat (fst (dyadic_iv_node_iv_of l0 r0 k0
                   ((last lns, last rns), last ks)))"
      using defl_node_wide_of_count2[OF lr0 Pnz[unfolded Pform] sfP[unfolded Pform]
              dlt[unfolded Pform] ab d c yl]
      by (simp add: dyadic_iv_node_iv_of_def)
  qed
  \<comment> \<open>\<^bold>\<open>The bulk comes from \<open>hybrid_loop_step_pre\<close>\<close> --- fifteen of the args step's
     forty-three premises are literally its conjuncts, which is why the classic arms unfold it
     rather than carrying them.\<close>
  \<comment> \<open>\<^bold>\<open>Ten of the args step's premises are literally \<open>hybrid_loop_step_pre\<close>'s own
     conjuncts\<close> --- proved one at a time rather than by one \<open>simp_all\<close> over a
     ten-way \<open>have\<close>, which leaves residues that are hard to attribute.\<close>
  have accpush: "dyadic_interval_vec_pushable (al, ar, ak)"
    using pre by (auto simp: hybrid_loop_step_pre_def)
  have push2: "dyadic_interval_vec_pushable2 (butlast lns, butlast rns, butlast ks)"
    using pre by (auto simp: hybrid_loop_step_pre_def)
  have krp: "last ks * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    using pre by (auto simp: hybrid_loop_step_pre_def)
  have kcapl: "last ks + 1 < max_snat LENGTH(gmp_poly_len)"
    using pre by (auto simp: hybrid_loop_step_pre_def)
  have scap1: "last ss + 1 < max_snat LENGTH(gmp_poly_len)"
    using pre by (auto simp: hybrid_loop_step_pre_def)
  have qcap: "length (butlast qtodo) + 2 < max_snat LENGTH(gmp_poly_len)"
    using pre by (auto simp: hybrid_loop_step_pre_def)
  have ecapl: "length (butlast es) + 2 < max_snat LENGTH(gmp_poly_len)"
    using pre by (auto simp: hybrid_loop_step_pre_def)
  have sscap: "length (butlast ss) + 2 < max_snat LENGTH(gmp_poly_len)"
    using pre by (auto simp: hybrid_loop_step_pre_def)
  have ccap: "length (butlast cs) + 2 < max_snat LENGTH(gmp_poly_len)"
    using pre by (auto simp: hybrid_loop_step_pre_def)
  have gcap: "length (butlast gs) + 2 < max_snat LENGTH(gmp_poly_len)"
    using pre by (auto simp: hybrid_loop_step_pre_def)
  have push1: "dyadic_interval_vec_pushable (butlast lns, butlast rns, butlast ks)"
    using push2 unfolding dyadic_interval_vec_pushable_def dyadic_interval_vec_pushable2_def
    by simp
  have kslen: "length (butlast ks) + 1 < max_snat LENGTH(gmp_poly_len)"
    using qcap SL VL by simp
  \<comment> \<open>the popped node, and the depth bound its budget clause needs\<close>
  have node: "defl_node_ok rp (last lns) (last rns) (last ks)
                (last qtodo) (last gs) (last cs)"
  proof -
    have i: "length lns - 1 < length lns" using lne by simp
    have "defl_node_ok rp (lns ! (length lns - 1)) (rns ! (length lns - 1))
            (ks ! (length lns - 1)) (qtodo ! (length lns - 1)) (gs ! (length lns - 1))
            (cs ! (length lns - 1))"
      using cpl i SL VL unfolding defl_trunc_coupling_def by simp
    thus ?thesis using lne ne SL VL by (simp add: last_conv_nth)
  qed
  have kle: "int (last ks) \<le> hybrid_root_potential \<delta> k0"
    using hybrid_cap_invar_depth_le[OF capinv ilast] lne ne VL by (simp add: last_conv_nth)
  have g_roomk: "(last ks + 1) * length rp < 1099511627776" by (rule g_room[OF kle])
  have lrne: "last lns < last rns"
    using abq lr0 by (simp add: dyadic_iv_node_iv_of_def dyadic_iv_node_iv_def
                                dyadic_rat_def Let_def divide_less_cancel)
  \<comment> \<open>\<^bold>\<open>The node's depth headroom.\<close> The loop's \<open>es\<close> column is not capped (the window push stores
     \<open>e + 1\<close> while the gate caps only \<open>e\<close>), so no premise \<open>last es \<le> newton_pol_ecap\<close> is available
     here; the remaining exponent caps hold where the gate is open.\<close>
  have kroom258: "last ks + 258 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "int (last ks + 258) < int (max_snat LENGTH(gmp_poly_len))" using kle kroom by simp
    thus ?thesis by simp
  qed
  \<comment> \<open>and the three invariant clauses, popped\<close>
  have coupb: "defl_trunc_coupling (butlast lns, butlast rns, butlast ks)
                 (butlast qtodo) (butlast cs) (butlast gs) rp"
    by (rule defl_trunc_coupling_pop[OF cpl])
  have isob: "defl_acc_isolates (of_int_poly (Poly rp) :: real poly) (al, ar, ak)"
    using inv0 unfolding defl_loop_invar_def by simp
  have covb: "defl_dispatch_covers (of_int_poly (Poly rp) :: real poly) lo
                (butlast lns, butlast rns, butlast ks) (al, ar, ak)
                (last lns) (last rns) (last ks)"
    using inv0 unfolding defl_loop_invar_def
    by (simp add: defl_dispatch_covers_pop ne(7) VL)
  have lal: "length al = length ar" and lak: "length ar = length ak"
    using stinv unfolding hybrid_loop_state_invar_def dyadic_interval_vec_invar_def
    by (simp_all add: Let_def)
  have degb: "degree (of_int_poly (Poly rp) :: real poly) + 2 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "degree (of_int_poly (Poly rp) :: real poly) \<le> length rp"
      using degree_Poly[of rp] by simp
    then show ?thesis using rp_gb by linarith
  qed
  have accroom: "int (length al) + 2 < int (max_snat LENGTH(gmp_poly_len))"
    by (rule defl_acc_room[OF geom isob rpnz lal lak degb])
  have A: "defl_loop_body_checked_monadic (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. (hybrid_loop_safe_invar s' \<and> defl_state_invar \<delta> P l0 r0 k0 (of_int_poly (Poly rp) :: real poly) lo s')
                \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                  < hybrid_state_mu \<delta> l0 r0 k0
                      (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak)))"
    by (rule defl_step_all_cols[OF dpos lr0 Pnz[unfolded Pr_def] sfP[unfolded Pr_def] dlt[unfolded Pr_def]
          lenP pbP gbP sintP smallP kcap kdepthP g_roomP kroom safe stinvar accroom cond rpnz sfrp])
  have arm: "defl_loop_step_args_monadic (lns, rns, ks) qtodo es ss cs gs (al, ar, ak) rp
       \<le> SPEC (\<lambda>x.
             defl_loop_invar (of_int_poly (Poly rp) :: real poly) lo x
           \<and> defl_arm_shape (butlast lns) (butlast rns) (butlast ks) (butlast qtodo)
               (butlast es) (butlast ss) (butlast cs) (butlast gs) (al, ar, ak) rp
               (last lns) (last rns) (last ks) (last es) (last ss) x)"
    by (rule defl_loop_step_args_step[OF tinv lne VL(1) VL(2) ne(1) ne(2) ne(3) ne(4) ne(5)
             node g_roomk rpnz sfrp lrne rp_len rp_gb rp_sint rp_small rp_pb krp kcapl
             kroom258 accpush qcap gcap ecapl sscap ccap
             push2 push1 kslen scap1 coupb isob covb BL(1) BL(2)[symmetric] lal lak])
  have G: "defl_loop_body_checked_monadic (((lns, rns, ks), qtodo, es, ss, cs, gs, rp), (al, ar, ak))
       \<le> SPEC (\<lambda>s'. defl_geom glo (fst (fst s')) (snd s'))"
    apply (subst defl_loop_body_under_cond[OF cond])
    apply (subst defl_loop_step_unfold)
    apply (rule order_trans[OF arm])
    apply (rule SPEC_rule)
    apply (elim conjE)
    apply (erule defl_geom_arm_shape[OF geom lne VL lal lak])
    done
  show ?thesis
    using SPEC_rule_conjI[OF A G] by (rule order_trans) (rule SPEC_rule, blast)
qed

lemma defl_loop_strengthened_geom:
  "defl_loop_monadic todo qtodo es ss cs gs rp acc
     \<le> WHILEIT (\<lambda>st. (hybrid_loop_safe_invar st \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo st)
                     \<and> defl_geom glo (fst (fst st)) (snd st))
         hybrid_loop_cond defl_loop_body_checked_monadic
         ((todo, qtodo, es, ss, cs, gs, rp), acc)"
  unfolding defl_loop_monadic_unfold
  by (rule WHILEIT_weaken) simp

lemma defl_loop_correct_geom:
  assumes init: "(hybrid_loop_safe_invar ((todo, qtodo, es, ss, cs, gs, rp), acc)
                  \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo ((todo, qtodo, es, ss, cs, gs, rp), acc))
                 \<and> defl_geom glo todo acc"
    and step: "\<And>s. \<lbrakk> (hybrid_loop_safe_invar s \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo s)
                        \<and> defl_geom glo (fst (fst s)) (snd s);
                      hybrid_loop_cond s \<rbrakk>
               \<Longrightarrow> defl_loop_body_checked_monadic s
                 \<le> SPEC (\<lambda>s'. ((hybrid_loop_safe_invar s'
                                 \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo s')
                                \<and> defl_geom glo (fst (fst s')) (snd s'))
                          \<and> hybrid_state_mu \<delta> l0 r0 k0 s'
                            < hybrid_state_mu \<delta> l0 r0 k0 s)"
    and exit: "\<And>s. \<lbrakk> (hybrid_loop_safe_invar s \<and> defl_state_invar \<delta> P l0 r0 k0 P0 lo s)
                        \<and> defl_geom glo (fst (fst s)) (snd s);
                      \<not> hybrid_loop_cond s \<rbrakk> \<Longrightarrow> \<Phi> s"
  shows "defl_loop_monadic todo qtodo es ss cs gs rp acc \<le> SPEC \<Phi>"
  apply (rule order_trans[OF defl_loop_strengthened_geom])
  apply (rule WHILEIT_rule[where
      R = "{(st', st). hybrid_state_mu \<delta> l0 r0 k0 st' < hybrid_state_mu \<delta> l0 r0 k0 st}"])
  apply (rule hybrid_state_mu_wf)
  apply (simp only: fst_conv snd_conv, rule init)
  apply (simp only: mem_Collect_eq prod.case)
  apply (rule step, assumption+)
  apply (rule exit, assumption+)
  done


lemma defl_geom_seed:
  assumes lr: "l < r" and glo: "glo \<le> real_of_int l / 2 ^ k"
  shows "defl_geom glo ([l], [r], [k]) ([], [], [])"
proof -
  have "real_of_int l / 2 ^ k < real_of_int r / 2 ^ k" using lr by (simp add: divide_strict_right_mono)
  then show ?thesis
    using glo unfolding defl_geom_def defl_wins_def dyadic_interval_vec_triples_def iv_in_def by auto
qed

lemma defl_geom_exit_nil:
  assumes "defl_geom glo (lns, rns, ks) acc" and "lns = []"
  shows "iv_disj_mset (mset (defl_wins acc)) \<and> (\<forall>w \<in> set (defl_wins acc). \<forall>x. iv_in x w \<longrightarrow> glo < x)"
  using assms unfolding defl_geom_def defl_wins_def dyadic_interval_vec_triples_def by simp

lemma defl_geom_exit:
  assumes "defl_geom glo ([], rns, ks) acc"
  shows "iv_disj_mset (mset (defl_wins acc)) \<and> (\<forall>w \<in> set (defl_wins acc). \<forall>x. iv_in x w \<longrightarrow> glo < x)"
  using assms unfolding defl_geom_def defl_wins_def dyadic_interval_vec_triples_def by simp

lemma defl_exit_acc_geom:
  assumes inv: "defl_loop_invar P0 lo
                  (((lns, rns, ks), qtodo, es, ss, cs, gs, rpx), (al, ar, ak))"
    and safe: "hybrid_loop_safe_invar
                 (((lns, rns, ks), qtodo, es, ss, cs, gs, rpx), (al, ar, ak))"
    and ncond: "\<not> hybrid_loop_cond
                    (((lns, rns, ks), qtodo, es, ss, cs, gs, rpx), (al, ar, ak))"
    and geom: "defl_geom glo (lns, rns, ks) (al, ar, ak)"
    and nz: "P0 \<noteq> 0"
    and degb: "degree P0 + 2 < max_snat LENGTH(gmp_poly_len)"
  shows "qtodo = []
       \<and> dyadic_interval_vec_invar (al, ar, ak)
       \<and> length (dyadic_interval_vec_triples (al, ar, ak)) + 1
           < max_snat LENGTH(gmp_poly_len)
       \<and> defl_acc_isolates P0 (al, ar, ak) \<and> defl_acc_covers P0 lo (al, ar, ak)"
proof -
  have stinv: "hybrid_loop_state_invar
                 (((lns, rns, ks), qtodo, es, ss, cs, gs, rpx), (al, ar, ak))"
    using safe unfolding hybrid_loop_safe_invar_def by simp
  have lal: "length al = length ar" and lak: "length ar = length ak"
    using stinv unfolding hybrid_loop_state_invar_def dyadic_interval_vec_invar_def
    by (simp_all add: Let_def)
  have iso: "defl_acc_isolates P0 (al, ar, ak)"
    using inv unfolding defl_loop_invar_def by simp
  show ?thesis
    by (rule defl_exit_acc[OF inv safe ncond defl_acc_room[OF geom iso nz lal lak degb]])
qed

lemma defl_main_list_correct_geom:
  fixes \<delta> :: real and Pl rp :: gmp_poly
  assumes dpos: "0 < \<delta>"
    and lr: "l_num < r_num"
    and P_eq: "Pl = carried_init_same_den l_num (2 ^ k) r_num rp"
    and canon: "coeffs (Poly Pl) = Pl"
    and Pnz: "(of_int_poly (Poly Pl) :: real poly) \<noteq> 0"
    and sfP: "square_free (of_int_poly (Poly Pl) :: real poly)"
    and dlt: "\<delta> \<le> delta_defl (of_int_poly (Poly Pl) :: real poly)"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and sfrp: "square_free (of_int_poly (Poly rp) :: real poly)"
    and cover: "\<And>y::real. lo < y \<Longrightarrow> poly (of_int_poly (Poly rp) :: real poly) y = 0 \<Longrightarrow>
                  real_of_int l_num / 2 ^ k < y \<and> y < real_of_int r_num / 2 ^ k"
    and lenP1: "0 < length Pl"
    and lenP2: "length Pl + 1 < max_snat LENGTH(gmp_poly_len)"
    and k1: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_len: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and pbP: "length (coeffs (Poly Pl)) * nat_bitlen (length (coeffs (Poly Pl)))
                < max_snat LENGTH(gmp_poly_len)"
    and gbP: "4398046511104 + length (coeffs (Poly Pl)) + length (coeffs (Poly Pl))
                < max_snat LENGTH(gmp_poly_len)"
    and sintP: "int (length (coeffs (Poly Pl))) < max_sint LENGTH(gmp_long_len)"
    and smallP: "length (coeffs (Poly Pl)) < 1099511627776"
    and lenC: "0 < length (coeffs (Poly Pl))"
    \<comment> \<open>\<^bold>\<open>Linear in \<open>\<mu>\<close>\<close>; a complete-binary-tree budget would need \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 + 1 < 2\<^sup>6\<^sup>3\<close>.\<close>
    and mucap: "int (dyadic_iv_interval_mu \<delta> (0, 1)) + 3 < int (max_snat LENGTH(gmp_poly_len))"
    and kcap: "hybrid_root_potential \<delta> k < int (max_snat LENGTH(gmp_poly_len))"
    and kroom: "hybrid_root_potential \<delta> k + 258 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepthP: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k \<Longrightarrow>
                    kD * (length (coeffs (Poly Pl)) - 1) < max_snat LENGTH(gmp_poly_len)"
    and g_roomP: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k \<Longrightarrow>
                    (kD + 1) * length (coeffs (Poly Pl)) < 1099511627776"
    and glo: "glo \<le> real_of_int l_num / 2 ^ k"
  \<comment> \<open>\<^bold>\<open>All four of \<open>qsolve\<close>'s conjuncts\<close> (see \<open>Power_Sub_Entry_Sound\<close>): the vector invariant and
     the bound on the number of emitted intervals are what the back-map's push capacity needs, and
     both are read off the loop's exit state.\<close>
  shows "defl_main_list_monadic e0 l_num r_num k Pl rp
       \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc
                    \<and> length (dyadic_interval_vec_triples acc) + 1
                        < max_snat LENGTH(gmp_poly_len)
                    \<and> defl_acc_isolates (of_int_poly (Poly rp) :: real poly) acc
                    \<and> defl_acc_covers (of_int_poly (Poly rp) :: real poly) lo acc
                    \<and> iv_disj_mset (mset (defl_wins acc))
                    \<and> (\<forall>w \<in> set (defl_wins acc). \<forall>x. iv_in x w \<longrightarrow> glo < x))"
proof -
  \<comment> \<open>\<^bold>\<open>The \<open>\<And>s\<close> STEP\<close> --- \<open>defl_step_all_cols\<close> at a destructured state, the classic's
     own shape (@{thm [source] hybrid_main_list_correct_strong}).\<close>
  have step: "\<And>s. \<lbrakk> (hybrid_loop_safe_invar s
                     \<and> defl_state_invar \<delta> (Poly Pl) l_num r_num k
                         (of_int_poly (Poly rp) :: real poly) lo s)
                     \<and> defl_geom glo (fst (fst s)) (snd s);
                     hybrid_loop_cond s \<rbrakk>
              \<Longrightarrow> defl_loop_body_checked_monadic s
                \<le> SPEC (\<lambda>s'. ((hybrid_loop_safe_invar s'
                                \<and> defl_state_invar \<delta> (Poly Pl) l_num r_num k
                                    (of_int_poly (Poly rp) :: real poly) lo s')
                                \<and> defl_geom glo (fst (fst s')) (snd s'))
                         \<and> hybrid_state_mu \<delta> l_num r_num k s'
                           < hybrid_state_mu \<delta> l_num r_num k s)"
  proof -
    fix s :: hybrid_state
    assume AG: "(hybrid_loop_safe_invar s
               \<and> defl_state_invar \<delta> (Poly Pl) l_num r_num k
                   (of_int_poly (Poly rp) :: real poly) lo s)
               \<and> defl_geom glo (fst (fst s)) (snd s)"
      and C: "hybrid_loop_cond s"
    note A = conjunct1[OF AG]
    obtain stx accx where s1: "s = (stx, accx)" by (rule prod.exhaust)
    obtain todo qtx esx ssx csx gsx rpx
      where s2: "stx = (todo, qtx, esx, ssx, csx, gsx, rpx)" by (rule prod_cases7)
    obtain lnsx rnsx ksx where s3: "todo = (lnsx, rnsx, ksx)" by (rule prod_cases3)
    obtain alx arx akx where s4: "accx = (alx, arx, akx)" by (rule prod_cases3)
    \<comment> \<open>\<^bold>\<open>The state carries its OWN root list\<close>, and \<open>defl_step_all_cols\<close> ties \<open>P\<^sub>0\<close> to it.
       The invariant's \<open>coeffs P = carried_init_same_den \<dots> rp\<^sub>x\<close> clause plus \<open>canon\<close> and
       \<open>P_eq\<close> makes the two agree after the map, and the map is injective on the real image.\<close>
    have Pcx: "coeffs (Poly Pl) = carried_init_same_den l_num (2 ^ k) r_num rpx"
      using A unfolding s1 s2 s3 s4 by simp
    have rpeq: "(of_int_poly (Poly rp) :: real poly) = of_int_poly (Poly rpx)"
      by (rule defl_cisd_inj_real[where k = k and xs = rp and ys = rpx, OF lr])
         (use Pcx canon P_eq in simp)
    have G: "defl_geom glo (lnsx, rnsx, ksx) (alx, arx, akx)"
      using conjunct2[OF AG] unfolding s1 s2 s3 s4 by simp
    show "defl_loop_body_checked_monadic s
        \<le> SPEC (\<lambda>s'. ((hybrid_loop_safe_invar s'
                        \<and> defl_state_invar \<delta> (Poly Pl) l_num r_num k
                            (of_int_poly (Poly rp) :: real poly) lo s')
                        \<and> defl_geom glo (fst (fst s')) (snd s'))
                 \<and> hybrid_state_mu \<delta> l_num r_num k s'
                   < hybrid_state_mu \<delta> l_num r_num k s)"
      unfolding s1 s2 s3 s4 rpeq
      apply (rule defl_step_all_cols_geom[OF dpos lr Pnz sfP dlt lenC pbP gbP
                sintP smallP kcap kdepthP g_roomP kroom
                conjunct1[OF A[unfolded s1 s2 s3 s4]]
                conjunct2[OF A[unfolded s1 s2 s3 s4 rpeq]]
                C[unfolded s1 s2 s3 s4]
                rpnz[unfolded rpeq] sfrp[unfolded rpeq] G])
      \<comment> \<open>\<open>OF kdepthP\<close> / \<open>OF g_roomP\<close> re-add their OWN hypotheses as fresh goals ---
         a \<open>\<And>\<close>-quantified CONDITIONAL fact composes by its conclusion. Both are the
         tautology they always are.\<close>
       apply assumption
      apply assumption
      done
  qed
  have degb: "degree (of_int_poly (Poly rp) :: real poly) + 2 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have lrp: "length Pl = length rp"
      using P_eq by (simp add: truncate_length_carried_init_same_den)
    have "degree (of_int_poly (Poly rp) :: real poly) \<le> length rp"
      using degree_Poly[of rp] by simp
    then show ?thesis using gbP[unfolded canon] lrp by linarith
  qed
  show ?thesis
  unfolding defl_main_list_monadic_def PR_CONST_def
      dyadic_interval_vec_empty_sz_monadic_def poly_empty_sz_monadic_def
      poly_push_coeff_monadic_def poly_vec_empty_sz_monadic_def poly_vec_push_monadic_def
  apply (refine_vcg defl_count_trunc_cs_ok_le4[THEN order_trans])
  \<comment> \<open>the seed vectors' pushability and the two length caps, exactly as the classic\<close>
  apply (all \<open>((insert lenP2, clarsimp simp: dyadic_interval_vec_pushable_def max_snat_def);
                fail)?\<close>)
  \<comment> \<open>the seed \<open>hybrid_loop_safe_invar\<close> --- REUSED, not cloned: the deflating loop runs
     the same safety predicate\<close>
  apply (all \<open>((clarsimp,
                rule hybrid_loop_safe_invar_seed[OF lenP1 lenP2 k1 rp_len rpb krp]); fail)?\<close>)
  apply clarsimp
  apply (rule defl_loop_correct_geom[OF _ step])
  \<comment> \<open>\<open>OF step\<close> re-adds \<open>step\<close>'s OWN two hypotheses as fresh goals --- the same
     \<open>\<And>\<close>-quantified-conditional trap; both are the tautology they always are.\<close>
  apply (all \<open>(assumption; fail)?\<close>)
  \<comment> \<open>\<^bold>\<open>The INIT\<close> --- the seed's four invariant clauses. The first two are the
     classic's own seed lemmas, unchanged: the deflating loop runs the same cap and budget
     invariants.\<close>
  subgoal
    apply (rule conjI)
     prefer 2
     apply (rule defl_geom_seed[OF lr glo])
    apply (rule conjI, assumption)
    apply (simp only: defl_state_invar_simp)
    apply (intro conjI)
       apply (rule hybrid_cap_invar_seed[OF lr])
      apply (rule defl_stack_invar_seed[OF mucap hybrid_alpha_views_seed[OF lr]])
      apply simp
    \<comment> \<open>\<open>unfold\<close>, not \<open>simp add:\<close> --- as rewrites \<open>P_eq\<close> fires first and \<open>canon\<close>
       then has nothing to match.\<close>
     apply (unfold canon)
     apply (rule P_eq)
    apply (rule defl_loop_invar_seed[OF cover P_eq canon _ _ Pnz])
    apply (all \<open>(assumption; fail)?\<close>)
    done
  \<comment> \<open>\<^bold>\<open>The EXIT\<close>, and the wrapper's tail with it. The three frees are
     \<open>ASSERT\<close>-then-\<open>RETURN ()\<close> ops, so the tail collapses to \<open>RETURN acc\<close> and the
     postcondition IS @{thm [source] defl_state_invar_exit}'s two clauses.\<close>
  subgoal for x s
    apply (clarsimp split: prod.splits
                    simp: poly_vec_free_empty_monadic_def dyadic_interval_vec_free_monadic_def
                          mop_free_def)
    apply (frule defl_exit_acc_geom[OF _ _ _ _ rpnz degb])
       apply assumption
      apply assumption
     apply assumption
    apply clarsimp
    apply (erule defl_geom_exit_nil)
    apply (simp add: hybrid_loop_cond_def)
    done
  done
qed


text \<open>\<^bold>\<open>The reflect level's form\<close>: the four conjuncts \<open>qsolve\<close> takes, with the geometry
  instantiated at the seed box's own left end (where it holds by construction) and dropped.\<close>

lemma defl_main_list_correct:
  fixes \<delta> :: real and Pl rp :: gmp_poly
  assumes dpos: "0 < \<delta>"
    and lr: "l_num < r_num"
    and P_eq: "Pl = carried_init_same_den l_num (2 ^ k) r_num rp"
    and canon: "coeffs (Poly Pl) = Pl"
    and Pnz: "(of_int_poly (Poly Pl) :: real poly) \<noteq> 0"
    and sfP: "square_free (of_int_poly (Poly Pl) :: real poly)"
    and dlt: "\<delta> \<le> delta_defl (of_int_poly (Poly Pl) :: real poly)"
    and rpnz: "(of_int_poly (Poly rp) :: real poly) \<noteq> 0"
    and sfrp: "square_free (of_int_poly (Poly rp) :: real poly)"
    and cover: "\<And>y::real. lo < y \<Longrightarrow> poly (of_int_poly (Poly rp) :: real poly) y = 0 \<Longrightarrow>
                  real_of_int l_num / 2 ^ k < y \<and> y < real_of_int r_num / 2 ^ k"
    and lenP1: "0 < length Pl"
    and lenP2: "length Pl + 1 < max_snat LENGTH(gmp_poly_len)"
    and k1: "k + 1 < max_snat LENGTH(gmp_poly_len)"
    and rp_len: "0 < length rp"
    and rpb: "length rp + 1 < max_snat LENGTH(gmp_poly_len)"
    and krp: "k * (length rp - 1) < max_snat LENGTH(gmp_poly_len)"
    and pbP: "length (coeffs (Poly Pl)) * nat_bitlen (length (coeffs (Poly Pl)))
                < max_snat LENGTH(gmp_poly_len)"
    and gbP: "4398046511104 + length (coeffs (Poly Pl)) + length (coeffs (Poly Pl))
                < max_snat LENGTH(gmp_poly_len)"
    and sintP: "int (length (coeffs (Poly Pl))) < max_sint LENGTH(gmp_long_len)"
    and smallP: "length (coeffs (Poly Pl)) < 1099511627776"
    and lenC: "0 < length (coeffs (Poly Pl))"
    \<comment> \<open>\<^bold>\<open>Linear in \<open>\<mu>\<close>\<close>; a complete-binary-tree budget would need \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 + 1 < 2\<^sup>6\<^sup>3\<close>.\<close>
    and mucap: "int (dyadic_iv_interval_mu \<delta> (0, 1)) + 3 < int (max_snat LENGTH(gmp_poly_len))"
    and kcap: "hybrid_root_potential \<delta> k < int (max_snat LENGTH(gmp_poly_len))"
    and kroom: "hybrid_root_potential \<delta> k + 258 < int (max_snat LENGTH(gmp_poly_len))"
    and kdepthP: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k \<Longrightarrow>
                    kD * (length (coeffs (Poly Pl)) - 1) < max_snat LENGTH(gmp_poly_len)"
    and g_roomP: "\<And>kD. int kD \<le> hybrid_root_potential \<delta> k \<Longrightarrow>
                    (kD + 1) * length (coeffs (Poly Pl)) < 1099511627776"
  shows "defl_main_list_monadic e0 l_num r_num k Pl rp
       \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc
                    \<and> length (dyadic_interval_vec_triples acc) + 1
                        < max_snat LENGTH(gmp_poly_len)
                    \<and> defl_acc_isolates (of_int_poly (Poly rp) :: real poly) acc
                    \<and> defl_acc_covers (of_int_poly (Poly rp) :: real poly) lo acc)"
proof -
  have G: "defl_main_list_monadic e0 l_num r_num k Pl rp
       \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc
                    \<and> length (dyadic_interval_vec_triples acc) + 1
                        < max_snat LENGTH(gmp_poly_len)
                    \<and> defl_acc_isolates (of_int_poly (Poly rp) :: real poly) acc
                    \<and> defl_acc_covers (of_int_poly (Poly rp) :: real poly) lo acc
                    \<and> iv_disj_mset (mset (defl_wins acc))
                    \<and> (\<forall>w \<in> set (defl_wins acc). \<forall>x. iv_in x w
                           \<longrightarrow> real_of_int l_num / 2 ^ k < x))"
    apply (rule defl_main_list_correct_geom[where glo = "real_of_int l_num / 2 ^ k"])
    apply (all \<open>(fact assms)?\<close>)
    apply simp
    done
  show ?thesis by (rule order_trans[OF G]) (rule SPEC_rule, blast)
qed
end
