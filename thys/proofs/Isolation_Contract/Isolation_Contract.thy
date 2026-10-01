theory Isolation_Contract
  imports Complex_Main "HOL-Library.Multiset"
begin

text \<open>\<^bold>\<open>The vocabulary of the isolation contract.\<close> A window \<open>(a, b)\<close> CONTAINS \<open>x\<close> when \<open>x\<close> lies
  strictly inside it or the window is the single point \<open>x\<close> (\<open>iv_in\<close>). Two windows are
  DISJOINT when no point is contained in both (\<open>iv_disj\<close>), and a multiset of windows is
  pairwise disjoint when every window is disjoint from every OTHER occurrence
  (\<open>iv_disj_mset\<close>) --- stated over a multiset so that it survives the permutations and
  multiset equalities the refinement chains are proven with. Pure real arithmetic, no solver
  vocabulary, so any check session can pull it in through \<open>sessions\<close> at no cost.\<close>

definition iv_in :: "real \<Rightarrow> real \<times> real \<Rightarrow> bool" where
  "iv_in x w \<longleftrightarrow> (fst w < x \<and> x < snd w) \<or> (fst w = x \<and> snd w = x)"

definition iv_disj :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> bool" where
  "iv_disj w w' \<longleftrightarrow> \<not> (\<exists>x. iv_in x w \<and> iv_in x w')"

definition iv_disj_mset :: "(real \<times> real) multiset \<Rightarrow> bool" where
  "iv_disj_mset M \<longleftrightarrow> (\<forall>w \<in># M. \<forall>w' \<in># M - {#w#}. iv_disj w w')"

lemma iv_disj_sym: "iv_disj w w' = iv_disj w' w"
  unfolding iv_disj_def by blast

lemma iv_disj_mset_empty[simp]: "iv_disj_mset {#}"
  unfolding iv_disj_mset_def by simp

lemma iv_disj_mset_union:
  assumes "iv_disj_mset A" "iv_disj_mset B" "\<forall>w \<in># A. \<forall>w' \<in># B. iv_disj w w'"
  shows "iv_disj_mset (A + B)"
  unfolding iv_disj_mset_def
proof (intro ballI)
  fix w w' assume w: "w \<in># A + B" and w': "w' \<in># A + B - {#w#}"
  show "iv_disj w w'"
  proof (cases "w \<in># A")
    case True
    have "A + B - {#w#} = (A - {#w#}) + B" using True by (simp add: diff_union_swap2)
    then have "w' \<in># (A - {#w#}) + B" using w' by simp
    then consider "w' \<in># A - {#w#}" | "w' \<in># B" by auto
    then show ?thesis
    proof cases
      case 1 then show ?thesis using assms(1) True unfolding iv_disj_mset_def by blast
    next
      case 2 then show ?thesis using assms(3) True by blast
    qed
  next
    case False
    then have wB: "w \<in># B" using w by simp
    have "A + B - {#w#} = A + (B - {#w#})" using wB False by (simp add: diff_union_swap2)
    then have "w' \<in># A + (B - {#w#})" using w' by simp
    then consider "w' \<in># A" | "w' \<in># B - {#w#}" by auto
    then show ?thesis
    proof cases
      case 1
      then have "iv_disj w' w" using assms(3) wB by blast
      then show ?thesis by (simp add: iv_disj_sym)
    next
      case 2 then show ?thesis using assms(2) wB unfolding iv_disj_mset_def by blast
    qed
  qed
qed

lemma iv_disj_mset_single[simp]: "iv_disj_mset {#w#}"
  unfolding iv_disj_mset_def by simp

definition iv_scale :: "real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real" where
  "iv_scale c w = (c * fst w, c * snd w)"

lemma iv_in_scale:
  assumes c: "0 < c"
  shows "iv_in x (iv_scale c w) \<longleftrightarrow> iv_in (x / c) w"
  using c unfolding iv_in_def iv_scale_def
  by (auto simp: field_simps)

lemma iv_scale_inj:
  assumes c: "0 < c"
  shows "inj (iv_scale c)"
  using c unfolding inj_def iv_scale_def by auto

lemma iv_disj_mset_scale:
  assumes c: "0 < c" and M: "iv_disj_mset M"
  shows "iv_disj_mset (image_mset (iv_scale c) M)"
  unfolding iv_disj_mset_def
proof (intro ballI)
  fix v v' assume v: "v \<in># image_mset (iv_scale c) M"
    and v': "v' \<in># image_mset (iv_scale c) M - {#v#}"
  from v obtain w where w: "w \<in># M" and vw: "v = iv_scale c w" by auto
  have "image_mset (iv_scale c) M - {#v#} = image_mset (iv_scale c) (M - {#w#})"
    using w vw by (simp add: image_mset_Diff)
  with v' obtain w' where w': "w' \<in># M - {#w#}" and vw': "v' = iv_scale c w'" by auto
  have "iv_disj w w'" using M w w' unfolding iv_disj_mset_def by blast
  then show "iv_disj v v'"
    unfolding iv_disj_def vw vw' iv_in_scale[OF c] by blast
qed

definition rat_pair_real :: "rat \<times> rat \<Rightarrow> real \<times> real" where
  "rat_pair_real I = (of_rat (fst I), of_rat (snd I))"

end
