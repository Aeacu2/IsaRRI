theory Stack_Bound
  imports Isolation_Contract
begin

text \<open>\<^bold>\<open>Two counting facts that bound the exported solver's loops linearly in the depth.\<close>
  Both loops pop their worklist from the end and push at most two children, each with a strictly
  smaller depth measure \<open>\<mu>\<close>. An invariant that charged every pending node the size of a complete
  binary tree below it, \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1\<close> entries, would need \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 < 2\<^sup>6\<^sup>3\<close> of its input. Neither
  fact below mentions a power of two.

  \<^item> \<open>stack_ok M ms\<close>: the measures \<open>ms\<close> of a LIFO worklist are dominated by ghost bounds
    \<open>bs \<le> M\<close> that decrease strictly except in the last pair. Popping, replacing the top by a
    node of smaller measure, and replacing the top by two such nodes all preserve it; with every
    measure at least 1 the worklist then has at most \<open>M + 1\<close> entries.
  \<^item> A list of pairwise-disjoint windows each containing a point of a finite set \<open>R\<close> has at most
    \<open>card R\<close> entries --- the output bound, instantiated with a polynomial's roots.\<close>

section \<open>A depth-first worklist is short\<close>

definition stack_ok :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "stack_ok M ms \<longleftrightarrow>
     (\<exists>bs. length bs = length ms \<and> list_all2 (\<le>) ms bs
        \<and> sorted_wrt (>) (butlast bs) \<and> sorted_wrt (\<ge>) bs \<and> (\<forall>b \<in> set bs. b \<le> M))"

lemma sorted_wrt_butlast_of: "sorted_wrt R xs \<Longrightarrow> sorted_wrt R (butlast xs)"
  by (simp add: butlast_conv_take)

lemma stack_ok_seed: "m \<le> M \<Longrightarrow> stack_ok M [m]"
  unfolding stack_ok_def by (intro exI[of _ "[m]"]) simp

lemma stack_ok_snoc_obtain:
  assumes "stack_ok M (ms @ [m])"
  obtains bs c where "length bs = length ms" "list_all2 (\<le>) ms bs" "m \<le> c"
    "sorted_wrt (>) bs" "sorted_wrt (\<ge>) (bs @ [c])" "\<forall>b \<in> set bs. b \<le> M" "c \<le> M"
proof -
  obtain bs0 where L: "length bs0 = length (ms @ [m])" and A: "list_all2 (\<le>) (ms @ [m]) bs0"
    and S1: "sorted_wrt (>) (butlast bs0)" and S2: "sorted_wrt (\<ge>) bs0"
    and B: "\<forall>b \<in> set bs0. b \<le> M"
    using assms unfolding stack_ok_def by blast
  have "bs0 \<noteq> []" using L by auto
  then obtain bs c where bs0: "bs0 = bs @ [c]" by (cases bs0 rule: rev_cases) auto
  have lb: "length bs = length ms" using L bs0 by simp
  have A': "list_all2 (\<le>) ms bs \<and> list_all2 (\<le>) [m] [c]"
    using A lb unfolding bs0 by (simp add: list_all2_append)
  show thesis
    by (rule that[OF lb]) (use A' S1 S2 B in \<open>auto simp: bs0\<close>)
qed

lemma stack_ok_pop:
  assumes "stack_ok M (ms @ [m])"
  shows "stack_ok M ms"
proof -
  obtain bs c where lb: "length bs = length ms" and A: "list_all2 (\<le>) ms bs"
    and S1: "sorted_wrt (>) bs" and S2: "sorted_wrt (\<ge>) (bs @ [c])"
    and B: "\<forall>b \<in> set bs. b \<le> M"
    by (rule stack_ok_snoc_obtain[OF assms])
  have "sorted_wrt (\<ge>) bs" using S2 by (simp add: sorted_wrt_append)
  then show ?thesis unfolding stack_ok_def
    using lb A sorted_wrt_butlast_of[OF S1] B by blast
qed

lemma stack_ok_replace:
  assumes "stack_ok M (ms @ [m])" and "m' \<le> m"
  shows "stack_ok M (ms @ [m'])"
proof -
  obtain bs c where lb: "length bs = length ms" and A: "list_all2 (\<le>) ms bs" and mc: "m \<le> c"
    and S1: "sorted_wrt (>) bs" and S2: "sorted_wrt (\<ge>) (bs @ [c])"
    and B: "\<forall>b \<in> set bs. b \<le> M" and cM: "c \<le> M"
    by (rule stack_ok_snoc_obtain[OF assms(1)])
  show ?thesis unfolding stack_ok_def
    by (intro exI[of _ "bs @ [c]"])
       (use lb A mc S1 S2 B cM assms(2) in \<open>auto simp: list_all2_append\<close>)
qed

lemma stack_ok_push2:
  assumes "stack_ok M (ms @ [m])" and a: "a < m" and b: "b < m"
  shows "stack_ok M (ms @ [a, b])"
proof -
  obtain bs c where lb: "length bs = length ms" and A: "list_all2 (\<le>) ms bs" and mc: "m \<le> c"
    and S1: "sorted_wrt (>) bs" and S2: "sorted_wrt (\<ge>) (bs @ [c])"
    and B: "\<forall>b \<in> set bs. b \<le> M" and cM: "c \<le> M"
    by (rule stack_ok_snoc_obtain[OF assms(1)])
  have ge: "\<forall>x \<in> set bs. c \<le> x" using S2 by (simp add: sorted_wrt_append)
  have S2': "sorted_wrt (\<ge>) bs" using S2 by (simp add: sorted_wrt_append)
  have gt: "\<forall>x \<in> set bs. m - 1 < x" using ge mc a by fastforce
  have "butlast (bs @ [m - 1, m - 1]) = bs @ [m - 1]" by (simp add: butlast_append)
  moreover have "sorted_wrt (>) (bs @ [m - 1])"
    using S1 gt by (simp add: sorted_wrt_append)
  moreover have "sorted_wrt (\<ge>) (bs @ [m - 1, m - 1])"
    using S2' gt by (auto simp: sorted_wrt_append less_imp_le)
  moreover have "list_all2 (\<le>) (ms @ [a, b]) (bs @ [m - 1, m - 1])"
    using A lb a b by (auto simp: list_all2_append)
  moreover have "\<forall>x \<in> set (bs @ [m - 1, m - 1]). x \<le> M" using B mc cM by auto
  ultimately show ?thesis unfolding stack_ok_def
    by (intro exI[of _ "bs @ [m - 1, m - 1]"]) (simp add: lb)
qed

lemma stack_ok_length:
  assumes st: "stack_ok M ms" and pos: "\<forall>x \<in> set ms. 1 \<le> x"
  shows "length ms \<le> Suc M"
proof (cases ms rule: rev_cases)
  case Nil then show ?thesis by simp
next
  case (snoc ms' m)
  obtain bs c where lb: "length bs = length ms'" and mc: "m \<le> c"
    and S1: "sorted_wrt (>) bs" and S2: "sorted_wrt (\<ge>) (bs @ [c])"
    and B: "\<forall>b \<in> set bs. b \<le> M"
    by (rule stack_ok_snoc_obtain[OF st[unfolded snoc]])
  have m1: "1 \<le> m" using pos snoc by simp
  have ge: "\<forall>x \<in> set bs. c \<le> x" using S2 by (simp add: sorted_wrt_append)
  have sub: "set bs \<subseteq> {1..M}" using ge mc m1 B by fastforce
  have dist: "distinct bs"
    using S1 by (induct bs) (auto simp: sorted_wrt_append)
  have "length bs = card (set bs)" using distinct_card[OF dist] by simp
  also have "\<dots> \<le> card {1..M}" by (rule card_mono[OF _ sub]) simp
  finally have "length bs \<le> M" by simp
  then show ?thesis using lb snoc by simp
qed

section \<open>Disjoint windows holding points of a finite set are at most that many\<close>

lemma iv_disj_mset_nth:
  assumes D: "iv_disj_mset (mset xs)" and i: "i < length xs" and j: "j < length xs"
    and ij: "i \<noteq> j"
  shows "iv_disj (xs ! i) (xs ! j)"
proof -
  define ys where "ys = take i xs @ drop (Suc i) xs"
  have ms: "mset xs = add_mset (xs ! i) (mset ys)"
    unfolding ys_def by (subst id_take_nth_drop[OF i]) simp
  have jy: "xs ! j \<in> set ys"
  proof (cases "j < i")
    case True
    then have "xs ! j = take i xs ! j" by simp
    moreover have "j < length (take i xs)" using True i by simp
    ultimately show ?thesis unfolding ys_def by (metis Un_iff nth_mem set_append)
  next
    case False
    then have ji: "Suc i \<le> j" using ij by simp
    then have "xs ! j = drop (Suc i) xs ! (j - Suc i)" using j by simp
    moreover have "j - Suc i < length (drop (Suc i) xs)" using ji j by simp
    ultimately show ?thesis unfolding ys_def by (metis Un_iff nth_mem set_append)
  qed
  have "xs ! i \<in># mset xs" using i by simp
  moreover have "xs ! j \<in># mset xs - {#xs ! i#}" using jy ms by simp
  ultimately show ?thesis using D unfolding iv_disj_mset_def by blast
qed

lemma iv_disj_mset_length_le_card:
  assumes D: "iv_disj_mset (mset ws)" and R: "finite R"
    and hit: "\<forall>w \<in> set ws. \<exists>x \<in> R. iv_in x w"
  shows "length ws \<le> card R"
proof -
  define f where "f i = (SOME x. x \<in> R \<and> iv_in x (ws ! i))" for i
  have fR: "f i \<in> R \<and> iv_in (f i) (ws ! i)" if "i < length ws" for i
  proof -
    have "\<exists>x. x \<in> R \<and> iv_in x (ws ! i)" using hit that nth_mem by blast
    then show ?thesis unfolding f_def by (rule someI_ex)
  qed
  have inj: "inj_on f {..<length ws}"
  proof (rule inj_onI)
    fix i j assume i: "i \<in> {..<length ws}" and j: "j \<in> {..<length ws}" and e: "f i = f j"
    show "i = j"
    proof (rule ccontr)
      assume ij: "i \<noteq> j"
      have "iv_disj (ws ! i) (ws ! j)" using iv_disj_mset_nth[OF D _ _ ij] i j by simp
      moreover have "iv_in (f i) (ws ! i)" using fR i by auto
      moreover have "iv_in (f i) (ws ! j)" using fR[of j] j e by auto
      ultimately show False unfolding iv_disj_def by blast
    qed
  qed
  have "length ws = card (f ` {..<length ws})" using card_image[OF inj] by simp
  also have "\<dots> \<le> card R" by (rule card_mono[OF R]) (use fR in auto)
  finally show ?thesis .
qed

end
