theory Isarri_Paths
  imports
    IsaRRI_Refine.Isolation_Contract
    IsaRRI.Power_Sub_Isolation_Strong
    IsaRRI.Lowdeg_Isolation_Strong
begin

text \<open>\<^bold>\<open>Per-path facts.\<close> The theorem about the exported function
  (\<open>Isarri_Memory\<close>) is generic in each path's \<open>\<le> SPEC\<close> postcondition. This theory supplies
  what the exported code needs beyond the isolation contract --- the vector-length invariant the
  output-copy loops read, and the value of the \<open>xs0\<close> flag --- and the uniform per-half contract
  every path is stated against.\<close>

section \<open>The power-substitution path: shape of the output when the substitution fires\<close>

lemma pow_sub_extract_nth0:
  assumes "0 < h" and "xs \<noteq> []"
  shows "pow_sub_extract h xs \<noteq> [] \<and> pow_sub_extract h xs ! 0 = xs ! 0"
  using assms unfolding pow_sub_extract_def by (simp del: upt_Suc add: nth_map_upt)

lemma pow_sub_entry_sub_mop_shape:
  fixes xs :: "int list" and d dlt :: nat
  defines "q \<equiv> pow_sub_extract d xs"
  assumes d2: "2 \<le> d" and db: "d < max_snat LENGTH(gmp_poly_len)"
    and ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and qsolve: "defl_isolate_all_split_main q \<le> SPEC (\<lambda>(accP, accN, xs0).
          dyadic_interval_vec_invar accP
          \<and> length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len)
          \<and> xs0 = (q \<noteq> [] \<and> q ! 0 = 0))"
  shows "pow_sub_entry_sub_mop d dlt xs
           \<le> SPEC (\<lambda>(out, xs0, ok). dyadic_interval_vec_invar out \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  have d0: "0 < d" using d2 by simp
  have lenxs: "length xs < max_snat LENGTH(gmp_poly_len)" using len1 by simp
  have ne': "0 < length xs" using ne by simp
  have qlen0: "0 < length q" unfolding q_def by simp
  have qlen: "length q + 1 < max_snat LENGTH(gmp_poly_len)"
  proof -
    have "length q = Suc ((length xs - 1) div d)" unfolding q_def by simp
    also have "\<dots> \<le> Suc (length xs - 1)" by (simp add: Euclidean_Rings.div_le_dividend)
    finally show ?thesis using len1 ne' by linarith
  qed
  have q0: "(q \<noteq> [] \<and> q ! 0 = 0) = (xs \<noteq> [] \<and> xs ! 0 = 0)"
    using pow_sub_extract_nth0[OF d0 ne] ne unfolding q_def by simp
  have bmc: "pow_sub_backmap_all_monadic d q dlt accP
        \<le> SPEC (\<lambda>(out, ok). dyadic_interval_vec_invar out)"
    if ivQ: "dyadic_interval_vec_invar accP"
      and n1: "length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len)"
    for accP
    by (rule weaken_SPEC[OF pow_sub_backmap_all_monadic_correct[OF d0 db qlen0 qlen ivQ n1]]) auto
  show ?thesis
    unfolding pow_sub_entry_sub_mop_def PR_CONST_def
      dyadic_interval_vec_free_monadic_def mop_free_def
    apply (refine_vcg
           pow_sub_extract_monadic_correct[OF d0 ne' lenxs, folded q_def, THEN order_trans]
           qsolve[THEN order_trans]
           bmc[THEN order_trans])
    apply (all \<open>use d0 db qlen0 qlen ne' lenxs q0 in \<open>auto simp: Let_def\<close>\<close>)
    done
qed

section \<open>The uniform per-half contract and the count\<close>

text \<open>\<^bold>\<open>One half of the output, as a caller reads it.\<close> \<open>ws\<close> are the emitted windows in real
  coordinates; \<open>Q\<close> is the input polynomial for the positive half and its reflection
  \<open>Poly (refl_list xs)\<close> for the negative half.\<close>

definition trip_wins :: "((int \<times> int) \<times> nat) list \<Rightarrow> (real \<times> real) list" where
  "trip_wins trs = map (\<lambda>((A, B), m). (real_of_int A / 2 ^ m, real_of_int B / 2 ^ m)) trs"

lemma defl_wins_trip_wins: "defl_wins v = trip_wins (dyadic_interval_vec_triples v)"
  unfolding defl_wins_def trip_wins_def ..

definition iso_half :: "real poly \<Rightarrow> (real \<times> real) list \<Rightarrow> bool" where
  "iso_half Q ws \<longleftrightarrow>
     (\<forall>w \<in> set ws. dsc_pair_ok Q w)
   \<and> (\<forall>x. 0 < x \<longrightarrow> poly Q x = 0 \<longrightarrow> (\<exists>w \<in> set ws. iv_in x w))
   \<and> iv_root_unique Q ws
   \<and> iv_wins_pos ws"

lemma dsc_pair_ok_root_set:
  assumes Q: "Q \<noteq> 0" and ok: "dsc_pair_ok Q w"
  shows "card {x. poly Q x = 0 \<and> iv_in x w} = 1"
proof (cases "fst w = snd w")
  case True
  then have "{x. poly Q x = 0 \<and> iv_in x w} = {fst w}"
    using ok unfolding dsc_pair_ok_def iv_in_def by auto
  then show ?thesis by simp
next
  case False
  then have lt: "fst w < snd w" and r1: "roots_in Q (fst w) (snd w) = 1"
    using ok unfolding dsc_pair_ok_def by auto
  have "{x. poly Q x = 0 \<and> iv_in x w} = proots_within Q {x. fst w < x \<and> x < snd w}"
    using lt unfolding iv_in_def proots_within_def by auto
  then show ?thesis
    using defl_proots_count_1_card[OF Q r1[unfolded roots_in_def]] by simp
qed

lemma dsc_pair_ok_root_ex:
  assumes Q: "Q \<noteq> 0" and ok: "dsc_pair_ok Q w"
  shows "\<exists>x. poly Q x = 0 \<and> iv_in x w"
  using dsc_pair_ok_root_set[OF Q ok] by (metis (mono_tags, lifting) One_nat_def card_1_singletonE
    insertI1 mem_Collect_eq)

lemma dsc_pair_ok_root_unique:
  assumes Q: "Q \<noteq> 0" and ok: "dsc_pair_ok Q w"
    and x: "poly Q x = 0" "iv_in x w" and y: "poly Q y = 0" "iv_in y w"
  shows "x = y"
proof -
  have "card {x. poly Q x = 0 \<and> iv_in x w} = 1" by (rule dsc_pair_ok_root_set[OF Q ok])
  then obtain z where Z: "{x. poly Q x = 0 \<and> iv_in x w} = {z}" by (rule card_1_singletonE)
  have "x \<in> {z}" unfolding Z[symmetric] using x by simp
  moreover have "y \<in> {z}" unfolding Z[symmetric] using y by simp
  ultimately show ?thesis by simp
qed

theorem iso_half_count:
  assumes Q: "Q \<noteq> 0" and iso: "iso_half Q ws"
  shows "length ws = card {x. 0 < x \<and> poly Q x = 0}"
proof -
  let ?R = "{x. 0 < x \<and> poly Q x = 0}"
  have S: "\<forall>w \<in> set ws. dsc_pair_ok Q w"
    and C: "\<forall>x. 0 < x \<longrightarrow> poly Q x = 0 \<longrightarrow> (\<exists>w \<in> set ws. iv_in x w)"
    and U: "iv_root_unique Q ws" and Pos: "iv_wins_pos ws"
    using iso unfolding iso_half_def by auto
  define f where "f i = (THE x. poly Q x = 0 \<and> iv_in x (ws ! i))" for i
  have f: "poly Q (f i) = 0 \<and> iv_in (f i) (ws ! i)" if i: "i < length ws" for i
  proof -
    have ok: "dsc_pair_ok Q (ws ! i)" using S i by simp
    obtain x where x: "poly Q x = 0 \<and> iv_in x (ws ! i)" using dsc_pair_ok_root_ex[OF Q ok] by blast
    show ?thesis unfolding f_def
      by (rule theI[of _ x]) (use x dsc_pair_ok_root_unique[OF Q ok] in blast)+
  qed
  have bij: "bij_betw f {..<length ws} ?R"
  proof (rule bij_betwI')
    fix i j assume i: "i \<in> {..<length ws}" and j: "j \<in> {..<length ws}"
    show "(f i = f j) = (i = j)"
    proof
      assume eq: "f i = f j"
      show "i = j"
      proof (rule ccontr)
        assume ij: "i \<noteq> j"
        have "\<exists>x. poly Q x = 0 \<and> iv_in x (ws ! i) \<and> iv_in x (ws ! j)"
          using f[of i] f[of j] i j eq by auto
        then show False using U i j ij unfolding iv_root_unique_def by auto
      qed
    qed simp
  next
    fix i assume i: "i \<in> {..<length ws}"
    have "ws ! i \<in> set ws" using i by simp
    then show "f i \<in> ?R" using f[of i] i Pos unfolding iv_wins_pos_def by auto
  next
    fix x assume "x \<in> ?R"
    then have x0: "0 < x" and rx: "poly Q x = 0" by auto
    obtain w where w: "w \<in> set ws" "iv_in x w" using C x0 rx by blast
    obtain i where i: "i < length ws" "ws ! i = w" using w(1) by (auto simp: in_set_conv_nth)
    have ok: "dsc_pair_ok Q (ws ! i)" using S nth_mem[OF i(1)] by blast
    have "f i = x"
      using dsc_pair_ok_root_unique[OF Q ok] f[OF i(1)] rx w(2) i(2) by blast
    then show "\<exists>i \<in> {..<length ws}. x = f i" using i by auto
  qed
  have "card {..<length ws} = card ?R" by (rule bij_betw_same_card[OF bij])
  then show ?thesis by simp
qed

section \<open>Bridges from each path's statements to the uniform contract\<close>

lemma iv_in_pow_sub_mirror: "iv_in x (pow_sub_mirror w) \<longleftrightarrow> iv_in (- x) w"
  unfolding iv_in_def pow_sub_mirror_def by auto

lemma dsc_pair_ok_reflect:
  fixes P :: "real poly"
  assumes P: "P \<noteq> 0" and ok: "dsc_pair_ok P (pow_sub_mirror w)"
  shows "dsc_pair_ok (P \<circ>\<^sub>p [:0, -1:]) w"
proof (cases "fst w = snd w")
  case True
  then show ?thesis using ok unfolding dsc_pair_ok_def pow_sub_mirror_def
    by (auto simp: poly_pcompose)
next
  case False
  then have lt: "fst w < snd w" and r1: "roots_in P (- snd w) (- fst w) = 1"
    using ok unfolding dsc_pair_ok_def pow_sub_mirror_def by auto
  have img: "poly [:0, -1:] ` {x. fst w < x \<and> x < snd w} = {x. - snd w < x \<and> x < - fst w}"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> poly [:0, -1:] ` {x. fst w < x \<and> x < snd w}"
    then show "y \<in> {x. - snd w < x \<and> x < - fst w}" by auto
  next
    fix y assume y: "y \<in> {x. - snd w < x \<and> x < - fst w}"
    have "y = poly [:0, -1:] (- y)" by simp
    moreover have "- y \<in> {x. fst w < x \<and> x < snd w}" using y by auto
    ultimately show "y \<in> poly [:0, -1:] ` {x. fst w < x \<and> x < snd w}" by blast
  qed
  have pc: "proots_count (P \<circ>\<^sub>p [:0, -1:]) {x. fst w < x \<and> x < snd w}
      = proots_count P (poly [:0, -1:] ` {x. fst w < x \<and> x < snd w})"
    by (rule proots_pcompose[OF P]) simp
  have "roots_in (P \<circ>\<^sub>p [:0, -1:]) (fst w) (snd w) = 1"
    unfolding roots_in_def pc img using r1 unfolding roots_in_def .
  then show ?thesis using lt unfolding dsc_pair_ok_def by simp
qed

lemma pow_sub_iso_halves:
  fixes P :: "real poly"
  assumes P: "P \<noteq> 0"
    and S: "\<forall>w \<in> set ws. dsc_pair_ok P w \<and> dsc_pair_ok P (pow_sub_mirror w)"
    and C: "\<forall>x. poly P x = 0 \<longrightarrow> (\<exists>w \<in> set ws. iv_in x w \<or> iv_in x (pow_sub_mirror w))"
    and K: "pow_sub_entry_contract P ws"
  shows "iso_half P ws \<and> iso_half (P \<circ>\<^sub>p [:0, -1:]) ws"
proof -
  have U: "iv_root_unique P ws" and Pos: "iv_wins_pos ws"
    and Um: "iv_root_unique P (map pow_sub_mirror ws)" and Neg: "iv_wins_neg (map pow_sub_mirror ws)"
    using K unfolding pow_sub_entry_contract_def by auto
  have Cp: "\<exists>w \<in> set ws. iv_in x w" if x0: "0 < x" and rx: "poly P x = 0" for x
  proof -
    obtain w where w: "w \<in> set ws" "iv_in x w \<or> iv_in x (pow_sub_mirror w)" using C rx by blast
    have "\<not> iv_in x (pow_sub_mirror w)"
      using Neg w(1) x0 unfolding iv_wins_neg_def by fastforce
    then show ?thesis using w by blast
  qed
  have Cn: "\<exists>w \<in> set ws. iv_in x w" if x0: "0 < x" and rx: "poly (P \<circ>\<^sub>p [:0, -1:]) x = 0" for x
  proof -
    have rx': "poly P (- x) = 0" using rx by (simp add: poly_pcompose)
    obtain w where w: "w \<in> set ws" "iv_in (- x) w \<or> iv_in (- x) (pow_sub_mirror w)"
      using C rx' by blast
    have "\<not> iv_in (- x) w" using Pos w(1) x0 unfolding iv_wins_pos_def by fastforce
    then show ?thesis using w by (auto simp: iv_in_pow_sub_mirror)
  qed
  have Un: "iv_root_unique (P \<circ>\<^sub>p [:0, -1:]) ws"
    unfolding iv_root_unique_def
  proof (intro allI impI notI)
    fix i j assume i: "i < length ws" and j: "j < length ws" and ij: "i \<noteq> j"
      and ex: "\<exists>x. poly (P \<circ>\<^sub>p [:0, -1:]) x = 0 \<and> iv_in x (ws ! i) \<and> iv_in x (ws ! j)"
    then obtain x where x: "poly P (- x) = 0" "iv_in (- x) (pow_sub_mirror (ws ! i))"
        "iv_in (- x) (pow_sub_mirror (ws ! j))"
      by (auto simp: poly_pcompose iv_in_pow_sub_mirror)
    have "\<not> (\<exists>y. poly P y = 0 \<and> iv_in y (map pow_sub_mirror ws ! i) \<and> iv_in y (map pow_sub_mirror ws ! j))"
      using Um i j ij unfolding iv_root_unique_def by simp
    then show False using x i j by simp
  qed
  show ?thesis
    unfolding iso_half_def
    using S U Pos Un Cp Cn P by (auto intro: dsc_pair_ok_reflect)
qed

lemma defl_iso_half:
  fixes P :: "real poly"
  assumes iso: "defl_acc_isolates P v" and cov: "defl_acc_covers P 0 v"
    and disj: "iv_disj_mset (mset (defl_wins v))"
    and pos: "\<forall>w \<in> set (defl_wins v). \<forall>x. iv_in x w \<longrightarrow> 0 < x"
  shows "iso_half P (defl_wins v)"
proof -
  have S: "\<forall>w \<in> set (defl_wins v). dsc_pair_ok P w"
    using iso unfolding defl_acc_isolates_def defl_wins_def
    by (auto simp: in_set_conv_nth split: prod.splits)
  have C: "\<forall>x. 0 < x \<longrightarrow> poly P x = 0 \<longrightarrow> (\<exists>w \<in> set (defl_wins v). iv_in x w)"
  proof (intro allI impI)
    fix x :: real assume x0: "0 < x" and rx: "poly P x = 0"
    obtain j A B m where j: "j < length (dyadic_interval_vec_triples v)"
        "dyadic_interval_vec_triples v ! j = ((A, B), m)"
        and xin: "real_of_int A / 2 ^ m < x \<and> x < real_of_int B / 2 ^ m
                  \<or> real_of_int A / 2 ^ m = x \<and> real_of_int B / 2 ^ m = x"
      using cov x0 rx unfolding defl_acc_covers_def by blast
    have "(real_of_int A / 2 ^ m, real_of_int B / 2 ^ m) \<in> set (defl_wins v)"
      using j unfolding defl_wins_def by (force simp: in_set_conv_nth)
    then show "\<exists>w \<in> set (defl_wins v). iv_in x w" using xin unfolding iv_in_def by force
  qed
  have U: "iv_root_unique P (defl_wins v)"
    unfolding iv_root_unique_def
    using iv_disj_mset_nth[OF disj] unfolding iv_disj_def by blast
  show ?thesis unfolding iso_half_def iv_wins_pos_def using S C U pos by blast
qed
section \<open>Path B at the monadic level\<close>

lemma SPEC_conj_rule:
  "m \<le> SPEC A \<Longrightarrow> m \<le> SPEC B \<Longrightarrow> m \<le> SPEC (\<lambda>x. A x \<and> B x)"
  by (auto simp: pw_le_iff refine_pw_simps)

lemma real_poly_nz:
  assumes "xs \<noteq> []" "last xs \<noteq> 0"
  shows "(real_of_int_poly (Poly xs) :: real poly) \<noteq> 0"
  proof -
  have "Poly xs \<noteq> 0" using assms by (auto simp: Poly_eq_0)
  then show ?thesis by simp
qed

lemma pow_sub_entry_monadic_shape:
  fixes xs :: "int list" and nfloor hcap dlt :: nat
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and hcb: "hcap < max_snat LENGTH(gmp_poly_len)"
    and qpre: "\<And>d. 2 \<le> d \<Longrightarrow> even d \<Longrightarrow> d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
          dsc_isolate_all_split_defl_pre (pow_sub_extract d xs)"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs
           \<le> SPEC (\<lambda>(out, xs0, ok). ok \<longrightarrow> dyadic_interval_vec_invar out \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  have lenxs: "length xs < max_snat LENGTH(gmp_poly_len)" using len1 by simp
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
        \<le> SPEC (\<lambda>(out, xs0, ok). dyadic_interval_vec_invar out \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
    if d2: "2 \<le> d" and par2: "2 \<le> gcd d 2" and db: "d < max_snat LENGTH(gmp_poly_len)"
      and deq: "d = gcd (pow_sub_h xs) hcap"
    for d
  proof -
    have ev: "even d" by (rule pow_sub_par_even[OF par2])
    have qs: "defl_isolate_all_split_main (pow_sub_extract d xs) \<le> SPEC (\<lambda>(accP, accN, xs0).
          dyadic_interval_vec_invar accP
          \<and> length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len)
          \<and> xs0 = (pow_sub_extract d xs \<noteq> [] \<and> pow_sub_extract d xs ! 0 = 0))"
      by (rule weaken_SPEC[OF defl_isolate_all_split_main_correct[OF qpre[OF d2 ev deq]]]) auto
    show ?thesis by (rule pow_sub_entry_sub_mop_shape[OF d2 db ne len1 qs])
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

theorem pow_sub_entry_monadic_iso:
  fixes xs :: "int list" and nfloor hcap dlt :: nat
  defines "P \<equiv> (real_of_int_poly (Poly xs) :: real poly)"
  assumes ne: "xs \<noteq> []" and len1: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    and hcb: "hcap < max_snat LENGTH(gmp_poly_len)"
    and nz: "last xs \<noteq> 0"
    and sfP: "squarefree P"
    and qpre: "\<And>d. 2 \<le> d \<Longrightarrow> even d \<Longrightarrow> d = gcd (pow_sub_h xs) hcap \<Longrightarrow>
          dsc_isolate_all_split_defl_pre (pow_sub_extract d xs)"
  shows "pow_sub_entry_monadic nfloor hcap dlt xs \<le> SPEC (\<lambda>(out, xs0, ok).
      ok \<longrightarrow> dyadic_interval_vec_invar out \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0)
           \<and> iso_half P (defl_wins out)
           \<and> iso_half (real_of_int_poly (Poly (refl_list xs))) (defl_wins out))"
proof -
  have P0: "P \<noteq> 0" unfolding P_def by (rule real_poly_nz[OF ne nz])
  note S = pow_sub_entry_monadic_correct_of_pre[OF ne len1 hcb nz sfP[unfolded P_def] qpre,
      of nfloor dlt, folded P_def]
  note C = pow_sub_entry_monadic_complete_strict_of_pre[OF ne len1 hcb nz sfP[unfolded P_def] qpre,
      of nfloor dlt, folded P_def]
  note U = pow_sub_entry_monadic_unique_of_pre[OF ne len1 hcb nz sfP[unfolded P_def] qpre,
      of nfloor dlt, folded P_def]
  note Sh = pow_sub_entry_monadic_shape[OF ne len1 hcb qpre, of nfloor dlt]
  have post: "ok \<longrightarrow> dyadic_interval_vec_invar out \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0)
           \<and> iso_half P (defl_wins out)
           \<and> iso_half (real_of_int_poly (Poly (refl_list xs))) (defl_wins out)"
    if s: "ok \<longrightarrow> (\<forall>j < length (dyadic_interval_vec_triples out).
                 case dyadic_interval_vec_triples out ! j of ((L, R), m) \<Rightarrow>
                   dsc_pair_ok P (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
                   \<and> dsc_pair_ok P (- (real_of_int R / 2 ^ m), - (real_of_int L / 2 ^ m)))"
      and c: "ok \<longrightarrow> (\<forall>x::real. poly P x = 0 \<longrightarrow>
        (\<exists>j L R m. j < length (dyadic_interval_vec_triples out)
           \<and> dyadic_interval_vec_triples out ! j = ((L, R), m)
           \<and> ((real_of_int L / 2 ^ m < x \<and> x < real_of_int R / 2 ^ m
                \<or> real_of_int L / 2 ^ m = x \<and> real_of_int R / 2 ^ m = x)
              \<or> (- (real_of_int R / 2 ^ m) < x \<and> x < - (real_of_int L / 2 ^ m)
                \<or> - (real_of_int R / 2 ^ m) = x \<and> - (real_of_int L / 2 ^ m) = x))))"
      and u: "ok \<longrightarrow> pow_sub_entry_contract P (defl_wins out)"
      and sh: "ok \<longrightarrow> dyadic_interval_vec_invar out \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0)"
    for out xs0 ok
  proof
    assume ok
    have S': "\<forall>w \<in> set (defl_wins out). dsc_pair_ok P w \<and> dsc_pair_ok P (pow_sub_mirror w)"
      using s \<open>ok\<close> unfolding defl_wins_def pow_sub_mirror_def
      by (auto simp: in_set_conv_nth split: prod.splits)
    have C': "\<forall>x. poly P x = 0 \<longrightarrow> (\<exists>w \<in> set (defl_wins out). iv_in x w \<or> iv_in x (pow_sub_mirror w))"
    proof (intro allI impI)
      fix x assume rx: "poly P x = 0"
      obtain j L R m where j: "j < length (dyadic_interval_vec_triples out)"
          "dyadic_interval_vec_triples out ! j = ((L, R), m)"
        and xin: "(real_of_int L / 2 ^ m < x \<and> x < real_of_int R / 2 ^ m
                \<or> real_of_int L / 2 ^ m = x \<and> real_of_int R / 2 ^ m = x)
              \<or> (- (real_of_int R / 2 ^ m) < x \<and> x < - (real_of_int L / 2 ^ m)
                \<or> - (real_of_int R / 2 ^ m) = x \<and> - (real_of_int L / 2 ^ m) = x)"
        using c \<open>ok\<close> rx by blast
      have "(real_of_int L / 2 ^ m, real_of_int R / 2 ^ m) \<in> set (defl_wins out)"
        using j unfolding defl_wins_def by (force simp: in_set_conv_nth)
      moreover have "iv_in x (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m)
          \<or> iv_in x (pow_sub_mirror (real_of_int L / 2 ^ m, real_of_int R / 2 ^ m))"
        using xin unfolding iv_in_def pow_sub_mirror_def by simp
      ultimately show "\<exists>w \<in> set (defl_wins out). iv_in x w \<or> iv_in x (pow_sub_mirror w)"
        by blast
    qed
    have iso: "iso_half P (defl_wins out) \<and> iso_half (P \<circ>\<^sub>p [:0, -1:]) (defl_wins out)"
      by (rule pow_sub_iso_halves[OF P0 S' C' u[rule_format, OF \<open>ok\<close>]])
    show "dyadic_interval_vec_invar out \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0)
           \<and> iso_half P (defl_wins out)
           \<and> iso_half (real_of_int_poly (Poly (refl_list xs))) (defl_wins out)"
      using sh \<open>ok\<close> iso unfolding P_def Poly_refl_list_eq_pcompose by simp
  qed
  show ?thesis
    apply (rule weaken_SPEC[OF SPEC_conj_rule[OF S SPEC_conj_rule[OF C SPEC_conj_rule[OF U Sh]]]])
    apply (all \<open>(solves \<open>simp only: \<close>)?\<close>)
    apply (all \<open>(solves \<open>arith\<close>)?\<close>)
    subgoal for x
      apply (cases x)
      apply (simp only: prod.case)
      apply (elim conjE)
      apply (rule post)
         apply assumption+
      done
    done
qed

section \<open>Path A (degree \<open>\<le> 8\<close>) and path C (the deflating stack) in the uniform contract\<close>

lemma rat_pair_real_triple:
  "rat_pair_real (dyadic_interval_of_triple t)
     = (case t of ((A, B), m) \<Rightarrow> (real_of_int A / 2 ^ m, real_of_int B / 2 ^ m))"
  by (cases t) (auto simp: dyadic_interval_of_triple_def rat_pair_real_def dyadic_rat_def
      of_rat_divide of_rat_power)

lemma defl_wins_to_list:
  "defl_wins acc = map rat_pair_real (dyadic_interval_vec_to_list acc)"
  unfolding defl_wins_trip_wins dyadic_interval_vec_to_list_def trip_wins_def
  by (auto simp: rat_pair_real_triple split: prod.splits)

lemma half_strong_iso_half:
  assumes hs: "half_strong P acc"
  shows "iso_half P (defl_wins acc)"
proof -
  let ?L = "dyadic_interval_vec_to_list acc"
  have W: "defl_wins acc = map rat_pair_real ?L" by (rule defl_wins_to_list)
  have S: "\<forall>w \<in> set (defl_wins acc). dsc_pair_ok P w"
    using hs unfolding W by auto
  have C: "\<forall>x. 0 < x \<longrightarrow> poly P x = 0 \<longrightarrow> (\<exists>w \<in> set (defl_wins acc). iv_in x w)"
    using hs unfolding W by fastforce
  have disj: "iv_disj_mset (mset (defl_wins acc))"
    using hs unfolding W by simp
  have U: "iv_root_unique P (defl_wins acc)"
    unfolding iv_root_unique_def
    using iv_disj_mset_nth[OF disj] unfolding iv_disj_def by blast
  have Pos: "\<forall>w \<in> set (defl_wins acc). \<forall>x. iv_in x w \<longrightarrow> 0 < x"
    using hs unfolding W by auto
  show ?thesis unfolding iso_half_def iv_wins_pos_def using S C U Pos by blast
qed

text \<open>\<^bold>\<open>The two linear bundles are one\<close>: the degree \<open>\<le> 8\<close> chain states its
  precondition as \<open>lowdeg_lin_pre\<close> because it cannot see the deflating chain's
  @{const dsc_isolate_all_split_lin_pre}; here, where both are in scope, they coincide.\<close>

lemma split_cap_lin_eq_bisect: "split_cap_lin = bisect_cap_lin"
  by (intro ext) (simp add: split_cap_lin_def bisect_cap_lin_def)

lemma dsc_isolate_all_split_lin_pre_lowdeg:
  assumes "dsc_isolate_all_split_lin_pre xs"
  shows "lowdeg_lin_pre xs"
  using assms unfolding dsc_isolate_all_split_lin_pre_def lowdeg_lin_pre_def split_cap_lin_eq_bisect
  by simp

theorem lowdeg_isolate_all_split_main_iso:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_lin_pre xs"
  shows "lowdeg_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accQ, xs0).
      dyadic_interval_vec_invar accP \<and> dyadic_interval_vec_invar accQ
    \<and> iso_half (real_of_int_poly (Poly xs)) (defl_wins accP)
    \<and> iso_half (real_of_int_poly (Poly (refl_list xs))) (defl_wins accQ)
    \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
  apply (rule weaken_SPEC[OF lowdeg_isolate_all_split_main_correct_strong[OF dsc_isolate_all_split_lin_pre_lowdeg[OF pre]]])
  apply (clarify)
  apply (intro conjI half_strong_iso_half)
  apply (simp_all only:)
  done

theorem defl_isolate_all_split_main_iso:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_defl_pre xs"
  shows "defl_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accQ, xs0).
      dyadic_interval_vec_invar accP \<and> dyadic_interval_vec_invar accQ
    \<and> iso_half (real_of_int_poly (Poly xs)) (defl_wins accP)
    \<and> iso_half (real_of_int_poly (Poly (refl_list xs))) (defl_wins accQ)
    \<and> xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
  apply (rule weaken_SPEC[OF defl_isolate_all_split_main_correct_geom[OF pre]])
  apply (clarify)
  apply (intro conjI defl_iso_half)
  apply (simp_all only:)
  done

end
