theory Kiou_Bound_Defl_Reflect
  imports "IsaRRI_Refine.Kiou_Bound_Hybrid_Reflect"
    "IsaRRI_Refine.Deflation_Loop_Geom"
begin

text \<open>The deflating solver at the reflect level: its end-to-end specification on both halves.\<close>


section \<open>The \<open>\<mu>\<close> bridge: \<open>delta_defl\<close> costs at most a constant extra depth\<close>

text \<open>\<^bold>\<open>Why the deflating solve needs this at all.\<close> The hybrid precondition states its two depth caps
  (\<open>hybrid_depth_cap\<close>) at \<open>\<delta> = delta_P Yinit\<close>, and the deflating solve needs them at
  \<open>\<delta> = delta_defl Yinit\<close>. @{thm [source] delta_defl_le_delta_P} says the deflating \<open>\<delta>\<close> is
  SMALLER, and @{const mu} is antitone in \<open>\<delta>\<close> --- so the deflating obligation is strictly
  stronger and does not simply inherit.

  \<^bold>\<open>But the excess is a CONSTANT, not a factor\<close>: \<open>delta_defl P = min (delta_P P) (1 / (4\<cdot>R\<^sub>0))\<close>
  with \<open>R\<^sub>0\<close> a numeral-bounded constant, so on the clamped branch \<open>\<mu>\<close> is a fixed number.
  That is what makes the deflating depth cap a strengthening one line wide rather than a new
  quantity.\<close>

subsection \<open>\<open>mu\<close> is antitone in \<open>\<delta>\<close>\<close>

lemma defl_mu_antitone:
  fixes \<delta>1 \<delta>2 :: real
  assumes pos: "0 < \<delta>1" and le: "\<delta>1 \<le> \<delta>2" and ab: "a \<le> b"
  shows "mu \<delta>2 a b \<le> mu \<delta>1 a b"
proof -
  have w: "0 \<le> b - a" using ab by simp
  have q: "(b - a) / \<delta>2 \<le> (b - a) / \<delta>1"
    using w pos le by (intro divide_left_mono) auto
  have m: "max 1 ((b - a) / \<delta>2) \<le> max 1 ((b - a) / \<delta>1)" using q by simp
  have p1: "(0::real) < max 1 ((b - a) / \<delta>2)" by simp
  have p2: "(0::real) < max 1 ((b - a) / \<delta>1)" by simp
  have logle: "log 2 (max 1 ((b - a) / \<delta>2)) \<le> log 2 (max 1 ((b - a) / \<delta>1))"
    using m p1 p2 by simp
  have ceil: "\<lceil>log 2 (max 1 ((b - a) / \<delta>2))\<rceil>
                \<le> \<lceil>log 2 (max 1 ((b - a) / \<delta>1))\<rceil>"
    using logle by (rule ceiling_mono)
  show ?thesis unfolding mu_def using nat_mono[OF ceil] by simp
qed

subsection \<open>The clamp is a NUMERAL, so its own \<open>\<mu>\<close> is a numeral\<close>

lemma defl_sqrt3_le2: "sqrt 3 \<le> 2"
proof -
  have "(3::real) \<le> 2\<^sup>2" by simp
  hence "sqrt 3 \<le> sqrt ((2::real)\<^sup>2)" by (rule real_sqrt_le_mono)
  thus ?thesis by (simp add: real_sqrt_abs)
qed

text \<open>\<open>R\<^sub>0 = 2/\<surd>3 \<approx> 1.1547\<close> exactly, but the crude triangle bound
  \<open>cmod z \<le> \<bar>Re z\<bar> + \<bar>Im z\<bar>\<close> already gives \<open>\<le> 1/2 + \<surd>3/6 + \<surd>3/3 \<le> 3/2\<close>, which is all
  the \<open>\<mu>\<close> estimate needs.\<close>

lemma defl_R0_le: "R0 \<le> 3/2"
proof -
  have "cmod (1/2 + (sqrt 3 / 6) * Complex.imaginary_unit)
          \<le> \<bar>Re (1/2 + (sqrt 3 / 6) * Complex.imaginary_unit)\<bar>
            + \<bar>Im (1/2 + (sqrt 3 / 6) * Complex.imaginary_unit)\<bar>"
    by (rule cmod_le)
  also have "\<dots> = 1/2 + sqrt 3 / 6" by simp
  finally have c: "cmod (1/2 + (sqrt 3 / 6) * Complex.imaginary_unit) \<le> 1/2 + sqrt 3 / 6" .
  have "R0 \<le> 1/2 + sqrt 3 / 6 + sqrt 3 / 3" unfolding R0_def using c by simp
  also have "\<dots> \<le> 1/2 + 2/6 + 2/3" using defl_sqrt3_le2 by simp
  finally show ?thesis by simp
qed

lemma defl_mu_clamp_le4: "mu (1 / (4 * R0)) 0 1 \<le> 4"
proof -
  have R: "0 < R0" by (rule R0_pos)
  have w: "(1 - 0) / (1 / (4 * R0)) = 4 * R0" using R by simp
  have le8: "max 1 (4 * R0) \<le> 8" using defl_R0_le R by simp
  have p: "(0::real) < max 1 (4 * R0)" by simp
  \<comment> \<open>through @{thm [source] log_le_iff}, not through \<open>log 2 8 = 3\<close>: as an EQUALITY
     that fact fights \<open>simp\<close>'s numeral evaluation, which rewrites \<open>2 ^ 3\<close> straight back
     to \<open>8\<close>. The inequality is all this needs.\<close>
  have "log 2 (max 1 (4 * R0)) \<le> 3"
    using le8 p by (subst log_le_iff) (simp_all add: powr_numeral)
  hence "\<lceil>log 2 (max 1 (4 * R0))\<rceil> \<le> 3" by (simp add: ceiling_le_iff)
  thus ?thesis unfolding mu_def w by simp
qed

subsection \<open>The bridge\<close>

lemma defl_iv_mu_unit: "dyadic_iv_interval_mu \<delta> (0, 1) = mu \<delta> 0 1"
  unfolding dyadic_iv_interval_mu_def by simp

lemma defl_mu_delta_defl_le:
  "dyadic_iv_interval_mu (delta_defl P) (0, 1)
     \<le> max (dyadic_iv_interval_mu (delta_P P) (0, 1)) 4"
proof (cases "delta_P P \<le> 1 / (4 * R0)")
  case True
  hence "delta_defl P = delta_P P" unfolding delta_defl_def by simp
  thus ?thesis by simp
next
  case False
  hence "delta_defl P = 1 / (4 * R0)" unfolding delta_defl_def by simp
  thus ?thesis using defl_mu_clamp_le4 by (simp add: defl_iv_mu_unit)
qed

text \<open>\<^bold>\<open>And the direction the STRENGTHENING needs\<close>: the deflating \<open>\<mu>\<close> dominates the classic
  one, so a depth cap stated at \<open>delta_defl\<close> implies the one stated at \<open>delta_P\<close>. That is what
  makes a deflating precondition a STRENGTHENING of the hybrid bundle rather than a different
  bundle --- every consumer of the hybrid precondition keeps working, and the satisfiability
  witness is needed once rather than twice.\<close>

lemma defl_mu_delta_P_le:
  assumes P0: "P \<noteq> 0"
  shows "dyadic_iv_interval_mu (delta_P P) (0, 1)
           \<le> dyadic_iv_interval_mu (delta_defl P) (0, 1)"
  unfolding defl_iv_mu_unit
  by (rule defl_mu_antitone[OF delta_defl_pos[OF P0] delta_defl_le_delta_P]) simp


section \<open>The deflating depth cap, and why the bundle strengthens rather than forks\<close>

text \<open>\<^bold>\<open>The gap, stated exactly.\<close> @{const hybrid_depth_cap}, the clause
  @{const dsc_isolate_all_split_hybrid_pre} carries and the source of the guard-headroom obligation,
  is quantified over \<open>kD \<le> 258 \<cdot> \<mu> (delta_P Yinit)\<close>. @{thm [source] defl_main_list_correct} needs the
  same two facts over \<open>kD \<le> hybrid_root_potential (delta_defl Yinit) 0\<close>, which is
  \<open>258 \<cdot> \<mu> (delta_defl Yinit)\<close>, and the bridge above says that range is the larger one. So the deflating
  obligation is not inherited; it is stated.

  \<^bold>\<open>The DEPTH-CAP half strengthens; the BUNDLES do not.\<close> @{thm [source] defl_mu_delta_P_le}
  makes the deflating range contain the classic one, so \<open>defl_depth_cap \<longrightarrow> hybrid_depth_cap\<close>
  (\<open>defl_depth_cap_imp_hybrid\<close>, below). That implication is all the bridge buys, and it does \<open>NOT\<close>
  lift to the bundles: \<open>dsc_isolate_all_split_defl_pre\<close> is built on
  \<open>dsc_isolate_all_split_lin_pre\<close>, which drops \<open>split_cap\<close>'s exponential clause, and at the
  base bundle it is only the converse that holds
  (\<open>dsc_isolate_all_split_pre \<longrightarrow> dsc_isolate_all_split_lin_pre\<close>). The two bundles are therefore
  \<open>INCOMPARABLE\<close> --- neither implies the other --- so each carries its own satisfiability
  witness, \<open>dsc_isolate_all_split_defl_pre_satisfiable\<close> and
  \<open>dsc_isolate_all_split_hybrid_pre_satisfiable\<close>, and the bundle note below states the same thing.

  \<^bold>\<open>Where the difference does cost a hypothesis.\<close> A consumer that takes the bundle
  as a hypothesis is affected: the reduced-polynomial hypothesis \<open>dqsolve\<close> of
  the power-substitution entry is quantified over every \<open>q\<close> meeting the precondition, and the capstone
  below delivers its \<open>SPEC\<close> only for the deflating class, so that hypothesis (\<open>qpre\<close>) is stated
  with the deflating bundle, which strengthens the obligation on the reduced polynomial.\<close>

subsection \<open>Both \<open>\<delta>\<close>s are positive UNCONDITIONALLY\<close>

text \<open>@{thm [source] delta_P_pos} and @{thm [source] delta_defl_pos} both take \<open>P \<noteq> 0\<close>, but
  neither needs it: @{const delta_P}'s own degenerate branch returns \<open>1\<close>. Dropping the
  hypothesis here keeps it out of every clause below.\<close>

lemma defl_delta_P_pos_always: "0 < delta_P P"
proof (cases "map_poly of_real P = (0 :: complex poly)")
  case True
  thus ?thesis unfolding delta_P_def by simp
next
  case False
  hence "P \<noteq> 0" by auto
  thus ?thesis by (rule delta_P_pos)
qed

lemma defl_delta_defl_pos_always: "0 < delta_defl P"
  unfolding delta_defl_def using defl_delta_P_pos_always[of P] R0_pos by simp

lemma defl_mu_delta_P_le_always:
  "dyadic_iv_interval_mu (delta_P P) (0, 1) \<le> dyadic_iv_interval_mu (delta_defl P) (0, 1)"
  unfolding defl_iv_mu_unit
  by (rule defl_mu_antitone[OF defl_delta_defl_pos_always delta_defl_le_delta_P]) simp

subsection \<open>The cap, and the bundle\<close>

text \<open>Verbatim @{const hybrid_depth_cap} with @{const delta_P} replaced by
  @{const delta_defl} --- same two clauses, same \<open>258 \<cdot> \<mu>\<close> shape, same \<open>length ys\<close> argument
  (\<open>length (refl_list xs) = length xs\<close>, so one argument serves both halves).\<close>

definition defl_depth_cap :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"defl_depth_cap ys k \<longleftrightarrow>
  (let Yinit = scale_poly_list (2 ^ k) ys;
       \<delta> = delta_defl (map_poly of_int (Poly Yinit) :: real poly) in
     (\<forall>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
              * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<longrightarrow>
        kD * (length ys - 1) < max_snat LENGTH(gmp_poly_len)) \<and>
     (\<forall>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
              * int (dyadic_iv_interval_mu \<delta> (0, 1)) \<longrightarrow>
        (kD + 1) * length ys < 1099511627776))"

lemma defl_depth_cap_imp_hybrid:
  assumes d: "defl_depth_cap ys k"
  shows "hybrid_depth_cap ys k"
proof -
  define Yinit where "Yinit = scale_poly_list (2 ^ k) ys"
  define Yr where "Yr = (map_poly of_int (Poly Yinit) :: real poly)"
  have mule: "dyadic_iv_interval_mu (delta_P Yr) (0, 1)
                \<le> dyadic_iv_interval_mu (delta_defl Yr) (0, 1)"
    by (rule defl_mu_delta_P_le_always)
  \<comment> \<open>the classic range is CONTAINED in the deflating one, so each classic \<open>kD\<close> is a
     deflating \<open>kD\<close> and the two clauses transfer one at a time\<close>
  have step: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                     * int (dyadic_iv_interval_mu (delta_P Yr) (0, 1))
              \<Longrightarrow> int kD \<le> int (2 ^ newton_pol_ecap + 2)
                     * int (dyadic_iv_interval_mu (delta_defl Yr) (0, 1))"
  proof -
    fix kD :: nat
    assume h: "int kD \<le> int (2 ^ newton_pol_ecap + 2)
                          * int (dyadic_iv_interval_mu (delta_P Yr) (0, 1))"
    \<comment> \<open>\<open>mult_left_mono\<close> gives the two PRODUCTS; the transitivity down to \<open>kD\<close> is a
       separate step and \<open>simp\<close> does not chain it.\<close>
    have "int (2 ^ newton_pol_ecap + 2) * int (dyadic_iv_interval_mu (delta_P Yr) (0, 1))
            \<le> int (2 ^ newton_pol_ecap + 2)
                 * int (dyadic_iv_interval_mu (delta_defl Yr) (0, 1))"
      using mule by (intro mult_left_mono) simp_all
    thus "int kD \<le> int (2 ^ newton_pol_ecap + 2)
                     * int (dyadic_iv_interval_mu (delta_defl Yr) (0, 1))"
      using h by linarith
  qed
  from d have d1: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                          * int (dyadic_iv_interval_mu (delta_defl Yr) (0, 1))
                   \<Longrightarrow> kD * (length ys - 1) < max_snat LENGTH(gmp_poly_len)"
    and d2: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                     * int (dyadic_iv_interval_mu (delta_defl Yr) (0, 1))
              \<Longrightarrow> (kD + 1) * length ys < 1099511627776"
    unfolding defl_depth_cap_def Yinit_def[symmetric] Yr_def[symmetric] Let_def by blast+
  show ?thesis
    unfolding hybrid_depth_cap_def Yinit_def[symmetric] Yr_def[symmetric] Let_def
    using d1 d2 step by blast
qed

text \<open>\<^bold>\<open>The deflating bundle: @{const split_cap} without its exponential clause.\<close>
  @{const split_cap}'s clause \<open>2\<^sup>\<mu>\<^sup>+\<^sup>1 + 1 < 2\<^sup>6\<^sup>3\<close>, i.e. \<open>\<mu> \<le> 61\<close>, is a root-separation floor of
  about \<open>4 \<cdot> 10\<^sup>-\<^sup>1\<^sup>8\<close> once the box is normalised. It feeds only word budgets of the kind that
  charge every pending node a complete binary tree; the deflating loop's budgets are linear in
  \<open>\<mu>\<close> (\<open>Deflation_Loop_Refine\<close>'s \<open>defl_stack_invar\<close>, \<open>Deflation_Loop_Geom\<close>'s accumulator bound), so
  this bundle does without it.

  \<^item> \<open>split_cap_lin\<close> is @{const split_cap} with that clause dropped and its \<open>k + \<mu> + 1\<close> clause
    widened to \<open>k + \<mu> + 3\<close> (the worklist of the degree \<open>\<le> 8\<close> bisection path is at most
    \<open>\<mu> + 1\<close> long and must fit two more).
  \<^item> \<open>dsc_isolate_all_split_lin_pre\<close> is @{const dsc_isolate_all_split_pre} over it.
  \<^item> \<open>dsc_isolate_all_split_defl_pre\<close> adds the length bounds and the deflating depth caps. It
    does not imply @{const dsc_isolate_all_split_hybrid_pre}; the hybrid entry keeps its own,
    stronger bundle.\<close>

definition split_cap_lin :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"split_cap_lin ys k \<longleftrightarrow>
  k * length ys < max_snat LENGTH(gmp_poly_len) \<and>
  (let Yinit = scale_poly_list (2 ^ k) ys;
       \<delta> = delta_P (map_poly of_int (Poly Yinit) :: real poly) in
     k + rational_interval_mu \<delta> (0, 1) + 3 < max_snat LENGTH(gmp_poly_len))"

definition dsc_isolate_all_split_lin_pre :: "int list \<Rightarrow> bool" where
"dsc_isolate_all_split_lin_pre xs \<longleftrightarrow>
  2 \<le> length xs \<and> last xs \<noteq> 0 \<and> kiou_headroom xs \<and>
  coeffs (Poly xs) = xs \<and>
  square_free (map_poly of_int (Poly xs) :: real poly) \<and>
  kiou_bound_k_monadic xs \<le> SPEC (split_cap_lin xs) \<and>
  kiou_bound_k_monadic (refl_list xs) \<le> SPEC (split_cap_lin (refl_list xs))"

definition dsc_isolate_all_split_defl_pre :: "int list \<Rightarrow> bool" where
"dsc_isolate_all_split_defl_pre xs \<longleftrightarrow>
  dsc_isolate_all_split_lin_pre xs \<and>
  length xs + 3 < max_snat LENGTH(gmp_poly_len) \<and>
  length xs < 1099511627776 \<and>
  kiou_bound_k_monadic xs \<le> SPEC (defl_depth_cap xs) \<and>
  kiou_bound_k_monadic (refl_list xs) \<le> SPEC (defl_depth_cap (refl_list xs))"

lemma split_cap_imp_lin:
  assumes c: "split_cap ys k" and l2: "2 \<le> length ys"
  shows "split_cap_lin ys k"
proof -
  let ?m = "rational_interval_mu (delta_P (map_poly of_int (Poly (scale_poly_list (2 ^ k) ys))
               :: real poly)) (0, 1)"
  have kl: "k * length ys < max_snat LENGTH(gmp_poly_len)"
    and e: "int (2 ^ Suc ?m) + 1 < int (max_snat LENGTH(gmp_poly_len))"
    using c unfolding split_cap_def Let_def by simp_all
  have m61: "Suc ?m < 63"
  proof -
    define A where "A = (2::nat) ^ Suc ?m"
    have "int A < int (2 ^ 63)" using e unfolding A_def[symmetric] by (simp add: max_snat_def)
    then have "(2::nat) ^ Suc ?m < 2 ^ 63" unfolding A_def by linarith
    then show ?thesis using power_less_imp_less_exp[of "2::nat" "Suc ?m" 63] by simp
  qed
  have kl2: "k * length ys < 9223372036854775808" using kl by (simp add: max_snat_def)
  have "k * 2 \<le> k * length ys" using l2 by (rule mult_le_mono2)
  then have k62: "k * 2 < 9223372036854775808" using kl2 by linarith
  have "k + ?m + 3 < 9223372036854775808" using k62 m61 by linarith
  then have "k + ?m + 3 < max_snat LENGTH(gmp_poly_len)" by (simp add: max_snat_def)
  then show ?thesis using kl unfolding split_cap_lin_def Let_def by simp
qed

text \<open>The capped kiou spec (@{thm [source] kiou_bound_k_monadic_spec_capped}) at the linear cap.\<close>

lemma kiou_bound_k_monadic_spec_capped_lin:
  fixes ys :: "int list"
  assumes len2: "2 \<le> length ys" and lastnz: "last ys \<noteq> 0"
    and hr: "kiou_headroom ys"
    and capY: "kiou_bound_k_monadic ys \<le> SPEC (split_cap_lin ys)"
  shows "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k.
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k) \<and>
      k * length ys < max_snat LENGTH(gmp_poly_len) \<and> k < max_snat LENGTH(gmp_poly_len) \<and>
      split_cap_lin ys k)"
proof -
  have len1: "1 \<le> length ys" using len2 by linarith
  have kcap: "\<And>k. k * length ys < max_snat LENGTH(gmp_poly_len) \<Longrightarrow>
      k < max_snat LENGTH(gmp_poly_len)"
  proof -
    fix k assume h: "k * length ys < max_snat LENGTH(gmp_poly_len)"
    have "k * 1 \<le> k * length ys" by (rule mult_le_mono2[OF len1])
    hence "k \<le> k * length ys" by linarith
    thus "k < max_snat LENGTH(gmp_poly_len)" using h by linarith
  qed
  have both: "kiou_bound_k_monadic ys \<le> SPEC (\<lambda>k.
      (\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly ys) x = 0 \<longrightarrow> x < 2 ^ k) \<and> split_cap_lin ys k)"
    by (rule kiou_le_SPEC_conj[OF kiou_bound_k_monadic_sound[OF len2 lastnz hr] capY])
  show ?thesis
    by (rule order_trans[OF both]) (use kcap in \<open>auto simp: split_cap_lin_def\<close>)
qed

text \<open>\<^bold>\<open>The seed's \<open>\<delta>\<close>-free facts\<close>, read off the input directly. The halves used to take them
  from @{thm [source] dsc_isolate_all_split_pos_hybrid_pre}, whose bundle also carries the
  exponential clause; every fact here is the same one-line derivation that lemma makes.\<close>

lemma defl_seed_facts:
  fixes ys :: "int list" and k :: nat
  assumes len2: "2 \<le> length ys" and lastnz: "last ys \<noteq> 0"
    and sf: "square_free (map_poly of_int (Poly ys) :: real poly)"
    and lenb3: "length ys + 3 < max_snat LENGTH(gmp_poly_len)"
  defines "Yinit \<equiv> scale_poly_list (2 ^ k) ys"
  shows "Suc 0 < length Yinit"
    and "square_free (map_poly of_int (Poly Yinit) :: real poly)"
    and "coeffs (Poly Yinit) = Yinit"
    and "length Yinit + 2 < max_snat LENGTH(gmp_poly_len)"
    and "Yinit = carried_init_same_den 0 (2 ^ 0) (2 ^ k) ys"
    and "length Yinit = length ys"
proof -
  have ne: "ys \<noteq> []" using len2 by auto
  have canon: "coeffs (Poly ys) = ys" by (rule coeffs_Poly_eq_self_of_last_nonzero[OF ne lastnz])
  have cpos: "(2::int) ^ k \<noteq> 0" by simp
  show le: "length Yinit = length ys"
    unfolding Yinit_def by (simp add: scale_poly_list_eq_map_upt)
  show "square_free (map_poly of_int (Poly Yinit) :: real poly)"
    unfolding Yinit_def
    using square_free_pcompose_linear[OF sf, of "2 ^ k"]
    by (simp add: Poly_scale_poly_list_eq_pcompose)
  show "coeffs (Poly Yinit) = Yinit"
    unfolding Yinit_def
    using coeffs_scale_poly_list[OF canon[symmetric], of "2 ^ k"] cpos
    by (simp add: scale_poly_list_correct[symmetric, of "2 ^ k" "Poly ys"] canon)
  show "Suc 0 < length Yinit" using len2 le by simp
  show "length Yinit + 2 < max_snat LENGTH(gmp_poly_len)" using lenb3 le by simp
  show "Yinit = carried_init_same_den 0 (2 ^ 0) (2 ^ k) ys"
    unfolding Yinit_def by (simp add: split_init_pow2_l0_eq_scale_poly_list)
qed

text \<open>\<^bold>\<open>The three \<open>\<mu>\<close>-caps of the deflating solve, from the depth cap alone.\<close> They used to come
  from the exponential clause (\<open>defl_kroom_of_mucap\<close>, via \<open>\<mu> \<le> 61\<close>). The depth
  cap's guard-headroom clause at \<open>kD = 258 \<cdot> \<mu>\<close> already says \<open>258 \<cdot> \<mu> + 1 < 2\<^sup>4\<^sup>0\<close>.\<close>

lemma defl_caps_of_depth:
  assumes d2: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                           * int (dyadic_iv_interval_mu \<delta> (0, 1))
                  \<Longrightarrow> (kD + 1) * n < 1099511627776"
    and n1: "1 \<le> n"
  shows "int (dyadic_iv_interval_mu \<delta> (0, 1)) + 3 < int (max_snat LENGTH(gmp_poly_len))"
    and "hybrid_root_potential \<delta> 0 < int (max_snat LENGTH(gmp_poly_len))"
    and "hybrid_root_potential \<delta> 0 + 258 < int (max_snat LENGTH(gmp_poly_len))"
proof -
  define m where "m = dyadic_iv_interval_mu \<delta> (0, 1)"
  have c: "(2::nat) ^ newton_pol_ecap + 2 = 258" by (simp add: newton_pol_ecap_def)
  have "(258 * m + 1) * n < 1099511627776"
    using d2[of "258 * m"] unfolding m_def[symmetric] c by simp
  moreover have "258 * m + 1 \<le> (258 * m + 1) * n"
    using mult_le_mono2[OF n1, of "258 * m + 1"] by simp
  ultimately have m40: "258 * m + 1 < 1099511627776" by linarith
  have pot: "hybrid_root_potential \<delta> 0 = 258 * int m"
    by (simp add: hybrid_root_potential_def newton_pol_ecap_def m_def)
  have mx: "(1099511627776::int) + 258 < int (max_snat LENGTH(gmp_poly_len))"
    by (simp add: max_snat_def)
  show "int (dyadic_iv_interval_mu \<delta> (0, 1)) + 3 < int (max_snat LENGTH(gmp_poly_len))"
    using m40 mx unfolding m_def[symmetric] by linarith
  show "hybrid_root_potential \<delta> 0 < int (max_snat LENGTH(gmp_poly_len))"
    using m40 mx unfolding pot by linarith
  show "hybrid_root_potential \<delta> 0 + 258 < int (max_snat LENGTH(gmp_poly_len))"
    using m40 mx unfolding pot by linarith
qed


text \<open>The exact-zero check, at the one fact it reads (@{thm [source]
  dsc_isolate_all_split_zero_check_correct} states it at the stronger bundle).\<close>

lemma dsc_split_zero_check_correct_len2:
  fixes xs :: "int list"
  assumes len2: "2 \<le> length xs"
  shows "dsc_split_zero_check_monadic xs \<le> SPEC (\<lambda>xs0. xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
  unfolding dsc_split_zero_check_monadic_def PR_CONST_def poly_coeff_sgn_monadic_def
  apply refine_vcg
  using len2 by (auto simp: sgn_eq_0_iff)

section \<open>The two numeric bridges the deflating solver call needs\<close>

text \<open>@{thm [source] defl_main_list_correct} takes its word caps at \<open>\<delta> = delta_defl\<close>, and the
  hybrid bundle supplies them at \<open>delta_P\<close>. The two depth clauses are a precondition clause (above);
  these two need no new hypothesis, because the constant bound of the \<open>\<mu>\<close> bridge closes the gap.\<close>

lemma defl_mucap_of_hybrid:
  assumes m: "int (2 ^ Suc (dyadic_iv_interval_mu (delta_P P) (0, 1))) + 1
                < int (max_snat LENGTH(gmp_poly_len))"
  shows "int (2 ^ Suc (dyadic_iv_interval_mu (delta_defl P) (0, 1))) + 1
           < int (max_snat LENGTH(gmp_poly_len))"
proof -
  have le: "dyadic_iv_interval_mu (delta_defl P) (0, 1)
              \<le> max (dyadic_iv_interval_mu (delta_P P) (0, 1)) 4"
    by (rule defl_mu_delta_defl_le)
  \<comment> \<open>\<^bold>\<open>The two powers are NAMED, and that is what makes this go through.\<close> Left as
     \<open>2\<^sup>S\<^sup>u\<^sup>c\<^sup>\<mu>\<close> they are rewritten by \<open>simp\<close> to \<open>2 \<cdot> 2\<^sup>\<mu>\<close> on BOTH sides of the
     \<open>nat\<close>/\<open>int\<close> coercion, which then prints identically and unifies with nothing --- three
     cycles were spent on goals of the literal form \<open>2\<^sup>\<mu> \<le> 16 \<Longrightarrow> 2\<^sup>\<mu> \<le> 16\<close>. As
     \<open>define\<close>d atoms the coercion is crossed once and the arithmetic is \<open>linarith\<close>'s.\<close>
  define D where "D = (2::nat) ^ Suc (dyadic_iv_interval_mu (delta_defl P) (0, 1))"
  define A where "A = (2::nat) ^ Suc (dyadic_iv_interval_mu (delta_P P) (0, 1))"
  have mA: "int A + 1 < int (max_snat LENGTH(gmp_poly_len))" using m by (simp add: A_def)
  have mx: "(33::int) < int (max_snat LENGTH(gmp_poly_len))" by (simp add: max_snat_def)
  \<comment> \<open>\<open>max\<close> is an atom to \<open>linarith\<close>, so its branches are separated here. The result is proved at
     the folded atom and unfolded once at the end: \<open>define\<close> rewrites the goal state, but \<open>?thesis\<close>
     still names the original \<open>shows\<close> text, so a \<open>show ?thesis\<close> inside the case split would see
     \<open>2\<^sup>S\<^sup>u\<^sup>c\<^sup>\<mu>\<close> again.\<close>
  have fin: "int D + 1 < int (max_snat LENGTH(gmp_poly_len))"
  proof (cases "dyadic_iv_interval_mu (delta_P P) (0, 1) \<le> 4")
    case True
    hence "dyadic_iv_interval_mu (delta_defl P) (0, 1) \<le> 4" using le by simp
    hence "D \<le> 2 ^ Suc 4" unfolding D_def by (intro power_increasing) simp_all
    hence "D \<le> 32" by simp
    hence "int D \<le> 32" by simp
    thus ?thesis using mx by linarith
  next
    case False
    hence "dyadic_iv_interval_mu (delta_defl P) (0, 1)
             \<le> dyadic_iv_interval_mu (delta_P P) (0, 1)" using le by simp
    hence "D \<le> A" unfolding D_def A_def by (intro power_increasing) simp_all
    hence "int D \<le> int A" by simp
    thus ?thesis using mA by linarith
  qed
  show ?thesis using fin by (simp add: D_def)
qed

text \<open>\<^bold>\<open>The k-potential's own cap, and its \<open>+ 258\<close> window headroom, come from \<open>mucap\<close>\<close> --- the
  same route the classic keystone's own \<open>kcap\<close> takes (@{thm [source] hybrid_seed_kcap} is the
  \<open>\<le>\<close> half; this is the \<open>< max_snat\<close> half). \<open>2\<^sup>S\<^sup>u\<^sup>c\<^sup>\<mu> < 2\<^sup>6\<^sup>3\<close> pins \<open>\<mu> \<le> 61\<close>, and
  \<open>258 \<cdot> 61 + 258 = 15996\<close> is a numeral.\<close>

lemma defl_mu_le_61:
  assumes m: "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
                < int (max_snat LENGTH(gmp_poly_len))"
  shows "dyadic_iv_interval_mu \<delta> (0, 1) \<le> 61"
proof (rule ccontr)
  assume "\<not> dyadic_iv_interval_mu \<delta> (0, 1) \<le> 61"
  hence g: "62 \<le> dyadic_iv_interval_mu \<delta> (0, 1)" by simp
  have "(2::nat) ^ 63 \<le> 2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))"
    using g by (intro power_increasing) simp_all
  moreover have "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) < int (2 ^ (63::nat))"
    using m by (simp add: max_snat_def)
  ultimately show False by linarith
qed

lemma defl_kroom_of_mucap:
  assumes m: "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
                < int (max_snat LENGTH(gmp_poly_len))"
  shows "hybrid_root_potential \<delta> 0 + 258 < int (max_snat LENGTH(gmp_poly_len))"
proof -
  have mu61: "dyadic_iv_interval_mu \<delta> (0, 1) \<le> 61" by (rule defl_mu_le_61[OF m])
  have "hybrid_root_potential \<delta> 0 = 258 * int (dyadic_iv_interval_mu \<delta> (0, 1))"
    by (simp add: hybrid_root_potential_def newton_pol_ecap_def)
  also have "\<dots> \<le> 258 * 61" using mu61 by simp
  finally have "hybrid_root_potential \<delta> 0 \<le> 15738" by simp
  thus ?thesis by (simp add: max_snat_def)
qed

lemma defl_kcap_of_mucap:
  assumes m: "int (2 ^ Suc (dyadic_iv_interval_mu \<delta> (0, 1))) + 1
                < int (max_snat LENGTH(gmp_poly_len))"
  shows "hybrid_root_potential \<delta> 0 < int (max_snat LENGTH(gmp_poly_len))"
  using defl_kroom_of_mucap[OF m] by simp



section \<open>The deflating positive half\<close>

text \<open>Structurally @{thm [source] hybrid_split_pos_solve_half_strong}: the same seeding chain,
  the same merged \<open>kiou_bound_k_monadic\<close> \<open>SPEC\<close>, the same \<open>rp = xs\<close> copy and
  \<open>Pinit\<^sub>0 = scale_poly_list (2\<^sup>k\<^sup>p\<^sup>o\<^sup>s) xs\<close> seed. Two differences, both simplifications:

  \<^item> the solver bound is @{thm [source] defl_main_list_correct}, whose four conjuncts are \<open>qsolve\<close>'s
    four symbol for symbol, so there is no \<open>real_to_rat_pair\<close> layer, no \<open>_from_pinned\<close> bridge and no
    rational-policy partner: the deflating loop never leaves the dyadic numerators;
  \<^item> its word caps are at \<open>delta_defl\<close>, supplied by the \<open>defl_depth_cap\<close> clause and the two numeric
    bridges above.\<close>

lemma defl_split_pos_solve_half:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_defl_pre xs"
  shows "defl_split_pos_solve_monadic xs
    \<le> SPEC (\<lambda>accP. dyadic_interval_vec_invar accP \<and>
        length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        defl_acc_isolates (of_int_poly (Poly xs) :: real poly) accP \<and>
        defl_acc_covers (of_int_poly (Poly xs) :: real poly) 0 accP)"
proof -
  from pre have pre': "dsc_isolate_all_split_lin_pre xs"
    and lenb3: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    unfolding dsc_isolate_all_split_defl_pre_def by simp_all
  from pre' have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    and canonxs: "coeffs (Poly xs) = xs"
    unfolding dsc_isolate_all_split_lin_pre_def by auto
  have P0: "Poly xs \<noteq> 0" using sfxs unfolding square_free_def by simp
  from pre have xs_small: "length xs < 1099511627776"
    unfolding dsc_isolate_all_split_defl_pre_def by simp
  have capY: "kiou_bound_k_monadic xs \<le> SPEC (split_cap_lin xs)"
    using pre' unfolding dsc_isolate_all_split_lin_pre_def by (simp add: Let_def)
  have capD: "kiou_bound_k_monadic xs \<le> SPEC (defl_depth_cap xs)"
    using pre unfolding dsc_isolate_all_split_defl_pre_def by (simp add: Let_def)
  \<comment> \<open>\<^bold>\<open>The two capacities have to be MERGED into one \<open>SPEC\<close>\<close>, exactly as on
     the classic side: only ONE \<open>\<le> SPEC\<close> fact fires per producer call, so a second one would
     never reach the continuation. @{thm [source] kiou_le_SPEC_conj} is what makes that legal.\<close>
  have merged: "kiou_bound_k_monadic xs \<le> SPEC (\<lambda>k.
      ((\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ k) \<and>
       k * length xs < max_snat LENGTH(gmp_poly_len) \<and>
       k < max_snat LENGTH(gmp_poly_len) \<and> split_cap_lin xs k)
      \<and> defl_depth_cap xs k)"
    by (rule kiou_le_SPEC_conj[OF kiou_bound_k_monadic_spec_capped_lin[OF len2 lastnz hr capY] capD])
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  show ?thesis
    unfolding defl_split_pos_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg merged[THEN order_trans])
    \<comment> \<open>the four ASSERT side goals, exactly as @{thm [source] hybrid_split_pos_solve_half_strong}
       takes them (the seeding chain is the same operation sequence). \<open>(cases xs)\<close>, not bare
       \<open>simp\<close>: \<open>0 < length xs\<close> normalises to \<open>xs \<noteq> []\<close>, which \<open>simp\<close> will not then
       derive from \<open>2 \<le> length xs\<close>.\<close>
    subgoal using len2 lenb by (cases xs) auto
    subgoal using lenb by simp
    subgoal premises p using p by simp
    subgoal premises p using p by simp
    subgoal premises kp for kpos
    proof -
      from kp have kpos_sound: "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly xs) x = 0 \<longrightarrow> x < 2 ^ kpos"
        and kpos_cap: "kpos * length xs < max_snat LENGTH(gmp_poly_len)"
        and kpos_lt: "kpos < max_snat LENGTH(gmp_poly_len)"
        and cap_at: "split_cap_lin xs kpos"
        and depth_at: "defl_depth_cap xs kpos" by blast+
      define Pinit0 where "Pinit0 = scale_poly_list (2 ^ kpos) xs"
      define Pr where "Pr = (map_poly of_int (Poly Pinit0) :: real poly)"
      have rp_eq: "poly_copy_monadic xs \<le> RETURN xs" by (rule poly_copy_correct[OF lenb])
      have Pinit_eq: "split_init_pow2_l0_monadic kpos xs \<le> RETURN Pinit0"
        using split_init_pow2_l0_monadic_correct[OF lenb kpos_cap]
        by (simp add: Pinit0_def split_init_pow2_l0_eq_scale_poly_list)
      \<comment> \<open>\<^bold>\<open>The seed's \<open>\<delta>\<close>-free facts, from the input\<close>, not through the hybrid bundle,
         which carries the exponential clause.\<close>
      note sd = defl_seed_facts[OF len2 lastnz sfxs lenb3, of kpos, folded Pinit0_def]
      have len2P: "Suc 0 < length Pinit0" by (rule sd(1))
      have sfPr: "square_free (map_poly of_int (Poly Pinit0) :: real poly)" by (rule sd(2))
      have canonP: "coeffs (Poly Pinit0) = Pinit0" by (rule sd(3))
      have lenbP: "length Pinit0 + 2 < max_snat LENGTH(gmp_poly_len)" by (rule sd(4))
      have P_eqP: "Pinit0 = carried_init_same_den 0 (2 ^ 0) (2 ^ kpos) xs" by (rule sd(5))
      have rpsmallP: "length xs < 1099511627776" by (rule xs_small)
      have lenPx: "length Pinit0 = length xs" by (simp add: Pinit0_def)
      \<comment> \<open>the one length premise the bundle does NOT state: \<open>nat_bitlen\<close> is a \<open>LEAST\<close>, so
         \<open>length < 2\<^sup>4\<^sup>0\<close> caps it at 40 and the product at \<open>40 \<cdot> 2\<^sup>4\<^sup>0\<close>.\<close>
      have bl40: "nat_bitlen (length Pinit0) \<le> 40"
        unfolding nat_bitlen_def by (rule Least_le) (use rpsmallP lenPx in simp)
      have pbP: "length Pinit0 * nat_bitlen (length Pinit0) < max_snat LENGTH(gmp_poly_len)"
      proof -
        have "length Pinit0 * nat_bitlen (length Pinit0) \<le> length Pinit0 * 40"
          using bl40 by (rule mult_le_mono2)
        also have "\<dots> < 1099511627776 * 40" using rpsmallP lenPx by simp
        finally show ?thesis by (simp add: max_snat_def)
      qed
      have potform: "hybrid_root_potential (delta_defl Pr) 0
                       = int (2 ^ newton_pol_ecap + 2)
                           * int (dyadic_iv_interval_mu (delta_defl Pr) (0, 1))"
        by (simp add: hybrid_root_potential_def)
      from depth_at[unfolded defl_depth_cap_def Let_def]
      have dcap1: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                            * int (dyadic_iv_interval_mu (delta_defl Pr) (0, 1))
                   \<Longrightarrow> kD * (length xs - 1) < max_snat LENGTH(gmp_poly_len)"
        and dcap2: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                             * int (dyadic_iv_interval_mu (delta_defl Pr) (0, 1))
                    \<Longrightarrow> (kD + 1) * length xs < 1099511627776"
        unfolding Pr_def Pinit0_def by blast+
      have caps: "int (dyadic_iv_interval_mu (delta_defl Pr) (0, 1)) + 3
                    < int (max_snat LENGTH(gmp_poly_len))"
                 "hybrid_root_potential (delta_defl Pr) 0 < int (max_snat LENGTH(gmp_poly_len))"
                 "hybrid_root_potential (delta_defl Pr) 0 + 258
                    < int (max_snat LENGTH(gmp_poly_len))"
      proof -
        have n1: "1 \<le> length xs" using len2 by linarith
        show "int (dyadic_iv_interval_mu (delta_defl Pr) (0, 1)) + 3 < int (max_snat LENGTH(gmp_poly_len))"
             "hybrid_root_potential (delta_defl Pr) 0 < int (max_snat LENGTH(gmp_poly_len))"
             "hybrid_root_potential (delta_defl Pr) 0 + 258 < int (max_snat LENGTH(gmp_poly_len))"
          using defl_caps_of_depth[OF dcap2 n1] by auto
      qed
      have solver: "defl_main_list_monadic split_pipeline_e0 0 (2 ^ kpos) 0 Pinit0 xs
          \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
              length (dyadic_interval_vec_triples acc) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
              defl_acc_isolates (of_int_poly (Poly xs) :: real poly) acc \<and>
              defl_acc_covers (of_int_poly (Poly xs) :: real poly) 0 acc)"
        apply (rule defl_main_list_correct[where \<delta> = "delta_defl Pr"])
        \<comment> \<open>26 premises, in order. Everything \<open>\<delta>\<close>-free comes from \<open>npre\<close>, because the deflating
           precondition strengthens that bundle; only 22--26 are re-derived at \<open>delta_defl\<close>.\<close>
        subgoal by (rule defl_delta_defl_pos_always)
        subgoal by simp
        subgoal by (rule P_eqP)
        subgoal by (rule canonP)
        subgoal using sfPr unfolding square_free_def Pr_def by simp
        subgoal using sfPr unfolding Pr_def by simp
        subgoal unfolding Pr_def by simp
        subgoal using sfxs unfolding square_free_def by simp
        subgoal using sfxs by simp
        \<comment> \<open>@{const ripoly} is an \<open>abbreviation (input)\<close>, so it is ALREADY unfolded in both
           the goal and \<open>kpos_sound\<close> --- there is no \<open>ripoly_def\<close> to add.\<close>
        subgoal using kpos_sound by simp
        subgoal using len2P by simp
        subgoal using lenbP by simp
        subgoal by (simp add: max_snat_def)
        \<comment> \<open>\<open>(cases xs)\<close>, not bare \<open>simp\<close>: \<open>0 < length xs\<close> normalises to \<open>xs \<noteq> []\<close>,
           which \<open>simp\<close> will not then derive from \<open>2 \<le> length xs\<close>.\<close>
        subgoal using len2 by (cases xs) auto
        subgoal using lenb by simp
        subgoal by (simp add: max_snat_def)
        subgoal using pbP canonP by simp
        subgoal using rpsmallP lenPx canonP by (simp add: max_snat_def)
        subgoal using rpsmallP lenPx canonP by (simp add: max_sint_def)
        subgoal using rpsmallP lenPx canonP by simp
        subgoal using len2P canonP by simp
        subgoal by (rule caps(1))
        subgoal by (rule caps(2))
        subgoal by (rule caps(3))
        subgoal premises p for kD using dcap1[of kD] p canonP lenPx potform by simp
        subgoal premises p for kD using dcap2[of kD] p canonP lenPx potform by simp
        done
      show ?thesis
        apply (refine_vcg rp_eq[THEN order_trans]
            Pinit_eq[unfolded Pinit0_def, THEN order_trans]
            mpz_pow2_monadic_spec[OF kpos_lt, THEN order_trans]
            solver[unfolded Pinit0_def, THEN order_trans])
        \<comment> \<open>the two post-copy ASSERTs at \<open>rp = xs\<close>, then the two at the seed poly\<close>
        subgoal using len2 lenb by (cases xs) auto
        subgoal using lenb by simp
        subgoal using len2P unfolding Pinit0_def[symmetric] by simp
        subgoal using lenbP unfolding Pinit0_def[symmetric] by simp
        \<comment> \<open>and the four SPEC conjuncts, which ARE \<open>solver\<close>'s postcondition\<close>
        apply (all \<open>((elim conjE, assumption); fail)?\<close>)
        done
    qed
    done
qed



section \<open>The deflating negative half\<close>

text \<open>\<^bold>\<open>What this half owes.\<close> The \<open>SPEC\<close> body of \<open>dqsolve\<close> (\<open>Power_Sub_Entry_Sound\<close>'s two
  \<open>_of_pre\<close> corollaries) mentions \<open>accP\<close> only: each positive \<open>Q\<close>-root lifts to \<open>\<plusminus>y\<close> under the even
  exponent, so the entry frees the reduced solve's negative vector unused, and \<open>\<le> SPEC (\<lambda>_. True)\<close>
  would suffice.

  \<^bold>\<open>It is stated with the full four conjuncts anyway\<close>: the \<open>nofail\<close> proof already has to discharge
  every one of @{thm [source] defl_main_list_correct}'s 26 premises at \<open>refl_list xs\<close>, and a
  \<open>\<lambda>_. True\<close> postcondition cannot be inspected for vacuity. The capstone weakens it where the entry
  does not need it.

  \<^bold>\<open>Coordinates.\<close> \<open>accQ\<close> is stated against \<open>refl_list xs\<close>, i.e. in reflected coordinates, the
  convention of the exported interface.\<close>

lemma defl_split_neg_solve_half:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_defl_pre xs"
  shows "defl_split_neg_solve_monadic xs
    \<le> SPEC (\<lambda>accQ. dyadic_interval_vec_invar accQ \<and>
        length (dyadic_interval_vec_triples accQ) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
        defl_acc_isolates (of_int_poly (Poly (refl_list xs)) :: real poly) accQ \<and>
        defl_acc_covers (of_int_poly (Poly (refl_list xs)) :: real poly) 0 accQ)"
proof -
  from pre have pre': "dsc_isolate_all_split_lin_pre xs"
    and lenb3: "length xs + 3 < max_snat LENGTH(gmp_poly_len)"
    and xs_small: "length xs < 1099511627776"
    unfolding dsc_isolate_all_split_defl_pre_def by simp_all
  from pre' have len2: "2 \<le> length xs" and lastnz: "last xs \<noteq> 0"
    and hr: "kiou_headroom xs" and sfxs: "square_free (map_poly of_int (Poly xs) :: real poly)"
    unfolding dsc_isolate_all_split_lin_pre_def by auto
  have xsne: "xs \<noteq> []" using len2 by auto
  \<comment> \<open>the reflected list's own well-formedness, verbatim from
     @{thm [source] hybrid_split_neg_solve_half}\<close>
  have sfQb: "square_free (map_poly of_int (Poly (refl_list xs)) :: real poly)"
    using square_free_pcompose_linear[OF sfxs, of "-1"]
    by (simp add: refl_list_eq_scale_poly_list_neg1 Poly_scale_poly_list_eq_pcompose)
  have Q0: "Poly (refl_list xs) \<noteq> 0" using sfQb unfolding square_free_def by simp
  have lastnzQb: "last (refl_list xs) \<noteq> 0" using last_refl_list_nz[OF xsne lastnz] .
  have hrQb: "kiou_headroom (refl_list xs)" using kiou_headroom_refl_list[of xs] hr by simp
  have len2Qb: "2 \<le> length (refl_list xs)" using len2 by simp
  have capYQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (split_cap_lin (refl_list xs))"
    using pre' unfolding dsc_isolate_all_split_lin_pre_def by (auto simp: Let_def)
  have capDQb: "kiou_bound_k_monadic (refl_list xs)
                  \<le> SPEC (defl_depth_cap (refl_list xs))"
    using pre unfolding dsc_isolate_all_split_defl_pre_def by (auto simp: Let_def)
  \<comment> \<open>\<^bold>\<open>MERGED\<close>, exactly as on the classic side and the positive half: only ONE \<open>\<le> SPEC\<close> fact fires
     per producer call, so a second one would never reach the continuation.\<close>
  have mergedQb: "kiou_bound_k_monadic (refl_list xs) \<le> SPEC (\<lambda>k.
      ((\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ k) \<and>
       k * length (refl_list xs) < max_snat LENGTH(gmp_poly_len) \<and>
       k < max_snat LENGTH(gmp_poly_len) \<and> split_cap_lin (refl_list xs) k)
      \<and> defl_depth_cap (refl_list xs) k)"
    by (rule kiou_le_SPEC_conj[OF kiou_bound_k_monadic_spec_capped_lin[OF len2Qb lastnzQb hrQb capYQb]
          capDQb])
  have lenb: "length xs + 1 < max_snat LENGTH(gmp_poly_len)"
    using kiou_headroom_lenb[OF hr] by linarith
  have lenbQb: "length (refl_list xs) + 1 < max_snat LENGTH(gmp_poly_len)" using lenb by simp
  have copy_correct: "poly_copy_monadic xs \<le> RETURN xs" by (rule poly_copy_correct[OF lenb])
  have poly_reflect_correct: "poly_reflect_in_place_monadic xs \<le> RETURN (refl_list xs)"
    using poly_reflect_in_place_correct[OF lenb] by (simp add: refl_list_def)
  show ?thesis
    unfolding defl_split_neg_solve_monadic_def
      PR_CONST_def COPY_def mpz_from_int_def mpzb_discard_monadic_def
    apply (refine_vcg
        copy_correct[THEN order_trans]
        poly_reflect_correct[THEN order_trans]
        mergedQb[THEN order_trans])
    subgoal using len2Qb lenb lenbQb by (cases xs) auto
    subgoal using len2Qb lenb lenbQb by auto
    subgoal using len2Qb lenb lenbQb by auto
    subgoal premises p using p by simp
    subgoal premises p using p by simp
    subgoal premises kp for kneg
    proof -
      from kp have kneg_sound:
          "\<forall>x::real. 0 < x \<longrightarrow> ripoly (Poly (refl_list xs)) x = 0 \<longrightarrow> x < 2 ^ kneg"
        and kneg_cap: "kneg * length (refl_list xs) < max_snat LENGTH(gmp_poly_len)"
        and kneg_lt: "kneg < max_snat LENGTH(gmp_poly_len)"
        and cap_at: "split_cap_lin (refl_list xs) kneg"
        and depth_at: "defl_depth_cap (refl_list xs) kneg" by blast+
      define Qinit0 where "Qinit0 = scale_poly_list (2 ^ kneg) (refl_list xs)"
      define Qr where "Qr = (map_poly of_int (Poly Qinit0) :: real poly)"
      have Qinit_eq: "split_init_pow2_l0_monadic kneg (refl_list xs) \<le> RETURN Qinit0"
        using split_init_pow2_l0_monadic_correct[OF lenbQb kneg_cap]
        by (simp add: Qinit0_def split_init_pow2_l0_eq_scale_poly_list)
      have lenb3Q: "length (refl_list xs) + 3 < max_snat LENGTH(gmp_poly_len)" using lenb3 by simp
      note sd = defl_seed_facts[OF len2Qb lastnzQb sfQb lenb3Q, of kneg, folded Qinit0_def]
      have len2Q: "Suc 0 < length Qinit0" by (rule sd(1))
      have sfQ: "square_free (map_poly of_int (Poly Qinit0) :: real poly)" by (rule sd(2))
      have canonQ: "coeffs (Poly Qinit0) = Qinit0" by (rule sd(3))
      have lenbQ: "length Qinit0 + 2 < max_snat LENGTH(gmp_poly_len)" by (rule sd(4))
      have Q_eqQ: "Qinit0 = carried_init_same_den 0 (2 ^ 0) (2 ^ kneg) (refl_list xs)" by (rule sd(5))
      have rpsmallQ: "length (refl_list xs) < 1099511627776" using xs_small by simp
      have lenQx: "length Qinit0 = length (refl_list xs)" by (simp add: Qinit0_def)
      have bl40: "nat_bitlen (length Qinit0) \<le> 40"
        unfolding nat_bitlen_def by (rule Least_le) (use rpsmallQ lenQx in simp)
      have pbQ: "length Qinit0 * nat_bitlen (length Qinit0) < max_snat LENGTH(gmp_poly_len)"
      proof -
        have "length Qinit0 * nat_bitlen (length Qinit0) \<le> length Qinit0 * 40"
          using bl40 by (rule mult_le_mono2)
        also have "\<dots> < 1099511627776 * 40" using rpsmallQ lenQx by simp
        finally show ?thesis by (simp add: max_snat_def)
      qed
      have potform: "hybrid_root_potential (delta_defl Qr) 0
                       = int (2 ^ newton_pol_ecap + 2)
                           * int (dyadic_iv_interval_mu (delta_defl Qr) (0, 1))"
        by (simp add: hybrid_root_potential_def)
      from depth_at[unfolded defl_depth_cap_def Let_def]
      have dcap1: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                            * int (dyadic_iv_interval_mu (delta_defl Qr) (0, 1))
                   \<Longrightarrow> kD * (length (refl_list xs) - 1) < max_snat LENGTH(gmp_poly_len)"
        and dcap2: "\<And>kD. int kD \<le> int (2 ^ newton_pol_ecap + 2)
                             * int (dyadic_iv_interval_mu (delta_defl Qr) (0, 1))
                    \<Longrightarrow> (kD + 1) * length (refl_list xs) < 1099511627776"
        unfolding Qr_def Qinit0_def by blast+
      have caps: "int (dyadic_iv_interval_mu (delta_defl Qr) (0, 1)) + 3
                    < int (max_snat LENGTH(gmp_poly_len))"
                 "hybrid_root_potential (delta_defl Qr) 0 < int (max_snat LENGTH(gmp_poly_len))"
                 "hybrid_root_potential (delta_defl Qr) 0 + 258
                    < int (max_snat LENGTH(gmp_poly_len))"
      proof -
        have n1: "1 \<le> length (refl_list xs)" using len2Qb by linarith
        show "int (dyadic_iv_interval_mu (delta_defl Qr) (0, 1)) + 3 < int (max_snat LENGTH(gmp_poly_len))"
             "hybrid_root_potential (delta_defl Qr) 0 < int (max_snat LENGTH(gmp_poly_len))"
             "hybrid_root_potential (delta_defl Qr) 0 + 258 < int (max_snat LENGTH(gmp_poly_len))"
          using defl_caps_of_depth[OF dcap2 n1] by auto
      qed
      have solver: "defl_main_list_monadic split_pipeline_e0 0 (2 ^ kneg) 0 Qinit0 (refl_list xs)
          \<le> SPEC (\<lambda>acc. dyadic_interval_vec_invar acc \<and>
              length (dyadic_interval_vec_triples acc) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
              defl_acc_isolates (of_int_poly (Poly (refl_list xs)) :: real poly) acc \<and>
              defl_acc_covers (of_int_poly (Poly (refl_list xs)) :: real poly) 0 acc)"
        apply (rule defl_main_list_correct[where \<delta> = "delta_defl Qr"])
        \<comment> \<open>26 premises, in the positive half's own order; only 22--26 are \<open>\<delta>\<close>-dependent.\<close>
        subgoal by (rule defl_delta_defl_pos_always)
        subgoal by simp
        subgoal by (rule Q_eqQ)
        subgoal by (rule canonQ)
        subgoal using sfQ unfolding square_free_def Qr_def by simp
        subgoal using sfQ unfolding Qr_def by simp
        subgoal unfolding Qr_def by simp
        subgoal using sfQb unfolding square_free_def by simp
        subgoal using sfQb by simp
        subgoal using kneg_sound by simp
        subgoal using len2Q by simp
        subgoal using lenbQ by simp
        subgoal by (simp add: max_snat_def)
        subgoal using len2Qb by (cases xs) auto
        subgoal using lenbQb by simp
        subgoal by (simp add: max_snat_def)
        subgoal using pbQ canonQ by simp
        subgoal using rpsmallQ lenQx canonQ by (simp add: max_snat_def)
        subgoal using rpsmallQ lenQx canonQ by (simp add: max_sint_def)
        subgoal using rpsmallQ lenQx canonQ by simp
        subgoal using len2Q canonQ by simp
        subgoal by (rule caps(1))
        subgoal by (rule caps(2))
        subgoal by (rule caps(3))
        subgoal premises p for kD using dcap1[of kD] p canonQ lenQx potform by simp
        subgoal premises p for kD using dcap2[of kD] p canonQ lenQx potform by simp
        done
      show ?thesis
        apply (refine_vcg Qinit_eq[unfolded Qinit0_def, THEN order_trans]
            mpz_pow2_monadic_spec[OF kneg_lt, THEN order_trans]
            solver[unfolded Qinit0_def, THEN order_trans])
        subgoal using len2Q unfolding Qinit0_def[symmetric] by simp
        subgoal using lenbQ unfolding Qinit0_def[symmetric] by simp
        subgoal using len2Qb by (cases xs) auto
        apply (all \<open>((elim conjE, assumption); fail)?\<close>)
        done
    qed
    done
qed



section \<open>The deflating capstone\<close>

text \<open>\<^bold>\<open>What this theorem is for.\<close> It supplies \<open>dqsolve\<close>, the named hypothesis of
  \<open>Power_Sub_Entry_Sound\<close>'s two \<open>_of_pre\<close> corollaries. Its four live conjuncts are \<open>qsolve\<close>'s four
  symbol for symbol: @{const defl_acc_isolates} and @{const defl_acc_covers}\<open> \<dots> 0\<close> have the same
  bodies as \<open>pow_sub_reduced_isolates\<close> / \<open>pow_sub_reduced_covers\<close>, so the bridge at the consumer is
  definitional unfolding. They are restated rather than imported because the power-substitution
  theories come later in the build.

  \<^bold>\<open>Structurally @{thm [source] hybrid_isolate_all_split_main_correct_pos_pinned}\<close>, with two
  simplifications: there is no \<open>real_to_rat_pair\<close> layer (the deflating loop never leaves the dyadic
  numerators), and the negative half, stated in reflected coordinates, is not consumed by the entry
  (each positive \<open>Q\<close>-root lifts to \<open>\<plusminus>y\<close> under the even exponent, so the entry frees \<open>accN\<close> unused).

  \<^bold>\<open>The precondition is \<open>dsc_isolate_all_split_defl_pre\<close>\<close>, which neither implies nor is implied by
  the hybrid bundle: it lacks @{const split_cap}'s exponential clause, and the deflating \<open>\<delta>\<close> is
  smaller, so its \<open>\<mu>\<close> is larger and the depth caps are stated over the larger \<open>kD\<close> range. The
  corollaries' reduced-polynomial hypothesis \<open>qpre\<close> is stated with this bundle too. Its
  satisfiability witness is \<open>dsc_isolate_all_split_defl_pre_satisfiable\<close>.\<close>

theorem defl_isolate_all_split_main_correct:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_defl_pre xs"
  shows "defl_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accN, xs0).
      dyadic_interval_vec_invar accP \<and>
      length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      defl_acc_isolates (of_int_poly (Poly xs) :: real poly) accP \<and>
      defl_acc_covers (of_int_poly (Poly xs) :: real poly) 0 accP \<and>
      dyadic_interval_vec_invar accN \<and>
      length (dyadic_interval_vec_triples accN) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      defl_acc_isolates (of_int_poly (Poly (refl_list xs)) :: real poly) accN \<and>
      defl_acc_covers (of_int_poly (Poly (refl_list xs)) :: real poly) 0 accN \<and>
      xs0 = (xs \<noteq> [] \<and> xs ! 0 = 0))"
proof -
  have len2: "2 \<le> length xs"
    using pre unfolding dsc_isolate_all_split_defl_pre_def dsc_isolate_all_split_lin_pre_def by auto
  show ?thesis
    unfolding defl_isolate_all_split_main_def PR_CONST_def
    apply (refine_vcg
        defl_split_pos_solve_half[OF pre, THEN order_trans]
        defl_split_neg_solve_half[OF pre, THEN order_trans]
        dsc_split_zero_check_correct_len2[OF len2, THEN order_trans])
    using len2 by auto
qed

text \<open>\<^bold>\<open>\<open>dqsolve\<close> ITSELF\<close> --- the four conjuncts and nothing else, in the shape
  \<open>Power_Sub_Entry_Sound.thy\<close>'s two corollaries take. Step 7 re-points \<open>qpre\<close> at
  @{const dsc_isolate_all_split_defl_pre} and discharges \<open>dqsolve\<close> with THIS.\<close>

corollary defl_isolate_all_split_main_correct_qsolve:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_defl_pre xs"
  shows "defl_isolate_all_split_main xs \<le> SPEC (\<lambda>(accP, accN, xs0).
      dyadic_interval_vec_invar accP \<and>
      length (dyadic_interval_vec_triples accP) + 1 < max_snat LENGTH(gmp_poly_len) \<and>
      defl_acc_isolates (real_of_int_poly (Poly xs)) accP \<and>
      defl_acc_covers (real_of_int_poly (Poly xs)) 0 accP)"
  by (rule weaken_SPEC[OF defl_isolate_all_split_main_correct[OF pre]]) auto

text \<open>Explicit termination corollary, the classic's own
  (@{thm [source] hybrid_isolate_all_split_main_terminates}): every loop below this point is a
  well-founded \<open>WHILET\<close>, so \<open>\<le> SPEC\<close> genuinely excludes non-termination.\<close>

corollary defl_isolate_all_split_main_terminates:
  fixes xs :: "int list"
  assumes pre: "dsc_isolate_all_split_defl_pre xs"
  shows "nofail (defl_isolate_all_split_main xs)"
  using defl_isolate_all_split_main_correct[OF pre] by (rule SPEC_nofail)


end
