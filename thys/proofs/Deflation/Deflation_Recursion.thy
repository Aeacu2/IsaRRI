theory Deflation_Recursion
  imports Deflation_Transport
begin

section \<open>The deflating recursion, and the invariant that makes the transport usable\<close>

text \<open>A new recursion beside @{const newdsc_pol}; @{const dsc_int} and @{const newdsc_pol} are unchanged.
  Its claim is isolation plus a separate completeness theorem, not the multiset equality, which
  deflation cannot satisfy because it returns different intervals.

  \<^bold>\<open>What deflation is.\<close> @{const newdsc_pol} detects a root at a box midpoint, emits the degenerate pair
  \<open>[(m,m)]\<close>, and passes the unchanged \<open>P\<close> to both halves. Deflation instead divides the linear factor out
  and permanently reduces the working degree, as msolve does (\<open>is_zero_root\<close> in its \<open>usolve.c\<close>). Since
  counting and child construction are both \<open>O(n\<^sup>2)\<close> in the working degree, that cheapens every later
  operation on the subtree.

  \<^bold>\<open>What makes it possible.\<close> \<open>Bernstein_changes_small_interval_le_1_of_dvd\<close> gives one \<open>\<delta>\<close>
  serving every divisor, and every polynomial this recursion can reach is a divisor of the input
  (@{text defl_reachable_dvd} below).\<close>

subsection \<open>The deflation step\<close>

definition defl_step :: "real poly \<Rightarrow> real \<Rightarrow> real poly" where
  "defl_step P m = (if poly P m = 0 then P div [:-m, 1:] else P)"

text \<open>\<^bold>\<open>Rewrite these by hand, never with a bare \<open>simp\<close> on the product.\<close> \<open>simp\<close>
  normalises \<open>[:-m, 1:] * X\<close> into \<open>pCons\<close>/\<open>smult\<close> form and then cannot close the goal
  it just created — three of this file's goals failed that way before the products were
  rewritten explicitly.\<close>

lemma defl_step_factor:
  assumes root: "poly P m = 0"
  shows "P = [:-m, 1:] * defl_step P m"
proof -
  have d: "[:-m, 1:] dvd P" using root by (simp add: poly_eq_0_iff_dvd)
  have "[:-m, 1:] * defl_step P m = [:-m, 1:] * (P div [:-m, 1:])"
    by (simp add: defl_step_def root)
  also have "\<dots> = P" by (rule dvd_mult_div_cancel[OF d])
  finally show ?thesis by (rule sym)
qed

lemma defl_step_dvd: "defl_step P m dvd P"
proof (cases "poly P m = 0")
  case True
  have "defl_step P m dvd [:-m, 1:] * defl_step P m" by (rule dvd_triv_right)
  thus ?thesis using defl_step_factor[OF True] by simp
next
  case False
  thus ?thesis by (simp add: defl_step_def)
qed

lemma defl_step_nz:
  assumes P0: "P \<noteq> 0"
  shows "defl_step P m \<noteq> 0"
proof (cases "poly P m = 0")
  case True
  show ?thesis
  proof
    assume "defl_step P m = 0"
    hence "P = 0" using defl_step_factor[OF True] by simp
    thus False using P0 by simp
  qed
next
  case False
  thus ?thesis using P0 by (simp add: defl_step_def)
qed

text \<open>\<^bold>\<open>The degree strictly drops when the step fires\<close> — this is the whole performance
  claim, and it is what makes the working degree shrink monotonically down any path.\<close>

lemma defl_step_degree_less:
  assumes P0: "P \<noteq> 0" and root: "poly P m = 0"
  shows "degree (defl_step P m) < degree P"
proof -
  have fac: "P = [:-m, 1:] * defl_step P m" using defl_step_factor[OF root] .
  have D0: "defl_step P m \<noteq> 0" using defl_step_nz[OF P0] .
  have l0: "([:-m, 1:] :: real poly) \<noteq> 0" by simp
  have "degree P = degree ([:-m, 1:] * defl_step P m)" using fac by simp
  also have "\<dots> = degree ([:-m, 1:] :: real poly) + degree (defl_step P m)"
    using l0 D0 by (rule degree_mult_eq)
  also have "\<dots> = 1 + degree (defl_step P m)" by simp
  finally show ?thesis by simp
qed

lemma defl_step_degree_le: "P \<noteq> 0 \<Longrightarrow> degree (defl_step P m) \<le> degree P"
  using defl_step_dvd dvd_imp_degree_le by blast

text \<open>\<^bold>\<open>Roots away from \<open>m\<close> are preserved exactly\<close> — the completeness half. No
  squarefreeness needed: it is pure factorisation.\<close>

lemma defl_step_poly_eq_0_iff:
  assumes "x \<noteq> m"
  shows "poly (defl_step P m) x = 0 \<longleftrightarrow> poly P x = 0"
proof (cases "poly P m = 0")
  case True
  have "poly P x = poly ([:-m, 1:] * defl_step P m) x"
    using defl_step_factor[OF True] by simp
  also have "\<dots> = poly [:-m, 1:] x * poly (defl_step P m) x" by (rule poly_mult)
  also have "\<dots> = (x - m) * poly (defl_step P m) x" by simp
  finally have "poly P x = (x - m) * poly (defl_step P m) x" .
  thus ?thesis using assms by simp
next
  case False
  thus ?thesis by (simp add: defl_step_def)
qed

text \<open>\<^bold>\<open>And \<open>m\<close> itself is GONE\<close> — the soundness half, and the one place squarefreeness of
  the input is load-bearing. Without it a multiple root would survive one deflation, be
  re-detected in a child, and be emitted twice, breaking the emitted multiset.\<close>

lemma defl_step_no_repeat:
  assumes P0: "P \<noteq> 0" and sf: "square_free P" and root: "poly P m = 0"
  shows "poly (defl_step P m) m \<noteq> 0"
proof
  assume "poly (defl_step P m) m = 0"
  hence "[:-m, 1:] dvd defl_step P m" by (simp add: poly_eq_0_iff_dvd)
  then obtain K where K: "defl_step P m = [:-m, 1:] * K" by (rule dvdE)
  \<comment> \<open>@{thm [source] square_free_def} guards on \<open>0 < degree q\<close>, NOT on \<open>\<not> is_unit q\<close>
      — checked, not assumed (the \<open>is_unit\<close> spelling cost a 10-minute runaway).\<close>
  have "P = [:-m, 1:] * defl_step P m" using defl_step_factor[OF root] .
  also have "\<dots> = [:-m, 1:] * ([:-m, 1:] * K)" by (simp only: K)
  also have "\<dots> = ([:-m, 1:] * [:-m, 1:]) * K" by (rule mult.assoc[symmetric])
  finally have "P = ([:-m, 1:] * [:-m, 1:]) * K" .
  hence dvd2: "[:-m, 1:] * [:-m, 1:] dvd P" by (rule dvdI)
  have "0 < degree ([:-m, 1:] :: real poly)" by simp
  thus False using sf dvd2 unfolding square_free_def by blast
qed

subsection \<open>Preservation of the transport's hypotheses\<close>

lemma defl_step_square_free:
  assumes "square_free P"
  shows "square_free (defl_step P m)"
  using square_free_factor[OF defl_step_dvd assms] .

text \<open>\<^bold>\<open>The invariant, in the form the termination argument consumes.\<close> Every polynomial the recursion
  can reach is a divisor of the input, so the single \<open>\<delta>\<close> covers all of them. Stated over an arbitrary
  chain of steps rather than over the recursion, so it does not depend on how the recursion is
  phrased.\<close>

fun defl_chain :: "real poly \<Rightarrow> real list \<Rightarrow> real poly" where
  "defl_chain P [] = P"
| "defl_chain P (m # ms) = defl_chain (defl_step P m) ms"

lemma defl_chain_dvd: "defl_chain P ms dvd P"
proof (induction ms arbitrary: P)
  case Nil thus ?case by simp
next
  case (Cons m ms)
  \<comment> \<open>Chain the two \<open>dvd\<close>s by an explicit @{thm [source] dvd_trans} instance. Left to \<open>fastforce\<close> with
      \<open>defl_step_dvd\<close> and \<open>dvd_trans\<close> in the fact list, this is a transitivity search over schematic \<open>P\<close>
      and \<open>m\<close> that does not terminate in reasonable time.\<close>
  have "defl_chain (defl_step P m) ms dvd P"
    by (rule dvd_trans[OF Cons.IH defl_step_dvd])
  thus ?case by simp
qed

lemma defl_chain_nz: "P \<noteq> 0 \<Longrightarrow> defl_chain P ms \<noteq> 0"
  using defl_chain_dvd[of P ms] by auto

lemma defl_chain_square_free:
  "square_free P \<Longrightarrow> square_free (defl_chain P ms)"
  using square_free_factor[OF defl_chain_dvd] .

subsection \<open>One \<open>\<delta>\<close> for the whole deflating run\<close>

text \<open>This is the theorem a deflating @{text domI_general} will instantiate. It says the
  smallness witness never has to be recomputed as the recursion sheds degree — which is exactly
  the property the non-deflating @{thm [source] newdsc_pol_domI_general} gets for free by keeping
  \<open>P\<close> fixed, and which deflation would otherwise lose.\<close>

theorem defl_chain_smallness_uniform:
  fixes P :: "real poly"
  assumes P0: "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0: "p \<noteq> 0"
      and sf: "square_free P"
      and ab: "a < b"
      and small: "b - a \<le> delta_defl P"
  shows "Bernstein_changes p a b (defl_chain P ms) \<le> 1"
  using Bernstein_changes_small_interval_le_1_of_dvd[OF P0 deg p0 sf defl_chain_dvd ab small] .

subsection \<open>The transport is not vacuous, and it fires on a GENUINE deflation\<close>

text \<open>@{thm [source] Bernstein_changes_small_interval_le_1_delta_defl} shows that the hypothesis set is
  that of @{thm [source] newdsc_pol_terminates_squarefree}, so the hypotheses are satisfiable. It does
  not show that the interesting case, \<open>D \<noteq> P\<close>, is reached. This lemma does: whenever a root is hit, the
  step produces a divisor of strictly smaller degree, and the transport covers it with the same \<open>\<delta>\<close>.
  Stating the conclusion at a concrete instance is the check against a vacuous hypothesis set.\<close>

theorem defl_transport_fires_on_real_deflation:
  fixes P :: "real poly"
  assumes P0: "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0: "p \<noteq> 0"
      and sf: "square_free P"
      and root: "poly P m = 0"
      and ab: "a < b"
      and small: "b - a \<le> delta_defl P"
  shows "degree (defl_step P m) < degree P
         \<and> Bernstein_changes p a b (defl_step P m) \<le> 1
         \<and> poly (defl_step P m) m \<noteq> 0"
  using defl_step_degree_less[OF P0 root]
        Bernstein_changes_small_interval_le_1_of_dvd[OF P0 deg p0 sf defl_step_dvd ab small]
        defl_step_no_repeat[OF P0 sf root]
  by blast

section \<open>The deflating recursion and its termination\<close>

text \<open>\<^bold>\<open>Route (b): @{const newdsc_pol} is left ALONE.\<close> This is a NEW recursion beside it,
  identical everywhere except the bisection branch, where the children receive
  @{term "defl_step P m"} instead of \<open>P\<close>. Everything else — the guards, the two accept
  branches, the \<open>e\<close>/\<open>dk\<close>/\<open>s\<close> tags — is copied unchanged, so a drift between the two is a
  drift in one visible line.\<close>

function (domintros) newdsc_pol_defl ::
  "newton_pol_real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real poly
     \<Rightarrow> (real \<times> real) list"
where
  "newdsc_pol_defl pol p a b e dk s P =
     (let v = Bernstein_changes p a b P in
      if v = 0 then []
      else if v = 1 then [(a, b)]
      else
        (case try_newton_g (snd (pol p a b e dk (s, v))) p a b (N_of e) P v of
           Some I \<Rightarrow> newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
         | None \<Rightarrow>
             (case try_blocks_g (fst (pol p a b e dk (s, v))) p a b (N_of e) P v of
                Some I \<Rightarrow> newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
              | None \<Rightarrow>
                  (let m  = (a + b) / 2;
                       e' = max 1 (e - 1);
                       s' = split_run_len_real p P a b s;
                       mid_root = (if poly P m = 0 then [(m, m)] else [])
                   in mid_root @ newdsc_pol_defl pol p a m e' (dk + 1) s' (defl_step P m)
                               @ newdsc_pol_defl pol p m b e' (dk + 1) s' (defl_step P m)))))"
  by pat_completeness auto

subsection \<open>Domain totality, with the divisor threaded\<close>

text \<open>The analogue of @{thm [source] newdsc_pol_domI_general}. The measure is the same, \<open>mu \<delta> a b\<close>, a
  function of the box only, so the box arithmetic carries over. Two things change:

    \<^item> the induction statement quantifies over the node polynomial \<open>Q\<close>, restricted to divisors of the
      input \<open>P0\<close>, because \<open>Q\<close> is a recursion variable;
    \<^item> the smallness witness must hold for every divisor at one \<open>\<delta>\<close>, which is
      @{thm [source] Bernstein_changes_small_interval_le_1_of_dvd}.

  The bisection branch is the only place the divisor premise has to be re-established, by
  @{thm [source] defl_step_dvd} and transitivity.\<close>

lemma newdsc_pol_defl_domI_general:
  fixes \<delta> :: real and p :: nat and P0 :: "real poly" and pol :: newton_pol_real
  assumes \<delta>_pos: "\<delta> > 0"
    and small: "\<And>Q a b. Q dvd P0 \<Longrightarrow> a < b \<Longrightarrow> b - a \<le> \<delta>
                  \<Longrightarrow> Bernstein_changes p a b Q \<le> 1"
  shows "\<And>Q a b e dk s. Q dvd P0 \<Longrightarrow> a < b
           \<Longrightarrow> newdsc_pol_defl_dom (pol, p, a, b, e, dk, s, Q)"
proof -
  define \<mu> where "\<mu> = (\<lambda>a b. mu \<delta> a b)"
  let ?Prop =
    "\<lambda>n::nat. \<forall>Q a b e dk s. Q dvd P0 \<longrightarrow> \<mu> a b < n \<longrightarrow> a < b
                 \<longrightarrow> newdsc_pol_defl_dom (pol, p, a, b, e, dk, s, Q)"

  have step: "\<And>n. (\<And>m. m < n \<Longrightarrow> ?Prop m) \<Longrightarrow> ?Prop n"
  proof -
    fix n
    assume IH: "\<And>m. m < n \<Longrightarrow> ?Prop m"
    show "?Prop n"
    proof (intro allI impI)
      fix Q :: "real poly" and a b :: real and e dk s :: nat
      assume Qdvd: "Q dvd P0"
        and mu_lt_n: "\<mu> a b < n"
        and ab: "a < b"
      show "newdsc_pol_defl_dom (pol, p, a, b, e, dk, s, Q)"
      proof -
        let ?v = "Bernstein_changes p a b Q"
        let ?gb = "fst (pol p a b e dk (s, ?v))"
        let ?gn = "snd (pol p a b e dk (s, ?v))"
        show ?thesis
        proof (cases "?v = 0 \<or> ?v = 1")
          case True
          then show ?thesis
            by (auto intro: newdsc_pol_defl.domintros)
        next
          case False
          have v_ge2: "2 \<le> ?v"
            using False Bernstein_changes_def by fastforce

          have \<delta>_lt_width: "\<delta> < b - a"
          proof (rule ccontr)
            assume "\<not> \<delta> < b - a"
            then have "b - a \<le> \<delta>" by linarith
            then have "Bernstein_changes p a b Q \<le> 1"
              using ab small Qdvd by presburger
            with v_ge2 show False by linarith
          qed

          have IH_at_mu: "?Prop (\<mu> a b)"
            using IH mu_lt_n by simp

          have Nof_pos: "N_of e > 0" using N_of_ge_2[of e] by simp

          have block_case:
            "\<forall>I. try_blocks_g ?gb p a b (N_of e) Q ?v = Some I
                 \<longrightarrow> newdsc_pol_defl_dom (pol, p, fst I, snd I, e + 1, dk + (2 ^ e + 2), s, Q)"
          proof (intro allI impI)
            fix I
            assume TBg: "try_blocks_g ?gb p a b (N_of e) Q ?v = Some I"
            have TB: "try_blocks p a b (N_of e) Q ?v = Some I"
              using TBg by (simp add: try_blocks_g_def split: if_split_asm)
            have width_I: "snd I - fst I = (b - a) / of_nat (N_of e)"
              using try_blocks_SomeD(3)[OF TB Nof_pos ab] by simp
            have mu_less: "\<mu> (fst I) (snd I) < \<mu> a b"
              using \<delta>_pos ab \<delta>_lt_width N_of_ge_2[of e] width_I
              by (simp add: \<mu>_def mu_subinterval_factor_strict)
            have fst_lt_snd: "fst I < snd I"
              by (metis Nof_pos ab diff_gt_0_iff_gt divide_pos_pos of_nat_0_less_iff width_I)
            show "newdsc_pol_defl_dom (pol, p, fst I, snd I, e + 1, dk + (2 ^ e + 2), s, Q)"
              using IH_at_mu mu_less fst_lt_snd Qdvd by blast
          qed

          have newton_case:
            "\<forall>I. try_newton_g ?gn p a b (N_of e) Q ?v = Some I \<longrightarrow>
                 newdsc_pol_defl_dom (pol, p, fst I, snd I, e + 1, dk + (2 ^ e + 2), s, Q)"
          proof (intro allI impI)
            fix I
            assume TNg: "try_newton_g ?gn p a b (N_of e) Q ?v = Some I"
            have TN: "try_newton p a b (N_of e) Q ?v = Some I"
              using TNg by (simp add: try_newton_g_def split: if_split_asm)
            have width_I: "snd I - fst I = (b - a) / of_nat (N_of e)"
              using try_newton_SomeD(3)[OF TN ab Nof_pos] by (simp add: Let_def)
            have mu_less: "\<mu> (fst I) (snd I) < \<mu> a b"
              using \<delta>_pos ab \<delta>_lt_width N_of_ge_2[of e] width_I
              by (simp add: \<mu>_def mu_subinterval_factor_strict)
            have fst_lt_snd: "fst I < snd I"
              by (metis Nof_pos ab diff_gt_0_iff_gt divide_pos_pos of_nat_0_less_iff width_I)
            show "newdsc_pol_defl_dom (pol, p, fst I, snd I, e + 1, dk + (2 ^ e + 2), s, Q)"
              using IH_at_mu mu_less fst_lt_snd Qdvd by blast
          qed

          define m where "m = (a + b) / 2"
          have am: "a < m" and mb: "m < b" using ab by (simp_all add: m_def)
          have mu_left_strict: "\<mu> a m < \<mu> a b"
            by (simp add: \<mu>_def \<delta>_pos \<delta>_lt_width ab m_def mu_halve_strict(1))
          have mu_right_strict: "\<mu> m b < \<mu> a b"
            by (simp add: \<mu>_def \<delta>_pos \<delta>_lt_width ab m_def mu_halve_strict(2))

          \<comment> \<open>\<^bold>\<open>The ONLY new step in the whole clone\<close>: the bisection children run on a
              DEFLATED polynomial, so the divisor premise has to be re-established for them.
              @{thm [source] defl_step_dvd} and transitivity are the whole of it.\<close>
          have Qdvd': "defl_step Q m dvd P0"
            by (rule dvd_trans[OF defl_step_dvd Qdvd])

          have IH_left:
            "\<And>e' dk' s'. newdsc_pol_defl_dom (pol, p, a, m, e', dk', s', defl_step Q m)"
            using IH_at_mu mu_left_strict am Qdvd' by blast
          have IH_right:
            "\<And>e' dk' s'. newdsc_pol_defl_dom (pol, p, m, b, e', dk', s', defl_step Q m)"
            using IH_at_mu mu_right_strict mb Qdvd' by blast

          \<comment> \<open>As in the original: the children's \<open>s'\<close> is an \<open>if\<close>, so \<open>domintros\<close> emits more
              subgoals than a fixed \<open>subgoal\<close> chain can track, and \<open>s\<close> is inert for the
              domain (the measure ignores it). A uniform closer is correct and robust.\<close>
          show ?thesis
            by (rule newdsc_pol_defl.domintros)
               (use IH_left IH_right newton_case block_case in \<open>auto simp: m_def\<close>)
        qed
      qed
    qed
  qed

  have all_Prop: "\<And>n. ?Prop n"
    by (rule less_induct, rule step)

  show "\<And>Q a b e dk s. Q dvd P0 \<Longrightarrow> a < b
          \<Longrightarrow> newdsc_pol_defl_dom (pol, p, a, b, e, dk, s, Q)"
    using all_Prop by blast
qed

subsection \<open>Termination\<close>

text \<open>The analogue of @{thm [source] newdsc_pol_terminates_squarefree}. Where that proof instantiates a
  smallness witness for one fixed \<open>P\<close>, this one needs a witness good for every divisor at once:
  @{thm [source] Bernstein_changes_small_interval_le_1_of_dvd} at \<open>\<delta> = delta_defl P\<close>.\<close>

theorem newdsc_pol_defl_terminates_squarefree:
  fixes P :: "real poly"
  assumes P0:  "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0:  "p \<noteq> 0"
      and sf:  "square_free P"
  shows "\<And>Q a b e dk s. Q dvd P \<Longrightarrow> a < b
           \<Longrightarrow> newdsc_pol_defl_dom (pol, p, a, b, e, dk, s, Q)"
proof -
  have \<delta>_pos: "delta_defl P > 0" using delta_defl_pos[OF P0] .
  have small: "\<And>Q a b. Q dvd P \<Longrightarrow> a < b \<Longrightarrow> b - a \<le> delta_defl P
                 \<Longrightarrow> Bernstein_changes p a b Q \<le> 1"
    using Bernstein_changes_small_interval_le_1_of_dvd[OF P0 deg p0 sf] by blast
  show "\<And>Q a b e dk s. Q dvd P \<Longrightarrow> a < b
          \<Longrightarrow> newdsc_pol_defl_dom (pol, p, a, b, e, dk, s, Q)"
    using newdsc_pol_defl_domI_general[OF \<delta>_pos small] by blast
qed

subsection \<open>The root-agreement invariant\<close>

text \<open>\<^bold>\<open>Divisibility alone does not give soundness.\<close> \<open>Q dvd P0\<close> gives \<open>roots Q \<subseteq> roots P0\<close>, but the
  recursion emits \<open>(a,b)\<close> when \<open>Bernstein_changes p a b Q = 1\<close>, one root of the node's polynomial, and
  \<open>P0\<close> may have more roots in that box: the ones deflated away on the path down. So \<open>dsc_pair_ok P0\<close>
  could be false while \<open>dsc_pair_ok Q\<close> is true.

  \<^bold>\<open>What makes it work is where deflation happens.\<close> A root is only shed at a box midpoint \<open>m\<close>, and
  the children's boxes are \<open>(a,m)\<close> and \<open>(m,b)\<close>, so a shed root is an endpoint, never interior to either
  child. Hence the invariant: inside the current open box, the node's polynomial has exactly the roots
  of the input.\<close>

definition defl_invar :: "real poly \<Rightarrow> real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "defl_invar P0 Q a b \<longleftrightarrow>
     Q dvd P0 \<and> (\<forall>x. a < x \<longrightarrow> x < b \<longrightarrow> (poly Q x = 0) = (poly P0 x = 0))"

lemma defl_invar_init: "defl_invar P0 P0 a b"
  unfolding defl_invar_def by simp

lemma defl_invar_dvd: "defl_invar P0 Q a b \<Longrightarrow> Q dvd P0"
  unfolding defl_invar_def by simp

text \<open>The two accept branches keep \<open>Q\<close> and shrink the box, so the \<open>\<forall>x\<close> clause only loses
  points.\<close>

lemma defl_invar_shrink:
  assumes "defl_invar P0 Q a b" and "a \<le> a'" and "b' \<le> b"
  shows "defl_invar P0 Q a' b'"
  using assms unfolding defl_invar_def by auto

text \<open>The bisection branch, the only place the polynomial changes. Both halves work because every
  interior point of a half differs from \<open>m\<close>, which is @{thm [source] defl_step_poly_eq_0_iff}. Stated for
  an arbitrary \<open>m\<close> in the box rather than the midpoint.\<close>

lemma defl_invar_left:
  assumes inv: "defl_invar P0 Q a b" and mb: "m \<le> b"
  shows "defl_invar P0 (defl_step Q m) a m"
  unfolding defl_invar_def
proof (intro conjI allI impI)
  show "defl_step Q m dvd P0"
    by (rule dvd_trans[OF defl_step_dvd defl_invar_dvd[OF inv]])
next
  fix x assume ax: "a < x" and xm: "x < m"
  have "x \<noteq> m" using xm by simp
  hence "(poly (defl_step Q m) x = 0) = (poly Q x = 0)"
    by (rule defl_step_poly_eq_0_iff)
  moreover have "(poly Q x = 0) = (poly P0 x = 0)"
    using inv ax xm mb unfolding defl_invar_def by simp
  ultimately show "(poly (defl_step Q m) x = 0) = (poly P0 x = 0)" by simp
qed

lemma defl_invar_right:
  assumes inv: "defl_invar P0 Q a b" and am: "a \<le> m"
  shows "defl_invar P0 (defl_step Q m) m b"
  unfolding defl_invar_def
proof (intro conjI allI impI)
  show "defl_step Q m dvd P0"
    by (rule dvd_trans[OF defl_step_dvd defl_invar_dvd[OF inv]])
next
  fix x assume mx: "m < x" and xb: "x < b"
  have "x \<noteq> m" using mx by simp
  hence "(poly (defl_step Q m) x = 0) = (poly Q x = 0)"
    by (rule defl_step_poly_eq_0_iff)
  moreover have "(poly Q x = 0) = (poly P0 x = 0)"
    using inv mx xb am unfolding defl_invar_def by simp
  ultimately show "(poly (defl_step Q m) x = 0) = (poly P0 x = 0)" by simp
qed

text \<open>\<^bold>\<open>What the invariant provides\<close>: inside the box, an isolation statement about the node's polynomial
  is one about the input. Both the soundness and the completeness proofs make this rewriting step, so
  it is proved once here.\<close>

lemma defl_invar_roots_agree:
  assumes "defl_invar P0 Q a b" and "a < x" and "x < b"
  shows "(poly Q x = 0) = (poly P0 x = 0)"
  using assms unfolding defl_invar_def by simp

corollary newdsc_pol_defl_terminates_squarefree_input:
  fixes P :: "real poly"
  assumes "P \<noteq> 0" "degree P \<le> p" "p \<noteq> 0" "square_free P" "a < b"
  shows "newdsc_pol_defl_dom (pol, p, a, b, e, dk, s, P)"
  using newdsc_pol_defl_terminates_squarefree[OF assms(1-4) dvd_refl assms(5)] .

section \<open>Soundness\<close>

text \<open>\<^bold>\<open>The claim\<close> is that every emitted window isolates a root of the input \<open>P0\<close> (@{const dsc_pair_ok}),
  not that the emitted multiset equals @{const dsc_int}'s, which deflation cannot satisfy because it
  returns different intervals.

  Structurally the proof follows @{thm [source] newdsc_pol_sound}, with @{const defl_invar} in place of
  the fixed \<open>P\<close> and two extra steps: the \<open>v = 1\<close> payload is transported from \<open>Q\<close> to \<open>P0\<close>, and the accept
  branches re-establish the invariant on the sub-box (using @{thm [source] try_newton_SomeD}(1,2) and
  @{thm [source] try_blocks_SomeD}(1,2), whose containment components the original proof did not
  need).\<close>

subsection \<open>Transporting a count from the node's polynomial to the input\<close>

lemma poly_zero_of_dvd:
  assumes "Q dvd P0" and "poly Q x = 0"
  shows "poly P0 x = 0"
  using assms by (auto elim!: dvdE)

text \<open>@{const roots_in} is a @{const proots_count}, i.e. WITH multiplicity, so agreeing root
  SETS is not by itself enough. Squarefreeness closes the gap: every order is \<open>1\<close>, so the count
  is the cardinality. (The argument is the one inside @{thm [source] proots_count_le_1}, extracted
  so it can be used for an equality rather than a bound.)\<close>

lemma proots_count_eq_card_of_rsquarefree:
  fixes p :: "real poly"
  assumes rsf: "rsquarefree p"
  shows "proots_count p S = card (proots_within p S)"
proof -
  from rsf have p0: "p \<noteq> 0" unfolding rsquarefree_def by auto
  have order_eq_1: "order z p = 1" if hz: "z \<in> proots_within p S" for z
  proof -
    from hz have "poly p z = 0" by (simp add: proots_within_def)
    with order_gt_0_iff[OF p0, of z] have "order z p > 0" by simp
    moreover from rsf have "order z p = 0 \<or> order z p = 1"
      unfolding rsquarefree_def by blast
    ultimately show ?thesis by linarith
  qed
  have "proots_count p S = (\<Sum>z\<in>proots_within p S. order z p)"
    by (simp add: proots_count_def)
  also have "\<dots> = (\<Sum>z\<in>proots_within p S. 1)" using order_eq_1 by simp
  also have "\<dots> = card (proots_within p S)" by simp
  finally show ?thesis .
qed

lemma defl_invar_roots_in_eq:
  assumes inv: "defl_invar P0 Q a b"
      and P0nz: "P0 \<noteq> 0"
      and sf: "square_free P0"
  shows "roots_in Q a b = roots_in P0 a b"
proof -
  have rsfP: "rsquarefree P0" using sf by (rule square_free_rsquarefree)
  have sfQ: "square_free Q" using square_free_factor[OF defl_invar_dvd[OF inv] sf] .
  have rsfQ: "rsquarefree Q" using sfQ by (rule square_free_rsquarefree)
  have sets_eq: "proots_within Q {x. a < x \<and> x < b} = proots_within P0 {x. a < x \<and> x < b}"
    using defl_invar_roots_agree[OF inv] unfolding proots_within_def by auto
  show ?thesis
    unfolding roots_in_def
    using proots_count_eq_card_of_rsquarefree[OF rsfQ]
          proots_count_eq_card_of_rsquarefree[OF rsfP] sets_eq
    by simp
qed

subsection \<open>The theorem\<close>

theorem newdsc_pol_defl_sound:
  assumes dom:  "newdsc_pol_defl_dom (pol, p, a, b, e, dk, s, Q)"
      and deg:  "degree P0 \<le> p"
      and P0nz: "P0 \<noteq> 0"
      and sf:   "square_free P0"
      and ab:   "a < b"
      and inv:  "defl_invar P0 Q a b"
  shows "\<forall>I \<in> set (newdsc_pol_defl pol p a b e dk s Q). dsc_pair_ok P0 I"
  using dom deg P0nz sf ab inv
proof (induction pol p a b e dk s Q rule: newdsc_pol_defl.pinduct)
  case (1 pol p a b e dk s Q)
  have defl_eq:
    "newdsc_pol_defl pol p a b e dk s Q =
       (let v = Bernstein_changes p a b Q in
        if v = 0 then []
        else if v = 1 then [(a, b)]
        else
          (case try_newton_g (snd (pol p a b e dk (s, v))) p a b (N_of e) Q v of
             Some I \<Rightarrow> newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q
           | None \<Rightarrow>
               (case try_blocks_g (fst (pol p a b e dk (s, v))) p a b (N_of e) Q v of
                  Some I \<Rightarrow> newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q
                | None \<Rightarrow>
                    (let m  = (a + b) / 2;
                         e' = max 1 (e - 1);
                         s' = split_run_len_real p Q a b s;
                         mid_root = (if poly Q m = 0 then [(m, m)] else [])
                     in mid_root @ newdsc_pol_defl pol p a m e' (dk + 1) s' (defl_step Q m)
                                 @ newdsc_pol_defl pol p m b e' (dk + 1) s' (defl_step Q m)))))"
    using "1.hyps" newdsc_pol_defl.psimps by blast

  show ?case
  proof -
    from 1 have ab: "a < b" and P0': "P0 \<noteq> 0" and deg': "degree P0 \<le> p"
            and sf': "square_free P0" and inv': "defl_invar P0 Q a b"
      by blast+

    \<comment> \<open>\<open>Q\<close>'s own side conditions are DERIVED from the invariant, not carried: a divisor of a
        nonzero polynomial is nonzero and no larger in degree.\<close>
    have Qdvd: "Q dvd P0" using defl_invar_dvd[OF inv'] .
    have Qnz: "Q \<noteq> 0" using Qdvd P0' by auto
    have degQ: "degree Q \<le> p" using dvd_imp_degree_le[OF Qdvd P0'] deg' by linarith

    let ?v = "Bernstein_changes p a b Q"
    let ?gb = "fst (pol p a b e dk (s, ?v))"
    let ?gn = "snd (pol p a b e dk (s, ?v))"

    show ?thesis
    proof (cases "?v = 0")
      case True
      then show ?thesis by (simp add: defl_eq Let_def)
    next
      case v0_ne: False
      show ?thesis
      proof (cases "?v = 1")
        case v1: True
        have v1_exact: "roots_in Q a b = 1"
          using Bernstein_changes_1_one_root[OF degQ Qnz ab v1] .
        \<comment> \<open>\<^bold>\<open>The transport step the non-deflating proof does not need.\<close>\<close>
        have v1_P0: "roots_in P0 a b = 1"
          using v1_exact defl_invar_roots_in_eq[OF inv' P0' sf'] by simp
        have dsc_ok_ab: "dsc_pair_ok P0 (a, b)"
          using v1_P0 ab by (simp add: dsc_pair_ok_def roots_in_def)
        show ?thesis using v1 v0_ne dsc_ok_ab by (simp add: defl_eq Let_def)
      next
        case v_ge2: False
        then have v_ge2': "?v \<ge> 2"
          using v0_ne by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)
        have Nof_pos: "N_of e > 0" using N_of_ge_2[of e] by simp

        have IH_newton:
          "\<And>I. try_newton_g ?gn p a b (N_of e) Q ?v = Some I \<Longrightarrow>
                \<forall>J\<in>set (newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q).
                   dsc_pair_ok P0 J"
        proof -
          fix I
          assume TNg: "try_newton_g ?gn p a b (N_of e) Q ?v = Some I"
          have TN: "try_newton p a b (N_of e) Q ?v = Some I"
            using TNg by (simp add: try_newton_g_def split: if_split_asm)
          have lo: "a \<le> fst I" using try_newton_SomeD(1)[OF TN ab Nof_pos] .
          have hi: "snd I \<le> b" using try_newton_SomeD(2)[OF TN ab Nof_pos] .
          have fst_lt_snd: "fst I < snd I"
          proof -
            have "snd I - fst I = (b - a) / of_nat (N_of e)"
              using try_newton_SomeD(3)[OF TN ab Nof_pos] by (simp add: Let_def)
            moreover have "(b - a) / of_nat (N_of e) > 0" using ab Nof_pos by simp
            ultimately show ?thesis by linarith
          qed
          have inv_I: "defl_invar P0 Q (fst I) (snd I)"
            using defl_invar_shrink[OF inv' lo hi] .
          show "\<forall>J\<in>set (newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q).
                   dsc_pair_ok P0 J"
            using "1.IH"(4) TNg deg' P0' sf' fst_lt_snd inv_I v0_ne v_ge2 by blast
        qed

        have IH_block:
          "\<And>I. \<lbrakk>try_newton_g ?gn p a b (N_of e) Q ?v = None;
                  try_blocks_g ?gb p a b (N_of e) Q ?v = Some I\<rbrakk> \<Longrightarrow>
                \<forall>J\<in>set (newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q).
                   dsc_pair_ok P0 J"
        proof -
          fix I
          assume TN0: "try_newton_g ?gn p a b (N_of e) Q ?v = None"
             and TBg: "try_blocks_g ?gb p a b (N_of e) Q ?v = Some I"
          have TB: "try_blocks p a b (N_of e) Q ?v = Some I"
            using TBg by (simp add: try_blocks_g_def split: if_split_asm)
          have lo: "a \<le> fst I" using try_blocks_SomeD(1)[OF TB Nof_pos ab] .
          have hi: "snd I \<le> b" using try_blocks_SomeD(2)[OF TB Nof_pos ab] .
          have fst_lt_snd: "fst I < snd I"
          proof -
            have "snd I - fst I = (b - a) / of_nat (N_of e)"
              using try_blocks_SomeD(3)[OF TB Nof_pos ab] by simp
            moreover have "(b - a) / of_nat (N_of e) > 0" using ab Nof_pos by simp
            ultimately show ?thesis by linarith
          qed
          have inv_I: "defl_invar P0 Q (fst I) (snd I)"
            using defl_invar_shrink[OF inv' lo hi] .
          show "\<forall>J\<in>set (newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q).
                   dsc_pair_ok P0 J"
            using "1.IH"(3) TN0 TBg deg' P0' sf' fst_lt_snd inv_I v0_ne v_ge2 by blast
        qed

        have IH_LR:
          "\<And>m e' s'.
             \<lbrakk>try_newton_g ?gn p a b (N_of e) Q ?v = None;
              try_blocks_g ?gb p a b (N_of e) Q ?v = None;
              m = (a + b) / 2; e' = max 1 (e - 1);
              s' = split_run_len_real p Q a b s\<rbrakk> \<Longrightarrow>
             (\<forall>I\<in>set (newdsc_pol_defl pol p a m e' (dk + 1) s' (defl_step Q m)). dsc_pair_ok P0 I)
             \<and> (\<forall>I\<in>set (newdsc_pol_defl pol p m b e' (dk + 1) s' (defl_step Q m)). dsc_pair_ok P0 I)"
        proof -
          fix m e' s'
          assume TN0: "try_newton_g ?gn p a b (N_of e) Q ?v = None"
             and TB0: "try_blocks_g ?gb p a b (N_of e) Q ?v = None"
             and m_def: "m = (a + b) / 2"
             and e'_def: "e' = max 1 (e - 1)"
             and s'_def: "s' = split_run_len_real p Q a b s"
          have am: "a < m" and mb: "m < b" using ab by (simp_all add: m_def)
          have inv_L: "defl_invar P0 (defl_step Q m) a m"
            using defl_invar_left[OF inv'] mb by simp
          have inv_R: "defl_invar P0 (defl_step Q m) m b"
            using defl_invar_right[OF inv'] am by simp
          have IH_left:
            "\<forall>I\<in>set (newdsc_pol_defl pol p a m e' (dk + 1) s' (defl_step Q m)). dsc_pair_ok P0 I"
            using "1.IH"(1) deg' v0_ne v_ge2 TN0 TB0 m_def e'_def s'_def P0' sf' am inv_L
            by blast
          have IH_right:
            "\<forall>I\<in>set (newdsc_pol_defl pol p m b e' (dk + 1) s' (defl_step Q m)). dsc_pair_ok P0 I"
            using "1.IH"(2) deg' v0_ne v_ge2 TN0 TB0 m_def e'_def s'_def P0' sf' mb inv_R
            by blast
          show "(\<forall>I\<in>set (newdsc_pol_defl pol p a m e' (dk + 1) s' (defl_step Q m)). dsc_pair_ok P0 I)
                \<and> (\<forall>I\<in>set (newdsc_pol_defl pol p m b e' (dk + 1) s' (defl_step Q m)). dsc_pair_ok P0 I)"
            using IH_left IH_right by simp
        qed

        show ?thesis
        proof (cases "try_newton_g ?gn p a b (N_of e) Q ?v")
          case (Some I)
          then have "\<forall>J\<in>set (newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q).
                        dsc_pair_ok P0 J"
            using IH_newton by blast
          thus ?thesis using Some v0_ne v_ge2 by (simp add: defl_eq Let_def)
        next
          case TN_None: None
          show ?thesis
          proof (cases "try_blocks_g ?gb p a b (N_of e) Q ?v")
            case (Some I)
            then have "\<forall>J\<in>set (newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q).
                          dsc_pair_ok P0 J"
              using IH_block TN_None by blast
            thus ?thesis using TN_None Some v0_ne v_ge2 by (simp add: defl_eq Let_def)
          next
            case TB_None: None
            let ?m = "(a + b) / 2"
            let ?e' = "max 1 (e - 1)"
            let ?s' = "split_run_len_real p Q a b s"
            from IH_LR[OF TN_None TB_None refl refl refl]
            have left_ok:
              "\<forall>I\<in>set (newdsc_pol_defl pol p a ?m ?e' (dk + 1) ?s' (defl_step Q ?m)).
                  dsc_pair_ok P0 I"
              and right_ok:
              "\<forall>I\<in>set (newdsc_pol_defl pol p ?m b ?e' (dk + 1) ?s' (defl_step Q ?m)).
                  dsc_pair_ok P0 I"
              by auto
            \<comment> \<open>The emitted degenerate pair is a root of \<open>Q\<close>; it is a root of \<open>P0\<close> because \<open>Q\<close> divides \<open>P0\<close>.\<close>
            have mid_ok:
              "\<forall>I\<in>set (if poly Q ?m = 0 then [(?m, ?m)] else []). dsc_pair_ok P0 I"
            proof (cases "poly Q ?m = 0")
              case True
              then have "set (if poly Q ?m = 0 then [(?m, ?m)] else []) = {(?m, ?m)}" by auto
              moreover have "dsc_pair_ok P0 (?m, ?m)"
                using poly_zero_of_dvd[OF Qdvd True] by (simp add: dsc_pair_ok_def)
              ultimately show ?thesis by auto
            next
              case False then show ?thesis by (simp add: dsc_pair_ok_def)
            qed
            show ?thesis
              using defl_eq TB_None TN_None v0_ne v_ge2 left_ok right_ok mid_ok
              by (auto simp: Let_def)
          qed
        qed
      qed
    qed
  qed
qed

section \<open>The window-accept argument\<close>

text \<open>\<^bold>\<open>The accept branches' content, which is about \<open>Q\<close> alone.\<close> Both window probes (@{const try_newton},
  @{const try_blocks}) return \<open>Some I\<close> only when the sub-box carries the parent's Bernstein count (the
  \<open>if v1 = v then Some I1\<close> test in \<open>NewDsc\<close>). That equation forces every root of the parent box into the
  open sub-box: a root strictly outside contributes a change of its own
  (@{thm [source] Bernstein_changes_pos_of_root}), and superadditivity
  (@{thm [source] Bernstein_changes_split}) then gives \<open>v \<ge> 1 + v\<close>; a root on an endpoint is handled
  by @{thm [source] Bernstein_changes_split_root}.

  It is a lemma of its own because its hypotheses mention only \<open>Q\<close>, \<open>p\<close>, the two boxes and the root,
  nothing about the probe that produced \<open>I\<close>. That is the shape the concrete gate-open arm needs, where
  the window child is \<open>newton_wcand e m X\<close> and the count equality comes from
  \<open>newton_window_pick_bail_count\<close> rather than from a probe. (\<open>NewDsc\<close>'s completeness proof contains the
  same argument inline.)\<close>

lemma Bernstein_window_no_roots_outside:
  fixes Q :: "real poly"
  assumes degQ: "degree Q \<le> p" and Qnz: "Q \<noteq> 0" and ab: "a < b"
    and lo: "a \<le> fst I" and split_props: "fst I < snd I" and hi: "snd I \<le> b"
    and v_I: "Bernstein_changes p (fst I) (snd I) Q = Bernstein_changes p a b Q"
    and root: "poly Q x = 0" and ax: "a < x" and xb: "x < b"
  shows "fst I < x \<and> x < snd I"
proof -
  let ?v = "Bernstein_changes p a b Q"
  have I_props: "fst I \<ge> a \<and> snd I \<le> b" using lo hi by simp
  have not_left: "\<not> (x < fst I)"
  proof
    assume "x < fst I"
    hence "a < x" "x < fst I" using ax by simp_all
    hence "Bernstein_changes p a (fst I) Q \<ge> 1"
      using Bernstein_changes_pos_of_root[OF degQ Qnz _ root]
      by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)
    have "Bernstein_changes p a b Q \<ge>
          Bernstein_changes p a (fst I) Q + Bernstein_changes p (fst I) b Q"
      using Bernstein_changes_split[OF _ _ degQ] I_props \<open>a < x\<close> \<open>x < fst I\<close> split_props
      by simp
    moreover have "Bernstein_changes p (fst I) b Q \<ge> Bernstein_changes p (fst I) (snd I) Q"
      using Bernstein_changes_split[OF split_props _ degQ] I_props
      by (smt (verit) Bernstein_changes_def int_nat_eq)
    ultimately have "?v \<ge> 1 + ?v"
      using v_I \<open>1 \<le> Bernstein_changes p a (fst I) Q\<close> by linarith
    thus False by simp
  qed
  have not_right: "\<not> (x > snd I)"
  proof
    assume "x > snd I"
    hence "snd I < x" "x < b" using xb by simp_all
    hence "Bernstein_changes p (snd I) b Q \<ge> 1"
      using Bernstein_changes_pos_of_root[OF degQ Qnz _ root]
      by (metis Bernstein_changes_def I_props add_0 dual_order.order_iff_strict
          int_one_le_iff_zero_less not_less_iff_gr_or_eq zle_iff_zadd)
    have "Bernstein_changes p a b Q \<ge>
          Bernstein_changes p a (snd I) Q + Bernstein_changes p (snd I) b Q"
      using Bernstein_changes_split[OF _ _ degQ] I_props \<open>snd I < x\<close> \<open>x < b\<close> split_props
      by simp
    moreover have "Bernstein_changes p a (snd I) Q \<ge> Bernstein_changes p (fst I) (snd I) Q"
      using Bernstein_changes_split[OF _ split_props degQ] I_props split_props
      by (smt (verit, ccfv_SIG) Bernstein_changes_def int_nat_eq)
    ultimately have "?v \<ge> ?v + 1"
      using v_I \<open>1 \<le> Bernstein_changes p (snd I) b Q\<close> by linarith
    thus False by simp
  qed
  have "x \<noteq> fst I"
  proof
    assume "x = fst I"
    then have "poly Q (fst I) = 0" using root by simp
    have "Bernstein_changes p a (fst I) Q + Bernstein_changes p (fst I) b Q + 1
          \<le> Bernstein_changes p a b Q"
      using Bernstein_changes_split_root \<open>x = fst I\<close> ax degQ root xb Qnz by blast
    moreover have "Bernstein_changes p (fst I) b Q \<ge> ?v"
    proof -
      have "Bernstein_changes p (fst I) b Q =
            Bernstein_changes p (fst I) (snd I) Q + Bernstein_changes p (snd I) b Q"
        using Bernstein_changes_split[OF split_props _ degQ] I_props
        by (smt (verit, ccfv_SIG) Bernstein_changes_def calculation of_nat_0_le_iff v_I)
      show ?thesis using Bernstein_changes_split[OF split_props _ degQ] I_props v_I
        by (metis Bernstein_changes_def
            \<open>Bernstein_changes p (fst I) b Q = Bernstein_changes p (fst I) (snd I) Q + Bernstein_changes p (snd I) b Q\<close>
            zle_iff_zadd)
    qed
    ultimately have "0 + ?v + 1 \<le> ?v"
      using Bernstein_changes_split[OF _ _ degQ] I_props
      by (smt (verit, ccfv_threshold) Bernstein_changes_def of_nat_0_le_iff)
    thus False by simp
  qed
  have "x \<noteq> snd I"
  proof
    assume "x = snd I"
    then have "poly Q (snd I) = 0" using root by simp
    have "Bernstein_changes p a (snd I) Q + Bernstein_changes p (snd I) b Q + 1
          \<le> Bernstein_changes p a b Q"
      using Bernstein_changes_split_root \<open>x = snd I\<close> ax degQ xb \<open>poly Q (snd I) = 0\<close> Qnz
      by blast
    moreover have "Bernstein_changes p a (snd I) Q \<ge> ?v"
      using Bernstein_changes_split[OF _ split_props degQ] I_props v_I
      by (metis Bernstein_changes_def \<open>x = snd I\<close> add.commute
          dual_order.order_iff_strict dual_order.trans zle_iff_zadd)
    ultimately have "?v + 0 + 1 \<le> ?v"
      by (smt (verit, ccfv_SIG) Bernstein_changes_def int_nat_eq)
    thus False by simp
  qed
  show "fst I < x \<and> x < snd I"
    using not_left not_right \<open>x \<noteq> fst I\<close> \<open>x \<noteq> snd I\<close> linorder_less_linear by blast
qed

section \<open>Completeness\<close>

text \<open>Every real root of the input in the initial box lies in some emitted window. The proof follows
  @{thm [source] newdsc_pol_complete} with @{const defl_invar} threaded through; the Bernstein-count
  arguments in the two accept branches are about the node's polynomial only.

  Three places differ:
    \<^item> the hypothesis is a root of \<open>P0\<close>; @{thm [source] defl_invar_roots_agree} turns it into a root of
      \<open>Q\<close> at the top;
    \<^item> the accept branches re-establish the invariant on the sub-box, so the \<open>IH_newton\<close>/\<open>IH_block\<close> steps
      are explicit proofs;
    \<^item> in the bisection branch the children carry \<open>defl_step Q m\<close>, and the \<open>x = m\<close> case is the emitted
      degenerate pair, which exists because \<open>poly Q m = 0\<close> follows from the invariant.

  \<^bold>\<open>Squarefreeness is not needed here\<close>: completeness needs only that the root sets agree inside the
  box, which is the invariant. Soundness needs the multiplicity argument.\<close>

theorem newdsc_pol_defl_complete:
  assumes dom:  "newdsc_pol_defl_dom (pol, p, a, b, e, dk, s, Q)"
      and deg:  "degree P0 \<le> p"
      and P0nz: "P0 \<noteq> 0"
      and inv:  "defl_invar P0 Q a b"
  shows "\<And>x. poly P0 x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol_defl pol p a b e dk s Q). fst I \<le> x \<and> x \<le> snd I)"
  using dom deg P0nz inv
proof (induction pol p a b e dk s Q rule: newdsc_pol_defl.pinduct)
  case (1 pol p a b e dk s Q)
  have defl_eq:
    "newdsc_pol_defl pol p a b e dk s Q =
       (let v = Bernstein_changes p a b Q in
        if v = 0 then []
        else if v = 1 then [(a, b)]
        else
          (case try_newton_g (snd (pol p a b e dk (s, v))) p a b (N_of e) Q v of
             Some I \<Rightarrow> newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q
           | None \<Rightarrow>
               (case try_blocks_g (fst (pol p a b e dk (s, v))) p a b (N_of e) Q v of
                  Some I \<Rightarrow> newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q
                | None \<Rightarrow>
                    (let m  = (a + b) / 2;
                         e' = max 1 (e - 1);
                         s' = split_run_len_real p Q a b s;
                         mid_root = (if poly Q m = 0 then [(m, m)] else [])
                     in mid_root @ newdsc_pol_defl pol p a m e' (dk + 1) s' (defl_step Q m)
                                 @ newdsc_pol_defl pol p m b e' (dk + 1) s' (defl_step Q m)))))"
    using "1.hyps" newdsc_pol_defl.psimps by blast

  show ?case
  proof -
    have H:
      "\<And>x::real. poly P0 x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (newdsc_pol_defl pol p a b e dk s Q). fst I \<le> x \<and> x \<le> snd I)"
    proof -
      fix x :: real
      assume rootP0: "poly P0 x = 0" and ax: "a < x" and xb: "x < b"
      have ab: "a < b" using ax xb by linarith
      from 1 have deg': "degree P0 \<le> p" and P0': "P0 \<noteq> 0"
              and inv': "defl_invar P0 Q a b" by blast+

      have Qdvd: "Q dvd P0" using defl_invar_dvd[OF inv'] .
      have Qnz: "Q \<noteq> 0" using Qdvd P0' by auto
      have degQ: "degree Q \<le> p" using dvd_imp_degree_le[OF Qdvd P0'] deg' by linarith

      \<comment> \<open>\<^bold>\<open>The one transport step\<close>: inside the box, a root of the input IS a root of the
          node's polynomial. Everything after this is the non-deflating argument with \<open>Q\<close> for \<open>P\<close>.\<close>
      have root: "poly Q x = 0"
        using defl_invar_roots_agree[OF inv' ax xb] rootP0 by simp

      show "\<exists>I\<in>set (newdsc_pol_defl pol p a b e dk s Q). fst I \<le> x \<and> x \<le> snd I"
      proof -
        let ?v = "Bernstein_changes p a b Q"
        let ?gb = "fst (pol p a b e dk (s, ?v))"
        let ?gn = "snd (pol p a b e dk (s, ?v))"
        have Nof_pos: "N_of e > 0" using N_of_ge_2[of e] by simp

        have v_nonzero: "?v \<noteq> 0"
        proof
          assume "?v = 0"
          then have "roots_in Q a b = 0"
            using Bernstein_changes_0_no_root[OF degQ Qnz ab] by simp
          then have "poly Q x \<noteq> 0"
            using ax xb Bernstein_changes_pos_of_root Qnz \<open>?v = 0\<close> ab degQ by blast
          with root show False by simp
        qed

        show ?thesis
        proof (cases "?v = 1")
          case v1: True
          have mem: "(a,b) \<in> set (newdsc_pol_defl pol p a b e dk s Q)"
            using defl_eq v1 v_nonzero by (simp add: Let_def)
          show ?thesis
          proof (intro bexI[of _ "(a,b)"])
            show "fst (a,b) \<le> x \<and> x \<le> snd (a,b)" using ax xb by simp
          next
            show "(a,b) \<in> set (newdsc_pol_defl pol p a b e dk s Q)" using mem .
          qed
        next
          case v_ne1: False
          hence v_ge2: "?v \<ge> 2"
            using v_nonzero by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)

          show ?thesis
          proof (cases "try_newton_g ?gn p a b (N_of e) Q ?v")
            case (Some I)
            then have TNg: "try_newton_g ?gn p a b (N_of e) Q ?v = Some I" by simp
            have TN: "try_newton p a b (N_of e) Q ?v = Some I"
              using TNg by (simp add: try_newton_g_def split: if_split_asm)
            have pos_in_I: "fst I < x \<and> x < snd I"
            proof -
              define w where "w = b - a"
              have "w > 0" using ab w_def by simp
              have I_props: "fst I \<ge> a \<and> snd I \<le> b \<and> snd I - fst I = w / of_nat (N_of e)"
                using try_newton_SomeD[OF TN ab Nof_pos] w_def by simp
              have split_props: "fst I < snd I"
                using I_props Nof_pos \<open>w > 0\<close>
                by (metis diff_gt_0_iff_gt of_nat_0_less_iff zero_less_divide_iff)
              have v_I: "Bernstein_changes p (fst I) (snd I) Q = ?v"
                using TN unfolding try_newton_def Let_def
                by (auto split: option.split_asm if_split_asm)
              \<comment> \<open>By @{thm [source] Bernstein_window_no_roots_outside}, which the \<open>try_blocks\<close> branch below and the
                 concrete gate-open arm also use.\<close>
              have lo': "a \<le> fst I" using I_props by simp
              have hi': "snd I \<le> b" using I_props by simp
              show ?thesis
                by (rule Bernstein_window_no_roots_outside[OF degQ Qnz ab lo' split_props hi'
                      v_I root ax xb])
            qed
            then have fstI_lt: "fst I < x" and x_lt_sndI: "x < snd I" by auto
            have lo: "a \<le> fst I" using try_newton_SomeD(1)[OF TN ab Nof_pos] .
            have hi: "snd I \<le> b" using try_newton_SomeD(2)[OF TN ab Nof_pos] .
            have inv_I: "defl_invar P0 Q (fst I) (snd I)"
              using defl_invar_shrink[OF inv' lo hi] .
            have "\<exists>J\<in>set (newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q).
                     fst J \<le> x \<and> x \<le> snd J"
              using "1.IH"(4) TNg deg' P0' inv_I rootP0 fstI_lt x_lt_sndI v_nonzero v_ne1 by blast
            then obtain J
              where J_in: "J \<in> set (newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q)"
                and J_cov: "fst J \<le> x \<and> x \<le> snd J" by blast
            have "newdsc_pol_defl pol p a b e dk s Q
                    = newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q"
              using defl_eq Some v_ne1 v_nonzero by (simp add: Let_def)
            then show ?thesis using J_in J_cov by auto
          next
            case TN_None: None
            show ?thesis
            proof (cases "try_blocks_g ?gb p a b (N_of e) Q ?v")
              case (Some I)
              then have TBg: "try_blocks_g ?gb p a b (N_of e) Q ?v = Some I" by simp
              have TB: "try_blocks p a b (N_of e) Q ?v = Some I"
                using TBg by (simp add: try_blocks_g_def split: if_split_asm)
              have pos_in_I: "fst I < x \<and> x < snd I"
              proof -
                define w where "w = b - a"
                have "w > 0" using ab w_def by simp
                have I_props: "fst I \<ge> a \<and> snd I \<le> b \<and> snd I - fst I = w / of_nat (N_of e)"
                  using TB Nof_pos ab try_blocks_SomeD(1,2,3) w_def by presburger
                then have fst_le_snd: "fst I < snd I"
                  using Nof_pos \<open>0 < w\<close> diff_gt_0_iff_gt by fastforce
                have v_I: "Bernstein_changes p (fst I) (snd I) Q = ?v"
                  using TB unfolding try_blocks_def Let_def by (auto split: if_split_asm)
                have lo': "a \<le> fst I" using I_props by simp
                have hi': "snd I \<le> b" using I_props by simp
                show ?thesis
                  by (rule Bernstein_window_no_roots_outside[OF degQ Qnz ab lo' fst_le_snd hi'
                        v_I root ax xb])
              qed
              then have fstI_lt: "fst I < x" and x_lt_sndI: "x < snd I" by auto
              have lo: "a \<le> fst I" using try_blocks_SomeD(1)[OF TB Nof_pos ab] .
              have hi: "snd I \<le> b" using try_blocks_SomeD(2)[OF TB Nof_pos ab] .
              have inv_I: "defl_invar P0 Q (fst I) (snd I)"
                using defl_invar_shrink[OF inv' lo hi] .
              have "\<exists>J\<in>set (newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q).
                       fst J \<le> x \<and> x \<le> snd J"
                using "1.IH"(3) TN_None TBg deg' P0' inv_I rootP0 fstI_lt x_lt_sndI v_nonzero v_ne1
                by blast
              then obtain J
                where J_in: "J \<in> set (newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q)"
                  and J_cov: "fst J \<le> x \<and> x \<le> snd J" by blast
              have "newdsc_pol_defl pol p a b e dk s Q
                      = newdsc_pol_defl pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s Q"
                using defl_eq TN_None Some v_ne1 v_nonzero by (simp add: Let_def)
              then show ?thesis using J_in J_cov by auto
            next
              case TB_None: None
              define m where "m = (a + b) / 2"
              define e' where "e' = max 1 (e - 1)"
              define s' where "s' = split_run_len_real p Q a b s"
              have am: "a < m" and mb: "m < b" using ab by (simp_all add: m_def)
              have inv_L: "defl_invar P0 (defl_step Q m) a m"
                using defl_invar_left[OF inv'] mb by simp
              have inv_R: "defl_invar P0 (defl_step Q m) m b"
                using defl_invar_right[OF inv'] am by simp

              have split:
                "(\<exists>I\<in>set (newdsc_pol_defl pol p a m e' (dk + 1) s' (defl_step Q m)).
                     fst I \<le> x \<and> x \<le> snd I) \<or>
                 (\<exists>I\<in>set (newdsc_pol_defl pol p m b e' (dk + 1) s' (defl_step Q m)).
                     fst I \<le> x \<and> x \<le> snd I) \<or> x = m"
              proof (cases "x < m")
                case True
                then have "a < x" "x < m" using ax by auto
                then have "\<exists>I\<in>set (newdsc_pol_defl pol p a m e' (dk + 1) s' (defl_step Q m)).
                              fst I \<le> x \<and> x \<le> snd I"
                  using "1.IH"(1) deg' v_ne1 v_nonzero TB_None TN_None m_def e'_def s'_def
                        rootP0 P0' inv_L by blast
                then show ?thesis by blast
              next
                case False
                then consider "x = m" | "x > m" by linarith
                then show ?thesis
                proof cases
                  case 1 then show ?thesis by blast
                next
                  case 2
                  then have "m < x" "x < b" using xb by auto
                  then have "\<exists>I\<in>set (newdsc_pol_defl pol p m b e' (dk + 1) s' (defl_step Q m)).
                                fst I \<le> x \<and> x \<le> snd I"
                    using "1.IH"(2) deg' v_ne1 v_nonzero TB_None TN_None m_def e'_def s'_def
                          rootP0 P0' inv_R by blast
                  then show ?thesis by blast
                qed
              qed

              have eq_lin:
                "newdsc_pol_defl pol p a b e dk s Q =
                   (if poly Q m = 0 then [(m, m)] else [])
                   @ newdsc_pol_defl pol p a m e' (dk + 1) s' (defl_step Q m)
                   @ newdsc_pol_defl pol p m b e' (dk + 1) s' (defl_step Q m)"
                using defl_eq TN_None TB_None v_ne1 v_nonzero
                by (simp add: Let_def m_def e'_def s'_def)

              from split show ?thesis
              proof (elim disjE)
                assume "\<exists>I\<in>set (newdsc_pol_defl pol p a m e' (dk + 1) s' (defl_step Q m)).
                           fst I \<le> x \<and> x \<le> snd I"
                then show ?thesis using eq_lin by auto
              next
                assume "\<exists>I\<in>set (newdsc_pol_defl pol p m b e' (dk + 1) s' (defl_step Q m)).
                           fst I \<le> x \<and> x \<le> snd I"
                then show ?thesis using eq_lin by auto
              next
                assume mid: "x = m"
                \<comment> \<open>The shed root IS emitted: \<open>poly Q m = 0\<close> comes from the invariant at \<open>m\<close>,
                    which is interior to the box.\<close>
                then have "poly Q m = 0" using root by blast
                then have memm: "(m, m) \<in> set (newdsc_pol_defl pol p a b e dk s Q)"
                  using eq_lin by simp
                show ?thesis
                proof (intro bexI[of _ "(m,m)"])
                  show "fst (m,m) \<le> x \<and> x \<le> snd (m,m)" using mid by simp
                next
                  show "(m,m) \<in> set (newdsc_pol_defl pol p a b e dk s Q)" using memm .
                qed
              qed
            qed
          qed
        qed
      qed
    qed
    show ?thesis using "1.prems" H by blast
  qed
qed

corollary newdsc_pol_defl_complete_input:
  fixes P :: "real poly"
  assumes "P \<noteq> 0" "degree P \<le> p" "p \<noteq> 0" "square_free P" "a < b"
      and "poly P x = 0" "a < x" "x < b"
  shows "\<exists>I \<in> set (newdsc_pol_defl pol p a b e dk s P). fst I \<le> x \<and> x \<le> snd I"
  using newdsc_pol_defl_complete
          [OF newdsc_pol_defl_terminates_squarefree_input[OF assms(1-5)]
              assms(2) assms(1) defl_invar_init assms(6-8)] .

corollary newdsc_pol_defl_sound_input:
  fixes P :: "real poly"
  assumes "P \<noteq> 0" "degree P \<le> p" "p \<noteq> 0" "square_free P" "a < b"
  shows "\<forall>I \<in> set (newdsc_pol_defl pol p a b e dk s P). dsc_pair_ok P I"
  using newdsc_pol_defl_sound
          [OF newdsc_pol_defl_terminates_squarefree_input[OF assms]
              assms(2) assms(1) assms(4) assms(5) defl_invar_init] .

section \<open>Non-vacuity — both conclusions, at a concrete input\<close>

text \<open>\<^bold>\<open>Non-vacuity of the conclusion.\<close> The two \<open>_input\<close> corollaries carry the hypothesis set of
  @{thm [source] newdsc_pol_terminates_squarefree}, so satisfiability is inherited; this lemma checks it
  at a concrete instance.

  Witness \<open>P = x\<close> on \<open>(-1, 1)\<close> at \<open>p = 1\<close>: squarefree, degree 1, with a root at \<open>0\<close> strictly inside the
  box, so completeness has something to find and the emitted set is non-empty. Both conclusions hold
  outright.\<close>

lemma square_free_pCons_0_1: "square_free [:0, 1::real:]"
  unfolding square_free_def
proof (intro conjI allI impI)
  show "[:0, 1::real:] \<noteq> 0" by simp
next
  fix q :: "real poly"
  assume dq: "0 < degree q"
  show "\<not> q * q dvd [:0, 1::real:]"
  proof
    assume dvd2: "q * q dvd [:0, 1::real:]"
    have q0: "q \<noteq> 0" using dq by auto
    have "degree (q * q) \<le> degree ([:0, 1::real:])"
      by (rule dvd_imp_degree_le[OF dvd2]) simp
    moreover have "degree (q * q) = degree q + degree q"
      using q0 by (simp add: degree_mult_eq)
    ultimately show False using dq by simp
  qed
qed

theorem defl_sound_and_complete_not_vacuous:
  fixes pol :: newton_pol_real
  shows "(\<forall>I \<in> set (newdsc_pol_defl pol 1 (-1) 1 e dk s [:0, 1::real:]).
             dsc_pair_ok [:0, 1::real:] I)
         \<and> (\<exists>I \<in> set (newdsc_pol_defl pol 1 (-1) 1 e dk s [:0, 1::real:]).
               fst I \<le> 0 \<and> 0 \<le> snd I)"
proof
  show "\<forall>I \<in> set (newdsc_pol_defl pol 1 (-1) 1 e dk s [:0, 1::real:]).
           dsc_pair_ok [:0, 1::real:] I"
    by (rule newdsc_pol_defl_sound_input) (simp_all add: square_free_pCons_0_1)
next
  show "\<exists>I \<in> set (newdsc_pol_defl pol 1 (-1) 1 e dk s [:0, 1::real:]).
           fst I \<le> 0 \<and> 0 \<le> snd I"
    by (rule newdsc_pol_defl_complete_input) (simp_all add: square_free_pCons_0_1)
qed

end
