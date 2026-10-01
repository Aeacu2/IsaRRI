theory Newton_Spec
  imports "IsaRRI_Spec.Dsc_Int"
begin

text \<open>Abstract layer of carried Newton/NewDsc acceleration — the
  POLICY-PARAMETERIZED NewDsc algorithm, with NO GMP/Sepref content. Layer:
  FUNCTIONAL SPEC.

  \<^bold>\<open>Why this exists.\<close> @{const newdsc_int} is deterministic, so a runtime-guarded
  implementation (which must be free to SKIP block/Newton attempts on cheap
  eligibility signals) cannot refine it as an exact multiset. This theory clones the
  NewDsc recursion ONCE with an explicit policy parameter \<open>pol\<close> deciding, per node,
  whether to attempt blocks and/or Newton. Soundness, completeness and termination are
  proven FOR ALL policies (a pruned attempt only means more bisection — the terminating
  skeleton); the implementation then refines \<open>newdsc_pol_int pol\<close> for its own
  concrete \<open>pol\<close> as an exact multiset, and every tuning knob lives inside that
  one \<open>pol\<close> definition, never re-opening a proof.

  Main exports (consumed by \<open>Newton.thy\<close>'s solver bridge):
  \<open>newdsc_pol\<close> (real level, e-form, \<open>function (domintros)\<close> like @{const newdsc}),
  \<open>newdsc_pol_main_int\<close>/\<open>newdsc_pol_int\<close> (rational worklist level), the four
  for-all-pol theorems \<open>newdsc_pol_sound\<close>/\<open>newdsc_pol_complete\<close>/
  \<open>newdsc_pol_terminates_squarefree\<close>/\<open>newdsc_pol_int_eq_newdsc_pol\<close>,
  and the dyadic window-child arithmetic (\<open>newton_window_child\<close>) with the carried
  window-algebra spine.\<close>

section \<open>The scheduling policy and its guarded tries\<close>

text \<open>A policy sees the polynomial's degree (bound) \<open>p\<close>, the node's endpoints, the
  NewDsc exponent \<open>e\<close> (so \<open>N = N_of e\<close>), an opaque depth tag \<open>dk\<close> (below), and the
  node's EXACT sign-variation count \<open>v\<close>, and returns
  (attempt-blocks?, attempt-newton?).

  \<^bold>\<open>The degree parameter.\<close> The impl's word-headroom gate must cover the in-place
  window transform's precondition \<open>(2^e + 2) * (len - 1) < max_snat\<close>
  (\<open>carried_init_inplace_monadic_correct\<close>'s hypothesis shape, \<open>Carried_Kernel.thy\<close>); the
  degree is CONSTANT through the whole solve (every carried transform preserves
  it), so threading it to \<open>pol\<close> costs nothing abstractly.

  \<^bold>\<open>The depth tag.\<close> \<open>rat\<close> normalizes, so the implementation's stored dyadic
  exponent \<open>k\<close> is NOT a function of \<open>(a, b)\<close> alone; word-headroom guards need it.
  The worklist entries therefore carry \<open>dk :: nat\<close> updated in lockstep with the
  impl (\<open>+1\<close> on bisection, \<open>+ (2^e + 2)\<close> on a window accept, seeded with the input
  exponent). The correctness proofs ignore \<open>dk\<close> — it exists only for \<open>pol\<close>.

  \<^bold>\<open>v-visibility.\<close> \<open>pol\<close> may read \<open>v\<close>, but a concrete implementation policy must
  factor as (v-free pre-gate) \<open>\<and>\<close> (v-conjunct): the impl computes only the 0/1/\<ge>2
  classify (the truncated count) on the no-attempt path and the exact
  \<open>v\<close> (needed by the tries anyway) only after the v-free gate fires.\<close>

type_synonym newton_pol_real =
  "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> int) \<Rightarrow> bool \<times> bool"
text \<open>The integer-level policy is a degree-indexed family of per-node policies: the worklist
  recursion consumes the node view (\<open>newton_pol_node\<close>, with the degree already applied; the degree
  is constant over a solve, so \<open>newdsc_pol_int\<close> applies it once at the wrapper). Keeping the
  function-typed tail-recursive argument at the node view also keeps the
  \<open>partial_function (tailrec)\<close> packaging on a shape that elaborates; threading \<open>degree P\<close> inside
  the body breaks the fixpoint-rule assembly (\<open>OF: no unifiers\<close>).\<close>
type_synonym newton_pol_node =
  "rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool \<times> bool"
type_synonym newton_pol = "nat \<Rightarrow> newton_pol_node"

text \<open>Guarded tries: a \<open>False\<close> gate prunes the attempt. Wrapping the EXISTING
  @{const try_blocks}/@{const try_newton} (rather than reformulating them) is what
  lets the correctness proofs reuse their acceptance payload lemmas verbatim.\<close>

definition try_blocks_g ::
  "bool \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_blocks_g g p a b N P v = (if g then try_blocks p a b N P v else None)"

definition try_newton_g ::
  "bool \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real poly \<Rightarrow> int \<Rightarrow> (real \<times> real) option"
where
  "try_newton_g g p a b N P v = (if g then try_newton p a b N P v else None)"

definition try_blocks_int_g ::
  "bool \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> nat \<Rightarrow> (rat \<times> rat) option"
where
  "try_blocks_int_g g a b N P v = (if g then try_blocks_int a b N P v else None)"

definition try_newton_int_g ::
  "bool \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> nat \<Rightarrow> (rat \<times> rat) option"
where
  "try_newton_int_g g a b N P v = (if g then try_newton_int a b N P v else None)"

text \<open>\<^bold>\<open>The proper-split run length\<close> (Kobel, Rouillier and Sagraloff, \<section>3.1). A bisection
  \<open>I \<rightarrow> I', I''\<close> is a proper split when both children keep a nonzero sign-variation count. By
  Obreshkoff's one-circle theorem that refutes the single-cluster hypothesis at \<open>I\<close>, so the Newton
  machinery should not be attempted nearby. A cluster shows the opposite: a long chain of nodes
  whose variations all follow one child. \<open>s\<close> counts consecutive bisections since the last proper
  split, and the policy gates on it.

  \<^bold>\<open>Decay update.\<close> The update forgets gradually rather than resetting: \<open>s + 1\<close> on a
  cluster-consistent step (a midpoint root, or a child with a zero count) and
  \<open>s - s div 11 = \<lfloor>10s/11\<rfloor>\<close> on a proper split. A hard reset to \<open>0\<close> would over-forget on nested
  clusters, where the proper-split evidence is spread across every level. The rate is a
  performance parameter; correctness does not depend on it. The update is its own constant rather
  than an inline \<open>let\<close> in the recursion bodies because the \<open>partial_function (tailrec)\<close> packaging
  of \<open>newdsc_pol_main_int\<close> does not elaborate with the conditional inline, and because it gives the
  implementation and the keystone one name to refine against.\<close>

definition split_run_len_real :: "nat \<Rightarrow> real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat"
where
  "split_run_len_real p P a b s =
     (let m = (a + b) / 2
      in if poly P m = 0 \<or> (Bernstein_changes p a m P \<noteq> 0 \<and> Bernstein_changes p m b P \<noteq> 0)
         then s - s div 11 else s + 1)"

definition split_run_len_int :: "int poly \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> nat"
where
  "split_run_len_int P a b s =
     (let m = (a + b) / 2
      in if poly (map_poly of_int P :: rat poly) m = 0
              \<or> (descartes_list_int a m (coeffs P) \<noteq> 0 \<and> descartes_list_int m b (coeffs P) \<noteq> 0)
         then s - s div 11 else s + 1)"

text \<open>\<^bold>\<open>The int/real proper-split counters agree.\<close> The ONE genuinely new obligation of the
  \<open>s\<close>-threading: both sides test the two children's sign-variation counts for nonzero-ness (and
  the midpoint-root bit), and the existing per-interval count correspondence
  (\<open>descartes_roots_test_sc_of_int\<close> + \<open>descartes_roots_test_sc_eq_Bernstein_changes\<close>) applies at
  \<open>(a, m)\<close> and \<open>(m, b)\<close> exactly as it does at \<open>(a, b)\<close> for the node's own \<open>v\<close>, since
  \<open>a < m < b\<close>.\<close>
lemma split_run_len_int_eq_real:
  assumes P0: "P \<noteq> 0" and ab: "a < b" and pdeg: "p = degree P"
  shows "split_run_len_real p (map_poly of_int P :: real poly) (of_rat a) (of_rat b) s
           = split_run_len_int P a b s"
proof -
  let ?m = "(a + b) / 2"
  have am: "a < ?m" and mb: "?m < b" using ab by simp_all
  have mid: "(of_rat a + of_rat b) / 2 = (of_rat ?m :: real)"
    by (simp add: of_rat_add of_rat_divide)
  have deg_p: "degree (map_poly of_int P :: real poly) = p" using pdeg by simp
  have L: "int (descartes_list_int a ?m (coeffs P))
             = Bernstein_changes p (of_rat a) (of_rat ?m) (map_poly of_int P :: real poly)"
    using descartes_roots_test_sc_of_int[OF am P0]
    by (simp add: descartes_roots_test_sc_eq_Bernstein_changes deg_p pdeg)
  have R: "int (descartes_list_int ?m b (coeffs P))
             = Bernstein_changes p (of_rat ?m) (of_rat b) (map_poly of_int P :: real poly)"
    using descartes_roots_test_sc_of_int[OF mb P0]
    by (simp add: descartes_roots_test_sc_eq_Bernstein_changes deg_p pdeg)
  have MID: "(poly (map_poly of_int P :: real poly) (of_rat ?m) = 0)
               = (poly (map_poly of_int P :: rat poly) ?m = 0)"
  proof -
    have hom: "poly (map_poly of_rat (q::rat poly) :: real poly) (of_rat y)
                 = of_rat (poly q y)" for q y
      by (induction q) (auto simp: of_rat_add of_rat_mult)
    have "(map_poly of_int P :: real poly) = map_poly of_rat (map_poly of_int P :: rat poly)"
      by (simp add: map_poly_map_poly o_def)
    hence "poly (map_poly of_int P :: real poly) (of_rat ?m)
             = of_rat (poly (map_poly of_int P :: rat poly) ?m)"
      using hom by simp
    thus ?thesis by simp
  qed
  show ?thesis
    unfolding split_run_len_real_def split_run_len_int_def Let_def
    using L R MID by (simp add: mid)
qed

text \<open>Child-item constructors, hoisted out of the worklist recursion. \<open>partial_function
  (tailrec)\<close>'s monotonicity prover blows up (\<open>OF: no unifiers\<close> / \<open>Interrupt_Breakdown\<close>)
  when the recursive call's list argument is a large inline term over a 5-tuple item; naming
  the two constructions keeps the fixpoint body small. Behaviourally these are just the
  accept-child and the bisection-children of the pre-\<open>s\<close> recursion, with \<open>s\<close> carried
  (accept) resp. recomputed (bisect).\<close>

definition accept_child_int ::
  "rat \<times> rat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
     \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat)"
where
  "accept_child_int I e dk s = (fst I, snd I, e + 1, dk + (2 ^ e + 2), s)"

definition bisect_children_int ::
  "int poly \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
     \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list"
where
  "bisect_children_int P a b e dk s =
     (let m = (a + b) / 2; e' = max 1 (e - 1); s' = split_run_len_int P a b s
      in [(a, m, e', dk + 1, s'), (m, b, e', dk + 1, s')])"

section \<open>The policy-parameterized recursion, real level (e-form)\<close>

text \<open>Clone of @{const newdsc} (\<open>NewDsc.thy\<close>) with three deltas: (1) the tries
  are pol-guarded; (2) the recursion is in e-form (\<open>N = N_of e\<close>) at the REAL level
  already — \<open>Nq (N_of e) = N_of (e+1)\<close> and the \<open>Nlin\<close>/\<open>max 1 (e - 1)\<close>
  correspondence are existing \<open>Dsc_Exec.thy\<close> lemmas, so nothing is
  lost and the int-level bridge aligns index-for-index; (3) the \<open>dk\<close> tag is
  threaded. Proof discipline: \<open>function (domintros)\<close> + \<open>psimps\<close>/\<open>pinduct\<close>
  conditional on \<open>newdsc_pol_dom\<close>, exactly like @{const newdsc}'s own theorems.\<close>

function (domintros) newdsc_pol ::
  "newton_pol_real \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real poly
     \<Rightarrow> (real \<times> real) list"
where
  "newdsc_pol pol p a b e dk s P =
     (let v = Bernstein_changes p a b P in
      if v = 0 then []
      else if v = 1 then [(a, b)]
      else
        (case try_newton_g (snd (pol p a b e dk (s, v))) p a b (N_of e) P v of
           Some I \<Rightarrow> newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
         | None \<Rightarrow>
             (case try_blocks_g (fst (pol p a b e dk (s, v))) p a b (N_of e) P v of
                Some I \<Rightarrow> newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
              | None \<Rightarrow>
                  (let m  = (a + b) / 2;
                       e' = max 1 (e - 1);
                       s' = split_run_len_real p P a b s;
                       mid_root = (if poly P m = 0 then [(m, m)] else [])
                   in mid_root @ newdsc_pol pol p a m e' (dk + 1) s' P
                             @ newdsc_pol pol p m b e' (dk + 1) s' P))))"
  by pat_completeness auto

section \<open>For-all-pol correctness\<close>

text \<open>The grid parameter \<open>N_of e = 2 ^ (2 ^ e)\<close> is always \<open>\<ge> 2\<close> (since \<open>2 ^ e \<ge> 1\<close>),
  so — unlike @{const newdsc}'s N-form which threads an \<open>N \<ge> 2\<close> invariant — the
  e-form clone needs NO lower-bound hypothesis on \<open>e\<close>: every reachable node's grid
  divisor is \<open>\<ge> 2\<close> for free. (The fact itself, \<open>N_of_ge_2\<close>, is already in
  \<open>IsaRRI_Spec.Dsc_Int\<close>; reused here, not redefined.)\<close>

text \<open>Domain totality for ALL policies, generic in a smallness witness \<open>\<delta>\<close> — a pruned
  clone of @{thm [source] newdsc_domI_general} (\<open>NewDsc.thy\<close>). The measure is
  identical (\<open>mu \<delta> a b\<close>); the guards only redirect a node from an accept branch to
  the bisection branch, which shrinks the measure just as hard (halving), so nothing
  in the well-foundedness argument changes. The two accept cases still use
  @{thm [source] try_blocks_SomeD}/@{thm [source] try_newton_SomeD} at \<open>N = N_of e\<close>
  (a guarded \<open>Some\<close> forces the guard true, so the raw try equals it).\<close>

lemma newdsc_pol_domI_general:
  fixes \<delta> :: real and p :: nat and P :: "real poly" and pol :: newton_pol_real
  assumes \<delta>_pos: "\<delta> > 0"
    and small: "\<And>a b. a < b \<Longrightarrow> b - a \<le> \<delta> \<Longrightarrow> Bernstein_changes p a b P \<le> 1"
  shows "\<And>a b e dk s. a < b \<Longrightarrow> newdsc_pol_dom (pol, p, a, b, e, dk, s, P)"
proof -
  define \<mu> where "\<mu> = (\<lambda>a b. mu \<delta> a b)"
  let ?Prop =
    "\<lambda>n::nat. \<forall>a b e dk s. \<mu> a b < n \<longrightarrow> a < b \<longrightarrow> newdsc_pol_dom (pol, p, a, b, e, dk, s, P)"

  have step: "\<And>n. (\<And>m. m < n \<Longrightarrow> ?Prop m) \<Longrightarrow> ?Prop n"
  proof -
    fix n
    assume IH: "\<And>m. m < n \<Longrightarrow> ?Prop m"
    show "?Prop n"
    proof (intro allI impI)
      fix a b :: real and e dk s :: nat
      assume mu_lt_n: "\<mu> a b < n"
        and ab: "a < b"
      show "newdsc_pol_dom (pol, p, a, b, e, dk, s, P)"
      proof -
        let ?v = "Bernstein_changes p a b P"
        let ?gb = "fst (pol p a b e dk (s, ?v))"
        let ?gn = "snd (pol p a b e dk (s, ?v))"
        show ?thesis
        proof (cases "?v = 0 \<or> ?v = 1")
          case True
          then show ?thesis
            by (auto intro: newdsc_pol.domintros)
        next
          case False
          have v_ge2: "2 \<le> ?v"
            using False Bernstein_changes_def by fastforce

          have \<delta>_lt_width: "\<delta> < b - a"
          proof (rule ccontr)
            assume "\<not> \<delta> < b - a"
            then have "b - a \<le> \<delta>" by linarith
            then have "Bernstein_changes p a b P \<le> 1"
              using ab small by presburger
            with v_ge2 show False by linarith
          qed

          have IH_at_mu: "?Prop (\<mu> a b)"
            using IH mu_lt_n by simp

          have Nof_pos: "N_of e > 0" using N_of_ge_2[of e] by simp

          have block_case:
            "\<forall>I. try_blocks_g ?gb p a b (N_of e) P ?v = Some I
                 \<longrightarrow> newdsc_pol_dom (pol, p, fst I, snd I, e + 1, dk + (2 ^ e + 2), s, P)"
          proof (intro allI impI)
            fix I
            assume TBg: "try_blocks_g ?gb p a b (N_of e) P ?v = Some I"
            have TB: "try_blocks p a b (N_of e) P ?v = Some I"
              using TBg by (simp add: try_blocks_g_def split: if_split_asm)
            have width_I: "snd I - fst I = (b - a) / of_nat (N_of e)"
              using try_blocks_SomeD(3)[OF TB Nof_pos ab] by simp
            have mu_less: "\<mu> (fst I) (snd I) < \<mu> a b"
              using \<delta>_pos ab \<delta>_lt_width N_of_ge_2[of e] width_I
              by (simp add: \<mu>_def mu_subinterval_factor_strict)
            have fst_lt_snd: "fst I < snd I"
              by (metis Nof_pos ab diff_gt_0_iff_gt divide_pos_pos of_nat_0_less_iff width_I)
            show "newdsc_pol_dom (pol, p, fst I, snd I, e + 1, dk + (2 ^ e + 2), s, P)"
              using IH_at_mu mu_less fst_lt_snd by blast
          qed

          have newton_case:
            "\<forall>I. try_newton_g ?gn p a b (N_of e) P ?v = Some I \<longrightarrow>
                 newdsc_pol_dom (pol, p, fst I, snd I, e + 1, dk + (2 ^ e + 2), s, P)"
          proof (intro allI impI)
            fix I
            assume TNg: "try_newton_g ?gn p a b (N_of e) P ?v = Some I"
            have TN: "try_newton p a b (N_of e) P ?v = Some I"
              using TNg by (simp add: try_newton_g_def split: if_split_asm)
            have width_I: "snd I - fst I = (b - a) / of_nat (N_of e)"
              using try_newton_SomeD(3)[OF TN ab Nof_pos] by (simp add: Let_def)
            have mu_less: "\<mu> (fst I) (snd I) < \<mu> a b"
              using \<delta>_pos ab \<delta>_lt_width N_of_ge_2[of e] width_I
              by (simp add: \<mu>_def mu_subinterval_factor_strict)
            have fst_lt_snd: "fst I < snd I"
              by (metis Nof_pos ab diff_gt_0_iff_gt divide_pos_pos of_nat_0_less_iff width_I)
            show "newdsc_pol_dom (pol, p, fst I, snd I, e + 1, dk + (2 ^ e + 2), s, P)"
              using IH_at_mu mu_less fst_lt_snd by blast
          qed

          define m where "m = (a + b) / 2"
          have am: "a < m" and mb: "m < b" using ab by (simp_all add: m_def)
          have mu_left_strict: "\<mu> a m < \<mu> a b"
            by (simp add: \<mu>_def \<delta>_pos \<delta>_lt_width ab m_def mu_halve_strict(1))
          have mu_right_strict: "\<mu> m b < \<mu> a b"
            by (simp add: \<mu>_def \<delta>_pos \<delta>_lt_width ab m_def mu_halve_strict(2))
          have IH_left: "\<And>e' dk' s'. newdsc_pol_dom (pol, p, a, m, e', dk', s', P)"
            using IH_at_mu mu_left_strict am by blast
          have IH_right: "\<And>e' dk' s'. newdsc_pol_dom (pol, p, m, b, e', dk', s', P)"
            using IH_at_mu mu_right_strict mb by blast

          \<comment> \<open>The bisection children's \<open>s'\<close> is an \<open>if\<close>, so \<open>domintros\<close> now emits MORE
             subgoals than the four of the pre-\<open>s\<close> version (one per branch of the
             proper-split test), in an order that a fixed \<open>subgoal\<close> chain cannot track.
             \<open>s\<close> is inert for the domain (the measure \<open>\<mu>\<close> ignores it), so a uniform
             closer over all subgoals is both correct and robust to that shape.\<close>
          show ?thesis
            by (rule newdsc_pol.domintros)
               (use IH_left IH_right newton_case block_case in \<open>auto simp: m_def\<close>)
        qed
      qed
    qed
  qed

  have all_Prop: "\<And>n. ?Prop n"
    by (rule less_induct, rule step)

  show "\<And>a b e dk s. a < b \<Longrightarrow> newdsc_pol_dom (pol, p, a, b, e, dk, s, P)"
    using all_Prop by blast
qed

text \<open>Sanity bridge: with the all-True policy the guards
  rewrite away and the per-node recursion of @{const newdsc_pol} IS @{const newdsc}'s
  at \<open>N = N_of e\<close> (\<open>try_blocks_g True = try_blocks\<close>, \<open>Nq (N_of e) = N_of (e+1)\<close> via
  @{thm [source] N_of_Nq}, \<open>Nlin (N_of e) = N_of (max 1 (e-1))\<close> via
  @{thm [source] N_of_Nlin}).

  \<^bold>\<open>Deliberately not restated as a separate theorem.\<close> Its only purpose — catching a
  miscopied recursion in the clone — is already discharged by the three theorems
  below: \<open>newdsc_pol_sound\<close>, \<open>newdsc_pol_complete\<close> and
  \<open>newdsc_pol_terminates_squarefree\<close> all certify against the ACTUAL
  @{const newdsc_pol} definition. A standalone all-True equality would additionally
  require a PARALLEL induction over both \<open>newdsc_pol_dom\<close> and \<open>newdsc_dom\<close>, and adds
  no assurance.\<close>

text \<open>Soundness for ALL pol: every emitted interval satisfies @{const dsc_pair_ok}.
  Route: pruned clone of @{thm [source] newdsc_sound}'s induction — the emission
  certificates (\<open>v = 1\<close> payload, midpoint-root case) and the window cases'
  interval-containment facts (@{thm [source] try_blocks_SomeD}, the snap-window
  bounds) are all existing per-case lemmas in \<open>NewDsc.thy\<close>, reused verbatim; only
  the induction skeleton is rewritten with the two guarded cases.\<close>

theorem newdsc_pol_sound:
  assumes dom: "newdsc_pol_dom (pol, p, a, b, e, dk, s, P)"
      and deg: "degree P \<le> p"
      and P0:  "P \<noteq> 0"
      and ab:  "a < b"
  shows "\<forall>I \<in> set (newdsc_pol pol p a b e dk s P). dsc_pair_ok P I"
  using dom deg P0 ab
proof (induction pol p a b e dk s P rule: newdsc_pol.pinduct)
  case (1 pol p a b e dk s P)
  have newdsc_eq:
    "newdsc_pol pol p a b e dk s P =
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a, b)]
        else
          (case try_newton_g (snd (pol p a b e dk (s, v))) p a b (N_of e) P v of
             Some I \<Rightarrow> newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
           | None \<Rightarrow>
               (case try_blocks_g (fst (pol p a b e dk (s, v))) p a b (N_of e) P v of
                  Some I \<Rightarrow> newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
                | None \<Rightarrow>
                    (let m  = (a + b) / 2;
                         e' = max 1 (e - 1);
                         s' = split_run_len_real p P a b s;
                         mid_root = (if poly P m = 0 then [(m, m)] else [])
                     in mid_root @ newdsc_pol pol p a m e' (dk + 1) s' P
                               @ newdsc_pol pol p m b e' (dk + 1) s' P))))"
    using "1.hyps" newdsc_pol.psimps by blast

  show ?case
  proof -
    from 1 have ab: "a < b" and P0': "P \<noteq> 0" and deg': "degree P \<le> p"
      by blast+
    let ?v = "Bernstein_changes p a b P"
    let ?gb = "fst (pol p a b e dk (s, ?v))"
    let ?gn = "snd (pol p a b e dk (s, ?v))"

    show ?thesis
    proof (cases "?v = 0")
      case True
      then show ?thesis by (simp add: newdsc_eq Let_def)
    next
      case v0_ne: False
      show ?thesis
      proof (cases "?v = 1")
        case v1: True
        have v1_exact: "roots_in P a b = 1"
          using Bernstein_changes_1_one_root[OF deg' P0' ab v1] .
        have dsc_ok_ab: "dsc_pair_ok P (a, b)"
          using v1_exact ab by (simp add: dsc_pair_ok_def roots_in_def)
        show ?thesis using v1 v0_ne dsc_ok_ab by (simp add: newdsc_eq Let_def)
      next
        case v_ge2: False
        then have v_ge2': "?v \<ge> 2"
          using v0_ne by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)
        have Nof_pos: "N_of e > 0" using N_of_ge_2[of e] by simp

        have IH_newton:
          "\<And>I. try_newton_g ?gn p a b (N_of e) P ?v = Some I \<Longrightarrow>
                \<forall>J\<in>set (newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                   dsc_pair_ok P J"
        proof -
          fix I
          assume TNg: "try_newton_g ?gn p a b (N_of e) P ?v = Some I"
          have TN: "try_newton p a b (N_of e) P ?v = Some I"
            using TNg by (simp add: try_newton_g_def split: if_split_asm)
          have fst_lt_snd: "fst I < snd I"
          proof -
            have "snd I - fst I = (b - a) / of_nat (N_of e)"
              using try_newton_SomeD(3)[OF TN ab Nof_pos] by (simp add: Let_def)
            moreover have "(b - a) / of_nat (N_of e) > 0" using ab Nof_pos by simp
            ultimately show ?thesis by linarith
          qed
          show "\<forall>J\<in>set (newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                   dsc_pair_ok P J"
            using "1.IH"(4) TNg deg' P0' fst_lt_snd v0_ne v_ge2 by blast
        qed

        have IH_block:
          "\<And>I. \<lbrakk>try_newton_g ?gn p a b (N_of e) P ?v = None;
                  try_blocks_g ?gb p a b (N_of e) P ?v = Some I\<rbrakk> \<Longrightarrow>
                \<forall>J\<in>set (newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                   dsc_pair_ok P J"
        proof -
          fix I
          assume TN0: "try_newton_g ?gn p a b (N_of e) P ?v = None"
             and TBg: "try_blocks_g ?gb p a b (N_of e) P ?v = Some I"
          have TB: "try_blocks p a b (N_of e) P ?v = Some I"
            using TBg by (simp add: try_blocks_g_def split: if_split_asm)
          have fst_lt_snd: "fst I < snd I"
          proof -
            have "snd I - fst I = (b - a) / of_nat (N_of e)"
              using try_blocks_SomeD(3)[OF TB Nof_pos ab] by simp
            moreover have "(b - a) / of_nat (N_of e) > 0" using ab Nof_pos by simp
            ultimately show ?thesis by linarith
          qed
          show "\<forall>J\<in>set (newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                   dsc_pair_ok P J"
            using "1.IH"(3) TN0 TBg deg' P0' fst_lt_snd v0_ne v_ge2 by blast
        qed

        have IH_LR:
          "\<And>m e' s'.
             \<lbrakk>try_newton_g ?gn p a b (N_of e) P ?v = None;
              try_blocks_g ?gb p a b (N_of e) P ?v = None;
              m = (a + b) / 2; e' = max 1 (e - 1);
              s' = split_run_len_real p P a b s\<rbrakk> \<Longrightarrow>
             (\<forall>I\<in>set (newdsc_pol pol p a m e' (dk + 1) s' P). dsc_pair_ok P I) \<and>
             (\<forall>I\<in>set (newdsc_pol pol p m b e' (dk + 1) s' P). dsc_pair_ok P I)"
        proof -
          fix m e' s'
          assume TN0: "try_newton_g ?gn p a b (N_of e) P ?v = None"
             and TB0: "try_blocks_g ?gb p a b (N_of e) P ?v = None"
             and m_def: "m = (a + b) / 2"
             and e'_def: "e' = max 1 (e - 1)"
             and s'_def: "s' = split_run_len_real p P a b s"
          have IH_left: "\<forall>I\<in>set (newdsc_pol pol p a m e' (dk + 1) s' P). dsc_pair_ok P I"
            using "1.IH"(1) deg' v0_ne v_ge2 TN0 TB0 m_def e'_def s'_def P0' ab
            by (metis field_less_half_sum)
          have IH_right: "\<forall>I\<in>set (newdsc_pol pol p m b e' (dk + 1) s' P). dsc_pair_ok P I"
            using "1.IH"(2) deg' v0_ne v_ge2 TN0 TB0 m_def e'_def s'_def P0' ab
            by (metis gt_half_sum one_add_one)
          show "(\<forall>I\<in>set (newdsc_pol pol p a m e' (dk + 1) s' P). dsc_pair_ok P I) \<and>
                (\<forall>I\<in>set (newdsc_pol pol p m b e' (dk + 1) s' P). dsc_pair_ok P I)"
            using IH_left IH_right by simp
        qed

        show ?thesis
        proof (cases "try_newton_g ?gn p a b (N_of e) P ?v")
          case (Some I)
          then have "\<forall>J\<in>set (newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                        dsc_pair_ok P J"
            using IH_newton by blast
          thus ?thesis using Some v0_ne v_ge2 by (simp add: newdsc_eq Let_def)
        next
          case TN_None: None
          show ?thesis
          proof (cases "try_blocks_g ?gb p a b (N_of e) P ?v")
            case (Some I)
            then have "\<forall>J\<in>set (newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                          dsc_pair_ok P J"
              using IH_block TN_None by blast
            thus ?thesis using TN_None Some v0_ne v_ge2 by (simp add: newdsc_eq Let_def)
          next
            case TB_None: None
            let ?m = "(a + b) / 2"
            let ?e' = "max 1 (e - 1)"
            let ?s' = "split_run_len_real p P a b s"
            from IH_LR[OF TN_None TB_None refl refl refl]
            have left_ok:  "\<forall>I\<in>set (newdsc_pol pol p a ?m ?e' (dk + 1) ?s' P). dsc_pair_ok P I"
              and right_ok: "\<forall>I\<in>set (newdsc_pol pol p ?m b ?e' (dk + 1) ?s' P). dsc_pair_ok P I"
              by auto
            have mid_ok:
              "\<forall>I\<in>set (if poly P ?m = 0 then [(?m, ?m)] else []). dsc_pair_ok P I"
            proof (cases "poly P ?m = 0")
              case True
              then have "set (if poly P ?m = 0 then [(?m, ?m)] else []) = {(?m, ?m)}" by auto
              moreover have "dsc_pair_ok P (?m, ?m)"
                using True by (simp add: dsc_pair_ok_def)
              ultimately show ?thesis by auto
            next
              case False then show ?thesis by (simp add: dsc_pair_ok_def)
            qed
            show ?thesis
              using newdsc_eq TB_None TN_None v0_ne v_ge2 left_ok right_ok mid_ok
              by (auto simp: Let_def)
          qed
        qed
      qed
    qed
  qed
qed

text \<open>Completeness for ALL pol: every root in \<open>(a, b)\<close> is covered. The only step
  that discards territory is window acceptance, whose \<open>v_window = v\<close> test
  preserves every root (the acceptance payloads inside @{thm [source]
  newdsc_complete}'s induction — reused); bisection covers \<open>(a,m) \<union> {m} \<union> (m,b)\<close>.
  Pruned clone again.\<close>

theorem newdsc_pol_complete:
  assumes dom: "newdsc_pol_dom (pol, p, a, b, e, dk, s, P)"
      and deg: "degree P \<le> p"
      and P0:  "P \<noteq> 0"
  shows "\<And>x. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
           (\<exists>I \<in> set (newdsc_pol pol p a b e dk s P). fst I \<le> x \<and> x \<le> snd I)"
  using dom deg P0
proof (induction pol p a b e dk s P rule: newdsc_pol.pinduct)
  case (1 pol p a b e dk s P)
  have newdsc_eq:
    "newdsc_pol pol p a b e dk s P =
       (let v = Bernstein_changes p a b P in
        if v = 0 then []
        else if v = 1 then [(a, b)]
        else
          (case try_newton_g (snd (pol p a b e dk (s, v))) p a b (N_of e) P v of
             Some I \<Rightarrow> newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
           | None \<Rightarrow>
               (case try_blocks_g (fst (pol p a b e dk (s, v))) p a b (N_of e) P v of
                  Some I \<Rightarrow> newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P
                | None \<Rightarrow>
                    (let m  = (a + b) / 2;
                         e' = max 1 (e - 1);
                         s' = split_run_len_real p P a b s;
                         mid_root = (if poly P m = 0 then [(m, m)] else [])
                     in mid_root @ newdsc_pol pol p a m e' (dk + 1) s' P
                               @ newdsc_pol pol p m b e' (dk + 1) s' P))))"
    using "1.hyps" newdsc_pol.psimps by blast

  show ?case
  proof -
    have H:
      "\<And>x::real. poly P x = 0 \<Longrightarrow> a < x \<Longrightarrow> x < b \<Longrightarrow>
             (\<exists>I\<in>set (newdsc_pol pol p a b e dk s P). fst I \<le> x \<and> x \<le> snd I)"
    proof -
      fix x :: real
      assume root: "poly P x = 0" and ax: "a < x" and xb: "x < b"
      show "\<exists>I\<in>set (newdsc_pol pol p a b e dk s P). fst I \<le> x \<and> x \<le> snd I"
      proof (cases "a \<ge> b \<or> P = 0")
        case True
        from True ax xb have False using "1.prems" by argo
        then show ?thesis by blast
      next
        case False
        hence ab: "a < b" and P0': "P \<noteq> 0" by auto
        from 1 have deg': "degree P \<le> p" by blast
        let ?v = "Bernstein_changes p a b P"
        let ?gb = "fst (pol p a b e dk (s, ?v))"
        let ?gn = "snd (pol p a b e dk (s, ?v))"
        have Nof_pos: "N_of e > 0" using N_of_ge_2[of e] by simp

        have v_nonzero: "?v \<noteq> 0"
        proof
          assume "?v = 0"
          then have "roots_in P a b = 0"
            using Bernstein_changes_0_no_root[OF deg' P0' ab] by simp
          then have "poly P x \<noteq> 0"
            using ax xb Bernstein_changes_pos_of_root P0' \<open>?v = 0\<close> ab deg' by blast
          with root show False by simp
        qed

        show ?thesis
        proof (cases "?v = 1")
          case v1: True
          have mem: "(a,b) \<in> set (newdsc_pol pol p a b e dk s P)"
            using newdsc_eq v1 v_nonzero by (simp add: Let_def)
          show ?thesis
          proof (intro bexI[of _ "(a,b)"])
            show "fst (a,b) \<le> x \<and> x \<le> snd (a,b)" using ax xb by simp
          next
            show "(a,b) \<in> set (newdsc_pol pol p a b e dk s P)" using mem .
          qed
        next
          case v_ne1: False
          hence v_ge2: "?v \<ge> 2"
            using v_nonzero by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)

          have IH_newton:
            "\<And>I x. \<lbrakk> try_newton_g ?gn p a b (N_of e) P ?v = Some I;
                       poly P x = 0; fst I < x; x < snd I \<rbrakk> \<Longrightarrow>
                   \<exists>J\<in>set (newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                      fst J \<le> x \<and> x \<le> snd J"
            using "1.IH"(4) deg' v_ne1 v_nonzero P0' by presburger

          have IH_block:
            "\<And>I x. \<lbrakk> try_newton_g ?gn p a b (N_of e) P ?v = None;
                       try_blocks_g ?gb p a b (N_of e) P ?v = Some I;
                       poly P x = 0; fst I < x; x < snd I \<rbrakk> \<Longrightarrow>
                   \<exists>J\<in>set (newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P).
                      fst J \<le> x \<and> x \<le> snd J"
            using "1.IH"(3) deg' v_ne1 v_nonzero P0' by presburger

          have IH_LR:
            "\<And>m e' s' x.
               \<lbrakk> try_newton_g ?gn p a b (N_of e) P ?v = None;
                  try_blocks_g ?gb p a b (N_of e) P ?v = None;
                  m = (a + b) / 2; e' = max 1 (e - 1);
                  s' = split_run_len_real p P a b s;
                  poly P x = 0; a < x; x < b \<rbrakk> \<Longrightarrow>
               (\<exists>I\<in>set (newdsc_pol pol p a m e' (dk + 1) s' P). fst I \<le> x \<and> x \<le> snd I) \<or>
               (\<exists>I\<in>set (newdsc_pol pol p m b e' (dk + 1) s' P). fst I \<le> x \<and> x \<le> snd I) \<or>
               (x = m)"
          proof -
            fix m e' s' x
            assume TB0: "try_blocks_g ?gb p a b (N_of e) P ?v = None"
               and TN0: "try_newton_g ?gn p a b (N_of e) P ?v = None"
               and m_def: "m = (a + b) / 2"
               and e'_def: "e' = max 1 (e - 1)"
               and s'_def: "s' = split_run_len_real p P a b s"
               and rootx: "poly P x = 0" and ax': "a < x" and xb': "x < b"
            have am: "a < m" and mb: "m < b" using ab by (simp_all add: m_def)
            show "(\<exists>I\<in>set (newdsc_pol pol p a m e' (dk + 1) s' P). fst I \<le> x \<and> x \<le> snd I) \<or>
                  (\<exists>I\<in>set (newdsc_pol pol p m b e' (dk + 1) s' P). fst I \<le> x \<and> x \<le> snd I) \<or> x = m"
            proof (cases "x < m")
              case True
              then have "a < x" "x < m" using ax' xb' am by auto
              then have "\<exists>I\<in>set (newdsc_pol pol p a m e' (dk + 1) s' P). fst I \<le> x \<and> x \<le> snd I"
                using "1.IH"(1) deg' v_ne1 v_nonzero TB0 TN0 m_def e'_def s'_def rootx P0' by blast
              then show ?thesis by blast
            next
              case False
              then consider "x = m" | "x > m" by linarith
              then show ?thesis
              proof cases
                case 1 then show ?thesis by blast
              next
                case 2
                then have "m < x" "x < b" using xb' mb by auto
                then have "\<exists>I\<in>set (newdsc_pol pol p m b e' (dk + 1) s' P). fst I \<le> x \<and> x \<le> snd I"
                  using "1.IH"(2) e'_def s'_def P0' TB0 TN0 ab deg' m_def rootx v_ne1 v_nonzero by blast
                then show ?thesis by blast
              qed
            qed
          qed

        show ?thesis
        proof (cases "try_newton_g ?gn p a b (N_of e) P ?v")
              case (Some I)
              then have TNg: "try_newton_g ?gn p a b (N_of e) P ?v = Some I" by simp
              have TN: "try_newton p a b (N_of e) P ?v = Some I"
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
                have v_I: "Bernstein_changes p (fst I) (snd I) P = ?v"
                  using TN unfolding try_newton_def Let_def
                  by (auto split: option.split_asm if_split_asm)
                have not_left: "\<not> (x < fst I)"
                proof
                  assume "x < fst I"
                  hence "a < x" "x < fst I" using ax by simp_all
                  hence "Bernstein_changes p a (fst I) P \<ge> 1"
                    using Bernstein_changes_pos_of_root[OF deg' P0' _ root]
                    by (smt (verit, ccfv_threshold) Bernstein_changes_def int_nat_eq)
                  have "Bernstein_changes p a b P \<ge>
                        Bernstein_changes p a (fst I) P + Bernstein_changes p (fst I) b P"
                    using Bernstein_changes_split[OF _ _ deg'] I_props \<open>a < x\<close> \<open>x < fst I\<close> split_props by simp
                  moreover have "Bernstein_changes p (fst I) b P \<ge> Bernstein_changes p (fst I) (snd I) P"
                    using Bernstein_changes_split[OF split_props _ deg'] I_props
                    by (smt (verit) Bernstein_changes_def int_nat_eq)
                  ultimately have "?v \<ge> 1 + ?v"
                    using v_I \<open>1 \<le> Bernstein_changes p a (fst I) P\<close> by linarith
                  thus False by simp
                qed
                have not_right: "\<not> (x > snd I)"
                proof
                  assume "x > snd I"
                  hence "snd I < x" "x < b" using xb by simp_all
                  hence "Bernstein_changes p (snd I) b P \<ge> 1"
                    using Bernstein_changes_pos_of_root[OF deg' P0' _ root]
                    by (metis Bernstein_changes_def I_props add_0 dual_order.order_iff_strict
                        int_one_le_iff_zero_less not_less_iff_gr_or_eq zle_iff_zadd)
                  have "Bernstein_changes p a b P \<ge>
                        Bernstein_changes p a (snd I) P + Bernstein_changes p (snd I) b P"
                    using Bernstein_changes_split[OF _ _ deg'] I_props \<open>snd I < x\<close> \<open>x < b\<close> split_props by simp
                  moreover have "Bernstein_changes p a (snd I) P \<ge> Bernstein_changes p (fst I) (snd I) P"
                    using Bernstein_changes_split[OF _ split_props deg'] I_props split_props
                    by (smt (verit, ccfv_SIG) Bernstein_changes_def int_nat_eq)
                  ultimately have "?v \<ge> ?v + 1"
                    using v_I \<open>1 \<le> Bernstein_changes p (snd I) b P\<close> by linarith
                  thus False by simp
                qed
                have "x \<noteq> fst I"
                proof
                  assume "x = fst I"
                  then have "poly P (fst I) = 0" using root by simp
                  have "Bernstein_changes p a (fst I) P + Bernstein_changes p (fst I) b P + 1
                        \<le> Bernstein_changes p a b P"
                    using Bernstein_changes_split_root \<open>x = fst I\<close> ax deg' root xb P0' by blast
                  moreover have "Bernstein_changes p (fst I) b P \<ge> ?v"
                  proof -
                    have "Bernstein_changes p (fst I) b P =
                          Bernstein_changes p (fst I) (snd I) P + Bernstein_changes p (snd I) b P"
                      using Bernstein_changes_split[OF split_props _ deg'] I_props
                      by (smt (verit, ccfv_SIG) Bernstein_changes_def calculation of_nat_0_le_iff v_I)
                    show ?thesis using Bernstein_changes_split[OF split_props _ deg'] I_props v_I
                      by (metis Bernstein_changes_def
                          \<open>Bernstein_changes p (fst I) b P = Bernstein_changes p (fst I) (snd I) P + Bernstein_changes p (snd I) b P\<close>
                          zle_iff_zadd)
                  qed
                  ultimately have "0 + ?v + 1 \<le> ?v"
                    using Bernstein_changes_split[OF _ _ deg'] I_props
                    by (smt (verit, ccfv_threshold) Bernstein_changes_def of_nat_0_le_iff)
                  thus False by simp
                qed
                have "x \<noteq> snd I"
                proof
                  assume "x = snd I"
                  then have "poly P (snd I) = 0" using root by simp
                  have "Bernstein_changes p a (snd I) P + Bernstein_changes p (snd I) b P + 1
                        \<le> Bernstein_changes p a b P"
                    using Bernstein_changes_split_root \<open>x = snd I\<close> ax deg' xb \<open>poly P (snd I) = 0\<close> P0'
                    by blast
                  moreover have "Bernstein_changes p a (snd I) P \<ge> ?v"
                    using Bernstein_changes_split[OF _ split_props deg'] I_props v_I
                    by (metis Bernstein_changes_def \<open>x = snd I\<close> add.commute
                        dual_order.order_iff_strict dual_order.trans zle_iff_zadd)
                  ultimately have "?v + 0 + 1 \<le> ?v"
                    by (smt (verit, ccfv_SIG) Bernstein_changes_def int_nat_eq)
                  thus False by simp
                qed
                show "fst I < x \<and> x < snd I"
                  using not_left not_right \<open>x \<noteq> fst I\<close> \<open>x \<noteq> snd I\<close> linorder_less_linear by blast
              qed
              then have fstI_lt: "fst I < x" and x_lt_sndI: "x < snd I" by auto
              from IH_newton[OF TNg root fstI_lt x_lt_sndI]
              obtain J where J_in: "J \<in> set (newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P)"
                            and J_cov: "fst J \<le> x \<and> x \<le> snd J" by blast
              have "newdsc_pol pol p a b e dk s P
                      = newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P"
                using newdsc_eq Some v_ne1 v_nonzero by (simp add: Let_def)
              then show ?thesis using J_in J_cov by auto
        next
          case TN_None: None
          show ?thesis
          proof (cases "try_blocks_g ?gb p a b (N_of e) P ?v")
            case (Some I)
            then have TBg: "try_blocks_g ?gb p a b (N_of e) P ?v = Some I" by simp
            have TB: "try_blocks p a b (N_of e) P ?v = Some I"
              using TBg by (simp add: try_blocks_g_def split: if_split_asm)
            have pos_in_I: "fst I < x \<and> x < snd I"
            proof -
              define w where "w = b - a"
              have "w > 0" using ab w_def by simp
              have I_props: "fst I \<ge> a \<and> snd I \<le> b \<and> snd I - fst I = w / of_nat (N_of e)"
                using TB Nof_pos ab try_blocks_SomeD(1,2,3) w_def by presburger
              then have fst_le_snd: "fst I < snd I"
                using Nof_pos \<open>0 < w\<close> diff_gt_0_iff_gt by fastforce
              have v_I: "Bernstein_changes p (fst I) (snd I) P = ?v"
                using TB unfolding try_blocks_def Let_def by (auto split: if_split_asm)
              have "x \<noteq> snd I"
              proof
                assume "x = snd I"
                then have "poly P (snd I) = 0" using root by simp
                have "Bernstein_changes p a (snd I) P + Bernstein_changes p (snd I) b P + 1
                        \<le> Bernstein_changes p a b P"
                  using Bernstein_changes_split_root \<open>poly P (snd I) = 0\<close> \<open>x = snd I\<close> ax deg' xb P0'
                  by blast
                moreover have "Bernstein_changes p a (snd I) P = ?v"
                  by (smt (verit, del_insts) TB fst_conv option.inject option.simps(3) snd_conv
                      try_blocks_def)
                ultimately have "?v + 0 + 1 \<le> ?v"
                  by (smt (verit) Bernstein_changes_def int_nat_eq)
                thus False by simp
              qed
              have "x \<noteq> fst I"
              proof
                assume "x = fst I"
                then have "poly P (fst I) = 0" using root by simp
                have "Bernstein_changes p a (fst I) P + Bernstein_changes p (fst I) b P + 1
                        \<le> Bernstein_changes p a b P"
                  using Bernstein_changes_split_root \<open>x = fst I\<close> ax deg' root xb P0' by blast
                moreover have "Bernstein_changes p (fst I) b P = ?v"
                  by (smt (verit, ccfv_threshold) I_props TB fst_conv option.distinct(1) option.inject
                      try_blocks_def w_def)
                ultimately have "?v + 0 + 1 \<le> ?v"
                  by (smt (verit) Bernstein_changes_def int_nat_eq)
                thus False by simp
              qed
              have not_left: "\<not> x < fst I"
              proof
                assume "x < fst I"
                hence "a < x" "x < fst I" using ax by simp_all
                hence "Bernstein_changes p a (fst I) P > 0"
                  using Bernstein_changes_pos_of_root[OF deg' P0' _ root]
                  by (metis Bernstein_changes_def I_props(1) dual_order.order_iff_strict int_nat_eq
                      order_less_asym')
                hence "Bernstein_changes p a (fst I) P \<ge> 1" by simp
                have "Bernstein_changes p a b P \<ge>
                      Bernstein_changes p a (fst I) P + Bernstein_changes p (fst I) b P"
                  using Bernstein_changes_split[of a "fst I" b] ab I_props \<open>a < x\<close> \<open>x < fst I\<close> deg' fst_le_snd by auto
                moreover have "Bernstein_changes p (fst I) b P \<ge>
                               Bernstein_changes p (fst I) (snd I) P"
                  using Bernstein_changes_split[of "fst I" "snd I" b] I_props fst_le_snd
                  by (smt (verit, del_insts) Bernstein_changes_def deg' int_nat_eq)
                then have "?v \<ge> 1 + ?v"
                  using v_I \<open>1 \<le> Bernstein_changes p a (fst I) P\<close> calculation by auto
                thus False by simp
              qed
              have not_right: "\<not> x > snd I"
              proof
                assume "x > snd I"
                hence "snd I < x" "x < b" using xb by simp_all
                hence "Bernstein_changes p (snd I) b P \<ge> 1"
                  using Bernstein_changes_pos_of_root[OF deg' P0' _ root]
                  by (metis Bernstein_changes_def I_props Orderings.order_eq_iff int_nat_eq
                      int_one_le_iff_zero_less not_le_imp_less not_less_iff_gr_or_eq)
                have "Bernstein_changes p a b P \<ge>
                      Bernstein_changes p a (snd I) P + Bernstein_changes p (snd I) b P"
                  using Bernstein_changes_split[of a "snd I" b] ab I_props \<open>snd I < x\<close> deg' fst_le_snd xb by force
                moreover have "Bernstein_changes p a (snd I) P \<ge>
                               Bernstein_changes p (fst I) (snd I) P"
                  using Bernstein_changes_split[of a "fst I" "snd I"] I_props fst_le_snd
                  by (smt (verit, best) TB fst_conv option.inject option.simps(3) try_blocks_def w_def)
                ultimately have "?v \<ge> ?v + 1"
                  using v_I \<open>1 \<le> Bernstein_changes p (snd I) b P\<close> by linarith
                thus False by simp
              qed
              show "fst I < x \<and> x < snd I"
                using not_left not_right \<open>x \<noteq> fst I\<close> \<open>x \<noteq> snd I\<close> linorder_less_linear by blast
            qed
            then have fstI_lt: "fst I < x" and x_lt_sndI: "x < snd I" by auto
            from IH_block[OF TN_None TBg root fstI_lt x_lt_sndI]
            obtain J where J_in: "J \<in> set (newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P)"
                          and J_cov: "fst J \<le> x \<and> x \<le> snd J" by blast
            have "newdsc_pol pol p a b e dk s P
                    = newdsc_pol pol p (fst I) (snd I) (e + 1) (dk + (2 ^ e + 2)) s P"
              using newdsc_eq TN_None Some v_ne1 v_nonzero by (simp add: Let_def)
            then show ?thesis using J_in J_cov by auto
          next
            case TB_None: None
              define m where "m = (a + b) / 2"
              define e' where "e' = max 1 (e - 1)"
              define s' where "s' = split_run_len_real p P a b s"
              have split:
                "(\<exists>I\<in>set (newdsc_pol pol p a m e' (dk + 1) s' P). fst I \<le> x \<and> x \<le> snd I) \<or>
                 (\<exists>I\<in>set (newdsc_pol pol p m b e' (dk + 1) s' P). fst I \<le> x \<and> x \<le> snd I) \<or> x = m"
                using IH_LR[OF TN_None TB_None m_def e'_def s'_def root ax xb] .
              have eq_lin:
                "newdsc_pol pol p a b e dk s P =
                   (if poly P m = 0 then [(m, m)] else [])
                   @ newdsc_pol pol p a m e' (dk + 1) s' P
                   @ newdsc_pol pol p m b e' (dk + 1) s' P"
                using newdsc_eq TN_None TB_None v_ne1 v_nonzero
                by (simp add: Let_def m_def e'_def s'_def)
              from split show ?thesis
              proof (elim disjE)
                assume "\<exists>I\<in>set (newdsc_pol pol p a m e' (dk + 1) s' P). fst I \<le> x \<and> x \<le> snd I"
                then show ?thesis using eq_lin by auto
              next
                assume "\<exists>I\<in>set (newdsc_pol pol p m b e' (dk + 1) s' P). fst I \<le> x \<and> x \<le> snd I"
                then show ?thesis using eq_lin by auto
              next
                assume mid: "x = m"
                then have "poly P m = 0" using root by blast
                then have memm: "(m, m) \<in> set (newdsc_pol pol p a b e dk s P)" using eq_lin by simp
                show ?thesis
                proof (intro bexI[of _ "(m,m)"])
                  show "fst (m,m) \<le> x \<and> x \<le> snd (m,m)" using mid by simp
                next
                  show "(m,m) \<in> set (newdsc_pol pol p a b e dk s P)" using memm .
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

text \<open>Termination for ALL pol on squarefree input: instantiate
  @{thm [source] newdsc_pol_domI_general} with the squarefree smallness witness
  \<open>delta_P P\<close> — exactly as @{thm [source] newdsc_terminates_squarefree} does for the
  N-form. No \<open>e\<close> lower bound is needed (@{thm [source] N_of_ge_2}).\<close>

theorem newdsc_pol_terminates_squarefree:
  fixes P :: "real poly"
  assumes P0:  "P \<noteq> 0"
      and deg: "degree P \<le> p"
      and p0:  "p \<noteq> 0"
      and sf:  "square_free P"
  shows "\<And>a b e dk s. a < b \<Longrightarrow> newdsc_pol_dom (pol, p, a, b, e, dk, s, P)"
proof -
  have \<delta>_pos: "delta_P P > 0"
    using P0 delta_P_pos by blast
  have small:
    "\<And>a b. a < b \<Longrightarrow> b - a \<le> delta_P P \<Longrightarrow> Bernstein_changes p a b P \<le> 1"
    using Bernstein_changes_small_interval_le_1 P0 deg p0 sf rsquarefree_lift by blast
  show "\<And>a b e dk s. a < b \<Longrightarrow> newdsc_pol_dom (pol, p, a, b, e, dk, s, P)"
    using newdsc_pol_domI_general[OF \<delta>_pos small] by blast
qed

section \<open>The policy-parameterized recursion, rational worklist level\<close>

text \<open>Clone of @{const newdsc_main_int} (\<open>Dsc_Int.thy\<close>) with the guards and the
  \<open>dk\<close> tag. LIFO worklist, tailrec — the shape the carried GMP loop refines
  (order-agnostic multiset accounting, exactly like the existing carried chain
  against @{const dsc_main_int}).\<close>

partial_function (tailrec) newdsc_pol_main_int ::
  "newton_pol_node \<Rightarrow> int poly \<Rightarrow> (rat \<times> rat \<times> nat \<times> nat \<times> nat) list \<Rightarrow> (rat \<times> rat) list
     \<Rightarrow> (rat \<times> rat) list"
where
  [code]:
  "newdsc_pol_main_int pol P todo acc =
     (case todo of
        [] \<Rightarrow> acc
      | (a, b, e, dk, s) # todo' \<Rightarrow>
          (let v = descartes_list_int a b (coeffs P) in
           if v = 0 then
             newdsc_pol_main_int pol P todo' acc
           else if v = 1 then
             newdsc_pol_main_int pol P todo' ((a, b) # acc)
           else
             (case try_newton_int_g (snd (pol a b e dk (s, v))) a b (N_of e) P v of
                Some I \<Rightarrow>
                  newdsc_pol_main_int pol P (accept_child_int I e dk s # todo') acc
              | None \<Rightarrow>
                  (case try_blocks_int_g (fst (pol a b e dk (s, v))) a b (N_of e) P v of
                     Some I \<Rightarrow>
                       newdsc_pol_main_int pol P (accept_child_int I e dk s # todo') acc
                   | None \<Rightarrow>
                       (let m  = (a + b) / 2;
                            acc' = (if poly (map_poly of_int P :: rat poly) m = 0
                                    then (m, m) # acc else acc)
                        in newdsc_pol_main_int pol P
                             (bisect_children_int P a b e dk s @ todo') acc')))))"

definition newdsc_pol_int ::
  "newton_pol \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> (rat \<times> rat) list"
where
  "newdsc_pol_int pol a b e dk P
     = newdsc_pol_main_int (pol (degree P)) P [(a, b, e, dk, 0)] []"

text \<open>Int\<leftrightarrow>real bridge (clone of @{thm [source] newdsc_int_eq_newdsc},
  \<open>Dsc_Int.thy\<close>, with the guard cases carried through). The pointwise policy
  relation \<open>polrel\<close> is discharged by the concrete policy's two definitions
  (\<open>pol_final\<close> and its real twin, \<open>Newton.thy\<close>).\<close>

text \<open>The worklist simulation: one real @{const newdsc_pol} subtree = one int
  @{const newdsc_pol_main_int} worklist step. Clone of @{thm [source]
  newdsc_main_int_sim_aux} (\<open>Dsc_Int.thy\<close>), e-form + \<open>dk\<close> tag + guards. The
  guards match on both sides via \<open>polrel\<close> (so a real-side guard equals its int-side
  twin), reducing each guarded try to the raw one already handled by the original's
  bridge lemmas (@{thm [source] try_blocks_int_Some_iff} etc.).\<close>

lemma newdsc_pol_main_int_sim_aux:
  assumes dom: "newdsc_pol_dom (polr, p, a', b', e, dk, s, P')"
    and aeq: "a' = of_rat a" and beq: "b' = of_rat b"
    and Peq: "P' = map_poly of_int P" and pdeg: "p = degree P"
    and P0: "P \<noteq> 0" and ab: "a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr p (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = nodepol a2 b2 e2 dk2 (s2, v)"
  shows
    "newdsc_pol_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
     newdsc_pol_main_int nodepol P todo
       (map real_to_rat_pair (rev (newdsc_pol polr p a' b' e dk s P')) @ acc)"
  using assms
proof (induction polr p a' b' e dk s P' arbitrary: a b todo acc rule: newdsc_pol.pinduct)
  case (1 polr p a' b' e dk s P' a b todo acc)
  have aeq: "a' = of_rat a" and beq: "b' = of_rat b" and Peq: "P' = map_poly of_int P"
    and pdeg: "p = degree P" and P0: "P \<noteq> 0" and ab: "a < b"
    and polrel: "\<And>a2 b2 e2 dk2 s2 v. polr p (of_rat a2) (of_rat b2) e2 dk2 (s2, int v)
                    = nodepol a2 b2 e2 dk2 (s2, v)"
    using "1.prems" by blast+
  let ?P_real = "map_poly of_int P :: real poly"
  let ?v = "Bernstein_changes p (of_rat a) (of_rat b) ?P_real"

  have deg_p: "degree ?P_real = p" using pdeg by simp
  have v_eq: "int (descartes_list_int a b (coeffs P)) = ?v"
    using descartes_roots_test_sc_of_int[OF \<open>a < b\<close> \<open>P \<noteq> 0\<close>]
    by (simp add: descartes_roots_test_sc_eq_Bernstein_changes deg_p pdeg)
  have vnn: "?v = int (nat ?v)" using v_eq by linarith

  \<comment> \<open>the two node guards, matched int-side vs real-side\<close>
  have pol_eq: "polr p (of_rat a) (of_rat b) e dk (s, ?v) = nodepol a b e dk (s, nat ?v)"
  proof -
    have "polr p (of_rat a) (of_rat b) e dk (s, ?v)
            = polr p (of_rat a) (of_rat b) e dk (s, int (nat ?v))" using vnn by simp
    also have "\<dots> = nodepol a b e dk (s, nat ?v)" using polrel by blast
    finally show ?thesis .
  qed
  have gb_eq: "fst (polr p (of_rat a) (of_rat b) e dk (s, ?v))
                 = fst (nodepol a b e dk (s, nat ?v))" using pol_eq by simp
  have gn_eq: "snd (polr p (of_rat a) (of_rat b) e dk (s, ?v))
                 = snd (nodepol a b e dk (s, nat ?v))" using pol_eq by simp
  let ?gb = "fst (nodepol a b e dk (s, nat ?v))"
  let ?gn = "snd (nodepol a b e dk (s, nat ?v))"

  have Npos: "N_of e > 0" using N_of_ge_2[of e] by simp
  have N2: "N_of e \<ge> 2" using N_of_ge_2 by simp
  have ab_real: "((of_rat a)::real) < of_rat b" using ab by (simp add: of_rat_less)

  show ?case
  proof (cases "?v = 0")
    case v0: True
    have nd0: "newdsc_pol polr p a' b' e dk s P' = []"
      using "1.hyps" aeq beq Peq v0 newdsc_pol.psimps by fastforce
    show ?thesis
      using nd0 newdsc_pol_main_int.simps Let_def v0 v_eq aeq beq Peq by auto
  next
    case v0: False
    show ?thesis
    proof (cases "?v = 1")
      case v1: True
      have nd1: "newdsc_pol polr p a' b' e dk s P' = [(a', b')]"
        using "1.hyps" aeq beq Peq v1 v0 newdsc_pol.psimps by fastforce
      show ?thesis
        using nd1 newdsc_pol_main_int.simps Let_def v0 v1 v_eq aeq beq Peq by auto
    next
      case v1: False
      have v_nat_eq: "descartes_list_int a b (coeffs P) = nat ?v" using v_eq by linarith
      have v_neq_0: "descartes_list_int a b (coeffs P) \<noteq> 0" using v0 v_eq by auto
      have v_neq_1: "descartes_list_int a b (coeffs P) \<noteq> 1" using v1 v_eq by auto

      show ?thesis
      proof (cases "try_newton_int_g ?gn a b (N_of e) P (nat ?v)")
        case (Some I_rat)
          have gnT: "?gn = True" and TNi: "try_newton_int a b (N_of e) P (nat ?v) = Some I_rat"
            using Some by (auto simp: try_newton_int_g_def split: if_split_asm)
          let ?I_real = "(real_of_rat (fst I_rat), real_of_rat (snd I_rat))"
          have TN_real: "try_newton p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = Some ?I_real"
            using try_newton_int_Some_iff[OF ab P0 Npos deg_p[symmetric]] TNi vnn by simp
          have TNg_real: "try_newton_g (snd (polr p (of_rat a) (of_rat b) e dk (s, ?v)))
                            p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = Some ?I_real"
            using TN_real gn_eq gnT by (simp add: try_newton_g_def)

          have nd_newton:
            "newdsc_pol polr p a' b' e dk s P'
               = newdsc_pol polr p (fst ?I_real) (snd ?I_real) (e + 1) (dk + (2 ^ e + 2)) s P'"
            using "1.hyps" aeq beq Peq v0 v1 TNg_real newdsc_pol.psimps by fastforce

          have main_newton:
            "newdsc_pol_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
             newdsc_pol_main_int nodepol P ((fst I_rat, snd I_rat, e + 1, dk + (2 ^ e + 2), s) # todo) acc"
            apply (subst newdsc_pol_main_int.simps)
            using v_neq_0 v_neq_1 Some v_nat_eq
            by (auto simp add: Let_def accept_child_int_def)

          have "fst ?I_real < snd ?I_real"
            using try_newton_Some_fst_lt_snd[OF TN_real ab_real N2] by simp
          hence rat_lt: "fst I_rat < snd I_rat" using of_rat_less by auto

          have stepI:
            "newdsc_pol_main_int nodepol P ((fst I_rat, snd I_rat, e + 1, dk + (2 ^ e + 2), s) # todo) acc =
             newdsc_pol_main_int nodepol P todo
               (map real_to_rat_pair (rev (newdsc_pol polr p (fst ?I_real) (snd ?I_real) (e + 1) (dk + (2 ^ e + 2)) s P')) @ acc)"
            using "1.IH"(4) aeq beq Peq pdeg P0 rat_lt polrel TNg_real v0 v1 by force

          show ?thesis using main_newton stepI nd_newton aeq beq by simp
      next
        case TN0i: None
          have TNg0_real: "try_newton_g (snd (polr p (of_rat a) (of_rat b) e dk (s, ?v)))
                             p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = None"
          proof (cases ?gn)
            case True
            then have TN0_rat: "try_newton_int a b (N_of e) P (nat ?v) = None"
              using TN0i by (simp add: try_newton_int_g_def)
            have "try_newton p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = None"
            proof -
              have "try_newton_sc (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v))
                      = try_newton p (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v))"
                using try_newton_sc_eq[OF deg_p[symmetric]] by simp
              moreover have "(try_newton_int a b (N_of e) P (nat ?v) = None)
                      = (try_newton_sc (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v)) = None)"
                using try_newton_int_eq_sc[OF ab P0 Npos, of "nat ?v"]
                by (auto split: option.splits)
              ultimately show ?thesis using TN0_rat vnn by simp
            qed
            then show ?thesis using gn_eq True by (simp add: try_newton_g_def)
          next
            case False
            then show ?thesis using gn_eq by (simp add: try_newton_g_def)
          qed
        show ?thesis
        proof (cases "try_blocks_int_g ?gb a b (N_of e) P (nat ?v)")
          case (Some I_rat)
        have gbT: "?gb = True" and TBi: "try_blocks_int a b (N_of e) P (nat ?v) = Some I_rat"
          using Some by (auto simp: try_blocks_int_g_def split: if_split_asm)
        let ?I_real = "(real_of_rat (fst I_rat), of_rat (snd I_rat))"
        have TB_real: "try_blocks p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = Some ?I_real"
          using try_blocks_int_Some_iff[OF ab P0 Npos deg_p[symmetric]] TBi vnn by simp
        have TBg_real: "try_blocks_g (fst (polr p (of_rat a) (of_rat b) e dk (s, ?v)))
                          p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = Some ?I_real"
          using TB_real gb_eq gbT by (simp add: try_blocks_g_def)

        have nd_block:
          "newdsc_pol polr p a' b' e dk s P'
             = newdsc_pol polr p (fst ?I_real) (snd ?I_real) (e + 1) (dk + (2 ^ e + 2)) s P'"
          using "1.hyps" aeq beq Peq v0 v1 TNg0_real TBg_real newdsc_pol.psimps by fastforce

        have main_block:
          "newdsc_pol_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
           newdsc_pol_main_int nodepol P ((fst I_rat, snd I_rat, e + 1, dk + (2 ^ e + 2), s) # todo) acc"
          apply (subst newdsc_pol_main_int.simps)
          using v_neq_0 v_neq_1 TN0i Some v_nat_eq
          by (auto simp add: Let_def accept_child_int_def)

        have "fst ?I_real < snd ?I_real"
          using try_blocks_Some_fst_lt_snd[OF TB_real ab_real N2] by simp
        hence rat_lt: "fst I_rat < snd I_rat" using of_rat_less by auto

        have stepI:
          "newdsc_pol_main_int nodepol P ((fst I_rat, snd I_rat, e + 1, dk + (2 ^ e + 2), s) # todo) acc =
           newdsc_pol_main_int nodepol P todo
             (map real_to_rat_pair (rev (newdsc_pol polr p (fst ?I_real) (snd ?I_real) (e + 1) (dk + (2 ^ e + 2)) s P')) @ acc)"
          using "1.IH"(3) aeq beq Peq pdeg P0 rat_lt polrel TNg0_real TBg_real v0 v1 by force

        show ?thesis using main_block stepI nd_block aeq beq by simp
        next
          case TB0i: None
        have TBg0_real: "try_blocks_g (fst (polr p (of_rat a) (of_rat b) e dk (s, ?v)))
                           p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = None"
        proof (cases ?gb)
          case True
          then have TB0_rat: "try_blocks_int a b (N_of e) P (nat ?v) = None"
            using TB0i by (simp add: try_blocks_int_g_def)
          have "try_blocks p (of_rat a) (of_rat b) (N_of e) ?P_real ?v = None"
          proof -
            have "try_blocks_sc (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v))
                    = try_blocks p (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v))"
              using try_block_sc_eq[OF deg_p[symmetric]] by simp
            moreover have "(try_blocks_int a b (N_of e) P (nat ?v) = None)
                    = (try_blocks_sc (of_rat a) (of_rat b) (N_of e) ?P_real (int (nat ?v)) = None)"
              using try_blocks_int_eq_sc[OF ab P0 Npos, of "nat ?v"]
              by (auto split: option.splits)
            ultimately show ?thesis using TB0_rat vnn by simp
          qed
          then show ?thesis using gb_eq True by (simp add: try_blocks_g_def)
        next
          case False
          then show ?thesis using gb_eq by (simp add: try_blocks_g_def)
        qed
          define m where "m = (a + b) / 2"
          define e' where "e' = max 1 (e - 1)"
          let ?m_real = "(of_rat a + of_rat b) / 2"
          have m_real_eq: "of_rat m = ?m_real" by (simp add: m_def of_rat_add of_rat_divide)
          \<comment> \<open>the two proper-split successors, identified by \<open>split_run_len_int_eq_real\<close>\<close>
          let ?s'_rat  = "split_run_len_int P a b s"
          let ?s'_real = "split_run_len_real p ?P_real (of_rat a) (of_rat b) s"
          have s'_eq: "?s'_real = ?s'_rat"
            by (rule split_run_len_int_eq_real[OF P0 ab pdeg])
          let ?mid_rat = "(if poly (map_poly of_int P :: rat poly) m = 0 then [(m, m)] else [])"
          let ?mid_real = "(if poly ?P_real ?m_real = 0 then [(?m_real, ?m_real)] else [])"
          have mid_map: "map real_to_rat_pair ?mid_real = ?mid_rat"
            using poly_rat_eq_poly_real m_real_eq
            by (smt (verit, ccfv_threshold) list.map(1,2) real_to_rat_pair_of_rat)

          have nd_split:
            "newdsc_pol polr p a' b' e dk s P' =
               ?mid_real @ newdsc_pol polr p a' ?m_real e' (dk + 1) ?s'_real P'
                         @ newdsc_pol polr p ?m_real b' e' (dk + 1) ?s'_real P'"
            using "1.hyps" aeq beq Peq newdsc_pol.psimps Let_def v0 v1 TBg0_real TNg0_real
                  m_real_eq[symmetric] e'_def
            by (smt (verit, ccfv_SIG) option.case(1))

          have main_split:
            "newdsc_pol_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
             newdsc_pol_main_int nodepol P ((a, m, e', dk + 1, ?s'_rat) # (m, b, e', dk + 1, ?s'_rat) # todo) (?mid_rat @ acc)"
          proof -
            have tmp:
              "newdsc_pol_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
               newdsc_pol_main_int nodepol P ((a, m, e', dk + 1, ?s'_rat) # (m, b, e', dk + 1, ?s'_rat) # todo)
                 (if poly (map_poly of_int P :: rat poly) m = 0 then (m, m) # acc else acc)"
              apply (subst newdsc_pol_main_int.simps)
              using v_neq_0 v_neq_1 TB0i TN0i m_def e'_def v_nat_eq
              \<comment> \<open>keep \<open>split_run_len_int\<close> FOLDED: \<open>bisect_children_int_def\<close> already produces exactly
                 the \<open>?s'_rat\<close> term, and unfolding it on one side only breaks the match.\<close>
              by (simp add: Let_def bisect_children_int_def m_def e'_def)
            show ?thesis using tmp by auto
          qed

          have a_lt_m: "a < m" using ab m_def by auto
          have m_lt_b: "m < b" using ab m_def by auto

          have stepL:
            "newdsc_pol_main_int nodepol P ((a, m, e', dk + 1, ?s'_rat) # (m, b, e', dk + 1, ?s'_rat) # todo) (?mid_rat @ acc) =
             newdsc_pol_main_int nodepol P ((m, b, e', dk + 1, ?s'_rat) # todo)
               (map real_to_rat_pair (rev (newdsc_pol polr p a' ?m_real e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc))"
          proof -
            have "newdsc_pol_main_int nodepol P ((a, m, e', dk + 1, ?s'_rat) # (m, b, e', dk + 1, ?s'_rat) # todo) (?mid_rat @ acc) =
                  newdsc_pol_main_int nodepol P ((m, b, e', dk + 1, ?s'_rat) # todo)
                    (map real_to_rat_pair (rev (newdsc_pol polr p a' (of_rat m) e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc))"
              using "1.IH"(1) aeq beq Peq pdeg P0 a_lt_m polrel TBg0_real TNg0_real v0 v1 e'_def s'_eq m_real_eq by metis
            thus ?thesis using m_real_eq by metis
          qed

          have stepR:
            "newdsc_pol_main_int nodepol P ((m, b, e', dk + 1, ?s'_rat) # todo)
               (map real_to_rat_pair (rev (newdsc_pol polr p a' ?m_real e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc)) =
             newdsc_pol_main_int nodepol P todo
               (map real_to_rat_pair (rev (newdsc_pol polr p ?m_real b' e' (dk + 1) ?s'_real P'))
                 @ (map real_to_rat_pair (rev (newdsc_pol polr p a' ?m_real e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc)))"
          proof -
            have "newdsc_pol_main_int nodepol P ((m, b, e', dk + 1, ?s'_rat) # todo)
                    (map real_to_rat_pair (rev (newdsc_pol polr p a' ?m_real e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc)) =
                  newdsc_pol_main_int nodepol P todo
                    (map real_to_rat_pair (rev (newdsc_pol polr p (of_rat m) b' e' (dk + 1) ?s'_real P'))
                      @ (map real_to_rat_pair (rev (newdsc_pol polr p a' ?m_real e' (dk + 1) ?s'_real P')) @ (?mid_rat @ acc)))"
              using "1.IH"(2) aeq beq Peq pdeg P0 m_lt_b polrel TBg0_real TNg0_real v0 v1 e'_def s'_eq m_real_eq by metis
            thus ?thesis using m_real_eq by metis
          qed

          have LHS_rewrite:
            "newdsc_pol_main_int nodepol P ((a, b, e, dk, s) # todo) acc =
             newdsc_pol_main_int nodepol P todo
               (map real_to_rat_pair (rev (newdsc_pol polr p ?m_real b' e' (dk + 1) ?s'_real P')
                 @ rev (newdsc_pol polr p a' ?m_real e' (dk + 1) ?s'_real P') @ ?mid_real) @ acc)"
            using main_split stepL stepR mid_map by simp

          have RHS_rewrite:
            "newdsc_pol_main_int nodepol P todo
               (map real_to_rat_pair (rev (newdsc_pol polr p a' b' e dk s P')) @ acc) =
             newdsc_pol_main_int nodepol P todo
               (map real_to_rat_pair (rev (newdsc_pol polr p ?m_real b' e' (dk + 1) ?s'_real P')
                 @ rev (newdsc_pol polr p a' ?m_real e' (dk + 1) ?s'_real P') @ ?mid_real) @ acc)"
            using nd_split by simp

          show ?thesis using LHS_rewrite RHS_rewrite by simp
        qed
      qed
    qed
  qed
qed

lemma newdsc_pol_int_eq_newdsc_pol:
  assumes dom:  "newdsc_pol_dom
                   (polr, p, of_rat a, of_rat b, e, dk, 0, map_poly of_int P :: real poly)"
    and pdeg:   "p = degree P"
    and P0:     "P \<noteq> 0"
    and ab:     "a < b"
    and polrel: "\<And>a' b' e' dk' s' v. polr p (of_rat a') (of_rat b') e' dk' (s', int v)
                    = pol (degree P) a' b' e' dk' (s', v)"
  shows "rev (newdsc_pol_int pol a b e dk P)
           = map real_to_rat_pair
               (newdsc_pol polr p (of_rat a) (of_rat b) e dk 0 (map_poly of_int P))"
proof -
  have tr: "newdsc_pol_int pol a b e dk P
              = map real_to_rat_pair (rev (newdsc_pol polr p (of_rat a) (of_rat b) e dk 0 (map_poly of_int P)))"
    unfolding newdsc_pol_int_def
    using newdsc_pol_main_int_sim_aux[OF dom refl refl refl pdeg P0 ab, where nodepol = "pol (degree P)", OF _ , of "[]" "[]"] polrel pdeg
    by (simp add: newdsc_pol_main_int.simps)
  thus ?thesis by (simp add: rev_map)
qed

text \<open>Sanity (deliberately NOT proved as a theorem, for the same reason as the
  real-level all-True bridge above): the all-True int instance
  \<open>newdsc_pol_int (\<lambda>_ _ _ _ _ _. (True, True))\<close> collapses to @{const newdsc_int}.
  It is OFF the critical path — the implementation's correctness runs
  impl \<Rightarrow> @{const newdsc_pol_int}\<open> pol_final\<close>
  \<open>\<Rightarrow>[newdsc_pol_int_eq_newdsc_pol]\<close> @{const newdsc_pol}\<open> pol_final_real\<close>
  \<open>\<Rightarrow>[newdsc_pol_sound/complete]\<close> isolation, never touching
  @{const newdsc_int}. The load-bearing bridge
  @{thm [source] newdsc_pol_int_eq_newdsc_pol} IS proved (above).\<close>

section \<open>Dyadic window arithmetic\<close>

text \<open>On a dyadic node \<open>(l/2^k, r/2^k)\<close> the
  grid divisor is \<open>s = 4 * N_of e = 2^(2^e + 2)\<close>, so EVERY window NewDsc can
  schedule is dyadic. \<open>newton_window_child l r k e m\<close> is the child interval for
  grid cells \<open>m..m+4\<close> in \<open>(num_l, num_r, k')\<close> form — the impl-side interval
  bookkeeping (blocks are the instances \<open>m = 0\<close> and \<open>m = s - 4\<close>).\<close>

definition newton_window_child ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<times> int \<times> nat"
where
  "newton_window_child l r k e m =
     (let j = 2 ^ e + 2
      in (l * 2 ^ j + m * (r - l),
          l * 2 ^ j + (m + 4) * (r - l),
          k + j))"

lemma four_N_of_pow2: "4 * N_of e = 2 ^ (2 ^ e + 2)"
  unfolding N_of_def by (simp add: power_add)

text \<open>The child's endpoints evaluate to exactly the abstract window endpoints.
  Route: unfold, push \<open>of_int\<close>/\<open>of_nat\<close> through, field_simps with
  @{thm [source] four_N_of_pow2}.\<close>

lemma dyadic_window_child_eval:
  fixes l r m :: int and k e :: nat
  assumes "m + 4 \<le> int (4 * N_of e)"
  shows "(of_int (fst (newton_window_child l r k e m))
            / 2 ^ (snd (snd (newton_window_child l r k e m))) :: rat)
           = of_int l / 2 ^ k
             + of_int m * (of_int (r - l) / 2 ^ k) / of_nat (4 * N_of e)"
    and "(of_int (fst (snd (newton_window_child l r k e m)))
            / 2 ^ (snd (snd (newton_window_child l r k e m))) :: rat)
           = of_int l / 2 ^ k
             + of_int (m + 4) * (of_int (r - l) / 2 ^ k) / of_nat (4 * N_of e)"
proof -
  define j where "j = 2 ^ e + (2::nat)"
  have jnat: "of_nat (4 * N_of e) = (2::rat) ^ j"
    unfolding j_def by (metis four_N_of_pow2 of_nat_numeral of_nat_power)
  have pk: "(2::rat) ^ (k + j) = 2 ^ k * 2 ^ j" by (simp add: power_add)
  have den: "snd (snd (newton_window_child l r k e m)) = k + j"
    unfolding newton_window_child_def Let_def j_def[symmetric] by simp
  have numL: "(of_int (fst (newton_window_child l r k e m)) :: rat)
                = of_int l * 2 ^ j + of_int m * of_int (r - l)"
    unfolding newton_window_child_def Let_def j_def[symmetric] fst_conv by simp
  have numR: "(of_int (fst (snd (newton_window_child l r k e m))) :: rat)
                = of_int l * 2 ^ j + of_int (m + 4) * of_int (r - l)"
    unfolding newton_window_child_def Let_def j_def[symmetric] fst_conv snd_conv by simp
  show "(of_int (fst (newton_window_child l r k e m))
            / 2 ^ (snd (snd (newton_window_child l r k e m))) :: rat)
           = of_int l / 2 ^ k
             + of_int m * (of_int (r - l) / 2 ^ k) / of_nat (4 * N_of e)"
    unfolding den numL jnat pk by (simp add: field_simps)
  show "(of_int (fst (snd (newton_window_child l r k e m)))
            / 2 ^ (snd (snd (newton_window_child l r k e m))) :: rat)
           = of_int l / 2 ^ k
             + of_int (m + 4) * (of_int (r - l) / 2 ^ k) / of_nat (4 * N_of e)"
    unfolding den numR jnat pk by (simp add: field_simps)
qed

text \<open>Dyadic preservation: starting from a dyadic seed, every worklist entry
  \<open>newdsc_pol_main_int\<close> ever schedules is dyadic with exponent = the \<open>dk\<close> tag
  (bisection: \<open>k+1\<close>; window: \<open>k + 2^e + 2\<close>) — i.e. the tag really is the impl's
  stored exponent. This is the worklist invariant the loop bridge needs to type the
  impl's \<open>(l_num, r_num, k)\<close> vectors, in the form of \<open>Dyadic_Interval.thy\<close>'s
  \<open>dyadic_interval_vec_invar\<close>.\<close>

section \<open>The carried window-algebra spine (repr composition)\<close>

text \<open>\<^bold>\<open>Why this theory does not import \<open>Bisection_Refine\<close>.\<close> That theory imports the whole
  Sepref/GMP bisection chain, and nothing here needs it: everything below is provable from
  \<open>IsaRRI_Spec.Dsc_Int\<close> alone. \<open>descartes_list_int\<close> is defined directly via the same scale/shift
  pipeline that \<open>fast_descartes_p3\<close> names, and \<open>p3_rat_equiv\<close>, \<open>sign_changes_fold_map_rat_of_int\<close> and
  \<open>sign_changes_fold_smult_list_pos\<close> (in \<open>Dsc_Int\<close>) bridge to it.

  \<^bold>\<open>The invariant used here is weaker than \<open>carried_repr\<close>.\<close>
  \<open>carried_repr P a b Q \<longleftrightarrow> rev Q = fast_descartes_p3 a b P\<close> is exact equality, provable for the
  bisection children only via lcm/gcd bookkeeping specific to bisecting at the midpoint
  (\<open>quotient_of_half\<close>'s odd-numerator argument for the left child, \<open>p3_scalar_bisect_eq\<close> for the
  right). An arbitrary Newton window \<open>[m/s, (m+4)/s]\<close> has no such structure, and
  \<open>carried_descartes_count\<close> depends only on \<open>Q\<close>'s sign pattern
  (@{thm [source] sign_changes_fold_smult_list_pos}: invariant under \<open>smult_list\<close> by a positive
  scalar). \<open>carried_repr_scalar\<close> below asks only for a positive rational scalar multiple, which
  composes across arbitrary windows using only the affine reparametrisation algebra, and still
  transports the count exactly (proved below). The Newton solver's loop invariant is stated
  against this predicate.\<close>

subsection \<open>The local-representation core (no quotient_of, no fast_descartes_p3)\<close>

text \<open>The rational polynomial \<open>P\<close> reparametrized to \<open>[a,b]\<close>: shift by \<open>a\<close>, then
  scale by the width \<open>b-a\<close>. This is exactly what \<open>fast_descartes_p3\<close> computes
  up to a positive rational scalar (@{thm [source] p3_rat_equiv}) — stated
  directly so nothing here needs \<open>quotient_of\<close>/coprimality reasoning.\<close>

definition local_poly_rat :: "rat \<Rightarrow> rat \<Rightarrow> int list \<Rightarrow> rat list" where
  "local_poly_rat a b xs = scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int xs))"

text \<open>The general affine-reparametrization COMPOSITION law: shifting by \<open>c1\<close> then
  scaling by \<open>d1\<close>, then shifting by \<open>c2\<close> then scaling by \<open>d2\<close>, equals ONE
  shift-then-scale by the composed affine map. Pure algebra, reusing three
  existing facts (\<open>taylor_scale_commute_rat\<close>, the generic
  \<open>taylor_shift_list c (taylor_shift_list d xs) = taylor_shift_list (c+d) xs\<close>
  restated locally below since its only existing copy lives in
  \<open>Bisection_Refine.thy\<close>, and \<open>scale_poly_list_scale_poly_list\<close>) — no
  induction, no \<open>pcompose\<close> needed directly.\<close>

lemma newton_taylor_shift_add:
  fixes c d :: "'a::comm_ring_1"
  shows "taylor_shift_list c (taylor_shift_list d xs) = taylor_shift_list (c + d) xs"
proof (rule poly_eq_same_length)
  show "length (taylor_shift_list c (taylor_shift_list d xs)) = length (taylor_shift_list (c + d) xs)"
    by simp
  have comp: "pcompose ([:d, 1:]::'a poly) [:c, 1:] = [:c + d, 1:]"
    by (simp add: pcompose_pCons add.commute)
  have "Poly (taylor_shift_list c (taylor_shift_list d xs))
      = pcompose (pcompose (Poly xs) [:d, 1:]) [:c, 1:]"
    by (simp add: Poly_taylor_shift_list)
  also have "\<dots> = pcompose (Poly xs) [:c + d, 1:]"
    by (simp add: comp add.commute flip: pcompose_assoc)
  also have "\<dots> = Poly (taylor_shift_list (c + d) xs)" by (simp add: Poly_taylor_shift_list)
  finally show "Poly (taylor_shift_list c (taylor_shift_list d xs)) = Poly (taylor_shift_list (c + d) xs)" .
qed

lemma newton_scale_taylor_compose:
  fixes c1 c2 d1 d2 :: rat
  shows "scale_poly_list d2 (taylor_shift_list c2 (scale_poly_list d1 (taylor_shift_list c1 xs)))
       = scale_poly_list (d1 * d2) (taylor_shift_list (c1 + c2 * d1) xs)"
proof -
  have "taylor_shift_list c2 (scale_poly_list d1 (taylor_shift_list c1 xs))
      = scale_poly_list d1 (taylor_shift_list (c2 * d1) (taylor_shift_list c1 xs))"
    by (rule taylor_scale_commute_rat)
  also have "\<dots> = scale_poly_list d1 (taylor_shift_list (c1 + c2 * d1) xs)"
    by (simp add: newton_taylor_shift_add add.commute)
  finally have step: "taylor_shift_list c2 (scale_poly_list d1 (taylor_shift_list c1 xs))
      = scale_poly_list d1 (taylor_shift_list (c1 + c2 * d1) xs)" .
  show ?thesis
    by (simp add: step scale_poly_list_scale_poly_list mult.commute)
qed

text \<open>\<open>descartes_list_int\<close> IS \<open>sign_changes_fold\<close> of the local-core reparametrization
  (up to the same positive scalar \<open>p3_rat_equiv\<close> names, which cancels via
  @{thm [source] sign_changes_fold_smult_list_pos}) — the count-side half of the
  bridge, entirely independent of \<open>carried_repr\<close>/\<open>fast_descartes_p3\<close>.\<close>

lemma descartes_list_int_via_local:
  assumes "length xs > 0" and "a \<noteq> b"
  shows "descartes_list_int a b xs
           = sign_changes_fold (taylor_shift_list (1::rat) (rev (local_poly_rat a b xs)))"
proof -
  define da where "da = snd (quotient_of a)"
  define dw where "dw = snd (quotient_of ((b - a) * of_int da))"
  define nw where "nw = fst (quotient_of ((b - a) * of_int da))"
  define p1 where "p1 = fractional_taylor_shift a xs"
  define p3 where "p3 = scale_for_fractional_shift dw 1 (rev (scale_poly_list nw p1))"
  have dli: "descartes_list_int a b xs = sign_changes_fold (taylor_shift_list (1::int) p3)"
    unfolding descartes_list_int_def da_def dw_def nw_def p1_def p3_def Let_def
    by (simp add: case_prod_beta)
  have rat_eq: "map rat_of_int p3
      = smult_list ((rat_of_int da * rat_of_int dw) ^ (length xs - 1))
          (rev (local_poly_rat a b xs))"
    unfolding p3_def dw_def nw_def da_def p1_def local_poly_rat_def
    using p3_rat_equiv[OF assms] by simp
  define S where "S = (rat_of_int da * rat_of_int dw) ^ (length xs - 1)"
  have Spos: "S > 0"
    unfolding S_def da_def dw_def
    using quotient_of_denom_pos[of a] quotient_of_denom_pos[of "(b - a) * of_int (snd (quotient_of a))"]
    by (simp add: quotient_of_denom_pos')
  have "sign_changes_fold (taylor_shift_list (1::int) p3)
      = sign_changes_fold (map rat_of_int (taylor_shift_list (1::int) p3))"
    by (simp add: sign_changes_fold_map_rat_of_int)
  also have "\<dots> = sign_changes_fold (taylor_shift_list (1::rat) (map rat_of_int p3))"
    by (simp add: map_rat_of_int_taylor_shift_list)
  also have "\<dots> = sign_changes_fold (taylor_shift_list (1::rat) (smult_list S (rev (local_poly_rat a b xs))))"
    using rat_eq S_def by simp
  also have "\<dots> = sign_changes_fold (smult_list S (taylor_shift_list (1::rat) (rev (local_poly_rat a b xs))))"
    by (simp add: taylor_shift_list_smult)
  also have "\<dots> = sign_changes_fold (taylor_shift_list (1::rat) (rev (local_poly_rat a b xs)))"
    by (simp add: sign_changes_fold_smult_list_pos Spos)
  finally show ?thesis using dli by simp
qed

subsection \<open>The scalar-relaxed carried representation\<close>

definition carried_repr_scalar :: "int list \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> int list \<Rightarrow> bool" where
  "carried_repr_scalar P a b Q \<longleftrightarrow>
     (\<exists>c::rat. c > 0 \<and> map rat_of_int (rev Q) = smult_list c (rev (local_poly_rat a b P)))"

text \<open>The count correspondence: a scalar-repr node's
  ET/exact/truncated count equals the abstract \<open>descartes_list_int\<close> count for its
  interval — the SAME quantity every existing carried count op already targets
  (\<open>carried_descartes_count_monadic_classify\<close>'s abstract side). Stated via the
  count's DEFINITION (\<open>sign_changes_fold (taylor_shift_list 1 (rev xs))\<close>) rather
  than the name \<open>carried_descartes_count\<close> itself, which lives in the impl-layer
  \<open>Carried_Kernel.thy\<close> and is not imported here; \<open>carried_descartes_count Q = \<dots>\<close>
  follows by unfolding its definition once that import is in scope.\<close>

lemma carried_repr_scalar_count:
  assumes "carried_repr_scalar P a b Q" and "length P > 0" and "a \<noteq> b"
  shows "sign_changes_fold (taylor_shift_list (1::int) (rev Q)) = descartes_list_int a b P"
proof -
  from assms(1) obtain c where cpos: "c > 0"
    and Qeq: "map rat_of_int (rev Q) = smult_list c (rev (local_poly_rat a b P))"
    unfolding carried_repr_scalar_def by blast
  have "sign_changes_fold (taylor_shift_list (1::int) (rev Q))
      = sign_changes_fold (map rat_of_int (taylor_shift_list (1::int) (rev Q)))"
    by (simp add: sign_changes_fold_map_rat_of_int)
  also have "\<dots> = sign_changes_fold (taylor_shift_list (1::rat) (map rat_of_int (rev Q)))"
    by (simp add: map_rat_of_int_taylor_shift_list)
  also have "\<dots> = sign_changes_fold (taylor_shift_list (1::rat) (smult_list c (rev (local_poly_rat a b P))))"
    using Qeq by simp
  also have "\<dots> = sign_changes_fold (smult_list c (taylor_shift_list (1::rat) (rev (local_poly_rat a b P))))"
    by (simp add: taylor_shift_list_smult)
  also have "\<dots> = sign_changes_fold (taylor_shift_list (1::rat) (rev (local_poly_rat a b P)))"
    by (simp add: sign_changes_fold_smult_list_pos cpos)
  also have "\<dots> = descartes_list_int a b P"
    using descartes_list_int_via_local[OF assms(2,3)] by simp
  finally show ?thesis .
qed

subsection \<open>The SPINE: window-child construction preserves \<open>carried_repr_scalar\<close>\<close>

text \<open>\<open>window_child_formula l d r xs\<close> is EXACTLY \<open>carried_init_same_den l d r xs\<close>
  (\<open>Carried_Kernel.thy\<close>, not imported here) restated locally so this theory stays
  free of the implementation layer;
  \<open>carried_init_same_den l d r xs = window_child_formula l d r xs\<close> is a one-line
  \<open>unfolding\<close> once both are in scope (in \<open>Newton.thy\<close>, which imports \<open>Bisection\<close>).\<close>

definition window_child_formula :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "window_child_formula l d r xs =
    scale_poly_list (r - l) (taylor_shift_list l (rev (scale_for_fractional_shift d 1 (rev xs))))"

text \<open>\<open>window_child_formula\<close> applied to ANY int list (borrowed or node poly, any
  \<open>d > 0\<close>) always satisfies \<open>carried_repr_scalar\<close> for the corresponding rational
  interval \<open>[l/d, r/d]\<close> — with witness scalar \<open>d^(length xs - 1) > 0\<close>. No
  coprimality/reduced-fraction hypothesis needed (unlike \<open>carried_repr_left\<close>'s
  odd-numerator condition) since we only need a POSITIVE scalar, not exact
  equality.\<close>

lemma window_child_formula_repr_scalar:
  fixes l r :: int and d :: int
  assumes dpos: "0 < d"
  shows "carried_repr_scalar xs (of_int l / of_int d) (of_int r / of_int d)
           (window_child_formula l d r xs)"
proof -
  define d' where "d' = rat_of_int d"
  have d'pos: "d' > 0" unfolding d'_def using dpos by simp
  define k where "k = length xs - 1"
  have rev_scale: "map rat_of_int (rev (scale_poly_list d (rev xs)))
      = rev (scale_poly_list d' (rev (map rat_of_int xs)))"
  proof -
    have "map rat_of_int (rev (scale_poly_list d (rev xs)))
        = rev (map rat_of_int (scale_poly_list d (rev xs)))"
      by (simp add: rev_map)
    also have "\<dots> = rev (scale_poly_list (rat_of_int d) (map rat_of_int (rev xs)))"
      by (simp add: map_rat_of_int_scale_poly_list)
    also have "\<dots> = rev (scale_poly_list d' (rev (map rat_of_int xs)))"
      by (simp add: d'_def rev_map)
    finally show ?thesis .
  qed
  have step1: "map rat_of_int (window_child_formula l d r xs)
      = scale_poly_list (rat_of_int (r - l))
          (taylor_shift_list (rat_of_int l)
            (rev (scale_poly_list d' (rev (map rat_of_int xs)))))"
    unfolding window_child_formula_def
    by (simp add: map_rat_of_int_scale_poly_list map_rat_of_int_taylor_shift_list
        scale_for_fractional_shift_eq_scale_poly_list rev_scale)
  have step2: "rev (scale_poly_list d' (rev (map rat_of_int xs)))
      = smult_list (d' ^ k) (scale_poly_list (1 / d') (map rat_of_int xs))"
    using scale_poly_list_rev[of d' "map rat_of_int xs"] d'pos
    by (simp add: k_def rev_smult_list rev_map)
  have step3: "taylor_shift_list (rat_of_int l) (scale_poly_list (1 / d') (map rat_of_int xs))
      = scale_poly_list (1 / d') (taylor_shift_list (rat_of_int l / d') (map rat_of_int xs))"
    using taylor_scale_commute_rat[of "rat_of_int l" "1 / d'" "map rat_of_int xs"]
    by (simp add: field_simps)
  have width_eq: "(rat_of_int r - rat_of_int l) / d' = rat_of_int r / d' - rat_of_int l / d'"
    by (simp add: diff_divide_distrib)
  have shift_eq: "rat_of_int l / d' + (rat_of_int r - rat_of_int l) / d' = rat_of_int r / d'"
    by (simp add: width_eq)
  have core: "map rat_of_int (window_child_formula l d r xs)
      = smult_list (d' ^ k) (local_poly_rat (of_int l / d') (of_int r / d') xs)"
    unfolding local_poly_rat_def step1 step2
    by (simp add: step3 scale_poly_list_smult_list taylor_shift_list_smult
        scale_poly_list_scale_poly_list width_eq shift_eq)
  have "map rat_of_int (rev (window_child_formula l d r xs))
      = rev (map rat_of_int (window_child_formula l d r xs))"
    by (simp add: rev_map)
  also have "\<dots> = smult_list (d' ^ k) (rev (local_poly_rat (of_int l / d') (of_int r / d') xs))"
    using core by (simp add: rev_smult_list)
  finally show ?thesis
    unfolding carried_repr_scalar_def d'_def
    using zero_less_power[OF d'pos, of k] d'_def by blast
qed

text \<open>Transitivity/COMPOSITION: a window \<open>[u,v]\<close> of a scalar-repr node \<open>Q\<close> (itself
  representing \<open>[a,b]\<close> of \<open>P\<close>) represents the GLOBAL window
  \<open>[a + u(b-a), a + v(b-a)]\<close> of \<open>P\<close>. This is the actual mathematical content of
  "the local poly of a window of a local poly is the local poly of the composed
  window" — proved via ONE application of
  @{thm [source] newton_scale_taylor_compose}, with no per-window lcm/gcd
  bookkeeping (which is what the positive-scalar relaxation avoids).\<close>

lemma carried_repr_scalar_compose:
  assumes PQ: "carried_repr_scalar P a b Q"
    and QR: "carried_repr_scalar Q u v R"
  shows "carried_repr_scalar P (a + u * (b - a)) (a + v * (b - a)) R"
proof -
  from PQ obtain c1 where c1pos: "c1 > 0"
    and Qeq: "map rat_of_int (rev Q) = smult_list c1 (rev (local_poly_rat a b P))"
    unfolding carried_repr_scalar_def by blast
  from QR obtain c2 where c2pos: "c2 > 0"
    and Req: "map rat_of_int (rev R) = smult_list c2 (rev (local_poly_rat u v Q))"
    unfolding carried_repr_scalar_def by blast
  have Qrat: "map rat_of_int Q = smult_list c1 (local_poly_rat a b P)"
  proof -
    have "map rat_of_int Q = rev (map rat_of_int (rev Q))" by (simp add: rev_map)
    also have "\<dots> = rev (smult_list c1 (rev (local_poly_rat a b P)))" using Qeq by simp
    also have "\<dots> = smult_list c1 (local_poly_rat a b P)" by (simp add: rev_smult_list)
    finally show ?thesis .
  qed
  have compose: "local_poly_rat u v Q = smult_list c1 (local_poly_rat (a + u * (b - a)) (a + v * (b - a)) P)"
  proof -
    have "local_poly_rat u v Q
        = scale_poly_list (v - u) (taylor_shift_list u (smult_list c1 (local_poly_rat a b P)))"
      unfolding local_poly_rat_def Qrat by simp
    also have "\<dots> = smult_list c1 (scale_poly_list (v - u) (taylor_shift_list u (local_poly_rat a b P)))"
      by (simp add: taylor_shift_list_smult scale_poly_list_smult_list)
    also have "\<dots> = smult_list c1 (scale_poly_list (v - u)
                       (taylor_shift_list u (scale_poly_list (b - a) (taylor_shift_list a (map rat_of_int P)))))"
      by (simp add: local_poly_rat_def)
    also have "\<dots> = smult_list c1 (scale_poly_list ((b - a) * (v - u))
                       (taylor_shift_list (a + u * (b - a)) (map rat_of_int P)))"
      by (simp add: newton_scale_taylor_compose)
    also have "\<dots> = smult_list c1 (local_poly_rat (a + u * (b - a)) (a + v * (b - a)) P)"
      unfolding local_poly_rat_def by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have "map rat_of_int (rev R) = smult_list c2 (rev (smult_list c1 (local_poly_rat (a + u * (b - a)) (a + v * (b - a)) P)))"
    using Req compose by simp
  also have "\<dots> = smult_list (c2 * c1) (rev (local_poly_rat (a + u * (b - a)) (a + v * (b - a)) P))"
    by (simp add: rev_smult_list smult_list_smult_list)
  finally show ?thesis
    unfolding carried_repr_scalar_def using mult_pos_pos[OF c2pos c1pos] by blast
qed

text \<open>THE SPINE, instantiated for the actual \<open>newton_window_child\<close> construction:
  the window child \<open>window_child_formula m s (m+4) Q\<close> (\<open>= carried_init_same_den
  m s (m+4) Q\<close>) represents the corresponding GLOBAL window of \<open>P\<close> —
  chaining the two lemmas above. Blocks (\<open>m=0\<close>, \<open>m=s-4\<close>) are instances;
  Newton snaps likewise.\<close>

lemma carried_window_repr_scalar:
  fixes m s :: int
  assumes Q: "carried_repr_scalar P a b Q"
    and spos: "0 < s"
  shows "carried_repr_scalar P
           (a + (of_int m / of_int s) * (b - a))
           (a + (of_int (m + 4) / of_int s) * (b - a))
           (window_child_formula m s (m + 4) Q)"
  using carried_repr_scalar_compose[OF Q window_child_formula_repr_scalar[OF spos, of Q m "m+4"]]
  by simp

text \<open>Corollary tying the two together (the impl's accept test): the window
  child's exact/classify count equals \<open>descartes_list_int\<close> of the GLOBAL window
  — exactly what the accept test \<open>count = v\<close> must match against the abstract
  \<open>try_blocks_int\<close>/\<open>try_newton_int\<close> acceptance, for free from
  @{thm [source] carried_repr_scalar_count} once the spine above supplies
  \<open>carried_repr_scalar\<close> for the child.\<close>

section \<open>The local Newton step\<close>

text \<open>With \<open>Q\<close> the node's local poly, \<open>\<lambda>_loc = -v * Q(0)/Q'(0)\<close> at the left endpoint
  (coefficient reads \<open>Q(0) = q\<^sub>0\<close>, \<open>Q'(0) = q\<^sub>1\<close>) resp.
  \<open>1 - v * Q(1)/Q'(1)\<close> at the right (\<open>Q(1) = \<Sigma>q\<^sub>i\<close>, \<open>Q'(1) = \<Sigma>i\<cdot>q\<^sub>i\<close>)
  satisfies \<open>\<lambda>_loc = (newton_at v P t - a) / w\<close> (affine chain rule: \<open>pderiv\<close>
  under \<open>pcompose\<close>; the positive carried scale cancels in the quotient — same
  mechanism as \<open>carried_repr_scalar_count\<close>'s cancellation, since \<open>pderiv\<close>
  commutes with a scalar multiple up to that same scalar), and the snap grid
  position satisfies \<open>\<lfloor>s * (\<lambda> - a) / w\<rfloor> = \<lfloor>s * \<lambda>_loc\<rfloor>\<close> computed exactly by
  integer floor division (HOL \<open>div\<close> IS floor = GMP \<open>fdiv\<close>). The monadic solver, loop
  invariant and multiset keystone are in \<open>Newton.thy\<close>, using \<open>carried_repr_scalar\<close>
  (not \<open>carried_repr\<close>) as the representation invariant throughout.\<close>

section \<open>Sign-evaluation window pre-filter (abstract necessary condition)\<close>

text \<open>The ANDimp admissible-points reject: a window \<open>[a',b']\<close> inside the node \<open>[a,b]\<close> can capture
  ALL \<open>v = Bernstein_changes p a b P\<close> variations only if there is no sign change of \<open>P\<close> OUTSIDE the
  window (in \<open>[a,a']\<close> or \<open>[b',b]\<close>). Contrapositive (the impl reject filter): a sign change just
  outside the window forces \<open>Bernstein_changes p a' b' P < v\<close>, so the window CANNOT accept and the
  costly carried-init + exact count can be skipped. Proof: a sign change gives a root outside
  (IVT), which makes the outside sub-interval's count \<open>\<ge> 1\<close> (@{thm [source]
  Bernstein_changes_pos_of_root}), and subadditivity (@{thm [source] Bernstein_changes_split})
  then bounds the window count below the node count. This is a NECESSARY condition for
  \<open>count = v\<close>, so as an impl fast-reject it preserves the exact \<open>Some \<longleftrightarrow> count = v\<close> window
  contract — the abstract semantics are unchanged.\<close>

lemma poly_sign_change_root:
  fixes P :: "real poly"
  assumes "a < b" and "poly P a * poly P b < 0"
  shows "\<exists>x. a < x \<and> x < b \<and> poly P x = 0"
  using assms by (metis mult_less_0_iff poly_IVT_neg poly_IVT_pos)

lemma bernstein_window_outside_root_reject:
  fixes P :: "real poly"
  assumes deg: "degree P \<le> p" and P0: "P \<noteq> 0"
    and box: "a \<le> a'" "a' < b'" "b' \<le> b"
    and sc: "poly P a * poly P a' < 0 \<or> poly P b' * poly P b < 0"
  shows "Bernstein_changes p a' b' P < Bernstein_changes p a b P"
proof -
  from box have abb: "a < b" by simp
  have bc_nn: "\<And>x y. 0 \<le> Bernstein_changes p x y P"
    by (simp add: Bernstein_changes_def changes_nonneg)
  from sc show ?thesis
  proof
    assume L: "poly P a * poly P a' < 0"
    have aa': "a < a'" using box(1) L by (smt (verit) mult_less_0_iff)
    have ab': "a < b'" using aa' box(2) by linarith
    obtain x where root: "a < x" "x < a'" "poly P x = 0"
      using poly_sign_change_root[OF aa' L] by blast
    have pos: "Bernstein_changes p a a' P \<noteq> 0"
      by (rule Bernstein_changes_pos_of_root[OF deg P0 aa' root(3) root(1) root(2)])
    have s1: "Bernstein_changes p a a' P + Bernstein_changes p a' b' P
        \<le> Bernstein_changes p a b' P"
      by (rule Bernstein_changes_split[OF aa' box(2) deg])
    have s2: "Bernstein_changes p a b' P \<le> Bernstein_changes p a b P"
    proof (cases "b' = b")
      case True thus ?thesis by simp
    next
      case False
      hence b'b: "b' < b" using box(3) by simp
      have "Bernstein_changes p a b' P + Bernstein_changes p b' b P
          \<le> Bernstein_changes p a b P"
        by (rule Bernstein_changes_split[OF ab' b'b deg])
      thus ?thesis using bc_nn by (smt (verit))
    qed
    from pos s1 s2 show ?thesis using bc_nn by (smt (verit))
  next
    assume R: "poly P b' * poly P b < 0"
    have b'b: "b' < b" using box(3) R by (smt (verit) mult_less_0_iff)
    have a'b: "a' < b" using box(2) b'b by linarith
    obtain x where root: "b' < x" "x < b" "poly P x = 0"
      using poly_sign_change_root[OF b'b R] by blast
    have pos: "Bernstein_changes p b' b P \<noteq> 0"
      by (rule Bernstein_changes_pos_of_root[OF deg P0 b'b root(3) root(1) root(2)])
    have s1: "Bernstein_changes p a' b' P + Bernstein_changes p b' b P
        \<le> Bernstein_changes p a' b P"
      by (rule Bernstein_changes_split[OF box(2) b'b deg])
    have s2: "Bernstein_changes p a' b P \<le> Bernstein_changes p a b P"
    proof (cases "a = a'")
      case True thus ?thesis by simp
    next
      case False
      hence "a < a'" using box(1) by simp
      have "Bernstein_changes p a a' P + Bernstein_changes p a' b P
          \<le> Bernstein_changes p a b P"
        by (rule Bernstein_changes_split[OF \<open>a < a'\<close> a'b deg])
      thus ?thesis using bc_nn by (smt (verit))
    qed
    from pos s1 s2 show ?thesis using bc_nn by (smt (verit))
  qed
qed

end
